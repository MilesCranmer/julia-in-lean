import JuliaLean.Core
import JuliaLean.base.reduce
import JuliaLean.base.hashing

namespace JuliaLean.base.hamt

open JuliaLean

variable {K V Q α : Type}

abbrev BITMAP := Nat

def ENTRY_COUNT : Nat := 32
def NBITS : Nat := 64
def BITS_PER_LEVEL : Nat := 5
def LEVEL_MASK : Nat := 31
def MAX_SHIFT : Nat := 55
def MASK32 : Nat := 2 ^ 32 - 1

def u32 (x : Nat) : BITMAP := x % (2 ^ 32)
def shiftLeftNat (x n : Nat) : Nat := x * 2 ^ n
def shiftRightNat (x n : Nat) : Nat := x / 2 ^ n

def countOnes : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % 2 + countOnes n (x / 2)

inductive HamtError where
  | bounds
  | undefinedReference
  | assertion
  | typeError
  | perfectHashCollision
  deriving Repr, DecidableEq

/-- Julia's `jl_object_id` runtime binding (`src/builtins.c:594-597`); it returns the object-identity word used to seed a HAMT `HashState`. -/
structure HamtObjectIdRuntime (K : Type) where
  objectid : K → JInt .u64

structure Leaf (K V : Type) where
  key : K
  val : V

inductive Entry (K V : Type) where
  | leaf (value : Leaf K V)
  | trie (handle : Nat)

structure HAMTNode (K V : Type) where
  data : Nat
  bitmap : BITMAP

structure HamtHeap (K V : Type) where
  vectors : List (List (Option (Entry K V)))
  nodes : List (HAMTNode K V)

abbrev HAMT (_K _V : Type) := Nat
abbrev HamtM (K V : Type) (α : Type) := ExceptT HamtError (StateM (HamtHeap K V)) α

structure VectorOps (K V : Type) where
  allocate : List (Option (Entry K V)) → HamtM K V Nat
  copy : Nat → HamtM K V Nat
  length : Nat → HamtM K V Nat
  get : Nat → Nat → HamtM K V (Entry K V)
  set : Nat → Nat → Entry K V → HamtM K V Unit
  insert : Nat → Nat → Entry K V → HamtM K V Unit

structure HashState (K : Type) where
  key : K
  hash : JInt .u64
  depth : Nat
  shift : Nat

structure BitmapIndex where
  x : Nat
  deriving Repr, BEq, DecidableEq

structure PathResult (K V : Type) where
  found : Bool
  present : Bool
  trie : HAMT K V
  index : Nat
  bi : BitmapIndex
  top : HAMT K V
  hash : HashState K

structure IterState (K V : Type) where
  frames : List (Nat × Nat)

def HamtHeap.empty : HamtHeap K V := ⟨[], []⟩

def runHamt (action : HamtM K V α) (heap : HamtHeap K V) : Except HamtError α × HamtHeap K V :=
  action.run.run heap

abbrev PartialHamtM (K V : Type) (α : Type) :=
  HamtHeap K V → Option (Except HamtError α × HamtHeap K V)

def runPartialHamt (action : PartialHamtM K V α) (heap : HamtHeap K V) :
    Option (Except HamtError α × HamtHeap K V) :=
  action heap

def heapVectorSlots (handle : Nat) : HamtM K V (List (Option (Entry K V))) := do
  match (← get).vectors[handle]? with
  | some slots => pure slots
  | none => throw .bounds

def heapVectorAllocate (slots : List (Option (Entry K V))) : HamtM K V Nat := do
  let heap ← get
  let handle := heap.vectors.length
  set { heap with vectors := heap.vectors ++ [slots] }
  pure handle

def heapVectorCopy (handle : Nat) : HamtM K V Nat := do
  let slots ← heapVectorSlots handle
  heapVectorAllocate slots

def heapVectorLength (handle : Nat) : HamtM K V Nat := do
  return (← heapVectorSlots handle).length

def heapVectorGet (handle : Nat) (oneBased : Nat) : HamtM K V (Entry K V) := do
  let slots ← heapVectorSlots handle
  if oneBased = 0 then throw .bounds
  match slots[oneBased - 1]? with
  | none => throw .bounds
  | some none => throw .undefinedReference
  | some (some entry) => pure entry

def heapVectorSet (handle : Nat) (oneBased : Nat) (entry : Entry K V) : HamtM K V Unit := do
  let heap ← get
  match heap.vectors[handle]? with
  | none => throw .bounds
  | some slots =>
      if oneBased = 0 || oneBased > slots.length then throw .bounds
      set { heap with vectors := heap.vectors.set handle (slots.set (oneBased - 1) (some entry)) }

def heapVectorInsert (handle : Nat) (oneBased : Nat) (entry : Entry K V) : HamtM K V Unit := do
  let heap ← get
  match heap.vectors[handle]? with
  | none => throw .bounds
  | some slots =>
      if oneBased = 0 || oneBased > slots.length + 1 then throw .bounds
      set { heap with vectors := heap.vectors.set handle (slots.insertIdx (oneBased - 1) (some entry)) }

def heapVectorOps : VectorOps K V where
  allocate := heapVectorAllocate
  copy := heapVectorCopy
  length := heapVectorLength
  get := heapVectorGet
  set := heapVectorSet
  insert := heapVectorInsert

def readNode (handle : HAMT K V) : HamtM K V (HAMTNode K V) := do
  match (← get).nodes[handle]? with
  | some node => pure node
  | none => throw .bounds

def nodeBitmap (handle : HAMT K V) : HamtM K V BITMAP := do
  return (← readNode handle).bitmap

def nodeData (handle : HAMT K V) : HamtM K V Nat := do
  return (← readNode handle).data

namespace HAMT

/--
Julia source: base/hamt.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    HAMT{K,V}(data, bitmap) where {K,V} = new{K,V}(data, bitmap)
```
-/

def inner (data : Nat) (bitmap : BITMAP) : HamtM K V (HAMT K V) := do
  let heap ← get
  let handle := heap.nodes.length
  set { heap with nodes := heap.nodes ++ [HAMTNode.mk data bitmap] }
  pure handle

/--
Julia source: base/hamt.jl:66-66 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    HAMT{K, V}() where {K, V} = new{K,V}(Vector{Union{Leaf{K, V}, HAMT{K, V}}}(undef, 0), zero(BITMAP))
```
-/

def emptyConstructor (vectors : VectorOps K V) : HamtM K V (HAMT K V) := do
  let data ← vectors.allocate []
  let heap ← get
  let handle := heap.nodes.length
  set { heap with nodes := heap.nodes ++ [HAMTNode.mk data 0] }
  pure handle

end HAMT

/--
Julia source: base/hamt.jl:69-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@assume_effects :nothrow :effect_free function init_hamt(K, V, k, v)
    # For a single element we can't have a 'hash-collision
    trie = HAMT{K,V}(Vector{Union{Leaf{K, V}, HAMT{K, V}}}(undef, 1), zero(BITMAP))
    trie.data[1] = Leaf{K,V}(k,v)
    return trie
end
```
-/

def init_hamt (vectors : VectorOps K V) (key : K) (value : V) : HamtM K V (HAMT K V) := do
  let data ← vectors.allocate [none]
  let heap ← get
  let trie := heap.nodes.length
  set { heap with nodes := heap.nodes ++ [HAMTNode.mk data 0] }
  let _ ← vectors.set data 1 (.leaf ⟨key, value⟩)
  pure trie

/-! ## Hash states and bitmap indexing -/
/--
Julia source: base/hamt.jl:93-93 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
HashState(key) = HashState(key, objectid(key), 0, 0)
```
-/

def HashState.fromKey (ops : HamtObjectIdRuntime K) (key : K) : HashState K :=
  ⟨key, ops.objectid key, 0, 0⟩

/--
Julia source: base/hamt.jl:103-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function next(h::HashState{K}) where {K}
    depth = h.depth + 1
    shift = h.shift + BITS_PER_LEVEL
    # Assert disabled for effect precision
    # @assert h.shift <= MAX_SHIFT
    if shift > MAX_SHIFT
        # Note we use `UInt(depth ÷ BITS_PER_LEVEL)` to seed the hash function
        # the hash docs, do we need to hash `UInt(depth ÷ BITS_PER_LEVEL)` first?
        h_hash = hash(objectid(h.key), UInt(depth ÷ BITS_PER_LEVEL))
        shift = 0
    else
        h_hash = h.hash
    end
    return HashState{K}(h.key, h_hash, depth, shift)
end
```
-/

def next (ops : HamtObjectIdRuntime K) (h : HashState K) : HashState K :=
  let depth := h.depth + 1
  let shift := h.shift + BITS_PER_LEVEL
  if shift > MAX_SHIFT then
    let hHash := JuliaLean.base.hashing.hashUInt64 (ops.objectid h.key)
      (JInt.wrap .u64 (depth / BITS_PER_LEVEL))
    ⟨h.key, hHash, depth, 0⟩
  else
    ⟨h.key, h.hash, depth, shift⟩

/--
Julia source: base/hamt.jl:94-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@assume_effects :terminates_locally function HashState{K}(@nospecialize(other::HashState), @nospecialize(key)) where {K}
    h = HashState{K}(key, objectid(key), 0, 0)
    while h.depth !== other.depth
        h = next(h)
    end
    return h
end
```
-/

def HashState.fromOtherAtDepth (ops : HamtObjectIdRuntime K) (other : HashState Q) (key : K) : HashState K := Id.run do
  let mut h := HashState.fromKey ops key
  while h.depth != other.depth do
    h := next ops h
  return h

/--
Julia source: base/hamt.jl:101-101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@assume_effects :terminates_locally HashState(other::HashState, key) = HashState{typeof(key)}(other, key)
```
-/

def HashState.inferAtDepth (ops : HamtObjectIdRuntime K) (other : HashState Q) (key : K) : HashState K :=
  HashState.fromOtherAtDepth ops other key

/--
Julia source: base/hamt.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitmapIndex(h::HashState) = BitmapIndex((h.hash >> h.shift) & LEVEL_MASK)
```
-/

def BitmapIndex.fromHash (h : HashState K) : BitmapIndex :=
  ⟨Nat.land (shiftRightNat h.hash.val.toNat h.shift) LEVEL_MASK⟩

/--
Julia source: base/hamt.jl:124-124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.:(<<)(v, bi::BitmapIndex) = v << bi.x
```
-/

def shiftLeftAt (shiftLeft : α → Nat → α) (value : α) (bi : BitmapIndex) : α :=
  shiftLeft value bi.x

/--
Julia source: base/hamt.jl:125-125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.:(>>)(v, bi::BitmapIndex) = v >> bi.x
```
-/

def shiftRightAt (shiftRight : α → Nat → α) (value : α) (bi : BitmapIndex) : α :=
  shiftRight value bi.x

/-! ## Bitmap operations -/
/--
Julia source: base/hamt.jl:127-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isset(trie::HAMT, bi::BitmapIndex) = isodd(trie.bitmap >> bi)
```
-/

def isset (trie : HAMT K V) (bi : BitmapIndex) : HamtM K V Bool := do
  let bitmap ← nodeBitmap trie
  pure ((shiftRightNat bitmap bi.x) % 2 == 1)

/--
Julia source: base/hamt.jl:128-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function set!(trie::HAMT, bi::BitmapIndex)
    trie.bitmap |= (UInt32(1) << bi)
    # Invariant: count_ones(trie.bitmap) == Base.length(trie.data)
end
```
-/

def set! (trie : HAMT K V) (bi : BitmapIndex) : HamtM K V BITMAP := do
  let node ← readNode trie
  let bitmap := u32 (Nat.lor node.bitmap (shiftLeftNat 1 bi.x))
  let heap ← get
  set { heap with nodes := heap.nodes.set trie { node with bitmap := bitmap } }
  pure bitmap

/--
Julia source: base/hamt.jl:133-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unset!(trie::HAMT, bi::BitmapIndex)
    trie.bitmap &= ~(UInt32(1) << bi)
    # Invariant: count_ones(trie.bitmap) == Base.length(trie.data)
end
```
-/

def unset! (trie : HAMT K V) (bi : BitmapIndex) : HamtM K V BITMAP := do
  let node ← readNode trie
  let bitmap := Nat.land node.bitmap (Nat.xor MASK32 (shiftLeftNat 1 bi.x))
  let heap ← get
  set { heap with nodes := heap.nodes.set trie { node with bitmap := bitmap } }
  pure bitmap

/--
Julia source: base/hamt.jl:138-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function entry_index(trie::HAMT, bi::BitmapIndex)
    mask = (UInt32(1) << bi.x) - UInt32(1)
    count_ones(trie.bitmap & mask) + 1
end
```
-/

def entry_index (trie : HAMT K V) (bi : BitmapIndex) : HamtM K V Nat := do
  let bitmap ← nodeBitmap trie
  let mask := shiftLeftNat 1 bi.x - 1
  pure (countOnes 32 (Nat.land bitmap mask) + 1)

/--
Julia source: base/hamt.jl:143-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
islevel_empty(trie::HAMT) = trie.bitmap == 0
```
-/

def islevel_empty (trie : HAMT K V) : HamtM K V Bool := do
  return (← nodeBitmap trie) == 0

/--
Julia source: base/hamt.jl:144-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
islevel_empty(::Leaf) = false
```
-/

def islevel_empty_leaf (_leaf : Leaf K V) : Bool := false

/--
Julia source: base/hamt.jl:76-81 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@assume_effects :effect_free function HAMT{K,V}((k,v)::Pair{K,V}) where {K, V}
    trie = init_hamt(K, V, k, v)
    bi = BitmapIndex(HashState(k))
    set!(trie, bi)
    return trie
end
```
-/

def HAMT.typedPairConstructor (vectors : VectorOps K V) (ops : HamtObjectIdRuntime K) (pair : K × V) : HamtM K V (HAMT K V) := do
  let trie ← init_hamt vectors pair.1 pair.2
  let bi := BitmapIndex.fromHash (HashState.fromKey ops pair.1)
  let _ ← set! trie bi
  pure trie

/--
Julia source: base/hamt.jl:82-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
HAMT{K,V}(kv::Pair) where {K, V} = HAMT{K,V}(convert(Pair{K,V}, kv))
```
-/

def HAMT.convertPair (vectors : VectorOps K V) (ops : HamtObjectIdRuntime K)
    (convert : Q → K × V) (kv : Q) : HamtM K V (HAMT K V) :=
  HAMT.typedPairConstructor vectors ops (convert kv)

/--
Julia source: base/hamt.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
HAMT(pair::Pair{K,V}) where {K, V} = HAMT{K,V}(pair)
```
-/

def HAMT.inferPair (vectors : VectorOps K V) (ops : HamtObjectIdRuntime K) (pair : K × V) :
    HamtM K V (HAMT K V) :=
  HAMT.convertPair vectors ops id pair

/-! ## Path traversal and insertion -/
/--
Julia source: base/hamt.jl:146-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    path(trie, h, copyf)::(found, present, trie, i, top, level)

Internal function that walks a HAMT and finds the slot for hash.
Returns if a value is `present` and a value is `found`.

It returns the `trie` and the index `i` into `trie.data`, as well
as the current `level`.

If a copy function is provided `copyf` use the return `top` for the
new persistent tree.
"""
@inline Base.@assume_effects :noub :terminates_locally function path(trie::HAMT{K,V}, h::HashState, copy=false) where {K, V}
    if copy
        trie = top = HAMT{K,V}(Base.copy(trie.data), trie.bitmap)
    else
        trie = top = trie
    end
    while true
        bi = BitmapIndex(h)
        i = entry_index(trie, bi)
        if isset(trie, bi)
            next = @inbounds trie.data[i]
            if next isa Leaf{K,V}
                # Check if key match if not we will need to grow.
                found = next.key === h.key
                return found, true, trie, i, bi, top, h
            end
            if copy
                next = HAMT{K,V}(Base.copy(next.data), next.bitmap)
                # :noub because entry_index is guaranteed to be inbounds for trie.data
                @inbounds trie.data[i] = next
            end
            trie = next::HAMT{K,V}
        else
            # found empty slot
            return true, false, trie, i, bi, top, h
        end
        h = HashArrayMappedTries.next(h)
    end
end
```
-/

def path (vectors : VectorOps K V) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (trie : HAMT K V) (initialHash : HashState K) (copy : Bool := false) :
    HamtM K V (PathResult K V) := do
  let mut current := trie
  let mut top := trie
  if copy then
    let node ← readNode trie
    let data ← vectors.copy node.data
    top ← HAMT.inner data node.bitmap
    current := top
  let mut h := initialHash
  let mut result : Option (PathResult K V) := none
  while result.isNone do
    let bi := BitmapIndex.fromHash h
    let i ← entry_index current bi
    if ← isset current bi then
      let node ← readNode current
      match ← vectors.get node.data i with
      | .leaf leaf =>
          result := some ⟨same leaf.key h.key, true, current, i, bi, top, h⟩
      | .trie child =>
          let nextTrie ← if copy then do
            let childNode ← readNode child
            let childData ← vectors.copy childNode.data
            let childCopy ← HAMT.inner childData childNode.bitmap
            let parentData ← nodeData current
            let _ ← vectors.set parentData i (.trie childCopy)
            pure childCopy
          else pure child
          current := nextTrie
          h := next ops h
    else
      result := some ⟨true, false, current, i, bi, top, h⟩
  match result with
  | some value => pure value
  | none => throw .bounds

/--
Julia source: base/hamt.jl:188-240 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
Internal function that given an obtained path, either set the value
or grows the HAMT by inserting a new trie instead.
"""
@inline @Base.assume_effects :terminates_locally function insert!(found, present, trie::HAMT{K,V}, i, bi, h, val) where {K,V}
    if found # we found a slot, just set it to the new leaf
        # replace or insert
        if present # replace
            @inbounds trie.data[i] = Leaf{K, V}(h.key, val)
        else
            Base.insert!(trie.data, i, Leaf{K, V}(h.key, val))
        end
        set!(trie, bi)
    else
        @assert present "!found && !present"
        # collision -> grow
        leaf = @inbounds trie.data[i]::Leaf{K,V}
        leaf_h = HashState{K}(h, leaf.key)
        if leaf_h.hash == h.hash
            error("Perfect hash collision")
        end
        while true
            new_trie = HAMT{K, V}()
            if present
                @inbounds trie.data[i] = new_trie
            else
                i = entry_index(trie, bi)
                Base.insert!(trie.data, i, new_trie)
            end
            set!(trie, bi)

            h = next(h)
            leaf_h = next(leaf_h)
            bi_new = BitmapIndex(h)
            bi_old = BitmapIndex(leaf_h)
            if bi_new == bi_old # collision in new trie -> retry
                trie = new_trie
                bi = bi_new
                present = false
                continue
            end
            i_new = entry_index(new_trie, bi_new)
            Base.insert!(new_trie.data, i_new, Leaf{K, V}(h.key, val))
            set!(new_trie, bi_new)

            i_old = entry_index(new_trie, bi_old)
            Base.insert!(new_trie.data, i_old, leaf)
            set!(new_trie, bi_old)

            break
        end
    end
end
```
-/

def insert! (vectors : VectorOps K V) (ops : HamtObjectIdRuntime K)
    (found present : Bool) (trie : HAMT K V) (initialIndex : Nat) (initialBi : BitmapIndex)
    (initialHash : HashState K) (value : V) : PartialHamtM K V (Option BITMAP) := fun heap =>
  if found then
    some (runHamt (do
      let data ← nodeData trie
      if present then
        vectors.set data initialIndex (.leaf ⟨initialHash.key, value⟩)
      else
        vectors.insert data initialIndex (.leaf ⟨initialHash.key, value⟩)
      return some (← set! trie initialBi)) heap)
  else
    let prelude : HamtM K V (Leaf K V × HashState K) := do
      if !present then throw .assertion
      let node ← readNode trie
      let leafEntry ← vectors.get node.data initialIndex
      let leaf ← match leafEntry with
        | .leaf leaf => pure leaf
        | .trie _ => throw .typeError
      let leafHash := HashState.fromOtherAtDepth ops initialHash leaf.key
      if leafHash.hash == initialHash.hash then throw .perfectHashCollision
      return (leaf, leafHash)
    match runHamt prelude heap with
    | (.error error, heap') => some (.error error, heap')
    | (.ok (leaf, leafHash), heap') =>
      let CollisionState := HashState K × HashState K × HAMT K V × BitmapIndex × Bool × Bool
      let collisionStep : CollisionState → HamtM K V (ForInStep CollisionState) :=
        fun (h, leafHash, current, bi, isPresent, finished) => do
          if finished then
            return .done (h, leafHash, current, bi, isPresent, finished)
          let newTrie ← HAMT.emptyConstructor vectors
          let node ← readNode current
          let slot ← if isPresent then pure initialIndex else entry_index current bi
          if isPresent then
            vectors.set node.data slot (.trie newTrie)
          else
            vectors.insert node.data slot (.trie newTrie)
          let _ ← set! current bi
          let h := next ops h
          let leafHash := next ops leafHash
          let biNew := BitmapIndex.fromHash h
          let biOld := BitmapIndex.fromHash leafHash
          if biNew == biOld then
            return .yield (h, leafHash, newTrie, biNew, false, finished)
          else
            let newData ← nodeData newTrie
            let iNew ← entry_index newTrie biNew
            vectors.insert newData iNew (.leaf ⟨h.key, value⟩)
            let _ ← set! newTrie biNew
            let iOld ← entry_index newTrie biOld
            vectors.insert newData iOld (.leaf leaf)
            let _ ← set! newTrie biOld
            return .yield (h, leafHash, current, bi, isPresent, true)
      let step (input : CollisionState × HamtHeap K V) :
          Except (HamtError × HamtHeap K V)
            (Sum (CollisionState × HamtHeap K V) (CollisionState × HamtHeap K V)) :=
        let (outcome, heapAfter) := runHamt (collisionStep input.1) input.2
        match outcome with
        | .error error => .error (error, heapAfter)
        | .ok (.done state') => .ok (.inl (state', heapAfter))
        | .ok (.yield state') => .ok (.inr (state', heapAfter))
      match JuliaLean.base.reduce.whileLoop step
          ((initialHash, leafHash, trie, initialBi, present, false), heap') with
      | none => none
      | some (.error (error, heapAfter)) => some (.error error, heapAfter)
      | some (.ok (_, heapAfter)) => some (.ok none, heapAfter)

def persistentInsert (vectors : VectorOps K V) (same : K → K → Bool) (ops : HamtObjectIdRuntime K)
    (trie : HAMT K V) (key : K) (value : V) : PartialHamtM K V (HAMT K V) := fun heap =>
  match runHamt (path vectors same ops trie (HashState.fromKey ops key) true) heap with
  | (.error error, heap1) => some (.error error, heap1)
  | (.ok pathResult, heap1) =>
      (insert! vectors ops pathResult.found pathResult.present pathResult.trie
        pathResult.index pathResult.bi pathResult.hash value heap1).map fun
        | (.error error, heap2) => (.error error, heap2)
        | (.ok _, heap2) => (.ok pathResult.top, heap2)

def PathResult.value? (vectors : VectorOps K V) (result : PathResult K V) : HamtM K V (Option V) := do
  if result.found && result.present then
    let node ← readNode result.trie
    match ← vectors.get node.data result.index with
    | .leaf leaf => pure (some leaf.val)
    | .trie _ => pure none
  else pure none

/-! ## Length, emptiness, and iteration -/
/--
Julia source: base/hamt.jl:242-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.length(::Leaf) = 1
```
-/

def lengthLeaf (_leaf : Leaf K V) : Nat := 1

mutual
  /--
Julia source: base/hamt.jl:243-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.length(trie::HAMT) = sum((length(trie.data[i]) for i in eachindex(trie.data)), init=0)
```
  -/
  def lengthHAMT (vectors : VectorOps K V) (trie : HAMT K V)
      (heap : HamtHeap K V) : Option (Except HamtError (JInt .i64) × HamtHeap K V) :=
    match runHamt (readNode trie) heap with
    | (.error error, heap') => some (.error error, heap')
    | (.ok node, heap') =>
      match runHamt (vectors.length node.data) heap' with
      | (.error error, heap'') => some (.error error, heap'')
      | (.ok len, heap'') => lengthEntries vectors node.data len 1 (JInt.lit .i64 0) heap''
  partial_fixpoint

  def lengthEntries (vectors : VectorOps K V) (data len i : Nat) (total : JInt .i64)
      (heap : HamtHeap K V) : Option (Except HamtError (JInt .i64) × HamtHeap K V) :=
    if i ≤ len then
      match runHamt (vectors.get data i) heap with
      | (.error error, heap') => some (.error error, heap')
      | (.ok (.leaf leaf), heap') =>
        lengthEntries vectors data len (i + 1)
          (JuliaLean.base.int.add total (JInt.lit .i64 (Int.ofNat (lengthLeaf leaf)))) heap'
      | (.ok (.trie child), heap') => do
        let (outcome, heap'') ← lengthHAMT vectors child heap'
        match outcome with
        | .error error => some (.error error, heap'')
        | .ok childLength =>
          lengthEntries vectors data len (i + 1) (JuliaLean.base.int.add total childLength) heap''
    else some (.ok total, heap)
  partial_fixpoint
end

/--
Julia source: base/hamt.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.isempty(::Leaf) = false
```
-/

def isemptyLeaf (_leaf : Leaf K V) : Bool := false

mutual
  /--
Julia source: base/hamt.jl:246-251 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.isempty(trie::HAMT)
    if islevel_empty(trie)
        return true
    end
    return all(isempty(trie.data[i]) for i in eachindex(trie.data))
end
```
  -/
  def isemptyHAMT (vectors : VectorOps K V) (trie : HAMT K V)
      (heap : HamtHeap K V) : Option (Except HamtError Bool × HamtHeap K V) :=
    match runHamt (islevel_empty trie) heap with
    | (.error error, heap') => some (.error error, heap')
    | (.ok true, heap') => some (.ok true, heap')
    | (.ok false, heap') =>
      match runHamt (readNode trie) heap' with
      | (.error error, heap'') => some (.error error, heap'')
      | (.ok node, heap'') =>
        match runHamt (vectors.length node.data) heap'' with
        | (.error error, heap''') => some (.error error, heap''')
        | (.ok len, heap''') => isemptyEntries vectors node.data len 1 true heap'''
  partial_fixpoint

  def isemptyEntries (vectors : VectorOps K V) (data len i : Nat) (empty : Bool)
      (heap : HamtHeap K V) : Option (Except HamtError Bool × HamtHeap K V) :=
    if i ≤ len && empty then
      match runHamt (vectors.get data i) heap with
      | (.error error, heap') => some (.error error, heap')
      | (.ok (.leaf leaf), heap') =>
        isemptyEntries vectors data len (i + 1) (isemptyLeaf leaf) heap'
      | (.ok (.trie child), heap') => do
        let (outcome, heap'') ← isemptyHAMT vectors child heap'
        match outcome with
        | .error error => some (.error error, heap'')
        | .ok childEmpty => isemptyEntries vectors data len (i + 1) childEmpty heap''
    else some (.ok empty, heap)
  partial_fixpoint
end

/--
Julia source: base/hamt.jl:254-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Base.iterate(trie::HAMT, state=nothing)
    if state === nothing
        state = (;parent=nothing, trie, i=1)
    end
    while state !== nothing
        i = state.i
        if i > Base.length(state.trie.data)
            state = state.parent
            continue
        end
        trie = state.trie.data[i]
        state = (;parent=state.parent, trie=state.trie, i=i+1)
        if trie isa Leaf
            return (trie.key => trie.val, state)
        else
            # we found a new level
            state = (;parent=state, trie, i=1)
            continue
        end
    end
    return nothing
end
```
-/

def iterate (vectors : VectorOps K V) (trie : HAMT K V)
    (state : Option (IterState K V) := none) :
    HamtM K V (Option ((K × V) × IterState K V)) := do
  let rootData ← nodeData trie
  let mut frames := match state with
    | some state => state.frames
    | none => [(rootData, 1)]
  let mut result : Option ((K × V) × IterState K V) := none
  while result.isNone && !frames.isEmpty do
    match frames with
    | [] => pure ()
    | (data, i) :: parents =>
        if i > (← vectors.length data) then
          frames := parents
        else
          let entry ← vectors.get data i
          frames := (data, i + 1) :: parents
          match entry with
          | .leaf leaf => result := some ((leaf.key, leaf.val), ⟨frames⟩)
          | .trie child =>
              let childData ← nodeData child
              frames := (childData, 1) :: frames
  pure result

partial def toList (vectors : VectorOps K V) (trie : HAMT K V) : HamtM K V (List (K × V)) := do
  let node ← readNode trie
  let len ← vectors.length node.data
  let mut pairs := []
  let mut i := 1
  while i ≤ len do
    match ← vectors.get node.data i with
    | .leaf leaf => pairs := pairs ++ [(leaf.key, leaf.val)]
    | .trie child => pairs := pairs ++ (← toList vectors child)
    i := i + 1
  pure pairs

end JuliaLean.base.hamt

namespace JuliaLean.DictsCov.HamtRows


abbrev R (α : Type) := Except String α

inductive Tree (K V : Type) where
  | leaf (key : K) (value : V)
  | branch (data : List (Tree K V)) (bitmap : Nat)
  deriving Repr

def mask32 : Nat := 2 ^ 32 - 1

def levelMask : Nat := 31

def bitsPerLevel : Nat := 5

def maxShift : Nat := 55

def u32 (x : Nat) : Nat := x % (2 ^ 32)

def shiftLeft (v n : Nat) : Nat := v * 2 ^ n

def shiftRight (v n : Nat) : Nat := v / 2 ^ n

def bitSet (bitmap i : Nat) : Nat := u32 (Nat.lor bitmap (shiftLeft 1 i))

def bitUnset (bitmap i : Nat) : Nat :=
  Nat.land bitmap (Nat.xor mask32 (shiftLeft 1 i))

def countOnes : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % 2 + countOnes n (x / 2)

structure HashState (K : Type) where
  key : K
  hash : Nat
  depth : Nat
  shift : Nat
  deriving Repr, DecidableEq

structure BitmapIndex where
  x : Nat
  deriving Repr, DecidableEq

/-- Inner HAMT constructor, `base/hamt.jl:65`. -/
def method65 (data : List (Tree K V)) (bitmap : Nat) : Tree K V := .branch data bitmap

/-- Empty HAMT constructor, `base/hamt.jl:66`. -/
def method66 : Tree K V := .branch [] 0

/-- Allocate a one-element, unset-bitmap HAMT, `base/hamt.jl:69-74`. -/
def method69 (k : K) (v : V) : Tree K V := .branch [.leaf k v] 0

/-- Default HashState constructor, `base/hamt.jl:93`. -/
def method93 (objectid : K → Nat) (key : K) : HashState K :=
  { key := key, hash := objectid key, depth := 0, shift := 0 }

/-- Advance a hash state, `base/hamt.jl:103-117`. -/
def method103 (rehash : Nat → Nat → Nat) (h : HashState K) : HashState K :=
  let depth := h.depth + 1
  let shift := h.shift + bitsPerLevel
  if shift > maxShift then
    { key := h.key, hash := rehash h.hash (depth / bitsPerLevel), depth := depth, shift := 0 }
  else
    { key := h.key, hash := h.hash, depth := depth, shift := shift }

def advanceToDepth (rehash : Nat → Nat → Nat) : Nat → HashState K → HashState K
  | 0, h => h
  | fuel + 1, h => method103 rehash (advanceToDepth rehash fuel h)

/-- Depth-aligning HashState constructor, `base/hamt.jl:94-100`. -/
def method94 (objectid : K → Nat) (rehash : Nat → Nat → Nat)
    (other : HashState Q) (key : K) : HashState K :=
  advanceToDepth rehash other.depth (method93 objectid key)

/-- Type-inferring HashState wrapper, `base/hamt.jl:101`. -/
def method101 (construct : HashState Q → K → HashState K) (other : HashState Q) (key : K) :=
  construct other key

/-- BitmapIndex constructor, `base/hamt.jl:122`. -/
def method122 (h : HashState K) : BitmapIndex :=
  ⟨Nat.land (shiftRight h.hash h.shift) levelMask⟩

/-- Bitmap-indexed left shift, `base/hamt.jl:124`. -/
def method124 (v : Nat) (bi : BitmapIndex) : Nat := shiftLeft v bi.x

/-- Bitmap-indexed right shift, `base/hamt.jl:125`. -/
def method125 (v : Nat) (bi : BitmapIndex) : Nat := shiftRight v bi.x

/-- Test a HAMT bitmap bit, `base/hamt.jl:127`. -/
def method127 : Tree K V → BitmapIndex → Bool
  | .leaf _ _, _ => false
  | .branch _ bitmap, bi => (shiftRight bitmap bi.x) % 2 == 1

/-- Set a HAMT bitmap bit, `base/hamt.jl:128-131`. -/
def method128 : Tree K V → BitmapIndex → Tree K V
  | .leaf k v, _ => .leaf k v
  | .branch data bitmap, bi => .branch data (bitSet bitmap bi.x)

/-- Unset a HAMT bitmap bit, `base/hamt.jl:133-136`. -/
def method133 : Tree K V → BitmapIndex → Tree K V
  | .leaf k v, _ => .leaf k v
  | .branch data bitmap, bi => .branch data (bitUnset bitmap bi.x)

/-- Sparse-array entry index, `base/hamt.jl:138-141`. -/
def method138 : Tree K V → BitmapIndex → Nat
  | .leaf _ _, _ => 1
  | .branch _ bitmap, bi =>
      let mask := shiftLeft 1 bi.x - 1
      countOnes 32 (Nat.land bitmap mask) + 1

/-- HAMT-level emptiness, `base/hamt.jl:143`. -/
def method143 : Tree K V → Bool
  | .leaf _ _ => false
  | .branch _ bitmap => bitmap == 0

/-- Leaf-level emptiness, `base/hamt.jl:144`. -/
def method144 (_leaf : K × V) : Bool := false

structure PathResult (K V : Type) where
  found : Bool
  present : Bool
  trie : Tree K V
  index : Nat
  bi : BitmapIndex
  top : Tree K V
  hash : HashState K
  deriving Repr

def replaceAt (xs : List α) (oneBased : Nat) (x : α) : List α :=
  if oneBased == 0 then xs else xs.set (oneBased - 1) x

def pathLoop (same : K → K → Bool) (rehash : Nat → Nat → Nat) (copy : Bool) :
    Nat → Tree K V → Tree K V → HashState K → R (PathResult K V)
  | 0, _, _, _ => .error "path fuel exhausted"
  | fuel + 1, .leaf _ _, _, _ => .error "path expected HAMT"
  | fuel + 1, .branch data bitmap, top, h =>
      let bi := method122 h
      let i := method138 (.branch data bitmap) bi
      if method127 (.branch data bitmap) bi then
        match data[i - 1]? with
        | none => .error "bounds"
        | some (.leaf key value) =>
            .ok ⟨same key h.key, true, .branch data bitmap, i, bi, top, h⟩
        | some (.branch childData childBitmap) =>
            let child := .branch childData childBitmap
            let child := if copy then .branch childData childBitmap else child
            let data := if copy then replaceAt data i child else data
            pathLoop same rehash copy fuel child top (method103 rehash h)
      else .ok ⟨true, false, .branch data bitmap, i, bi, top, h⟩

/-- HAMT path search and optional copy, `base/hamt.jl:158-186`. -/
def method158 (same : K → K → Bool) (rehash : Nat → Nat → Nat) (fuel : Nat)
    (trie : Tree K V) (h : HashState K) (copy : Bool) : R (PathResult K V) :=
  let top := match trie with
    | .leaf k v => .leaf k v
    | .branch data bitmap => if copy then .branch data bitmap else trie
  pathLoop same rehash copy fuel top top h

/-- Typed-pair HAMT constructor, `base/hamt.jl:76-81`. -/
def method76 (objectid : K → Nat) (k : K) (v : V) : Tree K V :=
  let trie := method69 k v
  let bi := method122 (method93 objectid k)
  method128 trie bi

/-- Converting-pair HAMT constructor, `base/hamt.jl:82`. -/
def method82 {Q : Type} (convert : Q → K × V) (construct : K × V → Tree K V) (kv : Q) : Tree K V :=
  construct (convert kv)

/-- Type-inferring HAMT constructor, `base/hamt.jl:84`. -/
def method84 (construct : K × V → Tree K V) (pair : K × V) : Tree K V := construct pair

/-- Leaf length, `base/hamt.jl:242`. -/
def method242 (_leaf : K × V) : Nat := 1

def treeLength : Tree K V → Nat
  | .leaf _ _ => 1
  | .branch data _ => (data.map treeLength).foldl (· + ·) 0

/-- HAMT length, `base/hamt.jl:243`. -/
def method243 : Tree K V → Nat
  | .leaf _ _ => 1
  | .branch data _ => (data.map treeLength).foldl (· + ·) 0

/-- Leaf isempty, `base/hamt.jl:245`. -/
def method245 (_leaf : K × V) : Bool := false

mutual
  def treeEmpty : Tree K V → Bool
    | .leaf _ _ => false
    | .branch data bitmap => bitmap == 0 || treeListEmpty data

  def treeListEmpty : List (Tree K V) → Bool
    | [] => true
    | tree :: trees => treeEmpty tree && treeListEmpty trees
end

/-- HAMT isempty, `base/hamt.jl:246-251`. -/
def method246 : Tree K V → Bool
  | .leaf _ _ => false
  | .branch data bitmap => if bitmap == 0 then true else treeListEmpty data

abbrev Frame (K V : Type) := List (Tree K V) × Nat

abbrev IterState (K V : Type) := List (Frame K V)

def iterLoop : Nat → IterState K V → Option ((K × V) × IterState K V)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, (data, i) :: parent =>
      if i ≥ data.length then iterLoop fuel parent
      else match data[i]? with
        | none => none
        | some (.leaf key value) => some ((key, value), (data, i + 1) :: parent)
        | some (.branch child _) => iterLoop fuel ((child, 0) :: (data, i + 1) :: parent)

/-- DFS iterator, `base/hamt.jl:254-275`. -/
def method254 (fuel : Nat) (trie : Tree K V) (state : Option (IterState K V)) :
    Option ((K × V) × IterState K V) :=
  let state := match state with
    | some state => state
    | none => match trie with
      | .leaf k v => [([.leaf k v], 0)]
      | .branch data _ => [(data, 0)]
  iterLoop fuel state

end JuliaLean.DictsCov.HamtRows

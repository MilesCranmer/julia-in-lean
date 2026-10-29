import JuliaLean.Core

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

structure HashFunctions (K : Type) where
  objectid : K → JInt .u64
  hash : JInt .u64 → JInt .u64 → JInt .u64

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

def HashState.fromKey (ops : HashFunctions K) (key : K) : HashState K :=
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

def next (ops : HashFunctions K) (h : HashState K) : HashState K :=
  let depth := h.depth + 1
  let shift := h.shift + BITS_PER_LEVEL
  if shift > MAX_SHIFT then
    let hHash := ops.hash (ops.objectid h.key) (JInt.wrap .u64 (depth / BITS_PER_LEVEL))
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

def HashState.fromOtherAtDepth (ops : HashFunctions K) (other : HashState Q) (key : K) : HashState K := Id.run do
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

def HashState.inferAtDepth (ops : HashFunctions K) (other : HashState Q) (key : K) : HashState K :=
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

def HAMT.typedPairConstructor (vectors : VectorOps K V) (ops : HashFunctions K) (pair : K × V) : HamtM K V (HAMT K V) := do
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

def HAMT.convertPair (vectors : VectorOps K V) (ops : HashFunctions K)
    (convert : Q → K × V) (kv : Q) : HamtM K V (HAMT K V) :=
  HAMT.typedPairConstructor vectors ops (convert kv)

/--
Julia source: base/hamt.jl:84-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
HAMT(pair::Pair{K,V}) where {K, V} = HAMT{K,V}(pair)
```
-/

def HAMT.inferPair (vectors : VectorOps K V) (ops : HashFunctions K) (pair : K × V) :
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

def path (vectors : VectorOps K V) (same : K → K → Bool) (ops : HashFunctions K)
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

def insert! (vectors : VectorOps K V) (ops : HashFunctions K)
    (found present : Bool) (trie : HAMT K V) (initialIndex : Nat) (initialBi : BitmapIndex)
    (initialHash : HashState K) (value : V) : HamtM K V (Option BITMAP) := do
  if found then
    let data ← nodeData trie
    if present then
      vectors.set data initialIndex (.leaf ⟨initialHash.key, value⟩)
    else
      vectors.insert data initialIndex (.leaf ⟨initialHash.key, value⟩)
    return some (← set! trie initialBi)
  else
    if !present then throw .assertion
    let node ← readNode trie
    let leafEntry ← vectors.get node.data initialIndex
    let leaf ← match leafEntry with
      | .leaf leaf => pure leaf
      | .trie _ => throw .typeError
    let mut h := initialHash
    let mut leafHash := HashState.fromOtherAtDepth ops h leaf.key
    if leafHash.hash == h.hash then throw .perfectHashCollision
    let mut current := trie
    let mut i := initialIndex
    let mut bi := initialBi
    let mut isPresent := present
    let mut finished := false
    while !finished do
      let newTrie ← HAMT.emptyConstructor vectors
      let node ← readNode current
      let slot ← if isPresent then pure i else entry_index current bi
      if isPresent then
        vectors.set node.data slot (.trie newTrie)
      else
        vectors.insert node.data slot (.trie newTrie)
      let _ ← set! current bi
      h := next ops h
      leafHash := next ops leafHash
      let biNew := BitmapIndex.fromHash h
      let biOld := BitmapIndex.fromHash leafHash
      if biNew == biOld then
        current := newTrie
        bi := biNew
        isPresent := false
      else
        let newData ← nodeData newTrie
        let iNew ← entry_index newTrie biNew
        vectors.insert newData iNew (.leaf ⟨h.key, value⟩)
        let _ ← set! newTrie biNew
        let iOld ← entry_index newTrie biOld
        vectors.insert newData iOld (.leaf leaf)
        let _ ← set! newTrie biOld
        finished := true
    pure none

def persistentInsert (vectors : VectorOps K V) (same : K → K → Bool) (ops : HashFunctions K)
    (trie : HAMT K V) (key : K) (value : V) : HamtM K V (HAMT K V) := do
  let pathResult ← path vectors same ops trie (HashState.fromKey ops key) true
  let _ ← insert! vectors ops pathResult.found pathResult.present pathResult.trie
    pathResult.index pathResult.bi pathResult.hash value
  pure pathResult.top

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

/--
Julia source: base/hamt.jl:243-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.length(trie::HAMT) = sum((length(trie.data[i]) for i in eachindex(trie.data)), init=0)
```
-/

partial def lengthHAMT (vectors : VectorOps K V) (trie : HAMT K V) : HamtM K V Nat := do
  let node ← readNode trie
  let len ← vectors.length node.data
  let mut total := 0
  let mut i := 1
  while i ≤ len do
    match ← vectors.get node.data i with
    | .leaf leaf => total := total + lengthLeaf leaf
    | .trie child => total := total + (← lengthHAMT vectors child)
    i := i + 1
  pure total

/--
Julia source: base/hamt.jl:245-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.isempty(::Leaf) = false
```
-/

def isemptyLeaf (_leaf : Leaf K V) : Bool := false

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

partial def isemptyHAMT (vectors : VectorOps K V) (trie : HAMT K V) : HamtM K V Bool := do
  if ← islevel_empty trie then return true
  let node ← readNode trie
  let len ← vectors.length node.data
  let mut empty := true
  let mut i := 1
  while i ≤ len && empty do
    match ← vectors.get node.data i with
    | .leaf leaf => empty := isemptyLeaf leaf
    | .trie child => empty := ← isemptyHAMT vectors child
    i := i + 1
  pure empty

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

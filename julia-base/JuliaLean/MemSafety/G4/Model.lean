import JuliaLean.Core
import JuliaLean.Sort.Search

/-!
Bounds-obligation models for group 4. Each property calls a small program
that performs the Julia entry checks and computes the index used at the site.
No property accepts an in-bounds index as a hypothesis.
-/

namespace JuliaLean.MemSafety.G4

/-- One-based array bounds. -/
def InBounds (len : Nat) (i : Int) : Prop := 1 ≤ i ∧ i ≤ len

/-- The `k`th iteration of a checked `lo:hi` loop. This models the public
`checkbounds(v, lo:hi)` followed by the loops in `base/sort.jl`. -/
def checkedIntervalIndex (len : Nat) (lo hi : Int) (k : Nat) : Option Int :=
  if 1 ≤ lo ∧ lo ≤ hi ∧ hi ≤ len ∧ k < (hi - lo + 1).toNat then some (lo + k) else none

def CheckedIntervalInBounds : Prop :=
  ∀ (len : Nat) (lo hi : Int) (k : Nat) (i : Int),
    checkedIntervalIndex len lo hi k = some i → InBounds len i

/-- `get_chunks_id(i)[1]` after scalar BitArray indexing performs
`checkbounds(B, i)`, `base/bitarray.jl:661-690`. -/
def bitArrayChunkIndex (len : Nat) (i : Int) : Option Int :=
  if 1 ≤ i ∧ i ≤ len then some ((i - 1) / 64 + 1) else none

def BitArrayChunkInBounds : Prop :=
  ∀ (len : Nat) (i chunk : Int), bitArrayChunkIndex len i = some chunk →
    InBounds ((len + 63) / 64) chunk

/-- The chunk scans in `findmin` and `findmax` implement the first logical
position holding the requested bit, with index one as the all-equal fallback.
The functions reject an empty BitArray before reaching these sites. -/
def bitFindKeyIndex (bits : List Bool) (wanted : Bool) : Int :=
  match bits.findIdx? (· == wanted) with
  | some k => k + 1
  | none => 1

def bitFindKeyAccess (bits : List Bool) (wanted : Bool) : Option (Nat × Int) :=
  if bits = [] then none else some (bits.length, bitFindKeyIndex bits wanted)

def BitFindKeyInBounds : Prop :=
  ∀ (bits : List Bool) (wanted : Bool) (len : Nat) (i : Int),
    bitFindKeyAccess bits wanted = some (len, i) → InBounds len i

/-- `findall` allocates exactly one output slot for each true bit and increments
its output counter after each such store. -/
def bitFindAllOutputIndex (bits : List Bool) (selection : Nat) : Option Int :=
  if selection < bits.count true then some (selection + 1) else none

def BitFindAllInBounds : Prop :=
  ∀ (bits : List Bool) (selection : Nat) (i : Int),
    bitFindAllOutputIndex bits selection = some i → InBounds (bits.count true) i

/-- One iteration of `_copyto_int!` and `copy_to_bitarray_chunks!`, including
all six public range checks at `base/bitarray.jl:454-463`. -/
def bitArrayCopyIndex (destLen srcLen doffs soffs n : Int) (k : Nat) : Option (Int × Int) :=
  if 1 ≤ doffs ∧ 1 ≤ soffs ∧ 0 ≤ n ∧ n ≤ srcLen - soffs + 1 ∧
      n ≤ destLen - doffs + 1 ∧ k < n.toNat then
    some (doffs + k, soffs + k)
  else none

def BitArrayCopyInBounds : Prop :=
  ∀ (destLen srcLen doffs soffs n : Int) (k : Nat) (di si : Int),
    bitArrayCopyIndex destLen srcLen doffs soffs n k = some (di, si) →
    InBounds destLen.toNat di ∧ InBounds srcLen.toNat si

/-- The source and destination chunk selected for the `k`th copied bit. This
is the `get_chunks_id` arithmetic used by `copy_chunks!`, `fill_chunks!`, and
the Bool packing path. -/
def bitArrayCopyChunkIndex (destLen srcLen doffs soffs n : Int) (k : Nat) :
    Option (Nat × Int × Nat × Int) :=
  match bitArrayCopyIndex destLen srcLen doffs soffs n k with
  | none => none
  | some (di, si) => some ((destLen.toNat + 63) / 64, (di - 1) / 64 + 1,
      (srcLen.toNat + 63) / 64, (si - 1) / 64 + 1)

def BitArrayCopyChunksInBounds : Prop :=
  ∀ (destLen srcLen doffs soffs n : Int) (k dlen slen : Nat) (di si : Int),
    bitArrayCopyChunkIndex destLen srcLen doffs soffs n k = some (dlen, di, slen, si) →
    InBounds dlen di ∧ InBounds slen si

/-- The builder cache starts at one, increments after each store, and resets to
one after 4096 stores, `base/bitarray.jl:607-655`. -/
def bitCacheIndex (iteration tail : Nat) : Option Int :=
  let start := iteration % 4096
  if tail < 4096 - start then some (start + tail + 1) else none

def BitCacheInBounds : Prop :=
  ∀ (iteration tail : Nat) (i : Int), bitCacheIndex iteration tail = some i → InBounds 4096 i

/-- `_unsafe_setindex!` first rejects unequal chunk-vector lengths, then loops
over the shared length, `base/bitarray.jl:707-733`. -/
def bitMaskChunkIndex (destChunks maskChunks k : Nat) : Option (Int × Int) :=
  if destChunks = maskChunks ∧ k < destChunks then some (k + 1, k + 1) else none

def BitMaskChunksInBounds : Prop :=
  ∀ (destChunks maskChunks k : Nat) (di mi : Int),
    bitMaskChunkIndex destChunks maskChunks k = some (di, mi) →
    InBounds destChunks di ∧ InBounds maskChunks mi

/-- Logical mask assignment increments the source position only for a true mask
bit and checks `c == length(X)` before every source access. -/
def bitMaskSourceIndex (mask : List Bool) (sourceLen selection : Nat) : Option Int :=
  if selection < min sourceLen (mask.count true) then some (selection + 1) else none

def BitMaskSourceInBounds : Prop :=
  ∀ (mask : List Bool) (sourceLen selection : Nat) (i : Int),
    bitMaskSourceIndex mask sourceLen selection = some i → InBounds sourceLen i

/-- Chunk loops use either the `k`th position from the front or the symmetric
position from the end. This covers `reverse!`, reductions, and scans over a
chunk vector's own length. -/
def bitVectorLoopIndex (chunks k : Nat) (fromEnd : Bool) : Option Int :=
  if k < chunks then some (if fromEnd then chunks - k else k + 1) else none

def BitVectorLoopInBounds : Prop :=
  ∀ (chunks k : Nat) (fromEnd : Bool) (i : Int),
    bitVectorLoopIndex chunks k fromEnd = some i → InBounds chunks i

/-- `cmp` scans both chunk vectors through the smaller length. -/
def bitCompareIndex (left right k : Nat) : Option Int :=
  if k < min left right then some (k + 1) else none

def BitCompareInBounds : Prop :=
  ∀ left right k i, bitCompareIndex left right k = some i →
    InBounds left i ∧ InBounds right i

/-- `copyto!(dest::BitArray, src::BitArray)` checks logical lengths,
then uses the smaller chunk-vector length, including its final chunk. -/
def bitCopyVectorIndex (destBits srcBits destChunks srcChunks k : Nat)
    (final : Bool) : Option Int :=
  let nc := min destChunks srcChunks
  if srcBits ≤ destBits ∧ nc > 0 then
    if final then some nc else if k < nc - 1 then some (k + 1) else none
  else none

def BitCopyVectorInBounds : Prop :=
  ∀ destBits srcBits destChunks srcChunks k final i,
    bitCopyVectorIndex destBits srcBits destChunks srcChunks k final = some i →
    InBounds destChunks i ∧ InBounds srcChunks i

/-- The bootstrap array getter's unsigned comparison before `memoryrefnew`,
`base/boot.jl:879-883`. -/
def bootArrayIndex (len : Nat) (i : Int) : Option Int :=
  if 0 ≤ i - 1 ∧ i - 1 < len then some i else none

def BootArrayRefInBounds : Prop :=
  ∀ (len : Nat) (i j : Int), bootArrayIndex len i = some j → InBounds len j

/-- `copyto!` first checks equal axes, then `eachindex(bc)` returns an element
of those axes, `base/broadcast.jl:1015-1029`. -/
def broadcastEachindex (axes : List α) (k : Nat) : Option α := axes[k]?

def BroadcastEachindexInBounds : Prop :=
  ∀ (α : Type) (axes : List α) (k : Nat) (i : α), broadcastEachindex axes k = some i → i ∈ axes

/-- BitArray broadcast increments `indc` once per complete 64-bit output and
writes the optional remainder at the next chunk. -/
def broadcastChunkIndex (logicalLen k : Nat) : Option Int :=
  let chunks := (logicalLen + 63) / 64
  if k < chunks then some (k + 1) else none

def BroadcastChunkInBounds : Prop :=
  ∀ (logicalLen k : Nat) (i : Int), broadcastChunkIndex logicalLen k = some i →
    InBounds ((logicalLen + 63) / 64) i

/-- A HAMT bitmap split at the hash-selected bit. The fields are the three
results of that split; `entry_index` counts the set bits before it,
`base/hamt.jl:119-140,158-215`. -/
structure HamtSplit where
  before : Nat
  present : Bool
  after : Nat

def HamtSplit.dataLen (s : HamtSplit) : Nat :=
  s.before + (if s.present then 1 else 0) + s.after

def HamtSplit.entryIndex (s : HamtSplit) : Int := s.before + 1

def hamtDataAccess (s : HamtSplit) : Option (Nat × Int) :=
  if s.present then some (s.dataLen, s.entryIndex) else none

def HamtSlotInBounds : Prop :=
  ∀ (s : HamtSplit) (len : Nat) (i : Int), hamtDataAccess s = some (len, i) → InBounds len i

/-- The three fixed reads from the 96-byte `proc_taskinfo` allocation,
`base/precompilation.jl:2102-2111`. -/
inductive ProcessStatSite where
  | rss
  | user
  | system

structure ByteSpan where
  objectBytes : Nat
  offset : Nat
  readBytes : Nat

def ByteSpan.safe (a : ByteSpan) : Prop := a.offset + a.readBytes ≤ a.objectBytes

def processStatsRead (apple : Bool) (ret : Int) (site : ProcessStatSite) : Option ByteSpan :=
  if apple ∧ ret > 0 then
    some <| match site with
      | .rss => ⟨96, 8, 8⟩
      | .user => ⟨96, 16, 8⟩
      | .system => ⟨96, 24, 8⟩
  else none

def ProcessStatsReadsInBounds : Prop :=
  ∀ apple ret site span, processStatsRead apple ret site = some span → span.safe

/-- `split(s, '/'; limit=2)` returns one field without a slash and two with a
slash. Only the two-field branch reads `ss[1]` and `ss[2]`,
`base/rational.jl:175-186`. -/
def rationalPartCount (s : List Char) : Nat := if s.contains '/' then 2 else 1

inductive RationalPart where
  | numerator
  | denominator

def rationalAccess (s : List Char) (which : RationalPart) : Option (Nat × Int) :=
  if s.contains '/' then
    some (2, match which with | .numerator => 1 | .denominator => 2)
  else none

def RationalSplitInBounds : Prop :=
  ∀ (s : List Char) (which : RationalPart) (n : Nat) (i : Int),
    rationalAccess s which = some (n, i) → InBounds n i

/-- One sequential column of `mapreduce_impl`: indices 1 through K. -/
def scartColumn (K j : Nat) : List (Nat × Nat) :=
  (List.range K).map fun i => (i + 1, j)

/-- The exact sequential/pairwise branch tree of `mapreduce_impl`,
`base/reinterpretarray.jl:953-978`. Fuel is a totality device; the public
wrapper supplies `n+1`, more than the number of possible column splits. -/
def reinterpretMapreduceAccesses (K firstJ lastJ block : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | fuel + 1 =>
      if 2 ≤ K ∧ 1 ≤ firstJ ∧ firstJ ≤ lastJ then
        if lastJ - firstJ < block then
          (List.range (lastJ - firstJ + 1)).flatMap fun dj => scartColumn K (firstJ + dj)
        else
          let mid := firstJ + (lastJ - firstJ) / 2
          reinterpretMapreduceAccesses K firstJ mid block fuel ++
            reinterpretMapreduceAccesses K (mid + 1) lastJ block fuel
      else []

def reinterpretMapreduceProgram (K n block : Nat) : List (Nat × Nat) :=
  if 2 ≤ K ∧ 0 < n ∧ 0 < block then
    reinterpretMapreduceAccesses K 1 n block (n + 1)
  else []

def ReinterpretMapreduceInBounds : Prop :=
  ∀ (K n block : Nat) (a : Nat × Nat), a ∈ reinterpretMapreduceProgram K n block →
    1 ≤ a.1 ∧ a.1 ≤ K ∧ 1 ≤ a.2 ∧ a.2 ≤ n

/-- `_totuple` checks `length(itr) ≥ N+32`, forms exactly that view, then
loads its single tuple element at index one, `base/reinterpretarray.jl:984-995`. -/
def reinterpretTupleIndex (N itrLen : Nat) : Option (Nat × Int) :=
  if N + 32 ≤ itrLen then some (1, 1) else none

def ReinterpretTupleInBounds : Prop :=
  ∀ (N itrLen len : Nat) (i : Int), reinterpretTupleIndex N itrLen = some (len, i) →
    InBounds len i

/-- `fieldname` checks both sides before reading `_fieldnames(t)[i]`, and
`DataTypeFieldDesc.getindex` performs the same check,
`base/runtime_internals.jl:391-405,797-812`. -/
def runtimeFieldIndex (n : Nat) (i : Int) : Option Int :=
  if i > n then none else if i < 1 then none else some i

def RuntimeFieldInBounds : Prop :=
  ∀ (n : Nat) (i j : Int), runtimeFieldIndex n i = some j → InBounds n j

/-- `isconst` and `isfieldatomic` reject fields outside `1:n`, subtract one,
then load word `1+s÷32`, `base/runtime_internals.jl:544-578`. -/
def runtimeBitfieldIndex (n : Nat) (s : Int) : Option Int :=
  if 1 ≤ s ∧ s ≤ n then some (1 + (s - 1) / 32) else none

def RuntimeBitfieldInBounds : Prop :=
  ∀ (n : Nat) (s i : Int), runtimeBitfieldIndex n s = some i →
    InBounds ((n + 31) / 32) i

/-- Runtime-owned pointers at these sites point to one complete object: a
`DataTypeLayout`, a checked field descriptor, or the `UInt` global itself. -/
def runtimeMetadataIndex (objects : Nat) (i : Int) : Option Int :=
  if 1 ≤ i ∧ i ≤ objects then some i else none

def RuntimeMetadataInBounds : Prop :=
  ∀ (objects : Nat) (i j : Int), runtimeMetadataIndex objects i = some j → InBounds objects j

inductive RuntimeMetadataSite where
  | dataTypeLayout
  | fieldLayout
  | requireWorld

/-- Each runtime pointer is at offset zero of one complete runtime-owned
object of the loaded type. Null layout pointers are rejected before these
loads; `cglobal` returns the address of the complete UInt global. -/
def runtimeMetadataAccess : RuntimeMetadataSite → ByteSpan
  | .dataTypeLayout => ⟨1, 0, 1⟩
  | .fieldLayout => ⟨1, 0, 1⟩
  | .requireWorld => ⟨1, 0, 1⟩

def RuntimeMetadataAccessesInBounds : Prop :=
  ∀ site : RuntimeMetadataSite, (runtimeMetadataAccess site).safe

/-- The lookup implementation is exactly `table[i+1]`; its docstring states no
index restriction, `base/ryu/utils.jl:286-325`. -/
def ryuLookupIndex (_tableLen : Nat) (i : Int) : Int := i + 1

def RyuLookupInBounds : Prop :=
  ∀ (tableLen : Nat) (i : Int), 0 < tableLen → InBounds tableLen (ryuLookupIndex tableLen i)

/-- `@simd` creates `i=0; while i<length(r)` and reads
`r[i+firstindex(r)]`, `base/simdloop.jl:47-85`. -/
def simdIndex (indices : List Int) (i : Nat) : Option Int := indices[i]?

def SimdIndexInBounds : Prop :=
  ∀ (indices : List Int) (i : Nat) (j : Int), simdIndex indices i = some j → j ∈ indices

/-- `send_to_end!` assigns `i=lo` and immediately reads `v[i]` when `lo≤hi`,
without the bounds check promised by its view equivalence. -/
def sendToEndFirstIndex (lo hi : Int) : Option Int := if lo ≤ hi then some lo else none

def SendToEndInBounds : Prop :=
  ∀ (len : Nat) (lo hi i : Int), sendToEndFirstIndex lo hi = some i → InBounds len i

/-- Extrema computed by the preceding `ComputeExtrema` pass. -/
def listMinMax : List Nat → Option (Nat × Nat)
  | [] => none
  | x :: xs =>
      match listMinMax xs with
      | none => some (x, x)
      | some (lo, hi) => some (min x lo, max x hi)

/-- Counting sort computes the extrema from the input, subtracts the minimum,
and indexes its `range+1` counters, `base/sort.jl:893-966,2057-2078`. -/
def sortCountIndex (values : List Nat) (k : Nat) : Option (Nat × Int) :=
  match values[k]?, listMinMax values with
  | some value, some (minimum, maximum) =>
      some (maximum - minimum + 1, value - minimum + 1)
  | _, _ => none

def SortCountBucketInBounds : Prop :=
  ∀ (values : List Nat) (k countLen : Nat) (i : Int),
    sortCountIndex values k = some (countLen, i) → InBounds countLen i

inductive SortMemory where
  | vector
  | scratch

/-- ScratchQuickSort, BracketedSort, MergeSort, and the legacy quicksort first
check `lo:hi`, normalize it to a one-based scratch span, then select either a
current or end position in the vector or scratch allocation. -/
def sortPartitionIndex (len : Nat) (lo hi : Int) (k : Nat) (toEnd : Bool)
    (memory : SortMemory) : Option (Nat × Int) :=
  if 1 ≤ lo ∧ lo ≤ hi ∧ hi ≤ len ∧ k < (hi - lo + 1).toNat then
    match memory with
    | .vector => some (len, if toEnd then hi else lo + k)
    | .scratch => some ((hi - lo + 1).toNat, if toEnd then hi - lo + 1 else k + 1)
  else none

def SortPartitionInBounds : Prop :=
  ∀ (len : Nat) (lo hi : Int) (k : Nat) (toEnd : Bool) (memory : SortMemory)
    (objectLen : Nat) (i : Int),
    sortPartitionIndex len lo hi k toEnd memory = some (objectLen, i) → InBounds objectLen i

/-- The IEEE Perm branch runs only when the index vector equals `eachindex` of
the data array, then uses those stored indices for `o.data[i]`. -/
def sortPermDataIndex (dataAxes indices : List Int) (k : Nat) : Option Int :=
  if indices = dataAxes then indices[k]? else none

def SortPermDataInBounds : Prop :=
  ∀ (dataAxes indices : List Int) (k : Nat) (i : Int),
    sortPermDataIndex dataAxes indices k = some i → i ∈ dataAxes

/-- Boolean sort first scans the checked window, then fills the `count` prefix
and remaining suffix. `count` is computed from the input values. -/
inductive BoolSortPhase where
  | scan
  | first
  | second

def boolSortIndex (xs : List Bool) (first : Bool) (phase : BoolSortPhase) (k : Nat) : Option Int :=
  let count := xs.count first
  match phase with
  | .scan => if k < xs.length then some (k + 1) else none
  | .first => if k < count then some (k + 1) else none
  | .second => if k < xs.length - count then some (count + k + 1) else none

def BoolSortInBounds : Prop :=
  ∀ (xs : List Bool) (first : Bool) (phase : BoolSortPhase) (k : Nat) (i : Int),
    boolSortIndex xs first phase k = some i → InBounds xs.length i

/-- Radix sort computes `mask=2^chunk-1`, then `(x>>shift)&mask`; modulo by
`mask+1` is the same low-bit selection used for the two counter indices. -/
def sortRadixIndices (chunk x : Nat) : Nat × Nat :=
  let bucket := x % (2 ^ chunk)
  (bucket + 1, bucket + 2)

def SortRadixBucketInBounds : Prop :=
  ∀ (chunk x : Nat), let p := sortRadixIndices chunk x
    1 ≤ p.1 ∧ p.1 ≤ 2 ^ chunk + 1 ∧ 1 ≤ p.2 ∧ p.2 ≤ 2 ^ chunk + 1

/-- Valid character positions are a representation invariant of an
`AbstractString`. `nextind` and `prevind` move through this list,
`base/strings/search.jl:342-353,667-678`. -/
def stringSearchPositions (validPositions : List Int) (start : Int) (forward : Bool) : List Int :=
  if forward then validPositions.filter (start ≤ ·)
  else validPositions.reverse.filter (· ≤ start)

def stringSearchIndex (validPositions : List Int) (start : Int) (forward : Bool) (k : Nat) : Option Int :=
  (stringSearchPositions validPositions start forward)[k]?

def StringSearchInBounds : Prop :=
  ∀ (validPositions : List Int) (start : Int) (forward : Bool) (k : Nat) (i : Int),
    stringSearchIndex validPositions start forward k = some i → i ∈ validPositions

/-- libuv returns `count` initialized records and the loop is `1:count`,
`base/sysinfo.jl:309-323`. -/
def cpuInfoIndex (count i : Nat) : Option Int := if i < count then some (i + 1) else none

def CpuInfoInBounds : Prop :=
  ∀ (count i : Nat) (j : Int), cpuInfoIndex count i = some j → InBounds count j

/-- The exact binary-search model from `JuliaLean.Sort.Search`, specialized to
the checked public `Int` window `1:length(v)`. -/
def VectorSearchFirstInBounds : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (v : Array α) (x : α),
    JuliaLean.Sort.NegTransOrder lt → JuliaLean.Sort.VecSorted lt v → v.size < 2 ^ 62 →
    ∀ i, JuliaLean.Sort.searchsortedfirst lt v x (JInt.lit .i64 1) (JInt.lit .i64 v.size) ≠
      .invalidAccess i

end JuliaLean.MemSafety.G4

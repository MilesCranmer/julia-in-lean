import JuliaLean.Core

/-!
Bounds-obligation models for the group 4 unchecked sites.

The detailed value models remain in their owning areas.  This file records the
small index calculations that those models rely on: checked intervals, BitArray
chunk selection, fixed C-structure offsets, HAMT bitmap ranks, and the few
computed indices that are local to this group.
-/

namespace JuliaLean.MemSafety.G4

/-- One-based array bounds. -/
def InBounds (len : Nat) (i : Int) : Prop := 1 ≤ i ∧ i ≤ len

/-- Every index visited by a checked inclusive interval is in bounds.  This is
the loop shape used throughout `base/sort.jl` and `base/broadcast.jl`. -/
def CheckedIntervalInBounds : Prop :=
  ∀ (len : Nat) (lo hi i : Int), 1 ≤ lo → lo ≤ hi → hi ≤ len → lo ≤ i → i ≤ hi →
    InBounds len i

/-- The chunk chosen by `get_chunks_id(i)` is present in a valid BitArray,
`base/bitarray.jl:120-122,661-685`. -/
def BitArrayChunkInBounds : Prop :=
  ∀ (len i : Nat), 1 ≤ i → i ≤ len → (i - 1) / 64 + 1 ≤ (len + 63) / 64

/-- A checked bit-copy window stays within both arrays,
`base/bitarray.jl:454-469`. -/
def BitArrayCopyInBounds : Prop :=
  ∀ (destLen srcLen doffs soffs n i : Int), 1 ≤ doffs → 1 ≤ soffs → 0 ≤ n →
    doffs + n - 1 ≤ destLen → soffs + n - 1 ≤ srcLen → 0 ≤ i → i < n →
    (1 ≤ doffs + i ∧ doffs + i ≤ destLen) ∧
    (1 ≤ soffs + i ∧ soffs + i ≤ srcLen)

/-- The 4096-element builder cache indices in `base/bitarray.jl:607-655` are
valid until the cache is flushed and reset to one. -/
def BitCacheInBounds : Prop :=
  ∀ (i : Int), 1 ≤ i → i ≤ 4096 → InBounds 4096 i

/-- The explicit unsigned range check before `memoryrefget` in the bootstrap
array getter implies a valid reference, `base/boot.jl:879-883`. -/
def BootArrayRefInBounds : Prop :=
  ∀ (len : Nat) (i : Int), 0 ≤ i - 1 → i - 1 < len → InBounds len i

/-- Equal broadcast axes make every `eachindex(bc)` index valid for both the
broadcast and its destination, `base/broadcast.jl:1015-1029`. -/
def BroadcastEachindexInBounds : Prop :=
  ∀ (destLen bcLen : Nat) (i : Int), destLen = bcLen → InBounds bcLen i →
    InBounds destLen i ∧ InBounds bcLen i

/-- At a present HAMT bitmap bit, `entry_index` is one plus the number of bits
before it.  The data length is the count before, that bit, and the count after,
so the read/write slot is valid; an absent bit gives a valid insertion slot.
This abstracts `base/hamt.jl:130-141,158-215`. -/
def HamtSlotInBounds : Prop :=
  ∀ (before after : Nat),
    let presentLen := before + 1 + after
    let presentSlot := before + 1
    let absentLen := before + after
    1 ≤ presentSlot ∧ presentSlot ≤ presentLen ∧ presentSlot ≤ absentLen + 1

/-- The three `UInt64` reads fit in the 96-byte `proc_taskinfo` buffer,
`base/precompilation.jl:2102-2111`. -/
def ProcessStatsReadsInBounds : Prop :=
  ∀ (bufLen off : Nat), bufLen = 96 → off ∈ [8, 16, 24] → off + 8 ≤ bufLen

/-- `split(s, '/'; limit=2)` returns one or two pieces, and the two-piece branch
may read both, `base/rational.jl:175-186`. -/
def RationalSplitInBounds : Prop :=
  ∀ (parts : Nat), (parts = 1 ∨ parts = 2) → parts ≠ 1 → 1 ≤ parts ∧ 2 ≤ parts

/-- All scalar indices used by the sequential `SCartesianIndex2` map-reduce
branch lie in its `K × n` axes, `base/reinterpretarray.jl:953-978`. -/
def ReinterpretMapreduceInBounds : Prop :=
  ∀ (K n firstJ lastJ i j : Nat), 2 ≤ K → 1 ≤ firstJ → firstJ ≤ lastJ → lastJ ≤ n →
    (((i = 1 ∨ i = 2) ∧ j = firstJ) ∨
      (3 ≤ i ∧ i ≤ K ∧ j = firstJ) ∨
      (1 ≤ i ∧ i ≤ K ∧ firstJ < j ∧ j ≤ lastJ)) →
    1 ≤ i ∧ i ≤ K ∧ 1 ≤ j ∧ j ≤ n

/-- `_totuple` checks that its `N+32`-element view is nonempty before loading
the first reinterpreted tuple, `base/reinterpretarray.jl:984-995`. -/
def ReinterpretTupleInBounds : Prop :=
  ∀ (N len : Nat), N + 32 ≤ len → 1 ≤ N + 32 ∧ N + 32 ≤ len

/-- A valid field number remains valid after the checks in `fieldname` and
`DataTypeFieldDesc.getindex`, `base/runtime_internals.jl:391-405,797-812`. -/
def RuntimeFieldInBounds : Prop :=
  ∀ (n : Nat) (i : Int), 1 ≤ i → i ≤ n → InBounds n i

/-- A field bit lies in the runtime bitmap word allocated for all fields,
`base/runtime_internals.jl:544-578`. -/
def RuntimeBitfieldInBounds : Prop :=
  ∀ (n s : Nat), 1 ≤ s → s ≤ n → 1 + (s - 1) / 32 ≤ (n + 31) / 32

/-- The fixed-size pointer reads of runtime metadata stay in their runtime-owned
objects, `base/runtime_internals.jl:642-645,797-809,1662`. -/
def RuntimeMetadataInBounds : Prop :=
  ∀ (objectBytes readBytes : Nat), 0 < readBytes → readBytes ≤ objectBytes →
    0 + readBytes ≤ objectBytes

/-- `append_d_digits` starts `append_c_digits` at `pos+1`; its capacity
precondition makes the two following byte accesses valid,
`base/ryu/utils.jl:225-229`. -/
def RyuAppendDigitsInBounds : Prop :=
  ∀ (bufLen pos digits : Nat), 1 ≤ pos → 1 ≤ digits → pos + digits ≤ bufLen →
    pos ≤ bufLen ∧ pos + 1 ≤ bufLen

/-- The lookup docstrings give no index restriction, so every accepted index
would have to make `i+1` a valid tuple index, `base/ryu/utils.jl:286-325`. -/
def RyuLookupInBounds : Prop :=
  ∀ (tableLen : Nat) (i : Int), 0 < tableLen → InBounds tableLen (i + 1)

/-- The default `@simd` lowering visits zero-based `i < length(r)` and reads
`r[i+firstindex(r)]`, `base/simdloop.jl:47-85`. -/
def SimdIndexInBounds : Prop :=
  ∀ (len i : Nat), i < len → 1 ≤ i + 1 ∧ i + 1 ≤ len

/-- `send_to_end!` may access every position in its supplied `lo:hi` window,
but the documented keyword method does not check that window,
`base/sort.jl:610-633`. -/
def SendToEndInBounds : Prop :=
  ∀ (len : Nat) (lo hi i : Int), lo ≤ hi → lo ≤ i → i ≤ hi → InBounds len i

/-- Counting-sort values are normalized to `0:range` before indexing the
`range+1` counters, `base/sort.jl:948-966,2058-2078`. -/
def SortCountBucketInBounds : Prop :=
  ∀ (range bucket : Nat), bucket ≤ range → 1 ≤ bucket + 1 ∧ bucket + 1 ≤ range + 1

/-- A radix digit is masked into `0:mask`, so its shifted counter index is in
the `mask+2` counter array, `base/sort.jl:1402-1427`. -/
def SortRadixBucketInBounds : Prop :=
  ∀ (mask bucket : Nat), bucket ≤ mask →
    1 ≤ bucket + 1 ∧ bucket + 1 ≤ mask + 2 ∧
    1 ≤ bucket + 2 ∧ bucket + 2 ≤ mask + 2

/-- Once the public string-search checks and loop guards hold, each `s[i]`,
`nextind`, and `prevind` call is at a valid code-unit position,
`base/strings/search.jl:342-353,667-678`. -/
def StringSearchInBounds : Prop :=
  ∀ (n : Nat) (i : Int), 1 ≤ i → i ≤ n → InBounds n i

/-- libuv returns `count` initialized records and `cpu_info` loops over exactly
those records, `base/sysinfo.jl:309-323`. -/
def CpuInfoInBounds : Prop :=
  ∀ (count i : Nat), 1 ≤ i → i ≤ count → i ≤ count

end JuliaLean.MemSafety.G4

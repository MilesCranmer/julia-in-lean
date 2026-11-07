import JuliaLean.Proofs.base.runtime_internals.Common

namespace JuliaLean.MemSafety.G4

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


theorem bitArrayChunkInBounds : BitArrayChunkInBounds := by
  intro len i chunk h
  unfold bitArrayChunkIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst chunk
    unfold InBounds
    omega
  · contradiction

theorem bitFindKeyInBounds : BitFindKeyInBounds := by
  intro bits wanted len i h
  unfold bitFindKeyAccess at h
  split at h
  · contradiction
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    unfold bitFindKeyIndex InBounds
    cases hfind : bits.findIdx? (· == wanted) with
    | none =>
        have hlen : 0 < bits.length := by
          cases bits with
          | nil => contradiction
          | cons => simp
        simp only [hfind]
        omega
    | some k =>
        have hk : k < bits.length := (List.findIdx?_eq_some_iff_getElem.mp hfind).1
        simp only [hfind]
        omega

theorem bitFindAllInBounds : BitFindAllInBounds := by
  intro bits selection i h
  unfold bitFindAllOutputIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    omega
  · contradiction

theorem bitArrayCopyInBounds : BitArrayCopyInBounds := by
  intro destLen srcLen doffs soffs n k di si h
  unfold bitArrayCopyIndex at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    unfold InBounds
    omega
  · contradiction

theorem bitArrayCopyChunksInBounds : BitArrayCopyChunksInBounds := by
  intro destLen srcLen doffs soffs n k dlen slen di si h
  unfold bitArrayCopyChunkIndex at h
  cases hc : bitArrayCopyIndex destLen srcLen doffs soffs n k with
  | none => simp [hc] at h
  | some p =>
      rcases p with ⟨dei, sei⟩
      simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      have hb := bitArrayCopyInBounds destLen srcLen doffs soffs n k dei sei hc
      constructor
      · apply bitArrayChunkInBounds destLen.toNat dei
        have hd := hb.1
        unfold InBounds at hd
        unfold bitArrayChunkIndex
        rw [if_pos hd]
      · apply bitArrayChunkInBounds srcLen.toNat sei
        have hs := hb.2
        unfold InBounds at hs
        unfold bitArrayChunkIndex
        rw [if_pos hs]

theorem bitCacheInBounds : BitCacheInBounds := by
  intro iteration tail i h
  dsimp [bitCacheIndex] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    have hm := Nat.mod_lt iteration (by decide : 0 < 4096)
    omega
  · contradiction

theorem bitMaskChunksInBounds : BitMaskChunksInBounds := by
  intro destChunks maskChunks k di mi h
  unfold bitMaskChunkIndex at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    unfold InBounds
    omega
  · contradiction

theorem bitMaskSourceInBounds : BitMaskSourceInBounds := by
  intro mask sourceLen selection i h
  unfold bitMaskSourceIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    omega
  · contradiction

theorem bitVectorLoopInBounds : BitVectorLoopInBounds := by
  intro chunks k fromEnd i h
  unfold bitVectorLoopIndex at h
  split at h
  · split at h <;> simp only [Option.some.injEq] at h <;> subst i <;>
      unfold InBounds <;> omega
  · contradiction

theorem bitCompareInBounds : BitCompareInBounds := by
  intro left right k i h
  unfold bitCompareIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    omega
  · contradiction

theorem bitCopyVectorInBounds : BitCopyVectorInBounds := by
  intro destBits srcBits destChunks srcChunks k final i h
  dsimp [bitCopyVectorIndex] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst i
      unfold InBounds
      omega
    · split at h
      · simp only [Option.some.injEq] at h
        subst i
        unfold InBounds
        omega
      · contradiction
  · contradiction

end JuliaLean.MemSafety.G4

import JuliaLean.base.abstractarray
import JuliaLean.base.range
import JuliaLean.base.number
import JuliaLean.base.tuple
import JuliaLean.Core
import JuliaLean.base.array
import JuliaLean.base.int
import JuliaLean.base.indices
import JuliaLean.Registry.Types

namespace JuliaLean.base.bitarray

open JuliaLean JuliaLean.base.array JuliaLean.base.int

abbrev I64 := JInt .i64
abbrev U64 := JInt .u64
abbrev MutationM (α : Type) := JuliaLean.base.array.MutationM α
abbrev BitMutationM := MutationM U64
abbrev BoolArray := Nat

def int (n : Int) : I64 := JInt.lit .i64 n
def u64 (n : Int) : U64 := JInt.lit .u64 n
def u64Max : U64 := not_int (u64 0)
def bitCacheChunks : I64 := int 64
def bitCacheSize : I64 := bitCacheChunks * bitCacheChunks

/-- Native UInt64 element layout and its distinct non-atomic GenericMemory header. -/
def uint64Element : JuliaLean.base.runtime_internals.DataTypeLayout :=
  JuliaLean.src.genericmemory_c.nativeLayout 8 0 0 (-1) 8 128

def uint64Metadata : JuliaLean.src.genericmemory_c.Metadata :=
  { runtimeType :=
      { identity := 2
        layout := JuliaLean.src.genericmemory_c.genericMemoryHeader 8 8 0 (-1)
        elementType := .datatype ⟨uint64Element, uint64Element, fun _ => 0⟩
        elementTag := .bitInteger .u64
        kind := .notAtomic }
    typeofBottom := none
    owner := 0
    mutexBytes := 0 }

def uint64Layout : JuliaLean.src.genericmemory_c.DictLayout where
  metadata := uint64Metadata
  nonAtomicKind := rfl
  nonAtomicFlag := rfl
  unlocked := rfl
  inlineDatatype := by
    intro _ _ _
    exact ⟨⟨uint64Element, uint64Element, fun _ => 0⟩, rfl⟩

def growChunkVector (chunks : Nat) (delta : I64) : BitMutationM Unit :=
  growend (mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)) (fun d => pure d)
    (growendInternal (mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout))) chunks delta

def deleteChunkEnd (chunks : Nat) (delta : I64) : BitMutationM Unit :=
  deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)) (fun d => pure d) chunks delta

structure BitArray (N : Nat) where
  chunks : Nat
  len : I64
  dims : List I64

def BitVector := BitArray 1
def BitMatrix := BitArray 2

structure BitRange where
  first : I64
  last : I64

inductive BitIteratorSize where
  | unknown
  | hasShape (rank : Nat)
  | hasLength
  | infinite
  deriving Repr, DecidableEq

inductive BitArrayTarget where
  | vector
  | array (rank : Nat)
  | other (name : String)
  deriving Repr, DecidableEq

inductive BitIndex where
  | scalar (index : I64)
  | cartesian (indices : List I64)
  deriving Repr, DecidableEq

partial def overflowWithin (i1 i2 size1 : I64) : I64 × I64 :=
  if i1 > size1 then overflowWithin (i1 - size1) (i2 + int 1) size1 else (i1, i2)

inductive BitSource where
  | bitArray (N : Nat) (value : BitArray N)
  | boolArray (handle : Nat)

/--
Julia source: base/bitarray.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(B::BitArray) = B.len
```
-/
def bitArrayLength {N : Nat} (B : BitArray N) : I64 := B.len

/--
Julia source: base/bitarray.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _div64(l) = l >> 6
```
-/
def div64 (l : I64) : I64 := ashr_int l (int 6)

/--
Julia source: base/bitarray.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _mod64(l) = l & 63
```
-/
def mod64 (l : I64) : I64 := and_int l (int 63)

/--
Julia source: base/bitarray.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _blsr(x)= x & (x-1) #zeros the last set bit. Has native instruction on many archs. needed in multidimensional.jl
```
-/
def blsr (x : U64) : U64 := and_int x (sub_int x (u64 1))

/--
Julia source: base/bitarray.jl:118-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _msk_end(l::Int) = _msk64 >>> _mod64(-l)
```
-/
def maskEnd (l : I64) : U64 := lshr_int (u64Max) (mod64 (-l))

/--
Julia source: base/bitarray.jl:119-119 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _msk_end(B::BitArray) = _msk_end(length(B))
```
-/
def maskEndArray {N : Nat} (B : BitArray N) : U64 := maskEnd (bitArrayLength B)

/--
Julia source: base/bitarray.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
num_bit_chunks(n::Int) = _div64(n) + !iszero(_mod64(n))
```
-/
def numBitChunks (n : I64) : I64 := div64 n + int (if mod64 n == int 0 then 0 else 1)

/--
Julia source: base/bitarray.jl:28-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function BitArray{N}(::UndefInitializer, dims::Vararg{Int,N}) where N
        i = 1
        for d in dims
            d >= 0 || throw(ArgumentError("dimension size must be ≥ 0, got $d for dimension $i"))
            i += 1
        end
        n = Core.checked_dims(dims...)
        nc = num_bit_chunks(n)
        chunks = Vector{UInt64}(undef, nc)
        nc > 0 && (chunks[end] = UInt64(0))
        b = new(chunks, n)
        N != 1 && (b.dims = dims)
        return b
    end
```
-/
def BitArrayUndef {N : Nat} (checkedDims : List I64 → MutationM U64 I64)
    (allocateChunks : Nat → MutationM U64 Nat) (dims : List I64) : MutationM U64 (BitArray N) := do
  let mut i := int 1
  for d in dims do
    if d.val < 0 then throw (.argument s!"dimension size must be ≥ 0, got {d.val} for dimension {i.val}")
    i := i + int 1
  let n ← checkedDims dims
  let nc := numBitChunks n
  let chunks ← allocateChunks nc.val.toNat
  if nc.val > 0 then
    mutableSet chunks (u64 0) nc
  pure ⟨chunks, n, dims⟩

/--
Julia source: base/bitarray.jl:122-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline get_chunks_id(i::Int) = _div64(i-1)+1, _mod64(i-1)
```
-/
def getChunksId (i : I64) : I64 × I64 := (div64 (i - int 1) + int 1, mod64 (i - int 1))

/--
Julia source: base/bitarray.jl:124-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function glue_src_bitchunks(src::Vector{UInt64}, k::Int, ks1::Int, msk_s0::UInt64, ls0::Int)
    @inbounds begin
        chunk = ((src[k] & msk_s0) >>> ls0)
        if ks1 > k && ls0 > 0
            chunk_n = (src[k + 1] & ~msk_s0)
            chunk |= (chunk_n << (64 - ls0))
        end
    end
    return chunk
end
```
-/
def glueSrcBitChunks (src : Nat) (k ks1 : I64) (mskS0 : U64) (ls0 : I64) : BitMutationM U64 := do
  let mut chunk := lshr_int (and_int (← mutableGet src k) mskS0) ls0
  if ks1 > k ∧ ls0 > int 0 then
    let chunkN := and_int (← mutableGet src (k + int 1)) (not_int mskS0)
    chunk := or_int chunk (shl_int chunkN (int 64 - ls0))
  pure chunk

mutual
/--
Julia source: base/bitarray.jl:135-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy_chunks!(dest::Vector{UInt64}, pos_d::Int, src::Vector{UInt64}, pos_s::Int, numbits::Int)
    numbits == 0 && return
    if dest === src && pos_d > pos_s
        return copy_chunks_rtol!(dest, pos_d, pos_s, numbits)
    end

    kd0, ld0 = get_chunks_id(pos_d)
    kd1, ld1 = get_chunks_id(pos_d + numbits - 1)
    ks0, ls0 = get_chunks_id(pos_s)
    ks1, ls1 = get_chunks_id(pos_s + numbits - 1)

    delta_kd = kd1 - kd0
    delta_ks = ks1 - ks0

    u = _msk64
    msk_d0 = ~(u << ld0)
    msk_d1 = (u << (ld1+1))
    if delta_kd == 0
        msk_d0 |= msk_d1
    end
    msk_s0 = (u << ls0)
    if delta_ks == 0
        msk_s0 &= ~(u << (ls1+1))
    end

    chunk_s0 = glue_src_bitchunks(src, ks0, ks1, msk_s0, ls0)

    dest[kd0] = (dest[kd0] & msk_d0) | ((chunk_s0 << ld0) & ~msk_d0)

    delta_kd == 0 && return

    for i = 1 : kd1 - kd0 - 1
        chunk_s1 = glue_src_bitchunks(src, ks0 + i, ks1, msk_s0, ls0)

        chunk_s = (chunk_s0 >>> (64 - ld0)) | (chunk_s1 << ld0)

        dest[kd0 + i] = chunk_s

        chunk_s0 = chunk_s1
    end

    if ks1 >= ks0 + delta_kd
        chunk_s1 = glue_src_bitchunks(src, ks0 + delta_kd, ks1, msk_s0, ls0)
    else
        chunk_s1 = UInt64(0)
    end

    chunk_s = (chunk_s0 >>> (64 - ld0)) | (chunk_s1 << ld0)

    dest[kd1] = (dest[kd1] & msk_d1) | (chunk_s & ~msk_d1)

    return
end
```
-/
def copyChunks : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit
  | dest, posD, src, posS, numbits => do
    if numbits == int 0 then return
    if h : dest = src ∧ posD > posS then
      return ← copyChunksRtol dest posD posS numbits
    let (kd0, ld0) := getChunksId posD
    let (kd1, ld1) := getChunksId (posD + numbits - int 1)
    let (ks0, ls0) := getChunksId posS
    let (ks1, ls1) := getChunksId (posS + numbits - int 1)
    let deltaKD := kd1 - kd0
    let deltaKS := ks1 - ks0
    let u := u64Max
    let mut mskD0 := not_int (shl_int u ld0)
    let mskD1 := shl_int u (ld1 + int 1)
    if deltaKD == int 0 then mskD0 := or_int mskD0 mskD1
    let mut mskS0 := shl_int u ls0
    if deltaKS == int 0 then mskS0 := and_int mskS0 (not_int (shl_int u (ls1 + int 1)))
    let mut chunkS0 ← glueSrcBitChunks src ks0 ks1 mskS0 ls0
    let destD0 ← mutableGet dest kd0
    mutableSet dest (or_int (and_int destD0 mskD0) (and_int (shl_int chunkS0 ld0) (not_int mskD0))) kd0
    if deltaKD == int 0 then return
    for i in intRange (int 1) (kd1 - kd0 - int 1) do
      let chunkS1 ← glueSrcBitChunks src (ks0 + i - int 1) ks1 mskS0 ls0
      let chunkS := or_int (lshr_int chunkS0 (int 64 - ld0)) (shl_int chunkS1 ld0)
      mutableSet dest chunkS (kd0 + i)
      chunkS0 := chunkS1
    let chunkS1 ← if ks1 ≥ ks0 + deltaKD then
      glueSrcBitChunks src (ks0 + deltaKD) ks1 mskS0 ls0
    else pure (u64 0)
    let chunkS := or_int (lshr_int chunkS0 (int 64 - ld0)) (shl_int chunkS1 ld0)
    let destD1 ← mutableGet dest kd1
    mutableSet dest (or_int (and_int destD1 mskD1) (and_int chunkS (not_int mskD1))) kd1
    pure ()
  termination_by dest posD src posS numbits => if posD > posS then 1 else 0
decreasing_by
    simp_wf
    rcases h with ⟨_, hd⟩
    change posS.val < posD.val at hd
    have hnot : ¬ posD < posS := by
      intro h'
      change posD.val < posS.val at h'
      omega
    have hgt : posS < posD := by change posS.val < posD.val; exact hd
    simp [hnot, hgt]

/--
Julia source: base/bitarray.jl:189-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy_chunks_rtol!(chunks::Vector{UInt64}, pos_d::Int, pos_s::Int, numbits::Int)
    pos_d == pos_s && return
    pos_d < pos_s && return copy_chunks!(chunks, pos_d, chunks, pos_s, numbits)

    left = numbits
    s = min(left, 64)
    b = left - s
    ps = pos_s + b
    pd = pos_d + b
    u = _msk64
    while left > 0
        kd0, ld0 = get_chunks_id(pd)
        kd1, ld1 = get_chunks_id(pd + s - 1)
        ks0, ls0 = get_chunks_id(ps)
        ks1, ls1 = get_chunks_id(ps + s - 1)

        delta_kd = kd1 - kd0
        delta_ks = ks1 - ks0

        msk_d0 = ~(u << ld0)
        msk_d1 = (u << (ld1+1))
        if delta_kd == 0
            msk_d0 |= msk_d1
        end
        msk_s0 = (u << ls0)
        if delta_ks == 0
            msk_s0 &= ~(u << (ls1+1))
        end

        chunk_s0 = glue_src_bitchunks(chunks, ks0, ks1, msk_s0, ls0) & ~(u << s)
        chunks[kd0] = (chunks[kd0] & msk_d0) | ((chunk_s0 << ld0) & ~msk_d0)

        if delta_kd != 0
            chunk_s = (chunk_s0 >>> (64 - ld0))

            chunks[kd1] = (chunks[kd1] & msk_d1) | (chunk_s & ~msk_d1)
        end

        left -= s
        s = min(left, 64)
        b = left - s
        ps = pos_s + b
        pd = pos_d + b
    end
end
```
-/
def copyChunksRtol : Nat → I64 → I64 → I64 → BitMutationM Unit
  | chunks, posD, posS, numbits => do
    if posD == posS then return
    if h : posD < posS then return ← copyChunks chunks posD chunks posS numbits
    let mut left := numbits
    let mut s := if left < int 64 then left else int 64
    let mut b := left - s
    let mut ps := posS + b
    let mut pd := posD + b
    let u := u64Max
    while left > int 0 do
      let (kd0, ld0) := getChunksId pd
      let (kd1, ld1) := getChunksId (pd + s - int 1)
      let (ks0, ls0) := getChunksId ps
      let (ks1, ls1) := getChunksId (ps + s - int 1)
      let deltaKD := kd1 - kd0
      let deltaKS := ks1 - ks0
      let mut mskD0 := not_int (shl_int u ld0)
      let mskD1 := shl_int u (ld1 + int 1)
      if deltaKD == int 0 then mskD0 := or_int mskD0 mskD1
      let mut mskS0 := shl_int u ls0
      if deltaKS == int 0 then mskS0 := and_int mskS0 (not_int (shl_int u (ls1 + int 1)))
      let chunkS0 := and_int (← glueSrcBitChunks chunks ks0 ks1 mskS0 ls0) (not_int (shl_int u s))
      let destD0 ← mutableGet chunks kd0
      mutableSet chunks (or_int (and_int destD0 mskD0) (and_int (shl_int chunkS0 ld0) (not_int mskD0))) kd0
      if deltaKD != int 0 then
        let chunkS := lshr_int chunkS0 (int 64 - ld0)
        let destD1 ← mutableGet chunks kd1
        mutableSet chunks (or_int (and_int destD1 mskD1) (and_int chunkS (not_int mskD1))) kd1
      left := left - s
      s := if left < int 64 then left else int 64
      b := left - s
      ps := posS + b
      pd := posD + b
    pure ()
  termination_by chunks posD posS numbits => if posD < posS then 1 else 0
decreasing_by
    simp_wf
    change posD.val < posS.val at h
    have hlt : posD < posS := by change posD.val < posS.val; exact h
    have hnot : ¬ posS < posD := by
      intro h'
      change posS.val < posD.val at h'
      omega
    simp [hlt, hnot]

end

/--
Julia source: base/bitarray.jl:235-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fill_chunks!(Bc::Array{UInt64}, x::Bool, pos::Int, numbits::Int)
    numbits <= 0 && return
    k0, l0 = get_chunks_id(pos)
    k1, l1 = get_chunks_id(pos+numbits-1)

    u = _msk64
    msk0 = (u << l0)
    msk1 = ~(u << (l1+1))
    if k1 == k0
        msk0 &= msk1
    end
    @inbounds if x
        Bc[k0] |= msk0
        for k = k0+1:k1-1
            Bc[k] = u
        end
        k1 > k0 && (Bc[k1] |= msk1)
    else
        Bc[k0] &= ~msk0
        for k = k0+1:k1-1
            Bc[k] = 0
        end
        k1 > k0 && (Bc[k1] &= ~msk1)
    end
end
```
-/
def fillChunks (bc : Nat) (x : Bool) (pos : I64) (numbits : I64) : BitMutationM Unit := do
  if numbits ≤ int 0 then return
  let (k0, l0) := getChunksId pos
  let (k1, l1) := getChunksId (pos + numbits - int 1)
  let u := u64Max
  let mut msk0 := shl_int u l0
  let msk1 := not_int (shl_int u (l1 + int 1))
  if k1 == k0 then msk0 := and_int msk0 msk1
  if x then
    let c0 ← mutableGet bc k0
    mutableSet bc (or_int c0 msk0) k0
    for k in intRange (k0 + int 1) (k1 - int 1) do mutableSet bc u k
    if k1 > k0 then
      let c1 ← mutableGet bc k1
      mutableSet bc (or_int c1 msk1) k1
  else
    let c0 ← mutableGet bc k0
    mutableSet bc (and_int c0 (not_int msk0)) k0
    for k in intRange (k0 + int 1) (k1 - int 1) do mutableSet bc (u64 0) k
    if k1 > k0 then
      let c1 ← mutableGet bc k1
      mutableSet bc (and_int c1 (not_int msk1)) k1

/--
Julia source: base/bitarray.jl:261-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy_to_bitarray_chunks!(dest::Vector{UInt64}, pos_d::Int, src::BitArray, pos_s::Int, numbits::Int) =
    copy_chunks!(dest, pos_d, src.chunks, pos_s, numbits)
```
-/
def copyToBitArrayChunksBit {N : Nat} (dest : Nat) (posD : I64) (src : BitArray N)
    (posS numbits : I64) : BitMutationM Unit :=
  copyChunks dest posD src.chunks posS numbits

/--
Julia source: base/bitarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pack8bools(z::UInt64)
    z |= z >>> 7
    z |= z >>> 14
    z |= z >>> 28
    z &= 0xFF
    return z
end
```
-/
def pack8bools (z : U64) : U64 :=
  and_int (or_int (or_int (or_int z (lshr_int z (u64 7)))
    (lshr_int z (u64 14))) (lshr_int z (u64 28))) (u64 255)

/--
Julia source: base/bitarray.jl:274-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy_to_bitarray_chunks!(Bc::Vector{UInt64}, pos_d::Int, C::Array{Bool}, pos_s::Int, numbits::Int)
    kd0, ld0 = get_chunks_id(pos_d)
    kd1, ld1 = get_chunks_id(pos_d + numbits - 1)

    delta_kd = kd1 - kd0

    u = _msk64
    if delta_kd == 0
        msk_d0 = msk_d1 = ~(u << ld0) | (u << (ld1+1))
        lt0 = ld1
    else
        msk_d0 = ~(u << ld0)
        msk_d1 = (u << (ld1+1))
        lt0 = 63
    end

    bind = kd0
    ind = pos_s
    @inbounds if ld0 > 0
        c = UInt64(0)
        for j = ld0:lt0
            c |= (UInt64(C[ind]) << j)
            ind += 1
        end
        Bc[kd0] = (Bc[kd0] & msk_d0) | (c & ~msk_d0)
        bind += 1
    end

    nc = _div64(numbits - ind + pos_s)
    nc8 = (nc >>> 3) << 3
    if nc8 > 0
        ind8 = 1
        P8 = Ptr{UInt64}(pointer(C, ind)) # unaligned i64 pointer
        @inbounds for _ = 1:nc8
            c = UInt64(0)
            for j = 0:7
                # unaligned load
                c |= (pack8bools(unsafe_load(P8, ind8)) << (j<<3))
                ind8 += 1
            end
            Bc[bind] = c
            bind += 1
        end
        ind += (ind8-1) << 3
    end
    @inbounds for _ = (nc8+1):nc
        c = UInt64(0)
        for j = 0:63
            c |= (UInt64(C[ind]) << j)
            ind += 1
        end
        Bc[bind] = c
        bind += 1
    end
    @inbounds if bind ≤ kd1
        @assert bind == kd1 "bind != kd1"
        c = UInt64(0)
        for j = 0:ld1
            c |= (UInt64(C[ind]) << j)
            ind += 1
        end
        Bc[kd1] = (Bc[kd1] & msk_d1) | (c & ~msk_d1)
    end
end
```
-/
def copyToBitArrayChunksBool {C P : Type} (bc : Nat) (posD : I64) (c : C) (posS numbits : I64)
    (getBool : C → I64 → BitMutationM Bool) (pointer : C → I64 → P)
    (unsafeLoad : P → I64 → BitMutationM U64) : BitMutationM Unit := do
  let (kd0, ld0) := getChunksId posD
  let (kd1, ld1) := getChunksId (posD + numbits - int 1)
  let deltaKD := kd1 - kd0
  let u := u64Max
  let mut mskD0 := u64 0
  let mut mskD1 := shl_int u (ld1 + int 1)
  let mut lt0 := int 0
  if deltaKD == int 0 then
    mskD0 := or_int (not_int (shl_int u ld0)) (shl_int u (ld1 + int 1))
    mskD1 := mskD0
    lt0 := ld1
  else
    mskD0 := not_int (shl_int u ld0)
    mskD1 := shl_int u (ld1 + int 1)
    lt0 := int 63
  let mut bind := kd0
  let mut ind := posS
  if ld0 > int 0 then
    let mut cWord := u64 0
    for j in intRange ld0 lt0 do
      let bit ← getBool c ind
      cWord := or_int cWord (shl_int (u64 (if bit then 1 else 0)) j)
      ind := ind + int 1
    let old ← mutableGet bc kd0
    mutableSet bc (or_int (and_int old mskD0) (and_int cWord (not_int mskD0))) kd0
    bind := bind + int 1
  let nc := div64 (numbits - ind + posS)
  let nc8 := shl_int (lshr_int nc (int 3)) (int 3)
  if nc8 > int 0 then
    let mut ind8 := int 1
    let p8 := pointer c ind
    for _ in intRange (int 1) nc8 do
      let mut cWord := u64 0
      for j in intRange (int 0) (int 7) do
        cWord := or_int cWord (shl_int (pack8bools (← unsafeLoad p8 ind8)) (shl_int (int 1) j))
        ind8 := ind8 + int 1
      mutableSet bc cWord bind
      bind := bind + int 1
    ind := ind + shl_int (ind8 - int 1) (int 3)
  for _ in intRange (nc8 + int 1) nc do
    let mut cWord := u64 0
    for j in intRange (int 0) (int 63) do
      let bit ← getBool c ind
      cWord := or_int cWord (shl_int (u64 (if bit then 1 else 0)) j)
      ind := ind + int 1
    mutableSet bc cWord bind
    bind := bind + int 1
  if bind ≤ kd1 then
    if bind != kd1 then throw (.assertion "bind != kd1")
    let mut cWord := u64 0
    for j in intRange (int 0) ld1 do
      let bit ← getBool c ind
      cWord := or_int cWord (shl_int (u64 (if bit then 1 else 0)) j)
      ind := ind + int 1
    let old ← mutableGet bc kd1
    mutableSet bc (or_int (and_int old mskD1) (and_int cWord (not_int mskD1))) kd1

/--
Julia source: base/bitarray.jl:347-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dumpbitcache(Bc::Vector{UInt64}, bind::Int, C::Vector{Bool}) =
    copy_to_bitarray_chunks!(Bc, ((bind - 1) << 6) + 1, C, 1, min(bitcache_size, (length(Bc)-bind+1) << 6))
```
-/
def dumpBitCache {C P : Type} (bc : Nat) (bind : I64) (c : C)
    (getBool : C → I64 → BitMutationM Bool) (pointer : C → I64 → P)
    (unsafeLoad : P → I64 → BitMutationM U64) (length : Nat → BitMutationM I64) : BitMutationM Unit := do
  let capacity := (← length bc) - bind + int 1
  let count := if capacity < int (64 * 64) then capacity else int (64 * 64)
  copyToBitArrayChunksBool bc ((shl_int (bind - int 1) (int 6)) + int 1) c (int 1)
    count getBool pointer unsafeLoad

/--
Julia source: base/bitarray.jl:352-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(B::BitArray, i::Int=0)
    i >= length(B) && return nothing
    (B.chunks[_div64(i)+1] & (UInt64(1)<<_mod64(i)) != 0, i+1)
end
```
-/
def bitArrayIterate {N : Nat} (B : BitArray N) (i : I64 := int 0) : BitMutationM (Option (Bool × I64)) := do
  if i ≥ B.len then return none
  let word ← mutableGet B.chunks (div64 i + int 1)
  let mask := shl_int (u64 1) (mod64 i)
  return some (and_int word mask != u64 0, i + int 1)

/--
Julia source: base/bitarray.jl:359-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(B::BitArray) = BitArray(undef, size(B))
```
-/
def similarBitArray {N : Nat} (allocate : List I64 → BitMutationM (BitArray N))
    (B : BitArray N) : BitMutationM (BitArray N) := allocate B.dims

/--
Julia source: base/bitarray.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(B::BitArray, T::Type{Bool}, dims::Dims) = BitArray(undef, dims)
```
-/
def similarBitArrayBool {N OutRank : Nat}
    (allocate : List I64 → BitMutationM (BitArray OutRank))
    (_B : BitArray N) (dims : List I64) : BitMutationM (BitArray OutRank) :=
  allocate dims

/--
Julia source: base/bitarray.jl:366-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(B::BitArray, T::Type, dims::Dims) = Array{T}(undef, dims)
```
-/
-- Source: base/bitarray.jl:366-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def similarBitArrayOtherDispatch {m : Type → Type} {N : Nat} {T A : Type}
    (allocate : T → List I64 → m A) (_B : BitArray N) (target : T)
    (dims : List I64) : m A := allocate target dims

-- Source: base/bitarray.jl:366-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def similarBitArrayOther {N : Nat} {T A : Type} (allocate : List I64 → BitMutationM A)
    (B : BitArray N) (typeToken : T) (dims : List I64) : BitMutationM A :=
  similarBitArrayOtherDispatch (fun _ shape => allocate shape) B typeToken dims

/--
Julia source: base/bitarray.jl:368-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fill!(B::BitArray, x)
    y = convert(Bool, x)
    isempty(B) && return B
    Bc = B.chunks
    if !y
        fill!(Bc, 0)
    else
        fill!(Bc, _msk64)
        Bc[end] &= _msk_end(B)
    end
    return B
end
```
-/
def fillBitArray {N : Nat} {X : Type} (convertBool : X → BitMutationM Bool)
    (fillChunksVector : Nat → U64 → BitMutationM Unit) (B : BitArray N) (x : X) : BitMutationM (BitArray N) := do
  let y ← convertBool x
  if B.len == int 0 then return B
  if !y then
    fillChunksVector B.chunks (u64 0)
  else
    fillChunksVector B.chunks u64Max
    let chunksLen ← mutableLength B.chunks
    let last ← mutableGet B.chunks chunksLen
    mutableSet B.chunks (and_int last (maskEndArray B)) (int 1)
  return B

/--
Julia source: base/bitarray.jl:661-666 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function unsafe_bitgetindex(Bc::Vector{UInt64}, i::Int)
    i1, i2 = get_chunks_id(i)
    u = UInt64(1) << i2
    @inbounds r = (Bc[i1] & u) != 0
    return r
end
```
-/
def unsafeBitGetIndex (bc : Nat) (i : I64) : BitMutationM Bool := do
  let (i1, i2) := getChunksId i
  let u := shl_int (u64 1) i2
  return and_int (← mutableGet bc i1) u != u64 0

/--
Julia source: base/bitarray.jl:680-686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _unsafe_bitsetindex!(Bc::Array{UInt64}, x::Bool, i1::Int, i2::Int)
    u = UInt64(1) << i2
    @inbounds begin
        c = Bc[i1]
        Bc[i1] = ifelse(x, c | u, c & ~u)
    end
end
```
-/
def unsafeBitSetIndexAt (bc : Nat) (x : Bool) (i1 i2 : I64) : BitMutationM Unit := do
  let u := shl_int (u64 1) i2
  let c ← mutableGet bc i1
  mutableSet bc (if x then or_int c u else and_int c (not_int u)) i1

/--
Julia source: base/bitarray.jl:675-678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function unsafe_bitsetindex!(Bc::Array{UInt64}, x::Bool, i::Int)
    i1, i2 = get_chunks_id(i)
    _unsafe_bitsetindex!(Bc, x, i1, i2)
end
```
-/
def unsafeBitSetIndex (bc : Nat) (x : Bool) (i : I64) : BitMutationM Unit := do
  let (i1, i2) := getChunksId i
  unsafeBitSetIndexAt bc x i1 i2

/--
Julia source: base/bitarray.jl:668-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function getindex(B::BitArray, i::Int)
    @boundscheck checkbounds(B, i)
    unsafe_bitgetindex(B.chunks, i)
end
```
-/
def bitArrayGetIndex {N : Nat} (checkbounds : BitArray N → I64 → BitMutationM Unit)
    (B : BitArray N) (i : I64) : BitMutationM Bool := do
  checkbounds B i
  unsafeBitGetIndex B.chunks i

/--
Julia source: base/bitarray.jl:688-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setindex!(B::BitArray, x, i::Int)
    @boundscheck checkbounds(B, i)
    unsafe_bitsetindex!(B.chunks, convert(Bool, x), i)
    return B
end
```
-/
def bitArraySetIndex {N : Nat} {X : Type}
    (checkbounds : BitArray N → I64 → BitMutationM Unit) (convertBool : X → BitMutationM Bool)
    (B : BitArray N) (x : X) (i : I64) : BitMutationM (BitArray N) := do
  checkbounds B i
  unsafeBitSetIndex B.chunks (← convertBool x) i
  return B

/--
Julia source: base/bitarray.jl:707-735 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _unsafe_setindex!(B::BitArray, X::AbstractArray, I::BitArray)
    Bc = B.chunks
    Ic = I.chunks
    length(Bc) == length(Ic) || throw_boundserror(B, I)
    lc = length(Bc)
    last_chunk_len = _mod64(length(B)-1)+1

    lx = length(X)
    c = 0
    Xi = first(eachindex(X))
    for i = 1:lc
        @inbounds Imsk = Ic[i]
        @inbounds C = Bc[i]
        u = UInt64(1)
        for _ = 1:(i < lc ? 64 : last_chunk_len)
            if Imsk & u != 0
                c == lx && throw_setindex_mismatch(X, count(I))
                @inbounds x = convert(Bool, X[Xi])
                C = ifelse(x, C | u, C & ~u)
                Xi = nextind(X, Xi)
                c += 1
            end
            u <<= 1
        end
        @inbounds Bc[i] = C
    end
    c == lx || throw_setindex_mismatch(X, count(I))
    return B
end
```
-/
def bitArrayUnsafeSetIndexMask {N : Nat} {A I : Type}
    (throwBounds : BitArray N → BitArray N → BitMutationM Unit)
    (length : A → I64) (firstIndex : A → I64) (nextind : A → I64 → I64)
    (getBool : A → I64 → BitMutationM Bool) (convertBool : A → I64 → BitMutationM Bool)
    (countMask : BitArray N → BitMutationM I64)
    (throwMismatch : A → I64 → BitMutationM Unit)
    (B : BitArray N) (x : A) (mask : BitArray N) : BitMutationM (BitArray N) := do
  let Bc := B.chunks
  let Ic := mask.chunks
  let nBc ← mutableLength Bc
  let nIc ← mutableLength Ic
  if nBc != nIc then throwBounds B mask
  let lc := nBc
  let lastChunkLen := mod64 (B.len - int 1) + int 1
  let lx := length x
  let mut c := int 0
  let mut xi := firstIndex x
  for i in intRange (int 1) lc do
    let mut imsk ← mutableGet Ic i
    let mut current ← mutableGet Bc i
    let limit := if i < lc then int 64 else lastChunkLen
    let mut u := u64 1
    for _ in intRange (int 1) limit do
      if and_int imsk u != u64 0 then
        if c == lx then throwMismatch x (← countMask mask)
        let v ← convertBool x xi
        current := if v then or_int current u else and_int current (not_int u)
        xi := nextind x xi
        c := c + int 1
      u := shl_int u (u64 1)
    mutableSet Bc current i
  if c != lx then throwMismatch x (← countMask mask)
  return B

/--
Julia source: base/bitarray.jl:739-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function push!(B::BitVector, item)
    # convert first so we don't grow the bitarray if the assignment won't work
    item = convert(Bool, item)

    Bc = B.chunks

    l = _mod64(length(B))
    if l == 0
        _growend!(Bc, 1)
        Bc[end] = UInt64(0)
    end
    B.len += 1
    if item
        B[end] = true
    end
    return B
end
```
-/
def bitVectorPush {X : Type} (convertBool : X → BitMutationM Bool)
    (checkbounds : BitVector → I64 → BitMutationM Unit)
    (B : BitVector) (item : X) : BitMutationM BitVector := do
  let item ← convertBool item
  let Bc := B.chunks
  let l := mod64 B.len
  if l == int 0 then
    growChunkVector Bc (int 1)
    mutableSet Bc (u64 0) (← mutableLength Bc)
  let B := { B with len := B.len + int 1 }
  if item then
    let _ ← bitArraySetIndex checkbounds (fun b => pure b) B item B.len
    pure ()
  return B

/--
Julia source: base/bitarray.jl:757-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function append!(B::BitVector, items::BitVector)
    n0 = length(B)
    n1 = length(items)
    n1 == 0 && return B
    n = checked_add(n0, n1)
    Bc = B.chunks
    k0 = length(Bc)
    k1 = num_bit_chunks(n)
    if k1 > k0
        _growend!(Bc, k1 - k0)
        Bc[end] = UInt64(0)
    end
    B.len = n
    copy_chunks!(Bc, n0+1, items.chunks, 1, n1)
    return B
end
```
-/
def bitVectorAppend (checkedAdd : I64 → I64 → BitMutationM I64)
    (B items : BitVector) : BitMutationM BitVector := do
  let n0 := B.len
  let n1 := items.len
  if n1 == int 0 then return B
  let n ← checkedAdd n0 n1
  let Bc := B.chunks
  let k0 ← mutableLength Bc
  let k1 := numBitChunks n
  if k1 > k0 then
    growChunkVector Bc (k1 - k0)
    mutableSet Bc (u64 0) (← mutableLength Bc)
  let B := { B with len := n }
  copyChunks Bc (n0 + int 1) items.chunks (int 1) n1
  return B

/--
Julia source: base/bitarray.jl:774-774 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
append!(B::BitVector, items) = append!(B, BitVector(items))
```
-/
def bitVectorAppendIterable {I : Type} (convert : I → BitMutationM BitVector)
    (append : BitVector → BitVector → BitMutationM BitVector) (B : BitVector) (items : I) : BitMutationM BitVector := do
  append B (← convert items)

/--
Julia source: base/bitarray.jl:775-775 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
append!(A::Vector{Bool}, items::BitVector) = append!(A, Array(items))
```
-/
def boolArrayAppendBitVector {A : Type} (append : A → BitVector → BitMutationM A)
    (A0 : A) (items : BitVector) : BitMutationM A := append A0 items

/--
Julia source: base/bitarray.jl:777-793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function prepend!(B::BitVector, items::BitVector)
    n0 = length(B)
    n1 = length(items)
    n1 == 0 && return B
    n = checked_add(n0, n1)
    Bc = B.chunks
    k0 = length(Bc)
    k1 = num_bit_chunks(n)
    if k1 > k0
        _growend!(Bc, k1 - k0)
        Bc[end] = UInt64(0)
    end
    B.len = n
    copy_chunks!(Bc, 1 + n1, Bc, 1, n0)
    copy_chunks!(Bc, 1, items.chunks, 1, n1)
    return B
end
```
-/
def bitVectorPrepend (checkedAdd : I64 → I64 → BitMutationM I64)
    (B items : BitVector) : BitMutationM BitVector := do
  let n0 := B.len
  let n1 := items.len
  if n1 == int 0 then return B
  let n ← checkedAdd n0 n1
  let Bc := B.chunks
  let k0 ← mutableLength Bc
  let k1 := numBitChunks n
  if k1 > k0 then
    growChunkVector Bc (k1 - k0)
    mutableSet Bc (u64 0) (← mutableLength Bc)
  let B := { B with len := n }
  copyChunks Bc (int 1 + n1) Bc (int 1) n0
  copyChunks Bc (int 1) items.chunks (int 1) n1
  return B

/--
Julia source: base/bitarray.jl:795-795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prepend!(B::BitVector, items) = prepend!(B, BitArray(items))
```
-/
-- Source: base/bitarray.jl:795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitVectorPrependIterableDispatch {m : Type → Type} [Monad m] {B I A R : Type}
    (toBitArray : I → m A) (prepend : B → A → m R) (target : B) (items : I) : m R := do
  prepend target (← toBitArray items)

def bitVectorPrependIterable {I : Type} (convert : I → BitMutationM BitVector)
    (prepend : BitVector → BitVector → BitMutationM BitVector) (B : BitVector) (items : I) : BitMutationM BitVector := do
  bitVectorPrependIterableDispatch convert prepend B items

/--
Julia source: base/bitarray.jl:796-796 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
prepend!(A::Vector{Bool}, items::BitVector) = prepend!(A, Array(items))
```
-/
def boolArrayPrependBitVector {A : Type} (prepend : A → BitVector → BitMutationM A)
    (A0 : A) (items : BitVector) : BitMutationM A := prepend A0 items

/--
Julia source: base/bitarray.jl:798-801 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sizehint!(B::BitVector, sz::Integer)
    sizehint!(B.chunks, num_bit_chunks(sz))
    return B
end
```
-/
def bitVectorSizehint (sizehint : Nat → I64 → BitMutationM Unit)
    (B : BitVector) (sz : I64) : BitMutationM BitVector := do
  sizehint B.chunks (numBitChunks sz)
  return B

/--
Julia source: base/bitarray.jl:955-977 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deleteat!(B::BitVector, r::AbstractUnitRange{Int})
    n = length(B)
    i_f = first(r)
    i_l = last(r)
    1 <= i_f || throw(BoundsError(B, i_f))
    i_l <= n || throw(BoundsError(B, n+1))

    Bc = B.chunks
    new_l = length(B) - length(r)
    delta_k = num_bit_chunks(new_l) - length(Bc)

    copy_chunks!(Bc, i_f, Bc, i_l+1, n-i_l)

    delta_k < 0 && _deleteend!(Bc, -delta_k)

    B.len = new_l

    if new_l > 0
        Bc[end] &= _msk_end(new_l)
    end

    return B
end
```
-/
def bitVectorDeleteRange (rangeLength : BitRange → I64) (B : BitVector) (r : BitRange) : BitMutationM BitVector := do
  let n := B.len
  let iF := r.first
  let iL := r.last
  if iF < int 1 then throw .bounds
  if iL > n then throw .bounds
  let Bc := B.chunks
  let newL := n - rangeLength r
  let deltaK := numBitChunks newL - (← mutableLength Bc)
  copyChunks Bc iF Bc (iL + int 1) (n - iL)
  if deltaK < int 0 then deleteChunkEnd Bc (-deltaK)
  let B := { B with len := newL }
  if newL > int 0 then
    let last ← mutableGet Bc (← mutableLength Bc)
    mutableSet Bc (and_int last (maskEnd newL)) (← mutableLength Bc)
  return B

/--
Julia source: base/bitarray.jl:804-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _resize_int!(B::BitVector, n::Int, first::Bool)
    n0 = length(B)
    n == n0 && return B
    n >= 0 || throw(BoundsError(B, n))
    if n < n0
        r = first ? (1:n0-n) : (n+1:n0)
        deleteat!(B, r)
        return B
    end
    Bc = B.chunks
    k0 = length(Bc)
    k1 = num_bit_chunks(n)
    if k1 > k0
        _growend!(Bc, k1 - k0)
        Bc[end] = UInt64(0)
    end
    if first
        copy_chunks!(Bc, 1 + n - n0, Bc, 1, n0)
    end
    B.len = n
    return B
end
```
-/
def bitVectorResizeInt (rangeLength : BitRange → I64)
    (B : BitVector) (n : I64) (first : Bool) : BitMutationM BitVector := do
  let n0 := B.len
  if n == n0 then return B
  if n < int 0 then throw .bounds
  if n < n0 then
    let r := if first then ⟨int 1, n0 - n⟩ else ⟨n + int 1, n0⟩
    return ← bitVectorDeleteRange rangeLength B r
  let Bc := B.chunks
  let k0 ← mutableLength Bc
  let k1 := numBitChunks n
  if k1 > k0 then
    growChunkVector Bc (k1 - k0)
    mutableSet Bc (u64 0) (← mutableLength Bc)
  if first then copyChunks Bc (int 1 + n - n0) Bc (int 1) n0
  return { B with len := n }

/--
Julia source: base/bitarray.jl:803-803 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
resize!(B::BitVector, n::Integer; first::Bool=false) = _resize_int!(B, Int(n), first)
```
-/
def bitVectorResize {X : Type} (toInt : X → I64) (B : BitVector) (n : X) (first : Bool := false)
    (rangeLength : BitRange → I64) : BitMutationM BitVector :=
  bitVectorResizeInt rangeLength B (toInt n) first

/--
Julia source: base/bitarray.jl:827-837 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pop!(B::BitVector)
    isempty(B) && throw(ArgumentError("argument must not be empty"))
    item = B[end]
    B[end] = false

    l = _mod64(length(B))
    l == 1 && _deleteend!(B.chunks, 1)
    B.len -= 1

    return item
end
```
-/
def bitVectorPop (getindex : BitVector → I64 → BitMutationM Bool)
    (setindex : BitVector → Bool → I64 → BitMutationM BitVector) (B : BitVector) : BitMutationM (BitVector × Bool) := do
  if B.len == int 0 then throw (.argument "argument must not be empty")
  let item ← getindex B B.len
  let _ ← setindex B false B.len
  let l := mod64 B.len
  if l == int 1 then deleteChunkEnd B.chunks (int 1)
  let B := { B with len := B.len - int 1 }
  return (B, item)

/--
Julia source: base/bitarray.jl:839-859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pushfirst!(B::BitVector, item)
    item = convert(Bool, item)

    Bc = B.chunks

    l = _mod64(length(B))
    if l == 0
        _growend!(Bc, 1)
        Bc[end] = UInt64(0)
    end
    B.len += 1
    if B.len == 1
        Bc[1] = item
        return B
    end
    for i = length(Bc) : -1 : 2
        Bc[i] = (Bc[i] << 1) | (Bc[i-1] >>> 63)
    end
    Bc[1] = UInt64(item) | (Bc[1] << 1)
    return B
end
```
-/
def bitVectorPushfirst {X : Type} (convertBool : X → BitMutationM Bool)
    (B : BitVector) (item : X) : BitMutationM BitVector := do
  let item ← convertBool item
  let Bc := B.chunks
  let l := mod64 B.len
  if l == int 0 then
    growChunkVector Bc (int 1)
    mutableSet Bc (u64 0) (← mutableLength Bc)
  let B := { B with len := B.len + int 1 }
  if B.len == int 1 then
    mutableSet Bc (u64 (if item then 1 else 0)) (int 1)
    return B
  for i in (intRange (int 2) (← mutableLength Bc)).reverse do
    let current ← mutableGet Bc i
    let previous ← mutableGet Bc (i - int 1)
    mutableSet Bc (or_int (shl_int current (int 1)) (lshr_int previous (int 63))) i
  let first ← mutableGet Bc (int 1)
  mutableSet Bc (or_int (u64 (if item then 1 else 0)) (shl_int first (int 1))) (int 1)
  return B

/--
Julia source: base/bitarray.jl:861-882 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function popfirst!(B::BitVector)
    isempty(B) && throw(ArgumentError("argument must not be empty"))
    @inbounds begin
        item = B[1]

        Bc = B.chunks

        for i = 1 : length(Bc) - 1
            Bc[i] = (Bc[i] >>> 1) | (Bc[i+1] << 63)
        end

        l = _mod64(length(B))
        if l == 1
            _deleteend!(Bc, 1)
        else
            Bc[end] >>>= 1
        end
        B.len -= 1
    end

    return item
end
```
-/
def bitVectorPopfirst (B : BitVector) : BitMutationM (BitVector × Bool) := do
  if B.len == int 0 then throw (.argument "argument must not be empty")
  let item ← unsafeBitGetIndex B.chunks (int 1)
  let Bc := B.chunks
  let nc ← mutableLength Bc
  for i in intRange (int 1) (nc - int 1) do
    let current ← mutableGet Bc i
    let next ← mutableGet Bc (i + int 1)
    mutableSet Bc (or_int (lshr_int current (int 1)) (shl_int next (int 63))) i
  let l := mod64 B.len
  if l == int 1 then
    deleteChunkEnd Bc (int 1)
  else
    let last ← mutableGet Bc nc
    mutableSet Bc (lshr_int last (int 1)) nc
  let B := { B with len := B.len - int 1 }
  return (B, item)

/--
Julia source: base/bitarray.jl:885-911 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _insert_int!(B::BitVector, i::Int, item)
    i = Int(i)
    n = length(B)
    1 <= i <= n+1 || throw(BoundsError(B, i))
    item = convert(Bool, item)

    Bc = B.chunks

    k, j = get_chunks_id(i)

    l = _mod64(length(B))
    if l == 0
        _growend!(Bc, 1)
        Bc[end] = UInt64(0)
    end
    B.len += 1

    for t = length(Bc) : -1 : k + 1
        Bc[t] = (Bc[t] << 1) | (Bc[t - 1] >>> 63)
    end

    msk_aft = (_msk64 << j)
    msk_bef = ~msk_aft
    Bc[k] = (msk_bef & Bc[k]) | ((msk_aft & Bc[k]) << 1)
    B[i] = item
    B
end
```
-/
def bitVectorInsertInt {X : Type} (convertBool : X → BitMutationM Bool)
    (B : BitVector) (i : I64) (item : X) : BitMutationM BitVector := do
  let i := i
  let n := B.len
  if !(int 1 ≤ i ∧ i ≤ n + int 1) then throw .bounds
  let item ← convertBool item
  let Bc := B.chunks
  let (k, j) := getChunksId i
  let l := mod64 B.len
  if l == int 0 then
    growChunkVector Bc (int 1)
    mutableSet Bc (u64 0) (← mutableLength Bc)
  let B := { B with len := B.len + int 1 }
  let nc ← mutableLength Bc
  for t in (intRange (k + int 1) nc).reverse do
    let current ← mutableGet Bc t
    let previous ← mutableGet Bc (t - int 1)
    mutableSet Bc (or_int (shl_int current (int 1)) (lshr_int previous (int 63))) t
  let mskAft := shl_int u64Max j
  let mskBef := not_int mskAft
  let word ← mutableGet Bc k
  mutableSet Bc (or_int (and_int mskBef word) (shl_int (and_int mskAft word) (int 1))) k
  let _ ← bitArraySetIndex (fun _ _ => pure ()) (fun x => pure x) B item i
  return B

/--
Julia source: base/bitarray.jl:884-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
insert!(B::BitVector, i::Integer, item) = _insert_int!(B, Int(i), item)
```
-/
def bitVectorInsert {X I : Type} (toInt : I → I64) (insertInt : BitVector → I64 → X → BitMutationM BitVector)
    (B : BitVector) (i : I) (item : X) : BitMutationM BitVector := insertInt B (toInt i) item

/--
Julia source: base/bitarray.jl:913-944 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _deleteat!(B::BitVector, i::Int)
    k, j = get_chunks_id(i)

    msk_bef = _msk64 >>> (63 - j)
    msk_aft = ~msk_bef
    msk_bef >>>= 1

    Bc = B.chunks

    @inbounds begin
        Bc[k] = (msk_bef & Bc[k]) | ((msk_aft & Bc[k]) >> 1)
        if length(Bc) > k
            Bc[k] |= (Bc[k + 1] << 63)
        end

        for t = k + 1 : length(Bc) - 1
            Bc[t] = (Bc[t] >>> 1) | (Bc[t + 1] << 63)
        end

        l = _mod64(length(B))

        if l == 1
            _deleteend!(Bc, 1)
        elseif length(Bc) > k
            Bc[end] >>>= 1
        end
    end

    B.len -= 1

    return B
end
```
-/
def bitVectorDeleteAtInt (B : BitVector) (i : I64) : BitMutationM BitVector := do
  let (k, j) := getChunksId i
  let mskBef := lshr_int u64Max (int 63 - j)
  let mskAft := not_int mskBef
  let mskBefShift := lshr_int mskBef (int 1)
  let Bc := B.chunks
  let word ← mutableGet Bc k
  let mut value := or_int (and_int mskBefShift word) (lshr_int (and_int mskAft word) (int 1))
  let nc ← mutableLength Bc
  if nc > k then value := or_int value (shl_int (← mutableGet Bc (k + int 1)) (int 63))
  mutableSet Bc value k
  for t in intRange (k + int 1) (nc - int 1) do
    let current ← mutableGet Bc t
    let next ← mutableGet Bc (t + int 1)
    mutableSet Bc (or_int (lshr_int current (int 1)) (shl_int next (int 63))) t
  let l := mod64 B.len
  if l == int 1 then deleteChunkEnd Bc (int 1)
  else if nc > k then
    let last ← mutableGet Bc nc
    mutableSet Bc (lshr_int last (int 1)) nc
  return { B with len := B.len - int 1 }

/--
Julia source: base/bitarray.jl:946-953 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deleteat!(B::BitVector, i::Integer)
    i isa Bool && depwarn("passing Bool as an index is deprecated", :deleteat!)
    i = Int(i)
    n = length(B)
    1 <= i <= n || throw(BoundsError(B, i))

    return _deleteat!(B, i)
end
```
-/
def bitVectorDeleteAt {I : Type} (isBool : I → Bool) (deprecate : String → BitMutationM Unit)
    (toInt : I → I64) (B : BitVector) (i : I) : BitMutationM BitVector := do
  if isBool i then deprecate "passing Bool as an index is deprecated"
  let i := toInt i
  if !(int 1 ≤ i ∧ i ≤ B.len) then throw .bounds
  bitVectorDeleteAtInt B i

/--
Julia source: base/bitarray.jl:979-1020 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deleteat!(B::BitVector, inds)
    n = new_l = length(B)
    y = iterate(inds)
    y === nothing && return B

    Bc = B.chunks

    (p, s) = y
    checkbounds(B, p)
    p isa Bool && throw(ArgumentError("invalid index $p of type Bool"))
    q = p+1
    new_l -= 1
    y = iterate(inds, s)
    while y !== nothing
        (i, s) = y
        if !(q <= i <= n)
            i isa Bool && throw(ArgumentError("invalid index $i of type Bool"))
            i < q && throw(ArgumentError("indices must be unique and sorted"))
            throw(BoundsError(B, i))
        end
        new_l -= 1
        if i > q
            copy_chunks!(Bc, Int(p), Bc, Int(q), Int(i-q))
            p += i-q
        end
        q = i+1
        y = iterate(inds, s)
    end

    q <= n && copy_chunks!(Bc, Int(p), Bc, Int(q), Int(n-q+1))

    delta_k = num_bit_chunks(new_l) - length(Bc)
    delta_k < 0 && _deleteend!(Bc, -delta_k)

    B.len = new_l

    if new_l > 0
        Bc[end] &= _msk_end(new_l)
    end

    return B
end
```
-/
def bitVectorDeleteAtIndices {I S : Type} (iterate : I → Option (I64 × S))
    (next : I → S → Option (I64 × S)) (checkbounds : BitVector → I64 → BitMutationM Unit) (isBool : I64 → Bool)
    (toInt : I64 → I64) (B : BitVector) (inds : I) : BitMutationM BitVector := do
  let n := B.len
  let mut newL := n
  let mut y := iterate inds
  let (p0, s0) ← match y with
    | none => return B
    | some pair => pure pair
  let p := toInt p0
  checkbounds B p
  if isBool p then throw (.argument "invalid Bool index")
  let mut p := p
  let mut q := p + int 1
  newL := newL - int 1
  y := next inds s0
  let Bc := B.chunks
  while y.isSome do
    match y with
    | none => pure ()
    | some (i0, s) => do
      let i := toInt i0
      if !(q ≤ i ∧ i ≤ n) then
        if isBool i then throw (Error.argument "invalid Bool index")
        if i < q then throw (Error.argument "indices must be unique and sorted")
        throw Error.bounds
      newL := newL - int 1
      if i > q then
        copyChunks Bc p Bc q (i - q)
        p := p + i - q
      q := i + int 1
      y := next inds s
  if q ≤ n then copyChunks Bc p Bc q (n - q + int 1)
  let deltaK := numBitChunks newL - (← mutableLength Bc)
  if deltaK < int 0 then deleteChunkEnd Bc (-deltaK)
  let B := { B with len := newL }
  if newL > int 0 then
    let last ← mutableGet Bc (← mutableLength Bc)
    mutableSet Bc (and_int last (maskEnd newL)) (← mutableLength Bc)
  return B

/--
Julia source: base/bitarray.jl:1022-1061 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function deleteat!(B::BitVector, inds::AbstractVector{Bool})
    length(inds) == length(B) || throw(BoundsError(B, inds))

    n = new_l = length(B)
    y = findfirst(inds)
    y === nothing && return B

    Bc = B.chunks

    p = y
    s = y + 1
    checkbounds(B, p)
    q = p + 1
    new_l -= 1
    y = findnext(inds, s)
    while y !== nothing
        i = y
        s = y + 1
        new_l -= 1
        if i > q
            copy_chunks!(Bc, Int(p), Bc, Int(q), Int(i-q))
            p += i - q
        end
        q = i + 1
        y = findnext(inds, s)
    end

    q <= n && copy_chunks!(Bc, Int(p), Bc, Int(q), Int(n - q + 1))

    delta_k = num_bit_chunks(new_l) - length(Bc)
    delta_k < 0 && _deleteend!(Bc, -delta_k)

    B.len = new_l

    if new_l > 0
        Bc[end] &= _msk_end(new_l)
    end

    return B
end
```
-/
def bitVectorDeleteAtBoolMask {I : Type} (length : I → I64) (findfirst : I → BitMutationM (Option I64))
    (findnext : I → I64 → BitMutationM (Option I64))
    (checkbounds : BitVector → I64 → BitMutationM Unit) (B : BitVector) (inds : I) : BitMutationM BitVector := do
  if length inds != B.len then throw .bounds
  let n := B.len
  let mut newL := B.len
  let mut y ← findfirst inds
  if y.isNone then return B
  let Bc := B.chunks
  let mut p := y.get!
  let mut s := p + int 1
  checkbounds B p
  let mut q := p + int 1
  newL := newL - int 1
  y ← findnext inds s
  while y.isSome do
    let i := y.get!
    s := i + int 1
    newL := newL - int 1
    if i > q then
      copyChunks Bc p Bc q (i - q)
      p := p + i - q
    q := i + int 1
    y ← findnext inds s
  if q ≤ n then copyChunks Bc p Bc q (n - q + int 1)
  let deltaK := numBitChunks newL - (← mutableLength Bc)
  if deltaK < int 0 then deleteChunkEnd Bc (-deltaK)
  let B := { B with len := newL }
  if newL > int 0 then
    let last ← mutableGet Bc (← mutableLength Bc)
    mutableSet Bc (and_int last (maskEnd newL)) (← mutableLength Bc)
  return B

/--
Julia source: base/bitarray.jl:1063-1063 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keepat!(B::BitVector, inds) = _keepat!(B, inds)
```
-/
def bitVectorKeepAt {I : Type} (keep : BitVector → I → BitMutationM BitVector) (B : BitVector) (inds : I) : BitMutationM BitVector := keep B inds

/--
Julia source: base/bitarray.jl:1064-1064 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
keepat!(B::BitVector, inds::AbstractVector{Bool}) = _keepat!(B, inds)
```
-/
def bitVectorKeepAtMask {I : Type} (keep : BitVector → I → BitMutationM BitVector) (B : BitVector) (inds : I) : BitMutationM BitVector := keep B inds

/--
Julia source: base/bitarray.jl:1126-1134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function splice!(B::BitVector, r::Union{AbstractUnitRange{Int}, Integer}, ins)
    Bins = BitVector(undef, length(ins))
    i = 1
    for x in ins
        Bins[i] = x
        i += 1
    end
    return splice!(B, r, Bins)
end
```
-/
def bitVectorSpliceIterable {I S : Type} (length : I → I64)
    (iterate : I → Option (Bool × S)) (next : I → S → Option (Bool × S))
    (allocate : I64 → BitMutationM BitVector) (setindex : BitVector → Bool → I64 → BitMutationM BitVector)
    (splice : BitVector → BitRange → BitVector → BitMutationM BitVector)
    (B : BitVector) (r : BitRange) (ins : I) : BitMutationM BitVector := do
  let Bins ← allocate (length ins)
  let mut i := int 1
  let mut y := iterate ins
  while y.isSome do
    match y with
    | none => pure ()
    | some (x, s) => do
      let _ ← setindex Bins x i
      i := i + int 1
      y := next ins s
  splice B r Bins

/--
Julia source: base/bitarray.jl:1087-1124 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _splice_int!(B::BitVector, r, ins)
    n = length(B)
    i_f, i_l = first(r), last(r)
    1 <= i_f <= n+1 || throw(BoundsError(B, i_f))
    i_l <= n || throw(BoundsError(B, n+1))

    Bins = convert(BitArray, ins)

    if (i_f > n)
        append!(B, Bins)
        return BitVector()
    end

    v = B[r]  # TODO: change to a copy if/when subscripting becomes an ArrayView

    Bc = B.chunks

    lins = length(Bins)
    ldel = length(r)

    new_l = length(B) + lins - ldel
    delta_k = num_bit_chunks(new_l) - length(Bc)

    delta_k > 0 && _growend!(Bc, delta_k)

    copy_chunks!(Bc, i_f+lins, Bc, i_l+1, n-i_l)
    copy_chunks!(Bc, i_f, Bins.chunks, 1, lins)

    delta_k < 0 && _deleteend!(Bc, -delta_k)

    B.len = new_l

    if new_l > 0
        Bc[end] &= _msk_end(new_l)
    end

    return v
end
```
-/
def bitVectorSpliceInt {A : Type} (convertBitArray : A → BitMutationM (BitArray 1))
    (checkedAdd : I64 → I64 → BitMutationM I64)
    (slice : BitVector → BitRange → BitMutationM BitVector)
    (empty : BitMutationM BitVector) (rangeLength : BitRange → I64)
    (setLength : BitVector → I64 → BitMutationM Unit) (B : BitVector) (r : BitRange) (ins : A) : BitMutationM BitVector := do
  let n := B.len
  let iF := r.first
  let iL := r.last
  if !(int 1 ≤ iF ∧ iF ≤ n + int 1) then throw .bounds
  if iL > n then throw .bounds
  let bins ← convertBitArray ins
  if iF > n then
    let _ ← bitVectorAppend checkedAdd B bins
    return ← empty
  let v ← slice B r
  let Bc := B.chunks
  let lins := bins.len
  let ldel := rangeLength r
  let newL ← checkedAdd (B.len + lins) (-ldel)
  let deltaK := numBitChunks newL - (← mutableLength Bc)
  if deltaK > int 0 then growChunkVector Bc deltaK
  copyChunks Bc (iF + lins) Bc (iL + int 1) (n - iL)
  copyChunks Bc iF bins.chunks (int 1) lins
  if deltaK < int 0 then deleteChunkEnd Bc (-deltaK)
  setLength B newL
  if newL > int 0 then
    let last ← mutableGet Bc (← mutableLength Bc)
    mutableSet Bc (and_int last (maskEnd newL)) (← mutableLength Bc)
  return v

/--
Julia source: base/bitarray.jl:1082-1085 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function splice!(B::BitVector, r::Union{AbstractUnitRange{Int}, Integer}, ins::AbstractArray = _default_bit_splice)
    r isa Bool && depwarn("passing Bool as an index is deprecated", :splice!)
    _splice_int!(B, isa(r, AbstractUnitRange{Int}) ? r : Int(r), ins)
end
```
-/
def bitVectorSpliceDefault {I : Type} (isBool : I → Bool) (deprecate : BitMutationM Unit)
    (toInt : I → I64) (spliceInt : BitVector → BitRange → BitSource → BitMutationM BitVector)
    (B : BitVector) (r : I) (ins : BitSource) : BitMutationM BitVector := do
  if isBool r then deprecate
  spliceInt B ⟨toInt r, toInt r⟩ ins

/--
Julia source: base/bitarray.jl:1137-1141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function empty!(B::BitVector)
    _deleteend!(B.chunks, length(B.chunks))
    B.len = 0
    return B
end
```
-/
def bitVectorEmptyBang (deleteEnd : Nat → I64 → BitMutationM Unit) (B : BitVector) : BitMutationM BitVector := do
  deleteEnd B.chunks (← mutableLength B.chunks)
  return { B with len := int 0 }

/--
Julia source: base/bitarray.jl:449-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_copyto!(dest::BitArray, doffs::Integer, src::Union{BitArray,Array}, soffs::Integer, n::Integer)
    copy_to_bitarray_chunks!(dest.chunks, Int(doffs), src, Int(soffs), Int(n))
    return dest
end
```
-/
def bitArrayUnsafeCopyto {N : Nat} {P : Type} (getBool : Nat → I64 → BitMutationM Bool)
    (pointer : Nat → I64 → P) (unsafeLoad : P → I64 → BitMutationM U64)
    (dest : BitArray N) (doffs : I64) (src : BitSource) (soffs n : I64) : BitMutationM (BitArray N) := do
  match src with
  | .bitArray _ B => copyToBitArrayChunksBit dest.chunks doffs B soffs n
  | .boolArray C => copyToBitArrayChunksBool dest.chunks doffs C soffs n getBool pointer unsafeLoad
  return dest

/--
Julia source: base/bitarray.jl:456-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _copyto_int!(dest::BitArray, doffs::Int, src::Union{BitArray,Array}, soffs::Int, n::Int)
    n == 0 && return dest
    n < 0 && throw(ArgumentError("Number of elements to copy must be non-negative."))
    soffs < 1 && throw(BoundsError(src, soffs))
    doffs < 1 && throw(BoundsError(dest, doffs))
    n > length(src) - soffs + 1 && throw(BoundsError(src, length(src)+1))
    n > length(dest) - doffs + 1 && throw(BoundsError(dest, length(dest)+1))
    return unsafe_copyto!(dest, doffs, src, soffs, n)
end
```
-/
def bitArrayCopytoInt {N : Nat} {P : Type} (sourceLength : BitSource → I64)
    (getBool : Nat → I64 → BitMutationM Bool) (pointer : Nat → I64 → P)
    (unsafeLoad : P → I64 → BitMutationM U64)
    (dest : BitArray N) (doffs : I64) (src : BitSource) (soffs n : I64) : BitMutationM (BitArray N) := do
  if n == int 0 then return dest
  if n < int 0 then throw (.argument "Number of elements to copy must be non-negative.")
  if soffs < int 1 then throw .bounds
  if doffs < int 1 then throw .bounds
  if n > sourceLength src - soffs + int 1 then throw .bounds
  if n > dest.len - doffs + int 1 then throw .bounds
  bitArrayUnsafeCopyto getBool pointer unsafeLoad dest doffs src soffs n

/--
Julia source: base/bitarray.jl:476-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _bitreshape(B::BitArray, dims::NTuple{N,Int}) where N
    len = Core.checked_dims(dims...)
    len == length(B) ||
        throw(DimensionMismatch("new dimensions $(dims) must be consistent with array length $(length(B))"))
    Br = BitArray{N}(undef, ntuple(i->0,Val(N))...)
    Br.chunks = B.chunks
    Br.len = len
    N != 1 && (Br.dims = dims)
    return Br
end
```
-/
def bitArrayReshapeInternal {InputRank OutputRank : Nat} (checkedDims : List I64 → BitMutationM I64)
    (allocate : List I64 → BitMutationM (BitArray OutputRank))
    (B : BitArray InputRank) (dims : List I64) : BitMutationM (BitArray OutputRank) := do
  let len ← checkedDims dims
  if len != B.len then throw (.dimensionMismatch "new dimensions must be consistent with array length")
  let Br ← allocate (List.replicate OutputRank (int 0))
  return { Br with chunks := B.chunks, len := len, dims := if OutputRank != 1 then dims else [len] }

/--
Julia source: base/bitarray.jl:507-533 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _copyto_bitarray!(B::BitArray, A::AbstractArray)
    l = length(A)
    l == 0 && return B
    l > length(B) && throw(BoundsError(B, length(B)+1))
    Bc = B.chunks
    nc = num_bit_chunks(l)
    Ai = first(eachindex(A))
    @inbounds begin
        for i = 1:nc-1
            c = UInt64(0)
            for j = 0:63
                c |= (UInt64(convert(Bool, A[Ai])::Bool) << j)
                Ai = nextind(A, Ai)
            end
            Bc[i] = c
        end
        c = UInt64(0)
        tail = _mod64(l - 1) + 1
        for j = 0:tail-1
            c |= (UInt64(convert(Bool, A[Ai])::Bool) << j)
            Ai = nextind(A, Ai)
        end
        msk = _msk_end(tail)
        Bc[nc] = (c & msk) | (Bc[nc] & ~msk)
    end
    return B
end
```
-/
def copytoBitArrayFromAbstract {N : Nat} {A : Type} (length : A → I64)
    (nextind : A → I64 → I64) (firstIndex : A → I64)
    (convertBool : A → I64 → BitMutationM Bool) (B : BitArray N) (a : A)
    : BitMutationM (BitArray N) := do
  let l := length a
  if l == int 0 then return B
  if l > B.len then throw .bounds
  let Bc := B.chunks
  let nc := numBitChunks l
  let mut ai := firstIndex a
  for i in intRange (int 1) (nc - int 1) do
    let mut c := u64 0
    for j in intRange (int 0) (int 63) do
      let x ← convertBool a ai
      c := or_int c (shl_int (u64 (if x then 1 else 0)) j)
      ai := nextind a ai
    mutableSet Bc c i
  let mut c := u64 0
  let tail := mod64 (l - int 1) + int 1
  for j in intRange (int 0) (tail - int 1) do
    let x ← convertBool a ai
    c := or_int c (shl_int (u64 (if x then 1 else 0)) j)
    ai := nextind a ai
  let msk := maskEnd tail
  let old ← mutableGet Bc nc
  mutableSet Bc (or_int (and_int c msk) (and_int old (not_int msk))) nc
  return B

/--
Julia source: base/bitarray.jl:500-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function BitArray{N}(A::AbstractArray{T,N}) where N where T
    B = BitArray(undef, convert(Dims{N}, size(A)::Dims{N}))
    _checkaxs(axes(B), axes(A))
    _copyto_bitarray!(B, A)
    return B::BitArray{N}
end
```
-/
def bitArrayFromAbstractTyped {N : Nat} {A : Type} (size : A → List I64)
    (convertDims : List I64 → BitMutationM (List I64)) (checkAxes : List I64 → A → BitMutationM Unit)
    (undef : List I64 → BitMutationM (BitArray N))
    (length : A → I64) (nextind : A → I64 → I64) (firstIndex : A → I64)
    (convertBool : A → I64 → BitMutationM Bool) (a : A) : BitMutationM (BitArray N) := do
  let dims ← convertDims (size a)
  let B ← undef dims
  checkAxes B.dims a
  copytoBitArrayFromAbstract length nextind firstIndex convertBool B a

/--
Julia source: base/bitarray.jl:498-498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitArray(A::AbstractArray{<:Any,N}) where {N} = BitArray{N}(A)
```
-/
-- Source: base/bitarray.jl:498-498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitArrayFromAbstractDispatch {m : Type → Type} {A R : Type}
    (rank : Nat) (construct : Nat → A → m R) (value : A) : m R := construct rank value

-- Source: base/bitarray.jl:498-498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitArrayFromAbstract {N : Nat} {A : Type}
    (construct : A → BitMutationM (BitArray N)) (a : A) : BitMutationM (BitArray N) :=
  bitArrayFromAbstractDispatch N (fun _ value => construct value) a

/--
Julia source: base/bitarray.jl:489-496 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function Array{T,N}(B::BitArray{N}) where {T,N}
    A = Array{T,N}(undef, size(B))
    Bc = B.chunks
    @inbounds for i = 1:length(A)
        A[i] = unsafe_bitgetindex(Bc, i)
    end
    return A
end
```
-/
def arrayFromBitArray {N : Nat} {A : Type} (allocate : List I64 → BitMutationM A)
    (length : A → I64) (set : A → Bool → I64 → BitMutationM A)
    (B : BitArray N) : BitMutationM A := do
  let a ← allocate B.dims
  let l := length a
  for i in intRange (int 1) l do
    let x ← unsafeBitGetIndex B.chunks i
    let _ ← set a x i
    pure ()
  return a

/--
Julia source: base/bitarray.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
falses(dims::NTuple{N, Integer}) where {N} = fill!(BitArray(undef, dims), false)
```
-/
def falsesIntegerDims {N : Nat} (undef : List I64 → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N)) (dims : List I64) : BitMutationM (BitArray N) := do
  fill (← undef dims) false

/--
Julia source: base/bitarray.jl:397-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
falses(dims::Tuple{}) = fill!(BitArray(undef, dims), false)
```
-/
def falsesEmptyDims {N : Nat} (undef : List I64 → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N)) : BitMutationM (BitArray N) := do
  fill (← undef []) false

/--
Julia source: base/bitarray.jl:398-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
falses(dims::NTuple{N, DimOrInd}) where {N} = fill!(similar(BitArray, dims), false)
```
-/
-- Source: base/bitarray.jl:398-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def falsesAxesDispatch {m : Type → Type} [Monad m] {D A R : Type}
    (similar : D → m A) (fill : A → Bool → m R) (dims : D) : m R := do
  fill (← similar dims) false

-- Source: base/bitarray.jl:398-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def falsesAxes {N : Nat} {D A : Type} (similar : D → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N)) (dims : D) : BitMutationM (BitArray N) :=
  falsesAxesDispatch similar fill dims

/--
Julia source: base/bitarray.jl:415-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trues(dims::NTuple{N, Integer}) where {N} = fill!(BitArray(undef, dims), true)
```
-/
def truesIntegerDims {N : Nat} (undef : List I64 → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N)) (dims : List I64) : BitMutationM (BitArray N) := do
  fill (← undef dims) true

/--
Julia source: base/bitarray.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trues(dims::Tuple{}) = fill!(BitArray(undef, dims), true)
```
-/
def truesEmptyDims {N : Nat} (undef : List I64 → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N)) : BitMutationM (BitArray N) := do
  fill (← undef []) true

/--
Julia source: base/bitarray.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trues(dims::NTuple{N, DimOrInd}) where {N} = fill!(similar(BitArray, dims), true)
```
-/
-- Source: base/bitarray.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def truesAxesDispatch {m : Type → Type} [Monad m] {D A R : Type}
    (similar : D → m A) (fill : A → Bool → m R) (dims : D) : m R := do
  fill (← similar dims) true

-- Source: base/bitarray.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def truesAxes {N : Nat} {D A : Type} (similar : D → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N)) (dims : D) : BitMutationM (BitArray N) :=
  truesAxesDispatch similar fill dims

/--
Julia source: base/bitarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
falses(dims::DimOrInd...) = falses(dims)
```
-/
-- Source: base/bitarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def falsesVarargsDispatch {m : Type → Type} {D R : Type}
    (dispatch : List D → m R) (dims : List D) : m R := dispatch dims

-- Source: base/bitarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def falsesVarargs {N : Nat} {D : Type} (dispatch : List D → BitMutationM (BitArray N))
    (dims : List D) : BitMutationM (BitArray N) := falsesVarargsDispatch dispatch dims

/--
Julia source: base/bitarray.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
falses(dims::NTuple{N, Union{Integer, OneTo}}) where {N} = falses(map(to_dim, dims))
```
-/
def falsesMappedDims {N : Nat} {D : Type} (toDim : D → I64)
    (falses : List I64 → BitMutationM (BitArray N)) (dims : List D) : BitMutationM (BitArray N) :=
  falses (dims.map toDim)

/--
Julia source: base/bitarray.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trues(dims::DimOrInd...) = trues(dims)
```
-/
-- Source: base/bitarray.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def truesVarargsDispatch {m : Type → Type} {D R : Type}
    (dispatch : List D → m R) (dims : List D) : m R := dispatch dims

-- Source: base/bitarray.jl:413-413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def truesVarargs {N : Nat} {D : Type} (dispatch : List D → BitMutationM (BitArray N))
    (dims : List D) : BitMutationM (BitArray N) := truesVarargsDispatch dispatch dims

/--
Julia source: base/bitarray.jl:414-414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
trues(dims::NTuple{N, Union{Integer, OneTo}}) where {N} = trues(map(to_dim, dims))
```
-/
def truesMappedDims {N : Nat} {D : Type} (toDim : D → I64)
    (trues : List I64 → BitMutationM (BitArray N)) (dims : List D) : BitMutationM (BitArray N) :=
  trues (dims.map toDim)

/--
Julia source: base/bitarray.jl:419-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function one(x::BitMatrix)
    m, n = size(x)
    m == n || throw(DimensionMismatch("multiplicative identity defined only for square matrices"))
    a = falses(n, n)
    for i = 1:n
        a[i,i] = true
    end
    return a
end
```
-/
def bitMatrixOne  (size : BitMatrix → BitMutationM (I64 × I64))
    (falses : List I64 → BitMutationM BitMatrix)
    (setIndex : BitMatrix → Bool → List I64 → BitMutationM BitMatrix)
    (x : BitMatrix) : BitMutationM BitMatrix := do
  let (m, n) ← size x
  if m != n then throw (.dimensionMismatch "multiplicative identity defined only for square matrices")
  let a ← falses [n, n]
  for i in intRange (int 1) n do
    let _ ← setIndex a true [i, i]
    pure ()
  return a

/--
Julia source: base/bitarray.jl:634-656 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fill_bitarray_from_itr!(B::BitArray, itr)
    C = Vector{Bool}(undef, bitcache_size)
    Bc = B.chunks
    ind = 1
    cind = 1
    y = iterate(itr)
    while y !== nothing
        x, st = y
        @inbounds C[ind] = x
        ind += 1
        if ind > bitcache_size
            dumpbitcache(Bc, cind, C)
            cind += bitcache_chunks
            ind = 1
        end
        y = iterate(itr, st)
    end
    if ind > 1
        @inbounds C[ind:bitcache_size] .= false
        dumpbitcache(Bc, cind, C)
    end
    return B
end
```
-/
def fillBitArrayFromItr {N : Nat} {I S C P : Type} (allocateCache : Nat → BitMutationM C)
    (iterate : I → Option S → BitMutationM (Option (Bool × S)))
    (cacheSet : C → Bool → I64 → BitMutationM Unit) (cacheFillFalse : C → I64 → I64 → BitMutationM Unit)
    (getBool : C → I64 → BitMutationM Bool) (pointer : C → I64 → P)
    (unsafeLoad : P → I64 → BitMutationM U64) (lengthChunks : Nat → BitMutationM I64)
    (B : BitArray N) (itr : I) : BitMutationM (BitArray N) := do
  let C ← allocateCache (64 * 64)
  let Bc := B.chunks
  let mut ind := int 1
  let mut cind := int 1
  let mut y ← iterate itr none
  while y.isSome do
    match y with
    | none => pure ()
    | some (x, st) => do
      cacheSet C x ind
      ind := ind + int 1
      if ind > bitCacheSize then
        dumpBitCache Bc cind C getBool pointer unsafeLoad lengthChunks
        cind := cind + bitCacheChunks
        ind := int 1
      y ← iterate itr (some st)
  if ind > int 1 then
    cacheFillFalse C ind bitCacheSize
    dumpBitCache Bc cind C getBool pointer unsafeLoad lengthChunks
  return B

/--
Julia source: base/bitarray.jl:607-632 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gen_bitarray_from_itr(itr)
    B = empty!(BitVector(undef, bitcache_size))
    C = Vector{Bool}(undef, bitcache_size)
    Bc = B.chunks
    ind = 1
    cind = 1
    y = iterate(itr)
    while y !== nothing
        x, st = y
        @inbounds C[ind] = x
        ind += 1
        if ind > bitcache_size
            resize!(B, length(B) + bitcache_size)
            dumpbitcache(Bc, cind, C)
            cind += bitcache_chunks
            ind = 1
        end
        y = iterate(itr, st)
    end
    if ind > 1
        @inbounds C[ind:bitcache_size] .= false
        resize!(B, length(B) + ind - 1)
        dumpbitcache(Bc, cind, C)
    end
    return B
end
```
-/
def genBitArrayFromIterator {I S C P : Type} (checkedDims : List I64 → BitMutationM I64)
    (allocateChunks : Nat → BitMutationM Nat) (allocateCache : Nat → BitMutationM C)
    (iterate : I → Option S → BitMutationM (Option (Bool × S)))
    (cacheSet : C → Bool → I64 → BitMutationM Unit) (cacheFillFalse : C → I64 → I64 → BitMutationM Unit)
    (getBool : C → I64 → BitMutationM Bool) (pointer : C → I64 → P)
    (unsafeLoad : P → I64 → BitMutationM U64) (lengthChunks : Nat → BitMutationM I64)
    (toInt : I64 → I64) (rangeLength : BitRange → I64) (itr : I) : BitMutationM BitVector := do
  let B0 ← BitArrayUndef checkedDims allocateChunks [int (64 * 64)]
  let mut B ← bitVectorEmptyBang deleteChunkEnd B0
  let C ← allocateCache (64 * 64)
  let Bc := B.chunks
  let mut ind := int 1
  let mut cind := int 1
  let mut y ← iterate itr none
  while y.isSome do
    match y with
    | none => pure ()
    | some (x, st) => do
      cacheSet C x ind
      ind := ind + int 1
      if ind > bitCacheSize then
        B ← bitVectorResize (fun x => x) B (B.len + bitCacheSize) false rangeLength
        dumpBitCache Bc cind C getBool pointer unsafeLoad lengthChunks
        cind := cind + bitCacheChunks
        ind := int 1
      y ← iterate itr (some st)
  if ind > int 1 then
    cacheFillFalse C ind bitCacheSize
    B ← bitVectorResize (fun x => x) B (B.len + ind - int 1) false rangeLength
    dumpBitCache Bc cind C getBool pointer unsafeLoad lengthChunks
  return B

/--
Julia source: base/bitarray.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gen_bitarray(isz::IteratorSize, itr) = gen_bitarray_from_itr(itr)
```
-/
-- Source: base/bitarray.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def genBitArrayUnknownDispatch {m : Type → Type} {I S R : Type}
    (gen : I → m R) (_size : S) (itr : I) : m R := gen itr

-- Source: base/bitarray.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def genBitArrayUnknown {I S C P : Type} (checkedDims : List I64 → BitMutationM I64)
    (allocateChunks : Nat → BitMutationM Nat) (allocateCache : Nat → BitMutationM C)
    (iterate : I → Option S → BitMutationM (Option (Bool × S)))
    (cacheSet : C → Bool → I64 → BitMutationM Unit)
    (cacheFillFalse : C → I64 → I64 → BitMutationM Unit)
    (getBool : C → I64 → BitMutationM Bool) (pointer : C → I64 → P)
    (unsafeLoad : P → I64 → BitMutationM U64) (lengthChunks : Nat → BitMutationM I64)
    (toInt : I64 → I64) (rangeLength : BitRange → I64)
    (itr : I) : BitMutationM BitVector :=
  genBitArrayUnknownDispatch
    (genBitArrayFromIterator checkedDims allocateChunks allocateCache iterate cacheSet cacheFillFalse
      getBool pointer unsafeLoad lengthChunks toInt rangeLength) () itr

/--
Julia source: base/bitarray.jl:576-582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gen_bitarray(::HasShape, itr)
    B = BitArray(undef, size(itr))
    for (I,x) in zip(CartesianIndices(axes(itr)), itr)
        B[I] = x
    end
    return B
end
```
-/
def genBitArrayHasShape {N : Nat} {I K : Type} (size : I → List I64)
    (undef : List I64 → BitMutationM (BitArray N))
    (zipCartesianValues : I → BitMutationM (List (K × Bool)))
    (setindex : BitArray N → K → Bool → BitMutationM (BitArray N)) (itr : I)
    : BitMutationM (BitArray N) := do
  let B ← undef (size itr)
  for (i, x) in (← zipCartesianValues itr) do
    let _ ← setindex B i x
    pure ()
  return B

/--
Julia source: base/bitarray.jl:585-588 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gen_bitarray(::HasShape, itr::Generator)
    B = BitArray(undef, size(itr))
    return fill_bitarray_from_itr!(B, itr)
end
```
-/
def genBitArrayGeneratorShape {N : Nat} {I S C P : Type} (size : I → List I64)
    (checkedDims : List I64 → BitMutationM I64) (allocateChunks : Nat → BitMutationM Nat)
    (allocateCache : Nat → BitMutationM C) (iterate : I → Option S → BitMutationM (Option (Bool × S)))
    (cacheSet : C → Bool → I64 → BitMutationM Unit) (cacheFillFalse : C → I64 → I64 → BitMutationM Unit)
    (getBool : C → I64 → BitMutationM Bool) (pointer : C → I64 → P) (unsafeLoad : P → I64 → BitMutationM U64)
    (lengthChunks : Nat → BitMutationM I64) (toInt : I64 → I64) (rangeLength : BitRange → I64)
    (itr : I) : BitMutationM (BitArray N) := do
  let B ← BitArrayUndef checkedDims allocateChunks (size itr)
  fillBitArrayFromItr allocateCache iterate cacheSet cacheFillFalse
    getBool pointer unsafeLoad lengthChunks B itr

/--
Julia source: base/bitarray.jl:589-592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function gen_bitarray(::HasLength, itr)
    b = BitVector(undef, length(itr))
    return fill_bitarray_from_itr!(b, itr)
end
```
-/
def genBitArrayHasLength {I C P : Type} (length : I → I64)
    (checkedDims : List I64 → BitMutationM I64) (allocateChunks : Nat → BitMutationM Nat)
    (allocateCache : Nat → BitMutationM C) (iterate : I → Option S → BitMutationM (Option (Bool × S)))
    (cacheSet : C → Bool → I64 → BitMutationM Unit) (cacheFillFalse : C → I64 → I64 → BitMutationM Unit)
    (getBool : C → I64 → BitMutationM Bool) (pointer : C → I64 → P) (unsafeLoad : P → I64 → BitMutationM U64)
    (lengthChunks : Nat → BitMutationM I64) (toInt : I64 → I64) (rangeLength : BitRange → I64)
    (itr : I) : BitMutationM BitVector := do
  let b ← BitArrayUndef checkedDims allocateChunks [length itr]
  fillBitArrayFromItr allocateCache iterate cacheSet cacheFillFalse
    getBool pointer unsafeLoad lengthChunks b itr

/--
Julia source: base/bitarray.jl:594-594 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gen_bitarray(::IsInfinite, itr) =  throw(ArgumentError("infinite-size iterable used in BitArray constructor"))
```
-/
def genBitArrayInfinite {N : Nat} {I : Type} (_itr : I) : BitMutationM (BitArray N) :=
  throw (.argument "infinite-size iterable used in BitArray constructor")

/--
Julia source: base/bitarray.jl:596-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gen_bitarrayN(::Type{BitVector}, itsz, itr)                        = gen_bitarray(itsz, itr)
```
-/
-- Source: base/bitarray.jl:596-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def genBitArrayNVectorDispatch {m : Type → Type} {I S R : Type}
    (gen : S → I → m R) (itsz : S) (itr : I) : m R := gen itsz itr

-- Source: base/bitarray.jl:596-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def genBitArrayNVector {I : Type} (gen : BitIteratorSize → I → BitMutationM BitVector)
    (itsz : BitIteratorSize) (itr : I) : BitMutationM BitVector :=
  genBitArrayNVectorDispatch gen itsz itr

/--
Julia source: base/bitarray.jl:597-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gen_bitarrayN(::Type{BitVector}, itsz::HasShape{1}, itr)           = gen_bitarray(itsz, itr)
```
-/
-- Source: base/bitarray.jl:597-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- HasShape{1} is a fieldless singleton represented by Unit.
def genBitArrayNVectorShapeOneDispatch {m : Type → Type} {I R : Type}
    (gen : Unit → I → m R) (itsz : Unit) (itr : I) : m R := gen itsz itr

-- Source: base/bitarray.jl:597-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def genBitArrayNVectorShapeOne {I : Type} (gen : BitIteratorSize → I → BitMutationM BitVector)
    (itsz : BitIteratorSize) (itr : I) : BitMutationM BitVector :=
  genBitArrayNVectorShapeOneDispatch (fun _ value => gen itsz value) () itr

/--
Julia source: base/bitarray.jl:598-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gen_bitarrayN(::Type{BitArray{N}}, itsz::HasShape{N}, itr) where N = gen_bitarray(itsz, itr)
```
-/
-- Source: base/bitarray.jl:598-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- The target rank and HasShape rank are the same dispatch parameter.
def genBitArrayNRankDispatch {m : Type → Type} {I R : Type} (_rank : Nat)
    (gen : Unit → I → m R) (itsz : Unit) (itr : I) : m R := gen itsz itr

-- Source: base/bitarray.jl:598-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def genBitArrayNRank {N : Nat} {I : Type} (gen : BitIteratorSize → I → BitMutationM (BitArray N))
    (itsz : BitIteratorSize) (itr : I) : BitMutationM (BitArray N) :=
  genBitArrayNRankDispatch N (fun _ value => gen itsz value) () itr

/--
Julia source: base/bitarray.jl:600-600 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gen_bitarrayN(::Type{BitVector}, itsz::HasShape{N}, itr) where N      = throw(DimensionMismatch("cannot create a BitVector from a $N-dimensional iterator"))
```
-/
def genBitArrayNVectorWrongShape {I : Type} (rank : Nat) (_itr : I) : BitMutationM BitVector :=
  throw (.dimensionMismatch "cannot create a BitVector from a multidimensional iterator")

/--
Julia source: base/bitarray.jl:601-601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gen_bitarrayN(@nospecialize(T::Type), itsz::HasShape{N}, itr) where N = throw(DimensionMismatch("cannot create a $T from a $N-dimensional iterator"))
```
-/
def genBitArrayNWrongShape {N : Nat} {I T : Type} (targetName : String) (_itr : I) : BitMutationM (BitArray N) :=
  throw (.dimensionMismatch s!"cannot create a {targetName} from a {N}-dimensional iterator")

/--
Julia source: base/bitarray.jl:602-602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gen_bitarrayN(@nospecialize(T::Type), itsz, itr) = throw(DimensionMismatch("cannot create a $T from a generic iterator"))
```
-/
def genBitArrayNGenericWrongShape {N : Nat} {I T : Type} (targetName : String) (_itr : I) : BitMutationM (BitArray N) :=
  throw (.dimensionMismatch s!"cannot create a {targetName} from a generic iterator")

/--
Julia source: base/bitarray.jl:68-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitArray(::UndefInitializer, dims::Integer...) = BitArray(undef, map(Int,dims))
```
-/
def bitArrayUndefVarargs {N : Nat} {α : Type} (mapInt : List α → List I64)
    (undef : List I64 → MutationM U64 (BitArray N)) (dims : List α) : MutationM U64 (BitArray N) :=
  undef (mapInt dims)

/--
Julia source: base/bitarray.jl:69-69 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitArray{N}(::UndefInitializer, dims::Integer...) where {N} = BitArray{N}(undef, map(Int,dims))::BitArray{N}
```
-/
def bitArrayNUndefVarargs {N : Nat} {α : Type} (mapInt : List α → List I64)
    (undef : List I64 → MutationM U64 (BitArray N)) (dims : List α) : MutationM U64 (BitArray N) := do
  return ← undef (mapInt dims)

/--
Julia source: base/bitarray.jl:70-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitArray(::UndefInitializer, dims::NTuple{N,Integer}) where {N} = BitArray{N}(undef, map(Int, dims)...)
```
-/
def bitArrayUndefTuple {N : Nat} {α : Type} (mapInt : List α → List I64)
    (undef : List I64 → MutationM U64 (BitArray N)) (dims : List α) : MutationM U64 (BitArray N) :=
  undef (mapInt dims)

/--
Julia source: base/bitarray.jl:71-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitArray{N}(::UndefInitializer, dims::NTuple{N,Integer}) where {N} = BitArray{N}(undef, map(Int, dims)...)
```
-/
def bitArrayNUndefTuple {N : Nat} {α : Type} (mapInt : List α → List I64)
    (undef : List I64 → MutationM U64 (BitArray N)) (dims : List α) : MutationM U64 (BitArray N) :=
  undef (mapInt dims)

/--
Julia source: base/bitarray.jl:76-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitVector() = BitVector(undef, 0)
```
-/
def bitVectorEmpty (undef : List I64 → MutationM U64 (BitArray 1)) : MutationM U64 (BitArray 1) :=
  undef [int 0]

/--
Julia source: base/bitarray.jl:95-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function BitVector(nt::Tuple{Vararg{Bool}})
    bv = BitVector(undef, length(nt))
    bv .= nt
end
```
-/
def bitVectorFromTuple {T : Type} (length : T → Nat)
    (undef : Nat → MutationM U64 (BitArray 1))
    (broadcastAssign : BitArray 1 → T → MutationM U64 (BitArray 1)) (nt : T) : MutationM U64 (BitArray 1) := do
  let bv ← undef (length nt)
  broadcastAssign bv nt

/--
Julia source: base/bitarray.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(B::BitVector) = (B.len,)
```
-/
def bitVectorSize (B : BitArray 1) : List I64 := [B.len]

/--
Julia source: base/bitarray.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(B::BitArray) = B.dims
```
-/
def bitArraySize {N : Nat} (B : BitArray N) : List I64 := B.dims

/-!
Julia source: base/bitarray.jl:103-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(B::BitVector) = (B.len,)
size(B::BitArray) = B.dims
```
-/
def bitArraySizeRanked {N : Nat} (B : BitArray N) : List I64 :=
  if N = 1 then [B.len] else B.dims

/--
Julia source: base/bitarray.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isassigned(B::BitArray, i::Int) = 1 <= i <= length(B)
```
-/
def bitArrayIsAssigned {N : Nat} (B : BitArray N) (i : I64) : Bool :=
  int 1 ≤ i ∧ i ≤ bitArrayLength B

/--
Julia source: base/bitarray.jl:108-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IndexStyle(::Type{<:BitArray}) = IndexLinear()
```
-/
def bitArrayIndexStyle : JuliaLean.base.indices.IndexStyle := .linear

/--
Julia source: base/bitarray.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
dataids(B::BitArray) = dataids(B.chunks)
```
-/
def bitArrayDataIds {N : Nat} {α : Type} (dataids : Nat → α) (B : BitArray N) : α :=
  dataids B.chunks

/--
Julia source: base/bitarray.jl:360-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(B::BitArray, dims::Int...) = BitArray(undef, dims)
```
-/
def similarBitArrayDims {N : Nat} (allocate : List I64 → BitMutationM (BitArray N))
    (dims : List I64) : BitMutationM (BitArray N) := allocate dims

/--
Julia source: base/bitarray.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(B::BitArray, dims::Dims) = BitArray(undef, dims...)
```
-/
def similarBitArrayDimsTuple {N : Nat} (allocate : List I64 → BitMutationM (BitArray N))
    (dims : List I64) : BitMutationM (BitArray N) := allocate dims

/--
Julia source: base/bitarray.jl:429-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(dest::BitArray, src::BitArray)
    length(src) > length(dest) && throw(BoundsError(dest, length(dest)+1))
    destc = dest.chunks; srcc = src.chunks
    nc = min(length(destc), length(srcc))
    nc == 0 && return dest
    @inbounds begin
        for i = 1 : nc - 1
            destc[i] = srcc[i]
        end
        if length(src) == length(dest)
            destc[nc] = srcc[nc]
        else
            msk_s = _msk_end(src)
            msk_d = ~msk_s
            destc[nc] = (msk_d & destc[nc]) | (msk_s & srcc[nc])
        end
    end
    return dest
end
```
-/
def bitArrayCopyto {N : Nat} (dest src : BitArray N) : BitMutationM (BitArray N) := do
  if src.len > dest.len then throw .bounds
  let destc := dest.chunks
  let srcc := src.chunks
  let destN ← mutableLength destc
  let srcN ← mutableLength srcc
  let nc := if destN < srcN then destN else srcN
  if nc == int 0 then return dest
  for i in intRange (int 1) (nc - int 1) do
    mutableSet destc (← mutableGet srcc i) i
  if src.len == dest.len then
    mutableSet destc (← mutableGet srcc nc) nc
  else
    let mskS := maskEndArray src
    let mskD := not_int mskS
    let oldD ← mutableGet destc nc
    let oldS ← mutableGet srcc nc
    mutableSet destc (or_int (and_int mskD oldD) (and_int mskS oldS)) nc
  return dest

/--
Julia source: base/bitarray.jl:454-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copyto!(dest::BitArray, doffs::Integer, src::Union{BitArray,Array}, soffs::Integer, n::Integer) =
    _copyto_int!(dest, Int(doffs), src, Int(soffs), Int(n))
```
-/
def bitArrayCopytoOffsets {N : Nat} {S P : Type}
    (toInt : S → I64) (sourceLength : BitSource → I64)
    (getBool : Nat → I64 → BitMutationM Bool) (pointer : Nat → I64 → P)
    (unsafeLoad : P → I64 → BitMutationM U64)
    (dest : BitArray N) (doffs : S) (src : BitSource) (soffs n : S) : BitMutationM (BitArray N) :=
  bitArrayCopytoInt sourceLength getBool pointer unsafeLoad dest (toInt doffs) src (toInt soffs) (toInt n)

/--
Julia source: base/bitarray.jl:466-470 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copyto!(dest::BitArray, src::Array)
    length(src) > length(dest) && throw(BoundsError(dest, length(dest)+1))
    length(src) == 0 && return dest
    return unsafe_copyto!(dest, 1, src, 1, length(src))
end
```
-/
def bitArrayCopytoBoolArray {N : Nat} {P : Type} (sourceLength : Nat → I64)
    (getBool : Nat → I64 → BitMutationM Bool) (pointer : Nat → I64 → P)
    (unsafeLoad : P → I64 → BitMutationM U64)
    (dest : BitArray N) (src : Nat) : BitMutationM (BitArray N) := do
  if sourceLength src > dest.len then throw .bounds
  if sourceLength src == int 0 then return dest
  bitArrayUnsafeCopyto getBool pointer unsafeLoad dest (int 1) (.boolArray src) (int 1) (sourceLength src)

/--
Julia source: base/bitarray.jl:472-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function reshape(B::BitArray{N}, dims::NTuple{N,Int}) where N
    return dims == size(B) ? B : _bitreshape(B, dims)
end
```
-/
def bitArrayReshapeSameRank {N : Nat} (checkedDims : List I64 → BitMutationM I64)
    (allocate : List I64 → BitMutationM (BitArray N)) (B : BitArray N) (dims : List I64) : BitMutationM (BitArray N) :=
  if dims == bitArraySizeRanked B then pure B else bitArrayReshapeInternal checkedDims allocate B dims

/--
Julia source: base/bitarray.jl:475-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(B::BitArray, dims::Tuple{Vararg{Int}}) = _bitreshape(B, dims)
```
-/
def bitArrayReshapeAny {InputRank OutputRank : Nat} (checkedDims : List I64 → BitMutationM I64)
    (allocate : List I64 → BitMutationM (BitArray OutputRank)) (B : BitArray InputRank)
    (dims : List I64) (_hDims : dims.length = OutputRank) : BitMutationM (BitArray OutputRank) :=
  bitArrayReshapeInternal checkedDims allocate B dims

/--
Julia source: base/bitarray.jl:535-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(::Type{T})(x::T) where {T<:BitArray} = copy(x)::T
```
-/
def bitArrayTypedCopy {N : Nat} {A : Type} (copy : BitArray N → BitMutationM (BitArray N)) (x : BitArray N) : BitMutationM (BitArray N) := copy x

/--
Julia source: base/bitarray.jl:536-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitArray(x::BitArray) = copy(x)
```
-/
def bitArrayCopySame {N : Nat} (copy : BitArray N → BitMutationM (BitArray N)) (x : BitArray N) : BitMutationM (BitArray N) := copy x

/--
Julia source: base/bitarray.jl:566-566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitArray(itr) = gen_bitarray(IteratorSize(itr), itr)
```
-/
-- Source: base/bitarray.jl:566-566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitArrayFromIteratorDispatch {m : Type → Type} [Monad m] {I S R : Type}
    (iteratorSize : I → m S) (gen : S → I → m R) (itr : I) : m R := do
  let size ← iteratorSize itr
  gen size itr

-- Source: base/bitarray.jl:566-566 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitArrayFromIterator {I S : Type} {N : Nat} (iteratorSize : I → S) (gen : S → I → BitMutationM (BitArray N)) (itr : I) : BitMutationM (BitArray N) :=
  bitArrayFromIteratorDispatch (fun value => pure (iteratorSize value)) gen itr

/--
Julia source: base/bitarray.jl:567-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitArray{N}(itr) where N = gen_bitarrayN(BitArray{N}, IteratorSize(itr), itr)
```
-/
-- Source: base/bitarray.jl:567-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitArrayNFromIteratorDispatch {m : Type → Type} [Monad m] {I S R : Type}
    (rank : Nat) (iteratorSize : I → m S) (gen : Nat → S → I → m R) (itr : I) : m R := do
  let size ← iteratorSize itr
  gen rank size itr

-- Source: base/bitarray.jl:567-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitArrayNFromIterator {N : Nat} {I S : Type} (iteratorSize : I → S)
    (gen : Nat → S → I → BitMutationM (BitArray N)) (itr : I) : BitMutationM (BitArray N) :=
  bitArrayNFromIteratorDispatch N (fun value => pure (iteratorSize value)) gen itr

/--
Julia source: base/bitarray.jl:569-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, a::AbstractArray) where {T<:BitArray} = a isa T ? a : T(a)::T
```
-/
-- Source: base/bitarray.jl:569-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Sum.inl retains the unchanged target-typed value from the built-in isa test.
def convertToBitArrayDispatch {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.array.Error m] {N : Nat} {A V : Type}
    (construct : A → m V) (asTarget : V → Option (BitArray N))
    (value : Sum (BitArray N) A) : m (BitArray N) :=
  match value with
  | .inl original => pure original
  | .inr other => do
      let converted ← construct other
      match asTarget converted with
      | some target => pure target
      | none => throwThe JuliaLean.base.array.Error (.typeError "convert(BitArray)")

-- Source: base/bitarray.jl:569-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def convertToBitArray {N : Nat} {A T : Type}
    (isa : A → T → Bool) (asTarget : A → T → BitArray N)
    (construct : T → A → BitMutationM (BitArray N)) (target : T) (a : A) : BitMutationM (BitArray N) :=
  convertToBitArrayDispatch (construct target) some
    (if isa a target then .inl (asTarget a target) else .inr a)

/--
Julia source: base/bitarray.jl:694-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
indexoffset(i) = first(i)-1
```
-/
-- Source: base/bitarray.jl:694-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def indexOffsetDispatch {m : Type → Type} [Monad m] {I A R : Type}
    (first : I → m A) (subtract : A → I64 → m R) (value : I) : m R := do
  let start ← first value
  subtract start (int 1)

-- Source: base/bitarray.jl:694-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def indexOffset {R : Type} (first : R → I64) (i : R) : I64 :=
  indexOffsetDispatch (m := Id) first (fun a b => a - b) i

/--
Julia source: base/bitarray.jl:695-695 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
indexoffset(::Colon) = 0
```
-/
def indexOffsetColon : I64 := int 0

/--
Julia source: base/bitarray.jl:697-699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@propagate_inbounds function setindex!(B::BitArray, X::AbstractArray, J0::Union{Colon,AbstractUnitRange{Int}})
    _setindex!(IndexStyle(B), B, X, to_indices(B, (J0,))[1])
end
```
-/
-- Source: base/bitarray.jl:697-699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- A pair with Unit represents the source's singleton index tuple.
def bitArraySetIndexRangeDispatch {m : Type → Type} [Monad m] {B X J K R : Type}
    (setindex : JuliaLean.base.indices.IndexStyle → B → X → K → m R)
    (toIndices : B → (J × Unit) → m (K × Unit))
    (array : B) (values : X) (j0 : J) : m R := do
  let indices ← toIndices array (j0, ())
  setindex bitArrayIndexStyle array values indices.1

-- Source: base/bitarray.jl:697-699 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitArraySetIndexRange {N : Nat} {X J : Type} (setindex : JuliaLean.base.indices.IndexStyle → BitArray N → X → J → BitMutationM (BitArray N))
    (toIndices : BitArray N → J → BitMutationM J) (B : BitArray N) (x : X) (j0 : J) : BitMutationM (BitArray N) :=
  bitArraySetIndexRangeDispatch setindex
    (fun array tuple => do pure (← toIndices array tuple.1, ())) B x j0

/--
Julia source: base/bitarray.jl:703-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function setindex!(B::BitArray, X::AbstractArray, I::BitArray)
    @boundscheck checkbounds(B, I)
    _unsafe_setindex!(B, X, I)
end
```
-/
def bitArraySetIndexMask {N : Nat} {X A : Type}
    (checkbounds : BitArray N → BitArray N → BitMutationM Unit)
    (unsafeSet : BitArray N → A → BitArray N → BitMutationM (BitArray N))
    (B : BitArray N) (x : A) (mask : BitArray N) : BitMutationM (BitArray N) := do
  checkbounds B mask
  unsafeSet B x mask

/--
Julia source: base/bitarray.jl:1066-1078 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function splice!(B::BitVector, i::Integer)
    # TODO: after deprecation remove the four lines below
    #       as v = B[i] is enough to do both bounds checking
    #       and Bool check then just pass Int(i) to _deleteat!
    i isa Bool && depwarn("passing Bool as an index is deprecated", :splice!)
    i = Int(i)
    n = length(B)
    1 <= i <= n || throw(BoundsError(B, i))

    v = B[i]   # TODO: change to a copy if/when subscripting becomes an ArrayView
    _deleteat!(B, i)
    return v
end
```
-/
def bitVectorSpliceIndex {I : Type} (isBool : I → Bool) (deprecate : BitMutationM Unit)
    (toInt : I → I64) (getindex : BitVector → I64 → BitMutationM Bool)
    (deleteAt : BitVector → I64 → BitMutationM BitVector) (B : BitVector) (i : I) : BitMutationM Bool := do
  if isBool i then deprecate
  let i := toInt i
  if !(int 1 ≤ i ∧ i ≤ B.len) then throw .bounds
  let v ← getindex B i
  let _ ← deleteAt B i
  return v

/--
Julia source: base/bitarray.jl:1145-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (-)(B::BitArray)
    A = zeros(Int, size(B))
    l = length(B)
    l == 0 && return A
    Bc = B.chunks
    ind = 1
    for i = 1:length(Bc)-1
        u = UInt64(1)
        c = Bc[i]
        for _ = 1:64
            if c & u != 0
                A[ind] = -1
            end
            ind += 1
            u <<= 1
        end
    end
    u = UInt64(1)
    c = Bc[end]
    for _ = 0:_mod64(l-1)
        if c & u != 0
            A[ind] = -1
        end
        ind += 1
        u <<= 1
    end
    return A
end
```
-/
def bitArrayUnaryMinus {N : Nat} {A : Type}
    (allocate : List I64 → BitMutationM A) (length : A → I64)
    (set : A → I64 → I64 → BitMutationM Unit) (B : BitArray N) : BitMutationM A := do
  let out ← allocate B.dims
  let l := length out
  if l == int 0 then return out
  let Bc := B.chunks
  let nc ← mutableLength Bc
  let mut ind := int 1
  for i in intRange (int 1) (nc - int 1) do
    let mut u := u64 1
    let mut c ← mutableGet Bc i
    for _ in intRange (int 1) (int 64) do
      if and_int c u != u64 0 then set out ind (int (-1)) else set out ind (int 0)
      ind := ind + int 1
      u := shl_int u (u64 1)
  let mut u := u64 1
  let mut c ← mutableGet Bc nc
  for _ in intRange (int 0) (mod64 (l - int 1)) do
    if and_int c u != u64 0 then set out ind (int (-1)) else set out ind (int 0)
    ind := ind + int 1
    u := shl_int u (u64 1)
  return out

/--
Julia source: base/bitarray.jl:1177-1189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval function ($f)(A::BitArray, B::BitArray)
        r = Array{Int}(undef, promote_shape(size(A), size(B)))
        ay, by = iterate(A), iterate(B)
        ri = 1
        # promote_shape guarantees that A and B have the
        # same iteration space
        while ay !== nothing
            @inbounds r[ri] = ($f)(ay[1], by[1])
            ri += 1
            ay, by = iterate(A, ay[2]), iterate(B, by[2])
        end
        return r
    end
```
-/
def bitArrayBinaryArithmetic {N M : Nat} {A : Type}
    (promoteShape : BitArray N → BitArray M → List I64)
    (set : A → I64 → I64 → BitMutationM Unit)
    (op : Bool → Bool → I64)
    (allocate : List I64 → BitMutationM A) (a : BitArray N) (b : BitArray M) : BitMutationM A := do
  let r ← allocate (promoteShape a b)
  let mut ay ← bitArrayIterate a
  let mut bi ← bitArrayIterate b
  let mut ri := int 1
  while ay.isSome do
    match ay, bi with
    | some (x, sa), some (y, sb) =>
      set r ri (op x y)
      ri := ri + int 1
      ay ← bitArrayIterate a sa
      bi ← bitArrayIterate b sb
    | _, _ => throw Error.bounds
  return r

/--
Julia source: base/bitarray.jl:1194-1194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
        ($f)(A::Union{BitMatrix,BitVector}, B::Union{BitMatrix,BitVector}) = ($f)(Array(A), Array(B))
```
-/
def bitArraySlashMatrices {A C : Type}
    (toArray : BitArray 2 → BitMutationM A) (divide : A → A → BitMutationM C)
    (a b : BitArray 2) : BitMutationM C := do
  divide (← toArray a) (← toArray b)

/--
Julia source: base/bitarray.jl:1197-1197 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(/)(B::BitArray, x::Number) = (/)(Array(B), x)
```
-/
def bitArrayDivideRight {N : Nat} {A B C : Type} (toArray : BitArray N → BitMutationM A)
    (divide : A → B → BitMutationM C) (a : BitArray N) (x : B) : BitMutationM C := do
  divide (← toArray a) x

/--
Julia source: base/bitarray.jl:1198-1198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(/)(x::Number, B::BitArray) = (/)(x, Array(B))
```
-/
def bitArrayDivideLeft {N : Nat} {A B C : Type} (toArray : BitArray N → BitMutationM A)
    (divide : B → A → BitMutationM C) (x : B) (a : BitArray N) : BitMutationM C := do
  divide x (← toArray a)

/--
Julia source: base/bitarray.jl:1206-1209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (==)(A::BitArray, B::BitArray)
    size(A) != size(B) && return false
    return A.chunks == B.chunks
end
```
-/
-- Source: base/bitarray.jl:1206-1209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitArrayEqualWith {N M : Nat} (chunkEqual : Nat → Nat → BitMutationM Bool)
    (a : BitArray N) (b : BitArray M) : BitMutationM Bool := do
  if bitArraySizeRanked a != bitArraySizeRanked b then return false
  chunkEqual a.chunks b.chunks

-- Source: base/array.jl:2188-2205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def equalUInt64ChunkVectors
    (memcmp : (Nat × I64) → (Nat × I64) → I64 → BitMutationM I64)
    (left right : Nat) : BitMutationM Bool :=
  JuliaLean.base.array.equalBitIntegerVector mutableRef
    (fun _ => pure ()) pure mutableLength (int 8) memcmp (fun _ => pure ()) left right

-- Source: base/bitarray.jl:1206-1209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitArrayEqualNative {N M : Nat}
    (memcmp : (Nat × I64) → (Nat × I64) → I64 → BitMutationM I64)
    (left : BitArray N) (right : BitArray M) : BitMutationM Bool :=
  bitArrayEqualWith (equalUInt64ChunkVectors memcmp) left right

def bitArrayEqual {N M : Nat} (chunkEqual : Nat → Nat → BitMutationM Bool)
    (a : BitArray N) (b : BitArray M) : BitMutationM Bool :=
  bitArrayEqualWith chunkEqual a b

/--
Julia source: base/bitarray.jl:1211-1218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cmp(A::BitVector, B::BitVector)
    Ac, Bc = A.chunks, B.chunks
    @inbounds for i in 1:min(length(Ac), length(Bc))
        d = xor(Ac[i], Bc[i])
        iszero(d) || return iszero(Bc[i] & d & -d) ? 1 : -1
    end
    return cmp(length(A), length(B))
end
```
-/
def bitVectorCmp {A : Type} (trailingZeros : U64 → I64) (topSetBit : U64 → I64)
    (cmpLength : I64 → I64 → I64) (a b : BitVector) : BitMutationM I64 := do
  let ac := a.chunks
  let bc := b.chunks
  let al ← mutableLength ac
  let bl ← mutableLength bc
  let n := if al < bl then al else bl
  for i in intRange (int 1) n do
    let d := xor_int (← mutableGet ac i) (← mutableGet bc i)
    if d != u64 0 then
      let low := and_int d (-d)
      if and_int (and_int (← mutableGet bc i) d) low == u64 0 then return int 1
      else return int (-1)
  return cmpLength a.len b.len

/--
Julia source: base/bitarray.jl:1225-1225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_reverse(A::BitArray, d::Tuple{Integer}) = _reverse(A, d[1])
```
-/
-- Source: base/bitarray.jl:1225 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitArrayReverseTupleDispatch {m : Type → Type} {A D R : Type}
    (reverseDim : A → D → m R) (array : A) (dims : D × Unit) : m R :=
  reverseDim array dims.1

def bitArrayReverseTuple {N : Nat} (reverseDim : BitArray N → I64 → BitMutationM (BitArray N))
    (a : BitArray N) (dims : List I64) : BitMutationM (BitArray N) :=
  bitArrayReverseTupleDispatch reverseDim a (dims.getD 0 (int 0), ())

/--
Julia source: base/bitarray.jl:1226-1270 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reverse(A::BitArray, d::Int)
    nd = ndims(A)
    1 ≤ d ≤ nd || throw(ArgumentError("dimension $d is not 1 ≤ $d ≤ $nd"))
    sd = size(A, d)
    sd == 1 && return copy(A)

    B = similar(A)

    nnd = 0
    for i = 1:nd
        nnd += size(A,i)==1 || i==d
    end
    if nnd == nd
        # reverse along the only non-singleton dimension
        for i = 1:sd
            B[i] = A[sd+1-i]
        end
        return B
    end

    d_in = size(A)
    leading = d_in[1:(d-1)]
    M = prod(leading)
    N = length(A)
    stride = M * sd

    if M == 1
        for j = 0:stride:(N-stride)
            for i = 1:sd
                ri = sd+1-i
                B[j + ri] = A[j + i]
            end
        end
    else
        for i = 1:sd
            ri = sd+1-i
            for j=0:stride:(N-stride)
                offs = j + 1 + (i-1)*M
                boffs = j + 1 + (ri-1)*M
                copy_chunks!(B.chunks, boffs, A.chunks, offs, M)
            end
        end
    end
    return B
end
```
-/
def bitArrayReverseDim {N : Nat} {A : Type}
    (ndims : BitArray N → I64) (sizeDim : BitArray N → I64 → I64)
    (copy : BitArray N → BitMutationM (BitArray N)) (similar : BitArray N → BitMutationM (BitArray N))
    (get : BitArray N → I64 → BitMutationM Bool) (set : BitArray N → Bool → I64 → BitMutationM Unit)
    (prod : List I64 → I64) (copyChunksCall : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (dimensionRange : BitArray N → I64 → I64 → I64 → List I64) (a : BitArray N) (d : I64) : BitMutationM (BitArray N) := do
  let nd := ndims a
  if !(int 1 ≤ d ∧ d ≤ nd) then throw (.argument "dimension is out of range")
  let sd := sizeDim a d
  if sd == int 1 then return ← copy a
  let b ← similar a
  let mut nnd := int 0
  for i in dimensionRange a (int 1) nd (int 1) do
    if sizeDim a i == int 1 ∨ i == d then nnd := nnd + int 1
  if nnd == nd then
    for i in intRange (int 1) sd do
      let _ ← set b (← get a (sd + int 1 - i)) i
    return b
  let dIn := a.dims
  let leading := dIn.take (d.val - 1).toNat
  let m := prod leading
  let n := a.len
  let stride := m * sd
  if m == int 1 then
    for j in dimensionRange a (int 0) (n - stride) stride do
      for i in intRange (int 1) sd do
        let ri := sd + int 1 - i
        let _ ← set b (← get a (j + i)) (j + ri)
  else
    for i in intRange (int 1) sd do
      let ri := sd + int 1 - i
      for j in dimensionRange a (int 0) (n - stride) stride do
        let offs := j + int 1 + (i - int 1) * m
        let boffs := j + int 1 + (ri - int 1) * m
        copyChunksCall b.chunks boffs a.chunks offs m
  return b

/--
Julia source: base/bitarray.jl:1272-1324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reverse!(B::BitVector, ::Colon)
    # Basic idea: each chunk is divided into two blocks of size k = n % 64, and
    # h = 64 - k. Walk from either end (with indices i and j) reversing chunks
    # and separately ORing their two blocks into place.
    #
    #           chunk 3                  chunk 2                  chunk 1
    # ┌───────────────┬───────┐┌───────────────┬───────┐┌───────────────┬───────┐
    # │000000000000000│   E   ││       D       │   C   ││       B       │   A   │
    # └───────────────┴───────┘└───────────────┴───────┘└───────────────┴───────┘
    #                     k            h           k            h            k
    # yielding:
    # ┌───────────────┬───────┐┌───────────────┬───────┐┌───────────────┬───────┐
    # │000000000000000│  A'   ││      B'       │  C'   ││      D'       │  E'   │
    # └───────────────┴───────┘└───────────────┴───────┘└───────────────┴───────┘

    n = length(B)
    n == 0 && return B

    k = _mod64(n+63) + 1
    h = 64 - k

    i, j = 0, length(B.chunks)
    u = UInt64(0)
    v = bitreverse(B.chunks[j])
    B.chunks[j] = 0
    @inbounds while true
        i += 1
        if i == j
            break
        end
        u = bitreverse(B.chunks[i])
        B.chunks[i] = 0
        B.chunks[j] |= u >>> h
        B.chunks[i] |= v >>> h

        j -= 1
        if i == j
            break
        end
        v = bitreverse(B.chunks[j])
        B.chunks[j] = 0
        B.chunks[i] |= v << k
        B.chunks[j] |= u << k
    end

    if isodd(length(B.chunks))
        B.chunks[i] |= v >>> h
    else
        B.chunks[i] |= u << k
    end

    return B
end
```
-/
def bitVectorReverseInPlace (bitreverse : U64 → U64) (isOdd : I64 → Bool) (B : BitVector) : BitMutationM BitVector := do
  let n := B.len
  if n == int 0 then return B
  let k := mod64 (n + int 63) + int 1
  let h := int 64 - k
  let mut i := int 0
  let mut j ← mutableLength B.chunks
  let mut u := u64 0
  let mut v := bitreverse (← mutableGet B.chunks j)
  mutableSet B.chunks (u64 0) j
  while true do
    i := i + int 1
    if i == j then break
    u := bitreverse (← mutableGet B.chunks i)
    mutableSet B.chunks (u64 0) i
    let oldJ ← mutableGet B.chunks j
    mutableSet B.chunks (or_int oldJ (lshr_int u h)) j
    let oldI ← mutableGet B.chunks i
    mutableSet B.chunks (or_int oldI (lshr_int v h)) i
    j := j - int 1
    if i == j then break
    v := bitreverse (← mutableGet B.chunks j)
    mutableSet B.chunks (u64 0) j
    let oldI ← mutableGet B.chunks i
    mutableSet B.chunks (or_int oldI (shl_int v k)) i
    let oldJ ← mutableGet B.chunks j
    mutableSet B.chunks (or_int oldJ (shl_int u k)) j
  let last ← mutableGet B.chunks i
  if isOdd (← mutableLength B.chunks) then
    mutableSet B.chunks (or_int last (lshr_int v h)) i
  else mutableSet B.chunks (or_int last (shl_int u k)) i
  return B

/--
Julia source: base/bitarray.jl:1326-1332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (<<)(B::BitVector, i::UInt)
    n = length(B)
    i == 0 && return copy(B)
    A = falses(n)
    i < n && copy_chunks!(A.chunks, 1, B.chunks, Int(i+1), Int(n-i))
    return A
end
```
-/
def bitVectorShiftLeftUnsigned (asUInt : I64 → U64) (asInt : U64 → I64)
    (copy : BitVector → BitMutationM BitVector) (falses : I64 → BitMutationM BitVector)
    (B : BitVector) (i : U64) : BitMutationM BitVector := do
  let n := B.len
  if i == u64 0 then return ← copy B
  let a ← falses n
  if asUInt n > i then copyChunks a.chunks (int 1) B.chunks (asInt i + int 1) (n - asInt i)
  return a

/--
Julia source: base/bitarray.jl:1334-1340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function (>>>)(B::BitVector, i::UInt)
    n = length(B)
    i == 0 && return copy(B)
    A = falses(n)
    i < n && copy_chunks!(A.chunks, Int(i+1), B.chunks, 1, Int(n-i))
    return A
end
```
-/
def bitVectorShiftRightUnsigned (asUInt : I64 → U64) (asInt : U64 → I64)
    (copy : BitVector → BitMutationM BitVector) (falses : I64 → BitMutationM BitVector)
    (B : BitVector) (i : U64) : BitMutationM BitVector := do
  let n := B.len
  if i == u64 0 then return ← copy B
  let a ← falses n
  if asUInt n > i then copyChunks a.chunks (asInt i + int 1) B.chunks (int 1) (n - asInt i)
  return a

/--
Julia source: base/bitarray.jl:1377-1377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(>>)(B::BitVector, i::Union{Int, UInt}) = B >>> i
```
-/
def bitVectorShiftRight {I : Type} (asUInt : I → U64) (asInt : I → I64)
    (asUIntOp : BitVector → U64 → BitMutationM BitVector) (B : BitVector) (i : I)
    : BitMutationM BitVector := asUIntOp B (asUInt i)

/--
Julia source: base/bitarray.jl:1415-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(<<)(B::BitVector, i::Int) = (i >=0 ? B << unsigned(i) : B >> unsigned(-i))
```
-/
def bitVectorShiftLeftSigned {I : Type} (toInt : I → I64) (toUnsigned : I64 → U64)
    (left : BitVector → U64 → BitMutationM BitVector) (right : BitVector → I64 → BitMutationM BitVector)
    (B : BitVector) (i : I) : BitMutationM BitVector :=
  if toInt i ≥ int 0 then left B (toUnsigned (toInt i)) else right B (-(toInt i))

/--
Julia source: base/bitarray.jl:1423-1423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
(>>>)(B::BitVector, i::Int) = (i >=0 ? B >> unsigned(i) : B << unsigned(-i))
```
-/
def bitVectorShiftRightSigned {I : Type} (toInt : I → I64) (toUnsigned : I64 → U64)
    (left : BitVector → I64 → BitMutationM BitVector) (right : BitVector → U64 → BitMutationM BitVector)
    (B : BitVector) (i : I) : BitMutationM BitVector :=
  if toInt i ≥ int 0 then right B (toUnsigned (toInt i)) else left B (-(toInt i))

/--
Julia source: base/bitarray.jl:1425-1425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
circshift!(dest::BitVector, src::BitVector, i::Integer) = _circshift_int!(dest, src, Int(i))
```
-/
def bitVectorCircshiftTo {I : Type} (toInt : I → I64)
    (shift : BitVector → BitVector → I64 → BitMutationM BitVector)
    (dest src : BitVector) (i : I) : BitMutationM BitVector := shift dest src (toInt i)

/--
Julia source: base/bitarray.jl:1426-1442 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _circshift_int!(dest::BitVector, src::BitVector, i::Int)
    i = Int(i)
    length(dest) == length(src) || throw(ArgumentError("destination and source should be of same size"))
    n = length(dest)
    i %= n
    i == 0 && return (src === dest ? src : copyto!(dest, src))
    Bc = (src === dest ? copy(src.chunks) : src.chunks)
    if i > 0 # right
        copy_chunks!(dest.chunks, i+1, Bc, 1, n-i)
        copy_chunks!(dest.chunks, 1, Bc, n-i+1, i)
    else # left
        i = -i
        copy_chunks!(dest.chunks, 1, Bc, i+1, n-i)
        copy_chunks!(dest.chunks, n-i+1, Bc, 1, i)
    end
    return dest
end
```
-/
def bitVectorCircshiftInt (copyChunksCall : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit)
    (copyChunkVector : Nat → BitMutationM Nat) (dest src : BitVector) (i : I64)
    : BitMutationM BitVector := do
  if dest.len != src.len then throw (.argument "destination and source should be of same size")
  let n := dest.len
  let i ← match JInt.remInt i n with
    | .ok q => pure q
    | .error _ => throw Error.divide
  if i == int 0 then
    if dest.chunks == src.chunks then return src
    let chunks ← copyChunkVector src.chunks
    copyChunksCall dest.chunks (int 1) chunks (int 1) (← mutableLength chunks)
    return dest
  let sourceChunks ← if dest.chunks == src.chunks then copyChunkVector src.chunks else pure src.chunks
  if i > int 0 then
    copyChunksCall dest.chunks (i + int 1) sourceChunks (int 1) (n - i)
    copyChunksCall dest.chunks (int 1) sourceChunks (n - i + int 1) i
  else
    let left := -i
    copyChunksCall dest.chunks (int 1) sourceChunks (left + int 1) (n - left)
    copyChunksCall dest.chunks (n - left + int 1) sourceChunks (int 1) left
  return dest

/--
Julia source: base/bitarray.jl:1444-1444 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
circshift!(B::BitVector, i::Integer) = circshift!(B, B, i)
```
-/
def bitVectorCircshiftInPlace (shift : BitVector → BitVector → I64 → BitMutationM BitVector)
    (B : BitVector) (i : I64) : BitMutationM BitVector := shift B B i

/--
Julia source: base/bitarray.jl:1448-1454 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bitcount(Bc::Vector{UInt64}; init::T=0) where {T}
    n::T = init
    @inbounds for i = 1:length(Bc)
        n = (n + count_ones(Bc[i])) % T
    end
    return n
end
```
-/
-- Source: base/bitarray.jl:1448-1454 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Shared source loop; each step executes immediately after a live UInt64 read.
def bitcountLoop {T : Type} (step : T → U64 → BitMutationM T)
    (init : T) (bc : Nat) : BitMutationM T := do
  let mut n := init
  let nc ← mutableLength bc
  for i in intRange (int 1) nc do
    n ← step n (← mutableGet bc i)
  return n

-- Source: base/bitarray.jl:1448-1454 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
/-- Open arithmetic retains the typed local's conversion and type assertion. -/
def bitcountDispatch {T A R C : Type}
    (convertInit : T → BitMutationM C) (add : T → I64 → BitMutationM A)
    (remainder : A → BitMutationM R) (convertResult : R → BitMutationM C)
    (asT : C → Option T) (init : T) (bc : Nat) : BitMutationM T := do
  let initial ← convertInit init
  let n ← match asT initial with
    | some value => pure value
    | none => throw (.typeError "bitcount: n")
  bitcountLoop (fun n word => do
    let added ← add n (JuliaLean.base.int.count_ones word)
    let reduced ← remainder added
    let converted ← convertResult reduced
    match asT converted with
    | some value => pure value
    | none => throw (.typeError "bitcount: n")) n bc

-- Source: base/bitarray.jl:1448-1454 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitcount {T : Type} (addCount : T → I64 → T) (remCount : T → T)
    (countOnes : U64 → I64) (init : T) (bc : Nat) : BitMutationM T :=
  bitcountLoop (fun n word => pure (remCount (addCount n (countOnes word)))) init bc

/--
Julia source: base/bitarray.jl:1456-1456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_count(::typeof(identity), B::BitArray, ::Colon, init) = bitcount(B.chunks; init)
```
-/
def bitArrayCountIdentity {N : Nat} {T : Type} (bitcount : Nat → T → BitMutationM T)
    (B : BitArray N) (init : T) : BitMutationM T := bitcount B.chunks init

-- Source: base/bitarray.jl:1456-1456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitArrayCountDispatch {N : Nat} {T A R C : Type}
    (convertInit : T → BitMutationM C) (add : T → I64 → BitMutationM A)
    (remainder : A → BitMutationM R) (convertResult : R → BitMutationM C)
    (asT : C → Option T) (B : BitArray N) (init : T) : BitMutationM T :=
  bitcountDispatch convertInit add remainder convertResult asT init B.chunks

/--
Julia source: base/bitarray.jl:1458-1475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_bitfindnext(Bc::Vector{UInt64}, start::Int)
    chunk_start = _div64(start-1)+1
    within_chunk_start = _mod64(start-1)
    mask = _msk64 << within_chunk_start

    @inbounds begin
        if Bc[chunk_start] & mask != 0
            return (chunk_start-1) << 6 + trailing_zeros(Bc[chunk_start] & mask) + 1
        end

        for i = chunk_start+1:length(Bc)
            if Bc[i] != 0
                return (i-1) << 6 + trailing_zeros(Bc[i]) + 1
            end
        end
    end
    return nothing
end
```
-/
def unsafeBitFindNext (trailingZeros : U64 → I64) (bc : Nat) (start : I64)
    : BitMutationM (Option I64) := do
  let chunkStart := div64 (start - int 1) + int 1
  let withinChunkStart := mod64 (start - int 1)
  let mask := shl_int u64Max withinChunkStart
  let c ← mutableGet bc chunkStart
  if and_int c mask != u64 0 then
    return some (shl_int (chunkStart - int 1) (int 6) + trailingZeros (and_int c mask) + int 1)
  let nc ← mutableLength bc
  for i in intRange (chunkStart + int 1) nc do
    let c ← mutableGet bc i
    if c != u64 0 then return some (shl_int (i - int 1) (int 6) + trailingZeros c + int 1)
  return none

/--
Julia source: base/bitarray.jl:1478-1483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findnext(B::BitArray, start::Integer)
    start = Int(start)
    start > 0 || throw(BoundsError(B, start))
    start > length(B) && return nothing
    unsafe_bitfindnext(B.chunks, start)
end
```
-/
def bitArrayFindNext {I : Type} (toInt : I → I64) (unsafeFind : Nat → I64 → BitMutationM (Option I64))
    (B : BitArray N) (start0 : I) : BitMutationM (Option I64) := do
  let start := toInt start0
  if start ≤ int 0 then throw Error.bounds
  if start > B.len then return none
  unsafeFind B.chunks start

/--
Julia source: base/bitarray.jl:1488-1516 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findnextnot(B::BitArray, start::Int)
    start > 0 || throw(BoundsError(B, start))
    start > length(B) && return nothing

    Bc = B.chunks
    l = length(Bc)
    l == 0 && return nothing

    chunk_start = _div64(start-1)+1
    within_chunk_start = _mod64(start-1)
    mask = ~(_msk64 << within_chunk_start)

    @inbounds if chunk_start < l
        if Bc[chunk_start] | mask != _msk64
            return (chunk_start-1) << 6 + trailing_ones(Bc[chunk_start] | mask) + 1
        end
        for i = chunk_start+1:l-1
            if Bc[i] != _msk64
                return (i-1) << 6 + trailing_ones(Bc[i]) + 1
            end
        end
        if Bc[l] != _msk_end(B)
            return (l-1) << 6 + trailing_ones(Bc[l]) + 1
        end
    elseif Bc[l] | mask != _msk_end(B)
        return (l-1) << 6 + trailing_ones(Bc[l] | mask) + 1
    end
    return nothing
end
```
-/
def bitArrayFindNextNot {N : Nat} (trailingOnes : U64 → I64) (B : BitArray N) (start : I64)
    : BitMutationM (Option I64) := do
  if start ≤ int 0 then throw Error.bounds
  if start > B.len then return none
  let Bc := B.chunks
  let l ← mutableLength Bc
  if l == int 0 then return none
  let chunkStart := div64 (start - int 1) + int 1
  let withinChunkStart := mod64 (start - int 1)
  let mask := not_int (shl_int u64Max withinChunkStart)
  if chunkStart < l then
    let c ← mutableGet Bc chunkStart
    if or_int c mask != u64Max then
      return some (shl_int (chunkStart - int 1) (int 6) + trailingOnes (or_int c mask) + int 1)
    for i in intRange (chunkStart + int 1) (l - int 1) do
      let c ← mutableGet Bc i
      if c != u64Max then return some (shl_int (i - int 1) (int 6) + trailingOnes c + int 1)
    let last ← mutableGet Bc l
    if last != maskEndArray B then return some (shl_int (l - int 1) (int 6) + trailingOnes last + int 1)
  else
    let last ← mutableGet Bc l
    if or_int last mask != maskEndArray B then
      return some (shl_int (l - int 1) (int 6) + trailingOnes (or_int last mask) + int 1)
  return none

/--
Julia source: base/bitarray.jl:1517-1517 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findfirstnot(B::BitArray) = findnextnot(B,1)
```
-/
def bitArrayFindFirstNot {N : Nat} (trailingOnes : U64 → I64) (B : BitArray N)
    : BitMutationM (Option I64) := bitArrayFindNextNot trailingOnes B (int 1)

/--
Julia source: base/bitarray.jl:1520-1526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findnext(pred::Fix2{<:Union{typeof(isequal),typeof(==)},Bool},
                  B::BitArray, start::Integer)
    v = pred.x
    v == false && return findnextnot(B, Int(start))
    v == true && return findnext(B, start)
    return nothing
end
```
-/
def bitArrayFindNextPred {N : Nat} {P : Type} (predValue : P → Bool)
    (findFalse : BitArray N → I64 → BitMutationM (Option I64))
    (findTrue : BitArray N → I64 → BitMutationM (Option I64))
    (pred : P) (B : BitArray N) (start : I64) : BitMutationM (Option I64) := do
  let v := predValue pred
  if !v then findFalse B start else findTrue B start

/--
Julia source: base/bitarray.jl:1530-1530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findnext(testf::Function, B::BitArray, start::Integer) = _findnext_int(testf, B, Int(start))
```
-/
def bitArrayFindNextFunction {F : Type} (findNextInt : F → BitArray N → I64 → BitMutationM (Option I64))
    (testf : F) (B : BitArray N) (start : I64) : BitMutationM (Option I64) :=
  findNextInt testf B start

/--
Julia source: base/bitarray.jl:1531-1541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findnext_int(testf::Function, B::BitArray, start::Int)
    f0::Bool = testf(false)
    f1::Bool = testf(true)
    !f0 && f1 && return findnext(B, start)
    f0 && !f1 && return findnextnot(B, start)

    start > 0 || throw(BoundsError(B, start))
    start > length(B) && return nothing
    f0 && f1 && return start
    return nothing # last case: !f0 && !f1
end
```
-/
def bitArrayFindNextInt {N : Nat} {F : Type} (test : F → Bool → BitMutationM Bool)
    (findTrue : BitArray N → I64 → BitMutationM (Option I64))
    (findFalse : BitArray N → I64 → BitMutationM (Option I64))
    (testf : F) (B : BitArray N) (start : I64) : BitMutationM (Option I64) := do
  let f0 ← test testf false
  let f1 ← test testf true
  if !f0 && f1 then return ← findTrue B start
  if f0 && !f1 then return ← findFalse B start
  if start ≤ int 0 then throw Error.bounds
  if start > B.len then return none
  if f0 && f1 then return some start
  return none

/--
Julia source: base/bitarray.jl:1544-1560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_bitfindprev(Bc::Vector{UInt64}, start::Int)
    chunk_start = _div64(start-1)+1
    mask = _msk_end(start)

    @inbounds begin
        if Bc[chunk_start] & mask != 0
            return (chunk_start-1) << 6 + (top_set_bit(Bc[chunk_start] & mask))
        end

        for i = (chunk_start-1):-1:1
            if Bc[i] != 0
                return (i-1) << 6 + (top_set_bit(Bc[i]))
            end
        end
    end
    return nothing
end
```
-/
def unsafeBitFindPrev (topSetBit : U64 → I64) (bc : Nat) (start : I64)
    : BitMutationM (Option I64) := do
  let chunkStart := div64 (start - int 1) + int 1
  let mask := maskEnd start
  let c ← mutableGet bc chunkStart
  if and_int c mask != u64 0 then
    return some (shl_int (chunkStart - int 1) (int 6) + topSetBit (and_int c mask))
  let mut i := chunkStart - int 1
  while i ≥ int 1 do
    let c ← mutableGet bc i
    if c != u64 0 then return some (shl_int (i - int 1) (int 6) + topSetBit c)
    i := i - int 1
  return none

/--
Julia source: base/bitarray.jl:1563-1568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findprev(B::BitArray, start::Integer)
    start = Int(start)
    start > 0 || return nothing
    start > length(B) && throw(BoundsError(B, start))
    unsafe_bitfindprev(B.chunks, start)
end
```
-/
def bitArrayFindPrev {I : Type} (toInt : I → I64) (unsafeFind : Nat → I64 → BitMutationM (Option I64))
    (B : BitArray N) (start0 : I) : BitMutationM (Option I64) := do
  let start := toInt start0
  if start ≤ int 0 then return none
  if start > B.len then throw Error.bounds
  unsafeFind B.chunks start

/--
Julia source: base/bitarray.jl:1570-1592 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findprevnot(B::BitArray, start::Int)
    start = Int(start)
    start > 0 || return nothing
    start > length(B) && throw(BoundsError(B, start))

    Bc = B.chunks

    chunk_start = _div64(start-1)+1
    mask = ~_msk_end(start)

    @inbounds begin
        if Bc[chunk_start] | mask != _msk64
            return (chunk_start-1) << 6 + (64 - leading_ones(Bc[chunk_start] | mask))
        end

        for i = chunk_start-1:-1:1
            if Bc[i] != _msk64
                return (i-1) << 6 + (64 - leading_ones(Bc[i]))
            end
        end
    end
    return nothing
end
```
-/
def bitArrayFindPrevNot {N : Nat} (leadingOnes : U64 → I64) (B : BitArray N) (start : I64)
    : BitMutationM (Option I64) := do
  if start ≤ int 0 then return none
  if start > B.len then throw Error.bounds
  let Bc := B.chunks
  let chunkStart := div64 (start - int 1) + int 1
  let mask := not_int (maskEnd start)
  let c ← mutableGet Bc chunkStart
  if or_int c mask != u64Max then
    return some (shl_int (chunkStart - int 1) (int 6) + (int 64 - leadingOnes (or_int c mask)))
  let mut i := chunkStart - int 1
  while i ≥ int 1 do
    let c ← mutableGet Bc i
    if c != u64Max then return some (shl_int (i - int 1) (int 6) + (int 64 - leadingOnes c))
    i := i - int 1
  return none

/--
Julia source: base/bitarray.jl:1593-1593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findlastnot(B::BitArray) = findprevnot(B, length(B))
```
-/
def bitArrayFindLastNot {N : Nat} (findPrevNot : BitArray N → I64 → BitMutationM (Option I64))
    (B : BitArray N) : BitMutationM (Option I64) := findPrevNot B B.len

/--
Julia source: base/bitarray.jl:1596-1602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findprev(pred::Fix2{<:Union{typeof(isequal),typeof(==)},Bool},
                  B::BitArray, start::Integer)
    v = pred.x
    v == false && return findprevnot(B, Int(start))
    v == true && return findprev(B, start)
    return nothing
end
```
-/
def bitArrayFindPrevPred {N : Nat} {P : Type} (predValue : P → Bool)
    (findFalse : BitArray N → I64 → BitMutationM (Option I64))
    (findTrue : BitArray N → I64 → BitMutationM (Option I64))
    (pred : P) (B : BitArray N) (start : I64) : BitMutationM (Option I64) := do
  let v := predValue pred
  if !v then findFalse B start else findTrue B start

/--
Julia source: base/bitarray.jl:1606-1606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findprev(testf::Function, B::BitArray, start::Integer) = _findprev_int(testf, B, Int(start))
```
-/
def bitArrayFindPrevFunction {F : Type} (findPrevInt : F → BitArray N → I64 → BitMutationM (Option I64))
    (testf : F) (B : BitArray N) (start : I64) : BitMutationM (Option I64) :=
  findPrevInt testf B start

/--
Julia source: base/bitarray.jl:1607-1617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _findprev_int(testf::Function, B::BitArray, start::Int)
    f0::Bool = testf(false)
    f1::Bool = testf(true)
    !f0 && f1 && return findprev(B, start)
    f0 && !f1 && return findprevnot(B, start)

    start > 0 || return nothing
    start > length(B) && throw(BoundsError(B, start))
    f0 && f1 && return start
    return nothing # last case: !f0 && !f1
end
```
-/
def bitArrayFindPrevInt {N : Nat} {F : Type} (test : F → Bool → BitMutationM Bool)
    (findTrue : BitArray N → I64 → BitMutationM (Option I64))
    (findFalse : BitArray N → I64 → BitMutationM (Option I64))
    (testf : F) (B : BitArray N) (start : I64) : BitMutationM (Option I64) := do
  let f0 ← test testf false
  let f1 ← test testf true
  if !f0 && f1 then return ← findTrue B start
  if f0 && !f1 then return ← findFalse B start
  if start ≤ int 0 then return none
  if start > B.len then throw Error.bounds
  if f0 && f1 then return some start
  return none

/--
Julia source: base/bitarray.jl:1620-1631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findmax(a::BitArray)
    isempty(a) && throw(ArgumentError("BitArray must be non-empty"))
    m, mi = false, 1
    ti = 1
    ac = a.chunks
    for i = 1:length(ac)
        @inbounds k = trailing_zeros(ac[i])
        ti += k
        k == 64 || return (true, @inbounds keys(a)[ti])
    end
    return m, @inbounds keys(a)[mi]
end
```
-/
def bitArrayFindMax {N : Nat} {K : Type} (trailingZeros : U64 → I64)
    (keyAt : BitArray N → I64 → BitMutationM K) (B : BitArray N) : BitMutationM (Bool × K) := do
  if B.len == int 0 then throw (.argument "BitArray must be non-empty")
  let mut ti := int 1
  let ac := B.chunks
  let nc ← mutableLength ac
  for i in intRange (int 1) nc do
    let k := trailingZeros (← mutableGet ac i)
    ti := ti + k
    if k != int 64 then return (true, ← keyAt B ti)
  return (false, ← keyAt B (int 1))

/--
Julia source: base/bitarray.jl:1633-1648 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findmin(a::BitArray)
    isempty(a) && throw(ArgumentError("BitArray must be non-empty"))
    m, mi = true, 1
    ti = 1
    ac = a.chunks
    for i = 1:length(ac)-1
        @inbounds k = trailing_ones(ac[i])
        ti += k
        k == 64 || return (false, @inbounds keys(a)[ti])
    end
    l = Base._mod64(length(a)-1) + 1
    @inbounds k = trailing_ones(ac[end] & Base._msk_end(l))
    ti += k
    k == l || return (false, @inbounds keys(a)[ti])
    return (m, @inbounds keys(a)[mi])
end
```
-/
def bitArrayFindMin {N : Nat} {K : Type} (trailingOnes : U64 → I64)
    (keyAt : BitArray N → I64 → BitMutationM K) (B : BitArray N) : BitMutationM (Bool × K) := do
  if B.len == int 0 then throw (.argument "BitArray must be non-empty")
  let mut ti := int 1
  let ac := B.chunks
  let nc ← mutableLength ac
  for i in intRange (int 1) (nc - int 1) do
    let k := trailingOnes (← mutableGet ac i)
    ti := ti + k
    if k != int 64 then return (false, ← keyAt B ti)
  let l := mod64 (B.len - int 1) + int 1
  let k := trailingOnes (and_int (← mutableGet ac nc) (maskEnd l))
  ti := ti + k
  if k != l then return (false, ← keyAt B ti)
  return (true, ← keyAt B (int 1))

/--
Julia source: base/bitarray.jl:1652-1658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function allindices!(I, B::BitArray)
    ind = first(keys(B))
    for k = 1:length(B)
        I[k] = ind
        ind = nextind(B, ind)
    end
end
```
-/
def bitArrayAllIndices {N : Nat} {I V : Type} (allocate : I64 → BitMutationM V)
    (firstKey : BitArray N → I) (nextind : BitArray N → I → I)
    (set : V → I → I64 → BitMutationM Unit) (B : BitArray N) : BitMutationM V := do
  let out ← allocate B.len
  let mut ind := firstKey B
  for k in intRange (int 1) B.len do
    set out ind k
    ind := nextind B ind
  return out

/--
Julia source: base/bitarray.jl:1661-1663 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function allindices!(I, B::BitVector)
    I[:] .= 1:length(B)
end
```
-/
def bitVectorAllIndices {V : Type} (allocate : I64 → BitMutationM V)
    (set : V → I64 → I64 → BitMutationM Unit) (B : BitVector) : BitMutationM V := do
  let out ← allocate B.len
  for i in intRange (int 1) B.len do set out i i
  return out

/--
Julia source: base/bitarray.jl:1666-1672 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function allindices!(I, B::BitMatrix)
    k = 1
    for c = 1:size(B,2), r = 1:size(B,1)
        I[k] = CartesianIndex(r, c)
        k += 1
    end
end
```
-/
def bitMatrixAllIndices {V : Type} (allocate : I64 → BitMutationM V)
    (set : V → BitIndex → I64 → BitMutationM Unit) (B : BitMatrix) : BitMutationM V := do
  let nrows := B.dims.getD 0 (int 0)
  let ncols := B.dims.getD 1 (int 0)
  let out ← allocate B.len
  let mut k := int 1
  for c in intRange (int 1) ncols do
    for r in intRange (int 1) nrows do
      set out (.cartesian [r, c]) k
      k := k + int 1
  return out

/--
Julia source: base/bitarray.jl:1674-1674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _overflowind(i1, irest::Tuple{}, size) = (i1, irest)
```
-/
def overflowIndEmpty (i1 : I64) (_irest : List I64) (_size : List I64) : I64 × List I64 := (i1, [])

/--
Julia source: base/bitarray.jl:1675-1683 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _overflowind(i1, irest, size)
    i2 = irest[1]
    while i1 > size[1]
        i1 -= size[1]
        i2 += 1
    end
    i2, irest = _overflowind(i2, tail(irest), tail(size))
    return (i1, (i2, irest...))
end
```
-/
def overflowInd : I64 → List I64 → List I64 → I64 × List I64
  | i1, [], _ => (i1, [])
  | i1, i2 :: irest, s1 :: stail =>
    let (i1, i2) := overflowWithin i1 i2 s1
    let (i2, rest) := overflowInd i2 irest stail
    (i1, i2 :: rest)
  | i1, _, _ => (i1, [])
termination_by i1 irest size => irest.length
decreasing_by all_goals simp_wf <;> omega

/--
Julia source: base/bitarray.jl:1685-1685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _toind(i1, irest::Tuple{}) = i1
```
-/
def toIndEmpty (i1 : I64) (_irest : List I64) : BitIndex := .scalar i1

/--
Julia source: base/bitarray.jl:1686-1686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _toind(i1, irest) = CartesianIndex(i1, irest...)
```
-/
def toInd (i1 : I64) (irest : List I64) : BitIndex := .cartesian (i1 :: irest)

/--
Julia source: base/bitarray.jl:1688-1714 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function findall(B::BitArray)
    nnzB = count(B)
    I = Vector{eltype(keys(B))}(undef, nnzB)
    nnzB == 0 && return I
    nnzB == length(B) && (allindices!(I, B); return I)
    Bc = B.chunks
    Bs = size(B)
    Bi = i1 = i = 1
    irest = ntuple(one, ndims(B) - 1)
    c = Bc[1]
    @inbounds while true
        while c == 0
            Bi == length(Bc) && return I
            i1 += 64
            Bi += 1
            c = Bc[Bi]
        end

        tz = trailing_zeros(c)
        c = _blsr(c)

        i1, irest = _overflowind(i1 + tz, irest, Bs)
        I[i] = _toind(i1, irest)
        i += 1
        i1 -= tz
    end
end
```
-/
def bitArrayFindAll {N : Nat} {V : Type}
    (countTrue : BitArray N → BitMutationM I64) (allocate : I64 → BitMutationM V)
    (set : V → BitIndex → I64 → BitMutationM Unit)
    (allindices : V → BitArray N → BitMutationM V)
    (trailingZeros : U64 → I64) (B : BitArray N) : BitMutationM V := do
  let nnzB ← countTrue B
  let I ← allocate nnzB
  if nnzB == int 0 then return I
  if nnzB == B.len then return ← allindices I B
  let Bc := B.chunks
  let Bs := B.dims
  let mut Bi := int 1
  let mut i1 := int 1
  let mut i := int 1
  let mut irest := List.replicate (N - 1) (int 1)
  let mut c ← mutableGet Bc (int 1)
  while true do
    while c == u64 0 do
      if Bi == (← mutableLength Bc) then return I
      i1 := i1 + int 64
      Bi := Bi + int 1
      c ← mutableGet Bc Bi
    let tz := trailingZeros c
    c := blsr c
    let (coord, rest) := overflowInd (i1 + tz) irest Bs
    let key := if rest.isEmpty then toIndEmpty coord rest else toInd coord rest
    set I key i
    i := i + int 1
    i1 := i1 - tz
    irest := rest
  return I

/--
Julia source: base/bitarray.jl:1717-1717 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
findall(::typeof(!iszero), B::BitArray) = findall(B)
```
-/
def bitArrayFindAllNotZero {N : Nat} {V : Type}
    (findAll : BitArray N → BitMutationM V) (B : BitArray N) : BitMutationM V := findAll B

/--
Julia source: base/bitarray.jl:1721-1721 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sum(A::BitArray, dims)    = reduce(+, A, dims=dims)
```
-/
def bitArraySumDims {A D R : Type} (reduce : A → D → BitMutationM R)
    (A0 : A) (dims : D) : BitMutationM R := reduce A0 dims

/--
Julia source: base/bitarray.jl:1722-1722 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_sum(B::BitArray, ::Colon) = count(B)
```
-/
def bitArraySumColon {N : Nat} {R : Type} (count : BitArray N → BitMutationM R)
    (B : BitArray N) : BitMutationM R := count B

/--
Julia source: base/bitarray.jl:1724-1734 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function all(B::BitArray)
    isempty(B) && return true
    Bc = B.chunks
    @inbounds begin
        for i = 1:length(Bc)-1
            Bc[i] == _msk64 || return false
        end
        Bc[end] == _msk_end(B) || return false
    end
    return true
end
```
-/
def bitArrayAll {N : Nat} (B : BitArray N) : BitMutationM Bool := do
  if B.len == int 0 then return true
  let Bc := B.chunks
  let nc ← mutableLength Bc
  for i in intRange (int 1) (nc - int 1) do
    if (← mutableGet Bc i) != u64Max then return false
  if (← mutableGet Bc nc) != maskEndArray B then return false
  return true

/--
Julia source: base/bitarray.jl:1736-1745 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function any(B::BitArray)
    isempty(B) && return false
    Bc = B.chunks
    @inbounds begin
        for i = 1:length(Bc)
            Bc[i] == 0 || return true
        end
    end
    return false
end
```
-/
def bitArrayAny {N : Nat} (B : BitArray N) : BitMutationM Bool := do
  if B.len == int 0 then return false
  let Bc := B.chunks
  let nc ← mutableLength Bc
  for i in intRange (int 1) nc do
    if (← mutableGet Bc i) != u64 0 then return true
  return false

/--
Julia source: base/bitarray.jl:1747-1747 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minimum(B::BitArray) = isempty(B) ? throw(ArgumentError("argument must be non-empty")) : all(B)
```
-/
def bitArrayMinimum {N : Nat} (all : BitArray N → BitMutationM Bool)
    (B : BitArray N) : BitMutationM Bool := do
  if B.len == int 0 then throw (.argument "argument must be non-empty")
  all B

/--
Julia source: base/bitarray.jl:1748-1748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maximum(B::BitArray) = isempty(B) ? throw(ArgumentError("argument must be non-empty")) : any(B)
```
-/
def bitArrayMaximum {N : Nat} (any : BitArray N → BitMutationM Bool)
    (B : BitArray N) : BitMutationM Bool := do
  if B.len == int 0 then throw (.argument "argument must be non-empty")
  any B

/--
Julia source: base/bitarray.jl:1756-1756 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(::Union{typeof(~), typeof(!)}, A::BitArray) = bit_map!(~, similar(A), A)
```
-/
def bitArrayMapNot {N : Nat} (similar : BitArray N → BitMutationM (BitArray N))
    (mapBang : BitArray N → BitArray N → BitMutationM (BitArray N)) (A : BitArray N) : BitMutationM (BitArray N) := do
  mapBang (← similar A) A

/--
Julia source: base/bitarray.jl:1757-1757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(::typeof(zero), A::BitArray) = fill!(similar(A), false)
```
-/
def bitArrayMapZero {N : Nat} (similar : BitArray N → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N)) (A : BitArray N) : BitMutationM (BitArray N) := do
  fill (← similar A) false

/--
Julia source: base/bitarray.jl:1758-1758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(::typeof(one), A::BitArray) = fill!(similar(A), true)
```
-/
def bitArrayMapOne {N : Nat} (similar : BitArray N → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N)) (A : BitArray N) : BitMutationM (BitArray N) := do
  fill (← similar A) true

/--
Julia source: base/bitarray.jl:1759-1759 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map(::typeof(identity), A::BitArray) = copy(A)
```
-/
def bitArrayMapIdentity {N : Nat} (copy : BitArray N → BitMutationM (BitArray N))
    (A : BitArray N) : BitMutationM (BitArray N) := copy A

/--
Julia source: base/bitarray.jl:1761-1761 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map!(::Union{typeof(~), typeof(!)}, dest::BitArray, A::BitArray) = bit_map!(~, dest, A)
```
-/
def bitArrayMapBangNot {N : Nat} (mapBang : BitArray N → BitArray N → BitMutationM (BitArray N))
    (dest A : BitArray N) : BitMutationM (BitArray N) := mapBang dest A

/--
Julia source: base/bitarray.jl:1762-1762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map!(::typeof(zero), dest::BitArray, A::BitArray) = bit_map_constant!(dest, A, false)
```
-/
def bitArrayMapBangZero {N : Nat} (mapBang : BitArray N → BitArray N → Bool → BitMutationM (BitArray N))
    (dest A : BitArray N) : BitMutationM (BitArray N) := mapBang dest A false

/--
Julia source: base/bitarray.jl:1763-1763 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map!(::typeof(one), dest::BitArray, A::BitArray) = bit_map_constant!(dest, A, true)
```
-/
def bitArrayMapBangOne {N : Nat} (mapBang : BitArray N → BitArray N → Bool → BitMutationM (BitArray N))
    (dest A : BitArray N) : BitMutationM (BitArray N) := mapBang dest A true

/--
Julia source: base/bitarray.jl:1764-1764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
map!(::typeof(identity), dest::BitArray, A::BitArray) = copyto!(dest, A)
```
-/
def bitArrayMapBangIdentity {N : Nat} (copy : BitArray N → BitArray N → BitMutationM (BitArray N))
    (dest A : BitArray N) : BitMutationM (BitArray N) := copy dest A

/--
Julia source: base/bitarray.jl:1776-1776 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval map(::$T, A::BitArray, B::BitArray) = bit_map($f, A, B)
```
-/
def bitArrayMapBinaryGenerated {N M : Nat} (op : U64 → U64 → U64)
    (map : BitArray N → BitArray M → BitMutationM (BitArray 1)) (A : BitArray N) (B : BitArray M)
    : BitMutationM (BitArray 1) := map A B

/--
Julia source: base/bitarray.jl:1777-1777 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    @eval map!(::$T, dest::BitArray, A::BitArray, B::BitArray) = bit_map!($f, dest, A, B)
```
-/
def bitArrayMapBangBinaryGenerated {N M : Nat} (op : U64 → U64 → U64)
    (mapBang : BitArray 1 → BitArray N → BitArray M → BitMutationM (BitArray 1))
    (dest : BitArray 1) (A : BitArray N) (B : BitArray M) : BitMutationM (BitArray 1) := mapBang dest A B

/--
Julia source: base/bitarray.jl:1783-1787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bit_map(f::F, A::BitArray, B::BitArray) where F
    AB = zip(A, B)
    dest = similar(BitArray, _similar_shape(AB, IteratorSize(AB)))
    bit_map!(f, dest, A, B)
end
```
-/
def bitArrayMapBinary {N M : Nat} (zipShape : BitArray N → BitArray M → List I64)
    (similar : List I64 → BitMutationM (BitArray 1))
    (mapBang : (U64 → U64 → U64) → BitArray 1 → BitArray N → BitArray M → BitMutationM (BitArray 1))
    (op : U64 → U64 → U64) (A : BitArray N) (B : BitArray M) : BitMutationM (BitArray 1) := do
  let ABShape := zipShape A B
  let dest ← similar ABShape
  mapBang op dest A B

/--
Julia source: base/bitarray.jl:1789-1793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bit_map_constant!(dest::BitArray, A::BitArray, x::Bool)
    length(A) <= length(dest) || throw(DimensionMismatch("length of destination must be >= length of collection"))
    fill_chunks!(dest.chunks, x, 1, length(A))
    return dest
end
```
-/
def bitArrayMapBangConstant {N : Nat} (fillChunksCall : Nat → Bool → I64 → I64 → BitMutationM Unit)
    (dest A : BitArray N) (x : Bool) : BitMutationM (BitArray N) := do
  if A.len > dest.len then throw (.dimensionMismatch "length of destination must be >= length of collection")
  fillChunksCall dest.chunks x (int 1) A.len
  return dest



/--
Julia source: base/bitarray.jl:1839-1842 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function filter(f, Bs::BitArray)
    boolmap::Array{Bool} = map(f, Bs)
    Bs[boolmap]
end
```
-/
def bitArrayFilter {N : Nat} {A : Type} (map : (Bool → BitMutationM Bool) → BitArray N → BitMutationM BoolArray)
    (logicalIndex : BitArray N → BoolArray → BitMutationM A) (f : Bool → BitMutationM Bool)
    (Bs : BitArray N) : BitMutationM A := do
  let boolmap ← map f Bs
  logicalIndex Bs boolmap

/--
Julia source: base/bitarray.jl:1847-1858 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hcat(B::BitVector...)
    height = length(B[1])
    for j = 2:length(B)
        length(B[j]) == height ||
            throw(DimensionMismatch("dimensions must match: $j-th argument has length $(length(B[j])), should have $height"))
    end
    M = BitMatrix(undef, height, length(B))
    for j = 1:length(B)
        copy_chunks!(M.chunks, (height*(j-1))+1, B[j].chunks, 1, height)
    end
    return M
end
```
-/
def bitArrayHcatVectors (vectors : List BitVector) (allocate : I64 → I64 → BitMutationM BitMatrix)
    : BitMutationM BitMatrix := do
  let first ← match vectors with | [] => throw Error.bounds | v :: _ => pure v
  let height := first.len
  for j in intRange (int 2) (int vectors.length) do
    let v := vectors.getD (j.val.toNat - 1) first
    if v.len != height then throw (.dimensionMismatch "dimensions must match")
  let out ← allocate height (int vectors.length)
  let mut pos := int 1
  for j in intRange (int 1) (int vectors.length) do
    let v := vectors.getD (j.val.toNat - 1) first
    copyChunks out.chunks pos v.chunks (int 1) height
    pos := pos + height
  return out

/--
Julia source: base/bitarray.jl:1860-1872 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function vcat(V::BitVector...)
    n = 0
    for Vk in V
        n += length(Vk)
    end
    B = BitVector(undef, n)
    j = 1
    for Vk in V
        copy_chunks!(B.chunks, j, Vk.chunks, 1, length(Vk))
        j += length(Vk)
    end
    return B
end
```
-/
def bitArrayVcatVectors (vectors : List BitVector) (allocate : I64 → BitMutationM BitVector)
    : BitMutationM BitVector := do
  let mut n := int 0
  for v in vectors do n := n + v.len
  let out ← allocate n
  let mut j := int 1
  for v in vectors do
    copyChunks out.chunks j v.chunks (int 1) v.len
    j := j + v.len
  return out

/--
Julia source: base/bitarray.jl:1874-1896 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function hcat(A::Union{BitMatrix,BitVector}...)
    nargs = length(A)
    nrows = size(A[1], 1)
    ncols = 0
    for j = 1:nargs
        Aj = A[j]
        nd = ndims(Aj)
        ncols += (nd==2 ? size(Aj,2) : 1)
        size(Aj, 1) == nrows ||
            throw(DimensionMismatch("row lengths must match: $j-th element has first dim $(size(Aj, 1)), should have $nrows"))
    end

    B = BitMatrix(undef, nrows, ncols)

    pos = 1
    for k = 1:nargs
        Ak = A[k]
        n = length(Ak)
        copy_chunks!(B.chunks, pos, Ak.chunks, 1, n)
        pos += n
    end
    return B
end
```
-/
def bitArrayHcatArrays (arrays : List (BitArray N)) (sizeDim : BitArray N → I64 → I64)
    (ndims : BitArray N → I64) (allocate : I64 → I64 → BitMutationM BitMatrix)
    : BitMutationM BitMatrix := do
  let first ← match arrays with | [] => throw Error.bounds | a :: _ => pure a
  let nargs := int arrays.length
  let nrows := sizeDim first (int 1)
  let mut ncols := int 0
  for j in intRange (int 1) nargs do
    let Aj := arrays.getD (j.val.toNat - 1) first
    let nd := ndims Aj
    ncols := ncols + (if nd == int 2 then sizeDim Aj (int 2) else int 1)
    if sizeDim Aj (int 1) != nrows then throw (.dimensionMismatch "row lengths must match")
  let out ← allocate nrows ncols
  let mut pos := int 1
  for a in arrays do
    copyChunks out.chunks pos a.chunks (int 1) a.len
    pos := pos + a.len
  return out

/--
Julia source: base/bitarray.jl:1898-1921 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function vcat(A::BitMatrix...)
    nargs = length(A)
    nrows, nrowsA = 0, sizehint!(Int[], nargs)
    for a in A
        sz1 = size(a, 1)
        nrows += sz1
        push!(nrowsA, sz1)
    end
    ncols = size(A[1], 2)
    for j = 2:nargs
        size(A[j], 2) == ncols ||
        throw(DimensionMismatch("column lengths must match: $j-th element has second dim $(size(A[j], 2)), should have $ncols"))
    end
    B = BitMatrix(undef, nrows, ncols)
    Bc = B.chunks
    pos_d = 1
    pos_s = fill(1, nargs)
    for j = 1:ncols, k = 1:nargs
        copy_chunks!(Bc, pos_d, A[k].chunks, pos_s[k], nrowsA[k])
        pos_s[k] += nrowsA[k]
        pos_d += nrowsA[k]
    end
    return B
end
```
-/
def bitArrayVcatMatrices (arrays : List BitMatrix) (sizeDim : BitMatrix → I64 → I64)
    (allocate : I64 → I64 → BitMutationM BitMatrix) : BitMutationM BitMatrix := do
  let first ← match arrays with | [] => throw Error.bounds | a :: _ => pure a
  let mut nrows := int 0
  let mut nrowsA := []
  for a in arrays do
    let sz1 := sizeDim a (int 1)
    nrows := nrows + sz1
    nrowsA := nrowsA ++ [sz1]
  let ncols := sizeDim first (int 2)
  for j in intRange (int 2) (int arrays.length) do
    let a := arrays.getD (j.val.toNat - 1) first
    if sizeDim a (int 2) != ncols then throw (.dimensionMismatch "column lengths must match")
  let out ← allocate nrows ncols
  let mut posD := int 1
  let mut posS := List.replicate arrays.length (int 1)
  for _ in intRange (int 1) ncols do
    for k in intRange (int 1) (int arrays.length) do
      let a := arrays.getD (k.val.toNat - 1) first
      let n := nrowsA.getD (k.val.toNat - 1) (int 0)
      let s := posS.getD (k.val.toNat - 1) (int 1)
      copyChunks out.chunks posD a.chunks s n
      posS := posS.set (k.val.toNat - 1) (s + n)
      posD := posD + n
  return out

/--
Julia source: base/bitarray.jl:1924-1924 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_cat(dims::Integer, X::Union{BitArray, Bool}...) = _cat(Int(dims)::Int, X...)
```
-/
def bitArrayCatDim {D : Type} {N : Nat} (toInt : D → I64)
    (catInt : I64 → List BitSource → BitMutationM (BitArray N))
    (dims : D) (items : List BitSource) : BitMutationM (BitArray N) := catInt (toInt dims) items

/--
Julia source: base/bitarray.jl:1925-1931 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _cat(dims::Int, X::Union{BitArray, Bool}...)
    dims = Int(dims)
    catdims = dims2cat(dims)
    shape = cat_shape(catdims, map(cat_size, X))
    A = falses(shape)
    return __cat(A, shape, catdims, X...)
end
```
-/
def bitArrayCatInt {N : Nat} (dims2cat : I64 → I64) (catShape : I64 → List (I64 × I64) → List I64)
    (catSize : BitSource → I64 × I64) (falses : List I64 → BitMutationM (BitArray N))
    (cat : BitArray N → List I64 → I64 → List BitSource → BitMutationM (BitArray N))
    (dims : I64) (items : List BitSource) : BitMutationM (BitArray N) := do
  let catdims := dims2cat dims
  let shape := catShape catdims (items.map catSize)
  let A ← falses shape
  cat A shape catdims items

/--
Julia source: base/bitarray.jl:1939-1939 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
sizeof(B::BitArray) = sizeof(B.chunks)
```
-/
def bitArraySizeof {N : Nat} (length : Nat → BitMutationM I64) (B : BitArray N) : BitMutationM I64 := do
  return (← length B.chunks) * int 8

/--
Julia source: base/bitarray.jl:1941-1946 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _split_rest(a::Union{Vector, BitVector}, n::Int)
    _check_length_split_rest(length(a), n)
    last_n = a[end-n+1:end]
    resize!(a, length(a) - n)
    return a, last_n
end
```
-/
def bitArraySplitRest {A : Type} (check : I64 → I64 → BitMutationM Unit)
    (getLastN : A → I64 → BitMutationM A) (resize : A → I64 → BitMutationM A)
    (length : A → I64) (a : A) (n : I64) : BitMutationM (A × A) := do
  check (length a) n
  let lastN ← getLastN a n
  let rest ← resize a (length a - n)
  return (rest, lastN)

end JuliaLean.base.bitarray

/-! ## Additive models batch 1, group 15. Existing declarations above are frozen. -/

namespace JuliaLean.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

-- Source: base/bitarray.jl:24-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct BitArray{N} <: AbstractArray{Bool, N}
--     chunks::Vector{UInt64}
--     len::Int
--     dims::NTuple{N,Int}
-- /Source
/-- A Julia dimension tuple has its rank in its type (base/bitarray.jl:27-28).
Negative entries remain admissible
inputs, so the constructor's ordered errors are not hidden by this representation. -/
abbrev Dims (N : Nat) := { ds : List I64 // ds.length = N }

-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
/-- Raw runtime data at the pre-existing `arrayUndef1` allocation boundary,
base/boot.jl:821-824, required by base/bitarray.jl:36.
`emptyMemory` names the runtime's shared empty UInt64 memory. `rawWord` supplies only
uninitialized isbits contents, indexed by fresh memory identity and zero-based slot.
It supplies no Julia callee, size check, conversion, or correctness assumption.
Resource exhaustion and native pointer values are outside the installed allocator boundary. -/
structure AllocationData where
  emptyMemory : Nat
  rawWord : Nat → Nat → U64

-- Source: base/bitarray.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         chunks = Vector{UInt64}(undef, nc)
-- /Source
/-- Concrete fresh-memory allocation at the existing primitive boundary underlying
base/boot.jl:821-824. All words are readable isbits values; no UndefRefError is fabricated. -/
def allocateRawWords (runtime : AllocationData) (n : Nat) : BitMutationM Nat := do
  let s ← get
  let identity := s.memories.length
  let words := (List.range n).map (fun i => some (runtime.rawWord identity i))
  set { s with memories := s.memories ++ [words] }
  return identity

-- Source: base/boot.jl:821-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- /Source
/-- `Vector{UInt64}(undef,n)`, the callee at base/bitarray.jl:36. The installed
base/boot.jl:821-824 model performs memory-size checking before fresh allocation. -/
def allocateChunks (runtime : AllocationData) (n : I64) : BitMutationM Nat :=
  JuliaLean.base.array.arrayUndef1
    (some (allocationSummary uint64Layout))
    (pure runtime.emptyMemory) (allocateRawWords runtime)
    (fun (memory : Nat) (ds : List I64) => do
      let s ← get
      let identity := s.arrays.length
      set { s with arrays := s.arrays ++ [MutableVector.mk (memory, int 1) (ds.headD n)] }
      return identity) n

-- Source: base/bitarray.jl:28-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function BitArray{N}(::UndefInitializer, dims::Vararg{Int,N}) where N
--         i = 1
--         for d in dims
--             d >= 0 || throw(ArgumentError("dimension size must be ≥ 0, got $d for dimension $i"))
--             i += 1
--         end
--         n = Core.checked_dims(dims...)
--         nc = num_bit_chunks(n)
--         chunks = Vector{UInt64}(undef, nc)
--         nc > 0 && (chunks[end] = UInt64(0))
--         b = new(chunks, n)
--         N != 1 && (b.dims = dims)
--         return b
--     end
-- /Source
/-- Native Int-tuple constructor, base/bitarray.jl:28-41. The [] marker at rank one
represents the deliberately uninitialized dims field; public size reads len there. -/
def undef {N : Nat} (runtime : AllocationData) (dims : Dims N) :
    BitMutationM (BitArray N) := do
  let mut i := int 1
  for d in dims.val do
    if d.val < 0 then
      throw (.argument s!"dimension size must be ≥ 0, got {d.val} for dimension {i.val}")
    i := i + int 1
  let n ← JuliaLean.base.array.checkedDims dims.val
  let nc := numBitChunks n
  let chunks ← allocateChunks runtime nc
  if nc > int 0 then
    mutableSet chunks (u64 0) (← mutableLength chunks)
  return ⟨chunks, n, if N = 1 then [] else dims.val⟩

-- Source: base/bitarray.jl:76-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BitVector() = BitVector(undef, 0)
-- /Source
/-- Empty BitVector constructor, base/bitarray.jl:76. -/
def empty (runtime : AllocationData) : BitMutationM BitVector :=
  undef runtime ⟨[int 0], rfl⟩

end JuliaLean.base.bitarray.Models1Group15

namespace JuliaLean.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

-- Source: base/tuple.jl:28-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(@nospecialize t::Tuple) = nfields(t)
-- firstindex(@nospecialize t::Tuple) = 1
-- lastindex(@nospecialize t::Tuple) = length(t)
-- size(@nospecialize(t::Tuple), d::Integer) = (d == 1) ? length(t) : throw(ArgumentError("invalid tuple dimension $d"))
-- axes(@nospecialize t::Tuple) = (OneTo(length(t)),)
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- /Source
/-- Native Boolean tuple representation for base/bitarray.jl:95. The field count
is machine representable; the values, including the empty tuple, are unrestricted.
The bound is a Julia tuple representation invariant, not a packing precondition. -/
structure BoolTuple where
  values : List Bool
  nativeCount : (values.length : Int) ≤ IntTy.max .i64
  deriving Repr

-- Source: base/tuple.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(@nospecialize t::Tuple) = nfields(t)
-- /Source
/-- The native Int result of tuple length, base/tuple.jl:28. The representation
bound makes this conversion exact; tuples satisfy the native length constraint. -/
def boolTupleLength (nt : BoolTuple) : I64 :=
  int (JuliaLean.base.tuple.lengthTuple nt.values)

-- Source: base/tuple.jl:32-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(@nospecialize t::Tuple) = (OneTo(length(t)),)
-- /Source
/-- Native tuple axes, base/tuple.jl:32. A OneTo{Int} axis is represented here by
its stop; the installed tuple model enumerates its indices, whose count gives
that same stop. This adapter reuses its actual axes implementation. -/
def boolTupleAxes (nt : BoolTuple) : Dims 1 :=
  ⟨(JuliaLean.base.tuple.axesTuple nt.values).map
      (fun indices => int indices.length), by
    simp [JuliaLean.base.tuple.axesTuple]⟩

-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source
/-- `axes` at a BitVector destination, base/abstractarray.jl:100-103. Each axis
is represented by the stop of its unchecked OneTo constructor. In particular a
stale or negative header length is not silently clamped by this adapter. -/
def boolTupleDestinationAxes (B : BitVector) : Dims 1 :=
  let result := JuliaLean.base.abstractarray.axesDefault
    (fun (A : BitVector) => .ok (bitVectorSize A))
    (fun stop => (JuliaLean.base.range.unchecked_oneto stop).stop) B
  match h : result with
  | .ok axes =>
      have eq : [B.len] = axes := by
        simpa [result, JuliaLean.base.abstractarray.axesDefault, bitVectorSize,
          JuliaLean.base.range.unchecked_oneto] using h
      ⟨axes, by rw [← eq]; rfl⟩
  | .error _ => by
      simp [result, JuliaLean.base.abstractarray.axesDefault, bitVectorSize,
        JuliaLean.base.range.unchecked_oneto] at h

-- Source: base/broadcast.jl:536-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _bcsm(a, b) = a == b || length(b) == 1
-- /Source
/-- `_bcsm` for two native OneTo axes, base/broadcast.jl:536. A singleton source
may expand, including into an empty destination. Equality compares both stops. -/
def boolTupleAxisCompatible (destination source : I64) : Bool :=
  destination == source || source == int 1

-- Source: base/broadcast.jl:548-561 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- check_broadcast_shape(shp) = nothing
-- check_broadcast_shape(shp, ::Tuple{}) = nothing
-- check_broadcast_shape(::Tuple{}, ::Tuple{}) = nothing
-- function check_broadcast_shape(::Tuple{}, Ashp::Tuple)
--     if any(ax -> length(ax) != 1, Ashp)
--         throw(DimensionMismatch("cannot broadcast array to have fewer non-singleton dimensions"))
--     end
--     nothing
-- end
-- function check_broadcast_shape(shp, Ashp::Tuple)
--     _bcsm(shp[1], Ashp[1]) || throw(DimensionMismatch("array could not be broadcast to match destination"))
--     check_broadcast_shape(tail(shp), tail(Ashp))
-- end
-- @inline check_broadcast_axes(shp, A) = check_broadcast_shape(shp, axes(A))
-- /Source
/-- The source's recursive broadcast-shape check, base/broadcast.jl:548-561,
closed over native OneTo axes. All rejection paths precede destination writes. -/
def boolTupleCheckShape : List I64 → List I64 → BitMutationM Unit
  | _, [] => pure ()
  | [], source => do
      if source.any (fun axis => axis != int 1) then
        throw (.dimensionMismatch "cannot broadcast array to have fewer non-singleton dimensions")
  | d :: ds, s :: ss => do
      if !boolTupleAxisCompatible d s then
        throw (.dimensionMismatch "array could not be broadcast to match destination")
      boolTupleCheckShape ds ss

-- Source: base/broadcast.jl:48-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- BroadcastStyle(::Type{<:Tuple}) = Style{Tuple}()
-- /Source
/-- Only the actual tuple style and its erased copyto style occur in the closed
Boolean tuple assignment path, base/broadcast.jl:48-49,215-216,980. -/
inductive BoolTupleBroadcastStyle where
  | tuple
  | erased
  deriving Repr, DecidableEq

-- Source: base/broadcast.jl:165-179 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # that specialize on `DestType` to be easily disambiguated from
-- # methods that instead specialize on `BroadcastStyle`,
-- #    copyto!(dest::AbstractArray, bc::Broadcasted{MyStyle})
-- 
-- struct Broadcasted{Style<:Union{Nothing,BroadcastStyle}, Axes, F, Args<:Tuple} <: Base.AbstractBroadcasted
--     style::Style
--     f::F
--     args::Args
--     axes::Axes          # the axes of the resulting object (may be bigger than implied by `args` if this is nested inside a larger `Broadcasted`)
-- 
--     Broadcasted(style::Union{Nothing,BroadcastStyle}, f::Tuple, args::Tuple) = error() # disambiguation: tuple is not callable
--     function Broadcasted(style::Union{Nothing,BroadcastStyle}, f::F, args::Tuple, axes=nothing) where {F}
--         # using Core.Typeof rather than F preserves inferrability when f is a type
--         return new{typeof(style), typeof(axes), Core.Typeof(f), typeof(args)}(style, f, args, axes)
--     end
-- /Source
/-- `Broadcasted(identity,(nt,),axes)` specialized to a Boolean tuple argument.
One native axis is retained in the type: this is the complete row95 path and
does not purport to model arbitrary broadcast expressions. -/
structure BoolTupleBroadcast (style : BoolTupleBroadcastStyle) where
  argument : BoolTuple
  axes : Option (Dims 1)

-- Source: base/broadcast.jl:1409-1413 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function broadcasted(f::F, arg1, args...) where {F}
--     arg1′ = broadcastable(arg1)
--     args′ = map(broadcastable, args)
--     broadcasted(combine_styles(arg1′, args′...), f, arg1′, args′...)
-- end
-- /Source
-- Source: base/broadcast.jl:1420-1420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline broadcasted(style::BroadcastStyle, f::F, args...) where {F} = Broadcasted(style, f, args)
-- /Source
/-- `broadcasted(identity,nt)`, base/broadcast.jl:1409-1420. Tuple
`broadcastable` is identity (738), `BroadcastStyle(Tuple)` is Tuple style (49),
and the one-argument combine_styles/result_style methods preserve it (432,458).
The only represented function is the actual native identity function. -/
def boolTupleBroadcasted (nt : BoolTuple) : BoolTupleBroadcast .tuple :=
  ⟨nt, none⟩

-- Source: base/broadcast.jl:240-242 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline Base.axes(bc::Broadcasted) = _axes(bc, bc.axes)
-- _axes(::Broadcasted, axes::Tuple) = axes
-- @inline _axes(bc::Broadcasted, ::Nothing)  = combine_axes(bc.args...)
-- /Source
/-- Explicit broadcast axes take precedence, base/broadcast.jl:240-242;
without them the single tuple argument supplies its native OneTo axis (501). -/
def boolTupleBroadcastAxes {style : BoolTupleBroadcastStyle}
    (bc : BoolTupleBroadcast style) : Dims 1 :=
  match bc.axes with
  | some axes => axes
  | none => boolTupleAxes bc.argument

-- Source: base/broadcast.jl:321-325 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- instantiate(bc::Broadcasted{Style{Tuple}, Nothing}) = bc
-- function instantiate(bc::Broadcasted{Style{Tuple}})
--     check_broadcast_axes(bc.axes, bc.args...)
--     return bc
-- end
-- /Source
/-- Actual Tuple-style instantiate dispatch, base/broadcast.jl:321-325.
Tuple expressions with no axes return unchanged; assignment axes are checked. -/
def boolTupleInstantiate (bc : BoolTupleBroadcast .tuple) :
    BitMutationM (BoolTupleBroadcast .tuple) := do
  match bc.axes with
  | none => return bc
  | some axes =>
      boolTupleCheckShape axes.val (boolTupleAxes bc.argument).val
      return bc

-- Source: base/broadcast.jl:672-672 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- extrude(x) = x
-- /Source
/-- `extrude` leaves a tuple unchanged, base/broadcast.jl:672. -/
def boolTupleExtrude (nt : BoolTuple) : BoolTuple := nt

-- Source: base/broadcast.jl:1001-1001 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcast_unalias(dest, src) = dest === src ? src : unalias(dest, src)
-- /Source
-- Source: base/broadcast.jl:1007-1012 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline preprocess(dest, bc::Broadcasted) = Broadcasted(bc.style, bc.f, preprocess_args(dest, bc.args), bc.axes)
-- preprocess(dest, x) = extrude(broadcast_unalias(dest, x))
-- 
-- @inline preprocess_args(dest, args::Tuple) = (preprocess(dest, args[1]), preprocess_args(dest, tail(args))...)
-- @inline preprocess_args(dest, args::Tuple{Any}) = (preprocess(dest, args[1]),)
-- @inline preprocess_args(dest, args::Tuple{}) = ()
-- /Source
/-- Closed tuple preprocessing, base/broadcast.jl:1001,1007-1012. A mutable
BitVector and an immutable Boolean tuple cannot be identical. The installed
`unaliasOther` follows base/abstractarray.jl:1568 and returns the tuple itself. -/
def boolTuplePreprocess {style : BoolTupleBroadcastStyle}
    (destination : BitVector) (bc : BoolTupleBroadcast style) :
    BoolTupleBroadcast style :=
  { bc with argument :=
      boolTupleExtrude (JuliaLean.base.abstractarray.unaliasOther destination bc.argument) }

-- Source: base/broadcast.jl:1098-1105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ischunkedbroadcast(R, bc::Broadcasted) = ischunkedbroadcast(R, bc, _chunkop(bc.f, bc.args))
-- ischunkedbroadcast(R, bc::Broadcasted, ::Nothing) = false
-- ischunkedbroadcast(R, bc::Broadcasted, f) = ischunkedbroadcast(R, bc.args)
-- ischunkedbroadcast(R, args) = false
-- ischunkedbroadcast(R, args::Tuple{<:BitArray,Vararg{Any}}) = size(R) == size(args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Bool,Vararg{Any}}) = ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{<:Broadcasted,Vararg{Any}}) = ischunkedbroadcast(R, args[1]) && ischunkedbroadcast(R, tail(args))
-- ischunkedbroadcast(R, args::Tuple{}) = true
-- /Source
/-- Closed chunked-broadcast dispatch, base/broadcast.jl:1098-1105.
The argument tuple contains a Tuple value, not a BitArray, Bool or Broadcasted;
therefore the generic argument fallback at line1101 returns false. -/
def boolTupleIsChunked (_destination : BitVector)
    (_bc : BoolTupleBroadcast .erased) : Bool := false

-- Source: base/broadcast.jl:654-655 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _broadcast_getindex(A::Tuple{Any}, I) = A[1]
-- Base.@propagate_inbounds _broadcast_getindex(A::Tuple, I) = A[I[1]]
-- /Source
-- Source: base/broadcast.jl:675-678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds function _broadcast_getindex(bc::Broadcasted{<:Any,<:Any,<:Any,<:Any}, I)
--     args = _getindex(bc.args, I)
--     return _broadcast_getindex_evalf(bc.f, args...)
-- end
-- /Source
-- Source: base/broadcast.jl:700-705 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.@propagate_inbounds _getindex(args::Tuple, I) = (_broadcast_getindex(args[1], I), _getindex(tail(args), I)...)
-- Base.@propagate_inbounds _getindex(args::Tuple{Any}, I) = (_broadcast_getindex(args[1], I),)
-- Base.@propagate_inbounds _getindex(args::Tuple{}, I) = ()
-- 
-- @inline _broadcast_getindex_evalf(f::Tf, args::Vararg{Any,N}) where {Tf,N} = f(args...)  # not propagate_inbounds
-- 
-- /Source
/-- Native identity-broadcast indexing, base/broadcast.jl:654-655,675-705.
The enclosing rank-one copy supplies `(i,CartesianIndex())`; flattening at
base/multidimensional.jl:90-92 and to_index at broadcast.jl:634-636 leave i.
The singleton-tuple method ignores it. Otherwise scalar `i[1]` uses the
installed Number indexing method before the installed tuple getindex method.
With the concrete equality used here, `number.getindexOne` and
`tuple.getindexInt` can fail only with BoundsError; no other exception class is
coerced to it. The explicit access backend reports that error for invalid
unchecked reads. -/
def boolTupleBroadcastGet {style : BoolTupleBroadcastStyle}
    (bc : BoolTupleBroadcast style) (i : I64) : BitMutationM Bool := do
  let index ← if boolTupleLength bc.argument == int 1 then pure (int 1) else
    match JuliaLean.base.number.getindexOne
        (fun (j : I64) => .ok (j == int 1)) i (int 1) with
    | .ok value => pure value
    | .error _ => throw .bounds
  match JuliaLean.base.tuple.getindexInt bc.argument.values index with
  | .ok value => return JuliaLean.base.operators.identity value
  | .error _ => throw .bounds

-- Source: base/broadcast.jl:1056-1062 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             while i <= last(ax1) - 64
--                 z = UInt64(0)
--                 @inbounds @simd for j = 0:63
--                     z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = z
--             end
-- /Source
/-- One complete source register pack, base/broadcast.jl:1056-1062.
Each source Int index advances before its tuple read; UInt64 conversion and
signed Int shifts use installed concrete integer callees. -/
def boolTupleFullWord (bc : BoolTupleBroadcast .erased) (initial : I64) :
    BitMutationM (I64 × U64) := do
  let mut i := initial
  let mut word := u64 0
  for j in intRange (int 0) (int 63) do
    i := i + int 1
    let value := JuliaLean.base.number.convertSame (← boolTupleBroadcastGet bc i)
    word := or_int word (shl_Int (ofBool .u64 value) (and_int j (int 63)))
  return (i, word)

-- Source: base/broadcast.jl:1035-1073 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function copyto!(dest::BitArray, bc::Broadcasted{Nothing})
--     axes(dest) == axes(bc) || throwdm(axes(dest), axes(bc))
--     ischunkedbroadcast(dest, bc) && return chunkedcopyto!(dest, bc)
--     ndims(dest) == 0 && (dest[] = bc[]; return dest)
--     bc′ = preprocess(dest, bc)
--     # The broadcast axes can have an unsigned eltype, so use the destination's Int axes
--     # to keep the index arithmetic below from wrapping.
--     ax = axes(dest)
--     ax1, out = ax[1], CartesianIndices(tail(ax))
--     destc, indc = dest.chunks, 0
--     bitst, remain = 0, UInt64(0)
--     for I in out
--         i = first(ax1) - 1
--         if ndims(bc) == 1 || bitst >= 64 - length(ax1)
--             if ndims(bc) > 1 && bitst != 0
--                 @inbounds @simd for j = bitst:63
--                     remain |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = remain
--                 bitst, remain = 0, UInt64(0)
--             end
--             while i <= last(ax1) - 64
--                 z = UInt64(0)
--                 @inbounds @simd for j = 0:63
--                     z |= UInt64(convert(Bool, bc′[i+=1, I])) << (j & 63)
--                 end
--                 @inbounds destc[indc+=1] = z
--             end
--         end
--         @inbounds @simd for j = i+1:last(ax1)
--             remain |= UInt64(convert(Bool, bc′[j, I])) << (bitst & 63)
--             bitst += 1
--         end
--     end
--     @inbounds if bitst != 0
--         destc[indc+1] = remain
--     end
--     return dest
-- end
-- /Source
-- Source: base/multidimensional.jl:298-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     CartesianIndices(::Tuple{}) = CartesianIndices{0,typeof(())}(())
-- /Source
-- Source: base/multidimensional.jl:486-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     iterate(iter::CartesianIndices{0}, done::Bool=false) = done ? nothing : (CartesianIndex(), true)
-- /Source
/-- BitArray broadcast copy specialized to the complete row95 argument types,
base/broadcast.jl:1035-1073. The destination and expression both have rank one;
the zero-rank and higher-rank carry branches are statically inapplicable.
CartesianIndices(tail(axes)) is CartesianIndices(()) and contributes exactly
one outer iteration, even for the empty tuple (multidimensional.jl:486).
All native signed indices, register packing order, bounds instrumentation,
individual chunk writes and the conditional final write remain explicit. -/
def boolTupleCopytoErased (destination : BitVector)
    (bc : BoolTupleBroadcast .erased) : BitMutationM BitVector := do
  if (boolTupleDestinationAxes destination).val != (boolTupleBroadcastAxes bc).val then
    throw (.dimensionMismatch "destination axes are not compatible with source axes")
  if h : boolTupleIsChunked destination bc = true then
    have impossible : False := by simp [boolTupleIsChunked] at h
    return False.elim impossible
  let ready := boolTuplePreprocess destination bc
  let axes := boolTupleDestinationAxes destination
  let firstAxis ← match JuliaLean.base.tuple.getindexInt axes.val (int 1) with
    | .ok axis => pure axis
    | .error _ => throw .bounds
  let chunks := destination.chunks
  let mut chunkIndex := int 0
  let mut bitIndex := int 0
  let mut remain := u64 0
  for _outer in [()] do
    let mut i := int 1 - int 1
    while i <= firstAxis - int 64 do
      let packed ← boolTupleFullWord ready i
      i := packed.1
      chunkIndex := chunkIndex + int 1
      mutableSet chunks packed.2 chunkIndex
    for j in intRange (i + int 1) firstAxis do
      let value := JuliaLean.base.number.convertSame (← boolTupleBroadcastGet ready j)
      remain := or_int remain (shl_Int (ofBool .u64 value) (and_int bitIndex (int 63)))
      bitIndex := bitIndex + int 1
  if bitIndex != int 0 then
    mutableSet chunks remain (chunkIndex + int 1)
  return destination

-- Source: base/broadcast.jl:215-216 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Base.convert(::Type{Broadcasted{NewStyle}}, bc::Broadcasted{<:Any,Axes,F,Args}) where {NewStyle,Axes,F,Args} =
--     Broadcasted{NewStyle,Axes,F,Args}(bc.f, bc.args, bc.axes)::Broadcasted{NewStyle,Axes,F,Args}
-- /Source
-- Source: base/broadcast.jl:980-980 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline copyto!(dest::AbstractArray, bc::Broadcasted) = copyto!(dest, convert(Broadcasted{Nothing}, bc))
-- /Source
/-- The general AbstractArray copyto broadcast method erases the style before
destination-specific dispatch, base/broadcast.jl:215-216,980. The source argument
is a tuple, so the AbstractArray identity shortcut at1018 does not apply. -/
def boolTupleCopytoStyled (destination : BitVector)
    (bc : BoolTupleBroadcast .tuple) : BitMutationM BitVector :=
  boolTupleCopytoErased destination
    ({ argument := bc.argument, axes := bc.axes } : BoolTupleBroadcast .erased)

-- Source: base/broadcast.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BroadcastStyle(a::AbstractArrayStyle, ::Style{Tuple})    = a
-- /Source
-- Source: base/broadcast.jl:431-438 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- combine_styles() = DefaultArrayStyle{0}()
-- combine_styles(c) = result_style(BroadcastStyle(typeof(c)))
-- function combine_styles(bc::Broadcasted)
--     bc.style isa Union{Nothing,Unknown} || return bc.style
--     throw(ArgumentError("Broadcasted{Unknown} wrappers do not have a style assigned"))
-- end
-- combine_styles(c1, c2) = result_style(combine_styles(c1), combine_styles(c2))
-- @inline combine_styles(c1, c2, cs...) = result_style(combine_styles(c1), combine_styles(c2, cs...))
-- /Source
/-- The destination's DefaultArrayStyle{1} wins over Tuple style. This is the
sole combined style reached by row95, base/broadcast.jl:136,431-438. -/
inductive BoolTupleAssignmentStyle where
  | arrayOne

-- Source: base/broadcast.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BroadcastStyle(a::AbstractArrayStyle, ::Style{Tuple})    = a
-- /Source
-- Source: base/broadcast.jl:437-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- combine_styles(c1, c2) = result_style(combine_styles(c1), combine_styles(c2))
-- /Source
/-- Closed combine_styles dispatch for the actual rank-one destination and
Tuple-style expression, base/broadcast.jl:136,437. -/
def boolTupleCombineStyles (_destination : BitVector)
    (_bc : BoolTupleBroadcast .tuple) : BoolTupleAssignmentStyle := .arrayOne

-- Source: base/broadcast.jl:932-934 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function materialize!(::BroadcastStyle, dest, bc::Broadcasted{<:Any})
--     return copyto!(dest, instantiate(Broadcasted(bc.style, bc.f, bc.args, axes(dest))))
-- end
-- /Source
/-- Styled materialization replaces the expression axes with destination axes,
then instantiates and calls the real copyto dispatch, base/broadcast.jl:932-934.
The combined style selects this method; the expression retains Tuple style
until copyto performs the separate Nothing conversion. -/
def boolTupleMaterializeStyled (_style : BoolTupleAssignmentStyle)
    (destination : BitVector) (bc : BoolTupleBroadcast .tuple) :
    BitMutationM BitVector := do
  let withAxes := { bc with axes := some (boolTupleDestinationAxes destination) }
  boolTupleCopytoStyled destination (← boolTupleInstantiate withAxes)

-- Source: base/broadcast.jl:928-930 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function materialize!(dest, bc::Broadcasted{<:Any})
--     return materialize!(combine_styles(dest, bc), dest, bc)
-- end
-- /Source
/-- The actual materialize! style-dispatch step, base/broadcast.jl:928-930. -/
def boolTupleMaterialize (destination : BitVector) (bc : BoolTupleBroadcast .tuple) :
    BitMutationM BitVector :=
  boolTupleMaterializeStyled (boolTupleCombineStyles destination bc) destination bc

-- Source: base/broadcast.jl:898-898 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- broadcast!(f::Tf, dest, As::Vararg{Any,N}) where {Tf,N} = (materialize!(dest, broadcasted(f, As...)); dest)
-- /Source
/-- Identity broadcast assignment, base/broadcast.jl:898. The pinned manual at
doc/src/manual/functions.md:1141-1143 specifies `X .= Y` as this broadcast! path
when there are no nested dotted calls, as in base/bitarray.jl:97. This is that
documented semantic specialization, not a claim to have inspected compiler IR. -/
def boolTupleBroadcastAssign (destination : BitVector) (nt : BoolTuple) :
    BitMutationM BitVector := do
  let _ ← boolTupleMaterialize destination (boolTupleBroadcasted nt)
  return destination

-- Source: base/bitarray.jl:95-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function BitVector(nt::Tuple{Vararg{Bool}})
--     bv = BitVector(undef, length(nt))
--     bv .= nt
-- end
-- /Source
/-- Complete Boolean-tuple BitVector constructor, base/bitarray.jl:95-98.
The native Int length selects the actual inner constructor at28; the final
assignment uses the closed tuple broadcast/style/check/register-pack chain.
No iterator callback, Boolean byte buffer or pointer-load abstraction is used. -/
def fromBoolTuple (runtime : AllocationData) (nt : BoolTuple) :
    BitMutationM BitVector := do
  let bv ← undef runtime ⟨[boolTupleLength nt], rfl⟩
  boolTupleBroadcastAssign bv nt

end JuliaLean.base.bitarray.Models1Group15

namespace JuliaLean.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

-- Source: base/bitarray.jl:124-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function glue_src_bitchunks(src::Vector{UInt64}, k::Int, ks1::Int, msk_s0::UInt64, ls0::Int)
--     @inbounds begin
--         chunk = ((src[k] & msk_s0) >>> ls0)
--         if ks1 > k && ls0 > 0
--             chunk_n = (src[k + 1] & ~msk_s0)
--             chunk |= (chunk_n << (64 - ls0))
--         end
--     end
--     return chunk
-- end
-- /Source
/-- Full signed-count glue helper, base/bitarray.jl:124-133. Julia's signed Int
shift operators reverse direction for negative counts; raw shift intrinsics
would be incorrect on the full typed input domain. -/
def glueSrcBitChunks (src : Nat) (k ks1 : I64) (mskS0 : U64) (ls0 : I64) :
    BitMutationM U64 := do
  let mut chunk := lshr_Int (and_int (← mutableGet src k) mskS0) ls0
  if ks1 > k ∧ ls0 > int 0 then
    let chunkN := and_int (← mutableGet src (k + int 1)) (not_int mskS0)
    chunk := or_int chunk (shl_Int chunkN (int 64 - ls0))
  return chunk

mutual

-- Source: base/bitarray.jl:135-187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copy_chunks!(dest::Vector{UInt64}, pos_d::Int, src::Vector{UInt64}, pos_s::Int, numbits::Int)
--     numbits == 0 && return
--     if dest === src && pos_d > pos_s
--         return copy_chunks_rtol!(dest, pos_d, pos_s, numbits)
--     end
-- 
--     kd0, ld0 = get_chunks_id(pos_d)
--     kd1, ld1 = get_chunks_id(pos_d + numbits - 1)
--     ks0, ls0 = get_chunks_id(pos_s)
--     ks1, ls1 = get_chunks_id(pos_s + numbits - 1)
-- 
--     delta_kd = kd1 - kd0
--     delta_ks = ks1 - ks0
-- 
--     u = _msk64
--     msk_d0 = ~(u << ld0)
--     msk_d1 = (u << (ld1+1))
--     if delta_kd == 0
--         msk_d0 |= msk_d1
--     end
--     msk_s0 = (u << ls0)
--     if delta_ks == 0
--         msk_s0 &= ~(u << (ls1+1))
--     end
-- 
--     chunk_s0 = glue_src_bitchunks(src, ks0, ks1, msk_s0, ls0)
-- 
--     dest[kd0] = (dest[kd0] & msk_d0) | ((chunk_s0 << ld0) & ~msk_d0)
-- 
--     delta_kd == 0 && return
-- 
--     for i = 1 : kd1 - kd0 - 1
--         chunk_s1 = glue_src_bitchunks(src, ks0 + i, ks1, msk_s0, ls0)
-- 
--         chunk_s = (chunk_s0 >>> (64 - ld0)) | (chunk_s1 << ld0)
-- 
--         dest[kd0 + i] = chunk_s
-- 
--         chunk_s0 = chunk_s1
--     end
-- 
--     if ks1 >= ks0 + delta_kd
--         chunk_s1 = glue_src_bitchunks(src, ks0 + delta_kd, ks1, msk_s0, ls0)
--     else
--         chunk_s1 = UInt64(0)
--     end
-- 
--     chunk_s = (chunk_s0 >>> (64 - ld0)) | (chunk_s1 << ld0)
-- 
--     dest[kd1] = (dest[kd1] & msk_d1) | (chunk_s & ~msk_d1)
-- 
--     return
-- end
-- /Source
/-- Source-faithful chunk copy, base/bitarray.jl:135-187, including aliased rightward copies. -/
def copyChunks : Nat → I64 → Nat → I64 → I64 → BitMutationM Unit
  | dest, posD, src, posS, numbits => do
    if numbits == int 0 then return
    if h : dest = src ∧ posD > posS then
      return ← copyChunksRtol dest posD posS numbits
    let (kd0, ld0) := getChunksId posD
    let (kd1, ld1) := getChunksId (posD + numbits - int 1)
    let (ks0, ls0) := getChunksId posS
    let (ks1, ls1) := getChunksId (posS + numbits - int 1)
    let deltaKD := kd1 - kd0
    let deltaKS := ks1 - ks0
    let u := u64Max
    let mut mskD0 := not_int (shl_Int u ld0)
    let mskD1 := shl_Int u (ld1 + int 1)
    if deltaKD == int 0 then mskD0 := or_int mskD0 mskD1
    let mut mskS0 := shl_Int u ls0
    if deltaKS == int 0 then mskS0 := and_int mskS0 (not_int (shl_Int u (ls1 + int 1)))
    let mut chunkS0 ← glueSrcBitChunks src ks0 ks1 mskS0 ls0
    let destD0 ← mutableGet dest kd0
    mutableSet dest (or_int (and_int destD0 mskD0) (and_int (shl_Int chunkS0 ld0) (not_int mskD0))) kd0
    if deltaKD == int 0 then return
    for i in intRange (int 1) (kd1 - kd0 - int 1) do
      let chunkS1 ← glueSrcBitChunks src (ks0 + i) ks1 mskS0 ls0
      let chunkS := or_int (lshr_Int chunkS0 (int 64 - ld0)) (shl_Int chunkS1 ld0)
      mutableSet dest chunkS (kd0 + i)
      chunkS0 := chunkS1
    let chunkS1 ← if ks1 ≥ ks0 + deltaKD then
      glueSrcBitChunks src (ks0 + deltaKD) ks1 mskS0 ls0
    else pure (u64 0)
    let chunkS := or_int (lshr_Int chunkS0 (int 64 - ld0)) (shl_Int chunkS1 ld0)
    let destD1 ← mutableGet dest kd1
    mutableSet dest (or_int (and_int destD1 mskD1) (and_int chunkS (not_int mskD1))) kd1
    pure ()
  termination_by dest posD src posS numbits => if posD > posS then 1 else 0
decreasing_by
    simp_wf
    rcases h with ⟨_, hd⟩
    change posS.val < posD.val at hd
    have hnot : ¬ posD < posS := by
      intro h'
      change posD.val < posS.val at h'
      omega
    have hgt : posS < posD := by change posS.val < posD.val; exact hd
    simp [hnot, hgt]

-- Source: base/bitarray.jl:189-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copy_chunks_rtol!(chunks::Vector{UInt64}, pos_d::Int, pos_s::Int, numbits::Int)
--     pos_d == pos_s && return
--     pos_d < pos_s && return copy_chunks!(chunks, pos_d, chunks, pos_s, numbits)
-- 
--     left = numbits
--     s = min(left, 64)
--     b = left - s
--     ps = pos_s + b
--     pd = pos_d + b
--     u = _msk64
--     while left > 0
--         kd0, ld0 = get_chunks_id(pd)
--         kd1, ld1 = get_chunks_id(pd + s - 1)
--         ks0, ls0 = get_chunks_id(ps)
--         ks1, ls1 = get_chunks_id(ps + s - 1)
-- 
--         delta_kd = kd1 - kd0
--         delta_ks = ks1 - ks0
-- 
--         msk_d0 = ~(u << ld0)
--         msk_d1 = (u << (ld1+1))
--         if delta_kd == 0
--             msk_d0 |= msk_d1
--         end
--         msk_s0 = (u << ls0)
--         if delta_ks == 0
--             msk_s0 &= ~(u << (ls1+1))
--         end
-- 
--         chunk_s0 = glue_src_bitchunks(chunks, ks0, ks1, msk_s0, ls0) & ~(u << s)
--         chunks[kd0] = (chunks[kd0] & msk_d0) | ((chunk_s0 << ld0) & ~msk_d0)
-- 
--         if delta_kd != 0
--             chunk_s = (chunk_s0 >>> (64 - ld0))
-- 
--             chunks[kd1] = (chunks[kd1] & msk_d1) | (chunk_s & ~msk_d1)
--         end
-- 
--         left -= s
--         s = min(left, 64)
--         b = left - s
--         ps = pos_s + b
--         pd = pos_d + b
--     end
-- end
-- /Source
/-- Right-to-left chunk copy, base/bitarray.jl:189-233. -/
def copyChunksRtol : Nat → I64 → I64 → I64 → BitMutationM Unit
  | chunks, posD, posS, numbits => do
    if posD == posS then return
    if h : posD < posS then return ← copyChunks chunks posD chunks posS numbits
    let mut left := numbits
    let mut s := if left < int 64 then left else int 64
    let mut b := left - s
    let mut ps := posS + b
    let mut pd := posD + b
    let u := u64Max
    while left > int 0 do
      let (kd0, ld0) := getChunksId pd
      let (kd1, ld1) := getChunksId (pd + s - int 1)
      let (ks0, ls0) := getChunksId ps
      let (ks1, ls1) := getChunksId (ps + s - int 1)
      let deltaKD := kd1 - kd0
      let deltaKS := ks1 - ks0
      let mut mskD0 := not_int (shl_Int u ld0)
      let mskD1 := shl_Int u (ld1 + int 1)
      if deltaKD == int 0 then mskD0 := or_int mskD0 mskD1
      let mut mskS0 := shl_Int u ls0
      if deltaKS == int 0 then mskS0 := and_int mskS0 (not_int (shl_Int u (ls1 + int 1)))
      let chunkS0 := and_int (← glueSrcBitChunks chunks ks0 ks1 mskS0 ls0) (not_int (shl_Int u s))
      let destD0 ← mutableGet chunks kd0
      mutableSet chunks (or_int (and_int destD0 mskD0) (and_int (shl_Int chunkS0 ld0) (not_int mskD0))) kd0
      if deltaKD != int 0 then
        let chunkS := lshr_Int chunkS0 (int 64 - ld0)
        let destD1 ← mutableGet chunks kd1
        mutableSet chunks (or_int (and_int destD1 mskD1) (and_int chunkS (not_int mskD1))) kd1
      left := left - s
      s := if left < int 64 then left else int 64
      b := left - s
      ps := posS + b
      pd := posD + b
    pure ()
  termination_by chunks posD posS numbits => if posD < posS then 1 else 0
decreasing_by
    simp_wf
    change posD.val < posS.val at h
    have hlt : posD < posS := by change posD.val < posS.val; exact h
    have hnot : ¬ posS < posD := by
      intro h'
      change posS.val < posD.val at h'
      omega
    simp [hlt, hnot]

end

-- Source: base/bitarray.jl:235-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill_chunks!(Bc::Array{UInt64}, x::Bool, pos::Int, numbits::Int)
--     numbits <= 0 && return
--     k0, l0 = get_chunks_id(pos)
--     k1, l1 = get_chunks_id(pos+numbits-1)
-- 
--     u = _msk64
--     msk0 = (u << l0)
--     msk1 = ~(u << (l1+1))
--     if k1 == k0
--         msk0 &= msk1
--     end
--     @inbounds if x
--         Bc[k0] |= msk0
--         for k = k0+1:k1-1
--             Bc[k] = u
--         end
--         k1 > k0 && (Bc[k1] |= msk1)
--     else
--         Bc[k0] &= ~msk0
--         for k = k0+1:k1-1
--             Bc[k] = 0
--         end
--         k1 > k0 && (Bc[k1] &= ~msk1)
--     end
-- end
-- /Source
/-- Observable return alternatives of Julia's final short-circuit assignment,
base/bitarray.jl:235-259.
`none` is Julia nothing, `some (.inl false)` is false, and `some (.inr word)` is UInt64. -/
abbrev FillChunkResult := Option (Bool ⊕ U64)

-- Source: base/bitarray.jl:235-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill_chunks!(Bc::Array{UInt64}, x::Bool, pos::Int, numbits::Int)
--     numbits <= 0 && return
--     k0, l0 = get_chunks_id(pos)
--     k1, l1 = get_chunks_id(pos+numbits-1)
-- 
--     u = _msk64
--     msk0 = (u << l0)
--     msk1 = ~(u << (l1+1))
--     if k1 == k0
--         msk0 &= msk1
--     end
--     @inbounds if x
--         Bc[k0] |= msk0
--         for k = k0+1:k1-1
--             Bc[k] = u
--         end
--         k1 > k0 && (Bc[k1] |= msk1)
--     else
--         Bc[k0] &= ~msk0
--         for k = k0+1:k1-1
--             Bc[k] = 0
--         end
--         k1 > k0 && (Bc[k1] &= ~msk1)
--     end
-- end
-- /Source
/-- Fill chunk bits and retain the source's return value, base/bitarray.jl:235-259. -/
def fillChunks (bc : Nat) (x : Bool) (pos numbits : I64) : BitMutationM FillChunkResult := do
  if numbits ≤ int 0 then return none
  let (k0, l0) := getChunksId pos
  let (k1, l1) := getChunksId (pos + numbits - int 1)
  let u := u64Max
  let mut msk0 := shl_Int u l0
  let msk1 := not_int (shl_Int u (l1 + int 1))
  if k1 == k0 then msk0 := and_int msk0 msk1
  if x then
    let c0 ← mutableGet bc k0
    mutableSet bc (or_int c0 msk0) k0
    for k in intRange (k0 + int 1) (k1 - int 1) do
      mutableSet bc u k
    if k1 > k0 then
      let c1 ← mutableGet bc k1
      let word := or_int c1 msk1
      mutableSet bc word k1
      return some (.inr word)
    return some (.inl false)
  else
    let c0 ← mutableGet bc k0
    mutableSet bc (and_int c0 (not_int msk0)) k0
    for k in intRange (k0 + int 1) (k1 - int 1) do
      mutableSet bc (u64 0) k
    if k1 > k0 then
      let c1 ← mutableGet bc k1
      let word := and_int c1 (not_int msk1)
      mutableSet bc word k1
      return some (.inr word)
    return some (.inl false)

-- Source: base/bitarray.jl:261-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- copy_to_bitarray_chunks!(dest::Vector{UInt64}, pos_d::Int, src::BitArray, pos_s::Int, numbits::Int) =
--     copy_chunks!(dest, pos_d, src.chunks, pos_s, numbits)
-- /Source
/-- Packed-source dispatch uses the corrected, concrete copy, base/bitarray.jl:261-262. -/
def copyToBitArrayChunks {N : Nat} (dest : Nat) (posD : I64) (src : BitArray N)
    (posS numbits : I64) : BitMutationM Unit :=
  copyChunks dest posD src.chunks posS numbits

-- Source: base/bitarray.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function pack8bools(z::UInt64)
--     z |= z >>> 7
--     z |= z >>> 14
--     z |= z >>> 28
--     z &= 0xFF
--     return z
-- end
-- /Source
/-- Each Julia compound assignment consumes the updated word, base/bitarray.jl:266-272. -/
def pack8bools (z : U64) : U64 :=
  let z := or_int z (lshr_Int z (int 7))
  let z := or_int z (lshr_Int z (int 14))
  let z := or_int z (lshr_Int z (int 28))
  let byteMask := JInt.lit .u8 255
  and_int z (JuliaLean.base.int.widenTo .u64 byteMask)

end JuliaLean.base.bitarray.Models1Group15

namespace JuliaLean.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

/-! Internal type-preservation facts for the already installed tuple map.
These close native dispatch without default values; they are not new public property proofs. -/
section NativeTupleMap
open JuliaLean.base.tuple

private theorem nativeDims_mapOneRecEq {α β : Type} (f : α → β) (fuel : Nat) :
    ∀ t : List α, t.length ≤ fuel → mapOneRec f fuel t = t.map f := by
  induction fuel with
  | zero =>
    intro t ht
    have hnil : t = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst t
    simp [mapOneRec, mapOneEmpty]
  | succ fuel ih =>
    intro t ht
    cases t with
    | nil => simp [mapOneRec, mapOneGeneric]
    | cons a t =>
      simp only [mapOneRec, mapOneGeneric, List.map_cons]
      rw [ih t (by simpa using Nat.le_of_succ_le_succ ht)]

private theorem nativeDims_mapOneLoopShift {α β : Type} (f : α → β) (a : α) (t : List α) :
    ∀ i k, mapOneLoop f (a :: t) (i + 1) k = mapOneLoop f t i k := by
  intro i k
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [mapOneLoop, ih]

private theorem nativeDims_mapOneLoopFull {α β : Type} (f : α → β) (t : List α) :
    mapOneLoop f t 0 t.length = t.map f := by
  induction t with
  | nil => rfl
  | cons a t ih =>
      change mapOneLoop f (a :: t) 0 (t.length + 1) = f a :: t.map f
      simp only [mapOneLoop, List.getElem?_cons_zero]
      rw [nativeDims_mapOneLoopShift f a t 0 t.length]
      exact congrArg (fun xs => f a :: xs) ih
private theorem nativeDims_mappedEffects {α β : Type} (f : α → R β) (xs : List α) :
    (mapOneRec f xs.length xs).mapM id = xs.mapM f := by
  rw [nativeDims_mapOneRecEq f _ _ (by omega), List.mapM_map]
  rfl

private theorem nativeDims_mapTupleModel {α β : Type} (f : α → R β) (xs : List α) :
    mapTuple f xs = xs.mapM f := by
  unfold mapTuple
  split
  · rw [show mapOneLong f xs = xs.map f by exact nativeDims_mapOneLoopFull f xs, List.mapM_map]
    rfl
  · have generic : ∀ ys : List α,
        (mapOneGeneric f ys.length ys).mapM id = ys.mapM f := by
      intro ys
      have hm := nativeDims_mapOneRecEq f (ys.length + 1) ys (by omega)
      simp only [mapOneRec] at hm
      rw [hm, List.mapM_map]
      rfl
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b xs =>
        cases xs with
        | nil => rfl
        | cons c xs =>
          cases xs with
          | nil => rfl
          | cons d xs => exact generic (a :: b :: c :: d :: xs)


-- Source: base/tuple.jl:358-362 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map(f, t::Tuple{})              = ()
-- map(f, t::Tuple{Any,})          = (@inline; (f(t[1]),))
-- map(f, t::Tuple{Any, Any})      = (@inline; (f(t[1]), f(t[2])))
-- map(f, t::Tuple{Any, Any, Any}) = (@inline; (f(t[1]), f(t[2]), f(t[3])))
-- map(f, t::Tuple)                = (@inline; (f(t[1]), map(f,tail(t))...))
-- /Source
-- Source: base/tuple.jl:394-401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function map(f, t::Any32)
--     n = length(t)
--     A = Vector{Any}(undef, n)
--     for i=1:n
--         A[i] = f(t[i])
--     end
--     (A...,)
-- end
-- /Source
/-- Native Int map at base/bitarray.jl:68-71, using the existing source-dispatched
mapTuple model, including its large-tuple path. The type witness records only
that mapping a native dimension tuple preserves its arity. -/
def nativeMapDims {N : Nat} (dims : Dims N) : Dims N :=
  let result := JuliaLean.base.tuple.mapTuple
    (fun x : I64 => pure (JuliaLean.base.number.convertSame x)) dims.val
  have exactResult : result = .ok dims.val := by
    have mapId : ∀ xs : List I64,
        xs.mapM (fun x => (pure x : JuliaLean.base.tuple.R I64)) = .ok xs := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih => simp only [List.mapM_cons, ih]; rfl
    simp only [result, nativeDims_mapTupleModel, JuliaLean.base.number.convertSame]
    exact mapId dims.val
  match h : result with
  | .ok ds => ⟨ds, by
      have eqds : ds = dims.val := Except.ok.inj exactResult
      simpa [eqds] using dims.property⟩
  | .error _ => False.elim (by cases exactResult)

end NativeTupleMap

-- Source: base/bitarray.jl:70-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BitArray(::UndefInitializer, dims::NTuple{N,Integer}) where {N} = BitArray{N}(undef, map(Int, dims)...)
-- BitArray{N}(::UndefInitializer, dims::NTuple{N,Integer}) where {N} = BitArray{N}(undef, map(Int, dims)...)
-- /Source
/-- Native Int specialization of tuple constructor dispatch at base/bitarray.jl:70-71.
Every Int-to-Int constructor is the installed same-type identity; this helper does
not claim to implement conversion of arbitrary Integer subtypes. -/
def nativeTupleUndef {N : Nat} (runtime : AllocationData) (dims : Dims N) :
    BitMutationM (BitArray N) :=
  undef runtime (nativeMapDims dims)

-- Source: base/bitarray.jl:68-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BitArray(::UndefInitializer, dims::Integer...) = BitArray(undef, map(Int,dims))
-- /Source
/-- Native Int-varargs specialization of the outer constructor, base/bitarray.jl:68.
Unlike the parameterized inner constructor, this maps Int once before the tuple
constructor maps it again. Both maps use the installed same-type conversion. -/
def nativeVarargsUndef {N : Nat} (runtime : AllocationData) (dims : Dims N) :
    BitMutationM (BitArray N) :=
  nativeTupleUndef runtime (nativeMapDims dims)

-- Source: base/bitarray.jl:359-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(B::BitArray) = BitArray(undef, size(B))
-- /Source
/-- Same-shape allocation, base/bitarray.jl:359. The witness is the Julia tuple-rank
representation invariant, not a behavioral assumption about this method. -/
def similar {N : Nat} (runtime : AllocationData) (B : BitArray N)
    (rank : (bitArraySizeRanked B).length = N) : BitMutationM (BitArray N) :=
  nativeTupleUndef runtime ⟨bitArraySizeRanked B, rank⟩

-- Source: base/bitarray.jl:360-360 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(B::BitArray, dims::Int...) = BitArray(undef, dims)
-- /Source
/-- Native dimension-varargs similar, base/bitarray.jl:360. The result rank follows dims. -/
def similarDims {N R : Nat} (runtime : AllocationData) (_B : BitArray N)
    (dims : Dims R) : BitMutationM (BitArray R) :=
  nativeTupleUndef runtime dims

-- Source: base/bitarray.jl:361-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(B::BitArray, dims::Dims) = BitArray(undef, dims...)
-- /Source
/-- Native dimension-tuple similar, base/bitarray.jl:361. Splat selects the outer
unparameterized constructor, including its two native tuple maps. -/
def similarDimsTuple {N R : Nat} (runtime : AllocationData) (_B : BitArray N)
    (dims : Dims R) : BitMutationM (BitArray R) :=
  nativeVarargsUndef runtime dims

-- Source: base/bitarray.jl:363-363 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(B::BitArray, T::Type{Bool}, dims::Dims) = BitArray(undef, dims)
-- /Source
/-- Bool-element similar, base/bitarray.jl:363. -/
def similarBool {N R : Nat} (runtime : AllocationData) (_B : BitArray N)
    (dims : Dims R) : BitMutationM (BitArray R) :=
  nativeTupleUndef runtime dims

-- Source: base/abstractarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexLinear, A::Union{Array, Memory}) = unchecked_oneto(length(A))
-- /Source
/-- Native dense UInt64 eachindex at the `fill!` call in base/bitarray.jl:374,376.
The installed dense-array dispatcher selects a one-based range; collecting its pure
native indices does not perform reads or move any writes before a check. -/
def chunkIndices (handle : Nat) : BitMutationM (List I64) :=
  JuliaLean.base.abstractarray.eachindexDense mutableLength (intRange (int 1)) handle

-- Source: base/array.jl:368-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill!(A::AbstractArray{T}, x) where T
--     @inline
--     xT = x isa T ? x : convert(T, x)::T
--     return _fill!(A, xT)
-- end
-- function _fill!(A::AbstractArray{T}, x::T) where T
--     for i in eachindex(A)
--         A[i] = x
--     end
--     return A
-- end
-- /Source
/-- Concrete UInt64-array fill callee at base/bitarray.jl:376. -/
def fillChunkWord (handle : Nat) (word : U64) : BitMutationM Unit := do
  let _ ← JuliaLean.base.array.fillBang
    (fun (_ : U64) => true) (fun x => x)
    (fun x => pure (JuliaLean.base.number.convertSame x))
    (JuliaLean.base.array.fillTyped chunkIndices mutableSet) handle word
  pure ()

-- Source: base/array.jl:368-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill!(A::AbstractArray{T}, x) where T
--     @inline
--     xT = x isa T ? x : convert(T, x)::T
--     return _fill!(A, xT)
-- end
-- function _fill!(A::AbstractArray{T}, x::T) where T
--     for i in eachindex(A)
--         A[i] = x
--     end
--     return A
-- end
-- /Source
/-- Int zero converts to UInt64 before the concrete array fill, base/bitarray.jl:374. -/
def fillChunkZero (handle : Nat) : BitMutationM Unit := do
  let _ ← JuliaLean.base.array.fillBang
    (fun (_ : I64) => false) (fun x => JInt.rem .u64 x)
    (fun x => match JuliaLean.base.int.convert .u64 x with
      | .ok word => pure word
      | .error _ => throw .inexact)
    (JuliaLean.base.array.fillTyped chunkIndices mutableSet) handle (int 0)
  pure ()

-- Source: base/bitarray.jl:368-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill!(B::BitArray, x)
--     y = convert(Bool, x)
--     isempty(B) && return B
--     Bc = B.chunks
--     if !y
--         fill!(Bc, 0)
--     else
--         fill!(Bc, _msk64)
--         Bc[end] &= _msk_end(B)
--     end
--     return B
-- end
-- /Source
/-- The open dispatch is convert(Bool,x); UInt64-array filling and final-word
masking use the installed concrete Base callees. Conversion runs even when B is empty. -/
def fillConvert {N : Nat} {X : Type}
    (convertBool : X → BitMutationM Bool) (B : BitArray N) (x : X) :
    BitMutationM (BitArray N) := do
  let y ← convertBool x
  if B.len == int 0 then return B
  let bc := B.chunks
  if !y then
    fillChunkZero bc
  else
    fillChunkWord bc u64Max
    let lastIndex ← mutableLength bc
    let last ← mutableGet bc lastIndex
    mutableSet bc (and_int last (maskEndArray B)) lastIndex
  return B

-- Source: base/bitarray.jl:368-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
/-- Bool-input compatibility specialization of fillConvert. -/
def fillBool {N : Nat} (B : BitArray N) (x : Bool) : BitMutationM (BitArray N) :=
  fillConvert (fun value => pure (JuliaLean.base.number.convertSame value)) B x

-- Source: base/bitarray.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- falses(dims::NTuple{N, Integer}) where {N} = fill!(BitArray(undef, dims), false)
-- /Source
/-- Native Int-tuple falses specialization, base/bitarray.jl:396; arbitrary Integer
conversion is not represented by this helper. -/
def falsesNative {N : Nat} (runtime : AllocationData) (dims : Dims N) :
    BitMutationM (BitArray N) := do
  let B ← nativeTupleUndef runtime dims
  fillBool B false

-- Source: base/bitarray.jl:397-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- falses(dims::Tuple{}) = fill!(BitArray(undef, dims), false)
-- /Source
/-- Empty dimensions mean a zero-dimensional, one-element BitArray, base/bitarray.jl:397. -/
def falsesEmpty (runtime : AllocationData) : BitMutationM (BitArray 0) := do
  let B ← nativeTupleUndef runtime ⟨[], rfl⟩
  fillBool B false

-- Source: base/bitarray.jl:415-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- trues(dims::NTuple{N, Integer}) where {N} = fill!(BitArray(undef, dims), true)
-- /Source
/-- Native Int-tuple trues specialization, base/bitarray.jl:415; arbitrary Integer
conversion is not represented by this helper. -/
def truesNative {N : Nat} (runtime : AllocationData) (dims : Dims N) :
    BitMutationM (BitArray N) := do
  let B ← nativeTupleUndef runtime dims
  fillBool B true

-- Source: base/bitarray.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- trues(dims::Tuple{}) = fill!(BitArray(undef, dims), true)
-- /Source
/-- Empty dimensions mean a zero-dimensional, one-element BitArray, base/bitarray.jl:416. -/
def truesEmpty (runtime : AllocationData) : BitMutationM (BitArray 0) := do
  let B ← nativeTupleUndef runtime ⟨[], rfl⟩
  fillBool B true

end JuliaLean.base.bitarray.Models1Group15

namespace JuliaLean.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

/-! Native coordinate dispatch used only by the assigned BitMatrix `one` method.
All range instances below are fixed Int dispatch, not caller-supplied interfaces. -/

private local instance nativeRangeType : JuliaLean.base.range.JType I64 where
  isBool := false
  isSigned := true
  isInteger := true
  isAbstractFloat := false
  bool_eq := by simp

private local instance nativeRangePrint : JuliaLean.base.range.JPrint I64 :=
  ⟨fun x => toString x.val⟩
private local instance nativeRangeZero : JuliaLean.base.range.JZero I64 := ⟨int 0⟩
private local instance nativeRangeOneunit : JuliaLean.base.range.JOneunit I64 := ⟨int 1⟩
private local instance nativeRangeMax : JuliaLean.base.range.JMax I64 I64 I64 :=
  ⟨fun x y => pure (JuliaLean.base.int.max_BitInteger x y)⟩
private local instance nativeRangeCtor : JuliaLean.base.range.JCtor I64 I64 :=
  ⟨fun x => pure (JuliaLean.base.number.convertSame x)⟩
private local instance nativeRangeOneToT : JuliaLean.base.range.JOneToT I64 I64 :=
  ⟨@JuliaLean.base.range.OneTo_T_stop I64 I64
    nativeRangeType nativeRangePrint nativeRangeZero nativeRangeMax⟩
private local instance nativeRangeOneTo : JuliaLean.base.range.JOneTo1 I64
    (JuliaLean.base.range.OneTo I64) :=
  ⟨@JuliaLean.base.range.OneTo_stop I64 nativeRangeOneToT⟩

/-- Native OneTo axes used by base/abstractarray.jl:100-103. -/
abbrev NativeAxis := JuliaLean.base.range.OneTo I64

/-- Extract a known total native primitive without a default value or an error-class
coercion. The proof is closed at each use and is never an input to a Julia model. -/
private def totalRangeValue (result : JuliaLean.base.range.JlX α)
    (total : ∃ value, result = .ok value) : α :=
  match h : result with
  | .ok value => value
  | .error _ => False.elim (by rcases total with ⟨value, hv⟩; cases hv)

-- Source: base/range.jl:487-507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function OneTo{T}(stop) where {T<:Integer}
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         T === Bool && throwbool(stop)
--         return new(max(zero(T), stop))
--     end
-- 
--     function OneTo{T}(r::AbstractRange) where {T<:Integer}
--         throwstart(r) = (@noinline; throw(ArgumentError("first element must be 1, got $(first(r))")))
--         throwstep(r)  = (@noinline; throw(ArgumentError("step must be 1, got $(step(r))")))
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         first(r) == 1 || throwstart(r)
--         step(r)  == 1 || throwstep(r)
--         T === Bool && throwbool(r)
--         return new(max(zero(T), last(r)))
--     end
-- 
--     global unchecked_oneto(stop::Integer) = new{typeof(stop)}(stop)
-- end
-- OneTo(stop::T) where {T<:Integer} = OneTo{T}(stop)
-- OneTo(r::AbstractRange{T}) where {T<:Integer} = OneTo{T}(r)
-- oneto(r) = OneTo(r)
-- /Source
/-- Closed `oneto(::Int)` call from base/abstractarray.jl:395. Its checked
OneTo constructor clamps negative stops; native Int construction cannot throw. -/
def nativeOneTo (n : I64) : NativeAxis :=
  totalRangeValue (@JuliaLean.base.range.oneto I64 NativeAxis nativeRangeOneTo n) (by
    refine ⟨⟨JuliaLean.base.int.max_BitInteger (int 0) n⟩, ?_⟩
    rfl)

-- Source: base/range.jl:810-817 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- let bigints = Union{Int, UInt, Int64, UInt64, Int128, UInt128},
--     smallints = (Int === Int64 ?
--                 Union{Int8, UInt8, Int16, UInt16, Int32, UInt32} :
--                 Union{Int8, UInt8, Int16, UInt16}),
--     bitints = Union{bigints, smallints}
--     global length, checked_length, firstindex
--     # compile optimization for which promote_type(T, Int) == T
--     length(r::OneTo{T}) where {T<:bigints} = r.stop
-- /Source
/-- Closed `length(::OneTo{Int})`, base/range.jl:817, through the existing
big-int length method selected for native Int on the 64-bit target. -/
def nativeAxisLength (axis : NativeAxis) : I64 :=
  JuliaLean.base.range.length_OneTo_bigints axis

/-- Only the genuine native BoundsError can leave the coordinate helpers below.
This internal refinement prevents coercing unrelated Julia exception classes. -/
private def BoundsOnly (result : JuliaLean.base.abstractarray.Result α) : Prop :=
  ∀ e, result = .error e → e = .julia .boundsError

private def liftNativeBounds (result : JuliaLean.base.abstractarray.Result α)
    (_only : BoundsOnly result) : BitMutationM α :=
  match result with
  | .ok value => pure value
  | .error _ => throw .bounds

private theorem tupleGetBounds (xs : List α) (i : I64) :
    BoundsOnly (JuliaLean.base.abstractarray.tupleGet xs i) := by
  unfold BoundsOnly JuliaLean.base.abstractarray.tupleGet
  split
  · intro e h; cases h; rfl
  · split
    · intro e h; cases h
    · intro e h; cases h; rfl

-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source
/-- Native metadata call from base/abstractarray.jl:100-103. -/
def nativeMatrixAxes (B : BitMatrix) : JuliaLean.base.abstractarray.Result (List NativeAxis) :=
  JuliaLean.base.abstractarray.axesDefault (fun x => pure (bitArraySize x))
    JuliaLean.base.range.unchecked_oneto B

-- Source: base/abstractarray.jl:722-728 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds_indices(::Type{Bool}, inds::Tuple, I::Tuple{Any, Vararg})
--     @inline
--     return checkindex(Bool, get(inds, 1, OneTo(1)), I[1])::Bool &&
--         checkbounds_indices(Bool, safe_tail(inds), tail(I))
-- end
-- 
-- checkbounds_indices(::Type{Bool}, inds::Tuple, ::Tuple{}) = (@inline; all(x->length(x)==1, inds))
-- /Source
/-- Native OneTo/integer `checkbounds_indices` recursion, base/abstractarray.jl:722-728. -/
def nativeCheckCoordinates (axes : List NativeAxis) : List I64 →
    JuliaLean.base.abstractarray.Result Bool
  | [] => JuliaLean.base.abstractarray.checkboundsIndicesNil
      (fun axis => pure (nativeAxisLength axis)) axes
  | i :: is => JuliaLean.base.abstractarray.checkboundsIndicesCons
      (JuliaLean.base.range.unchecked_oneto (int 1))
      (fun axis j => pure (JuliaLean.base.abstractarray.checkindexOneTo axis.stop j))
      (fun tail _ => nativeCheckCoordinates tail is) axes i is

private theorem allNativeAxesTotal (axes : List NativeAxis) :
    ∃ b, JuliaLean.base.abstractarray.checkboundsIndicesNil
      (fun axis => pure (nativeAxisLength axis)) axes = .ok b := by
  induction axes with
  | nil => exact ⟨true, rfl⟩
  | cons axis axes ih =>
    rcases ih with ⟨b, hb⟩
    simp only [JuliaLean.base.abstractarray.checkboundsIndicesNil] at hb ⊢
    simp only [JuliaLean.base.abstractarray.allTupleM]
    change ∃ b, (if (nativeAxisLength axis).val == 1 then
      JuliaLean.base.abstractarray.allTupleM
        (fun x => pure ((nativeAxisLength x).val == 1)) axes else pure false) = .ok b
    split
    · exact ⟨b, hb⟩
    · exact ⟨false, rfl⟩

private theorem nativeCheckCoordinatesTotal (axes : List NativeAxis) (is : List I64) :
    ∃ b, nativeCheckCoordinates axes is = .ok b := by
  induction is generalizing axes with
  | nil => exact allNativeAxesTotal axes
  | cons i is ih =>
    unfold nativeCheckCoordinates
    unfold JuliaLean.base.abstractarray.checkboundsIndicesCons
    change ∃ b, (if JuliaLean.base.abstractarray.checkindexOneTo
      (axes.headD (JuliaLean.base.range.unchecked_oneto (int 1))).stop i then
        nativeCheckCoordinates axes.tail is else pure false) = .ok b
    split
    · exact ih axes.tail
    · exact ⟨false, rfl⟩

-- Source: base/abstractarray.jl:681-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
-- function checkbounds(::Type{Bool}, A::AbstractArray, I...)
--     @inline
--     checkbounds_indices(Bool, axes(A), I)
-- end
-- 
-- # Linear indexing is explicitly allowed when there is only one (non-cartesian) index;
-- # indices that do not allow linear indexing (e.g., logical arrays, cartesian indices, etc)
-- # must add specialized methods to implement their restrictions
-- function checkbounds(::Type{Bool}, A::AbstractArray, i)
--     @inline
--     return checkindex(Bool, eachindex(IndexLinear(), A), i)
-- end
-- /Source
/-- Concrete coordinate bounds check selected by base/abstractarray.jl:1489.
No source storage is read by this metadata check. -/
def nativeMatrixCheck (B : BitMatrix) (is : List I64) : BitMutationM Unit := do
  let result := JuliaLean.base.abstractarray.checkboundsMany
    nativeMatrixAxes nativeCheckCoordinates B is
  let b ← liftNativeBounds result (by
    rcases nativeCheckCoordinatesTotal
      ((bitArraySize B).map JuliaLean.base.range.unchecked_oneto) is with ⟨b, hb⟩
    intro e h
    change nativeCheckCoordinates
      ((bitArraySize B).map JuliaLean.base.range.unchecked_oneto) is = .error e at h
    rw [hb] at h
    cases h)
  if !b then throw .bounds

-- Source: base/abstractarray.jl:3193-3208 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _sub2ind_recurse(::Any, L, ind) = ind
-- function _sub2ind_recurse(::Tuple{}, L, ind, i::Integer, I::Integer...)
--     @inline
--     _sub2ind_recurse((), L, ind+(i-1)*L, I...)
-- end
-- function _sub2ind_recurse(inds, L, ind, i::Integer, I::Integer...)
--     @inline
--     r1 = inds[1]
--     _sub2ind_recurse(tail(inds), nextL(L, r1), ind+offsetin(i, r1)*L, I...)
-- end
-- 
-- nextL(L, l::Integer) = L*l
-- nextL(L, r::AbstractUnitRange) = L*length(r)
-- nextL(L, r::Slice) = L*length(r.indices)
-- offsetin(i, l::Integer) = i-1
-- offsetin(i, r::AbstractUnitRange) = i-first(r)
-- /Source
/-- Native `_sub2ind_recurse` from base/abstractarray.jl:3193-3202; all
intermediate offsets, strides, products and sums remain wrapped Julia Ints. -/
def nativeLinearCoordinates (axes : List NativeAxis) (stride index : I64) :
    List I64 → JuliaLean.base.abstractarray.Result I64
  | [] => pure (JuliaLean.base.abstractarray.sub2indRecurseDone axes stride index)
  | i :: is =>
    match axes with
    | [] => JuliaLean.base.abstractarray.sub2indRecurseEmpty
        (fun a b => pure (sub_int a b)) (fun a b => pure (mul_int a b))
        (fun a b => pure (add_int a b))
        (fun _ next ind _ => nativeLinearCoordinates [] next ind is)
        stride index i is
    | _ :: _ => JuliaLean.base.abstractarray.sub2indRecurse
        (fun axs => JuliaLean.base.abstractarray.tupleGet axs (int 1))
        (fun axs => pure axs.tail)
        (JuliaLean.base.abstractarray.nextLRange
          (fun axis => pure (nativeAxisLength axis)) (fun a b => pure (mul_int a b)))
        (JuliaLean.base.abstractarray.offsetinRange
          (fun axis => pure (JuliaLean.base.range.first_OneTo axis))
          (fun a b => pure (sub_int a b)))
        (fun a b => pure (mul_int a b)) (fun a b => pure (add_int a b))
        (fun axs next ind _ => nativeLinearCoordinates axs next ind is)
        axes stride index i is

private theorem nativeLinearCoordinatesTotal (axes : List NativeAxis)
    (stride index : I64) (is : List I64) :
    ∃ value, nativeLinearCoordinates axes stride index is = .ok value := by
  induction is generalizing axes stride index with
  | nil => exact ⟨index, rfl⟩
  | cons i is ih =>
    cases axes with
    | nil =>
      change ∃ value, nativeLinearCoordinates [] stride
        (add_int index (mul_int (sub_int i (int 1)) stride)) is = .ok value
      exact ih [] stride _
    | cons axis axes =>
      change ∃ value, nativeLinearCoordinates axes
        (mul_int stride (nativeAxisLength axis))
        (add_int index (mul_int (sub_int i (int 1)) stride)) is = .ok value
      exact ih axes _ _

-- Source: base/abstractarray.jl:1401-1401 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _to_linear_index(A::AbstractArray, I::Integer...) = (@inline; _sub2ind(A, I...))
-- /Source
/-- `_to_linear_index` selected by base/abstractarray.jl:1490, reusing the
installed abstract-array/axes dispatch and the native recursion above. -/
def nativeMatrixLinear (B : BitMatrix) (is : List I64) : BitMutationM I64 :=
  let result := JuliaLean.base.abstractarray.toLinearMany
    (JuliaLean.base.abstractarray.sub2indArray nativeMatrixAxes
      (JuliaLean.base.abstractarray.sub2indAxes nativeLinearCoordinates)) B is
  liftNativeBounds result (by
    rcases nativeLinearCoordinatesTotal
      ((bitArraySize B).map JuliaLean.base.range.unchecked_oneto)
      (int 1) (int 1) is with ⟨value, hv⟩
    intro e h
    change nativeLinearCoordinates
      ((bitArraySize B).map JuliaLean.base.range.unchecked_oneto)
      (int 1) (int 1) is = .error e at h
    rw [hv] at h
    cases h)

-- Source: base/abstractarray.jl:690-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, i)
--     @inline
--     return checkindex(Bool, eachindex(IndexLinear(), A), i)
-- end
-- /Source
-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source
-- Source: base/abstractarray.jl:141-141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes1(A::AbstractArray) = (@inline; axes(A)[1])
-- /Source
-- Source: base/abstractarray.jl:395-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexLinear, A::AbstractArray) = (@inline; oneto(length(A)))
-- eachindex(::IndexLinear, A::AbstractVector) = (@inline; axes1(A))
-- /Source
/-- Rank-selected native eachindex at base/abstractarray.jl:395-396. BitVector
uses axes1 and the unchecked axis derived from its public singleton size; other
ranks use the generic checked oneto(length) constructor. This retains Julia's
actual dispatch even when a vector's stored length has wrapped negative. -/
def nativeScalarEachindex {N : Nat} (B : BitArray N) :
    JuliaLean.base.abstractarray.Result NativeAxis :=
  if N = 1 then
    JuliaLean.base.abstractarray.eachindexLinearVector
      (JuliaLean.base.abstractarray.axes1
        (JuliaLean.base.abstractarray.axesDefault
          (fun x : BitArray N => pure (bitArraySizeRanked x))
          JuliaLean.base.range.unchecked_oneto)) B
  else
    JuliaLean.base.abstractarray.eachindexLinear
      (fun x => pure (bitArrayLength x)) (fun n => pure (nativeOneTo n)) B

private theorem nativeScalarEachindexTotal {N : Nat} (B : BitArray N) :
    ∃ axis, nativeScalarEachindex B = .ok axis := by
  unfold nativeScalarEachindex
  split
  · refine ⟨JuliaLean.base.range.unchecked_oneto B.len, ?_⟩
    simp only [JuliaLean.base.abstractarray.eachindexLinearVector,
      JuliaLean.base.abstractarray.axes1, JuliaLean.base.abstractarray.axesDefault,
      bitArraySizeRanked, *]
    rfl
  · exact ⟨nativeOneTo (bitArrayLength B), rfl⟩

-- Source: base/abstractarray.jl:690-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, i)
--     @inline
--     return checkindex(Bool, eachindex(IndexLinear(), A), i)
-- end
-- /Source
/-- Concrete native linear bounds dispatch at base/bitarray.jl:689. -/
def nativeScalarBounds {N : Nat} (B : BitArray N) (i : I64) : BitMutationM Unit := do
  let result := JuliaLean.base.abstractarray.checkboundsOne nativeScalarEachindex
    (fun axis j => pure (JuliaLean.base.abstractarray.checkindexOneTo axis.stop j)) B i
  let b ← liftNativeBounds result (by
    rcases nativeScalarEachindexTotal B with ⟨axis, haxis⟩
    intro e h
    change (nativeScalarEachindex B >>= fun ax =>
      pure (JuliaLean.base.abstractarray.checkindexOneTo ax.stop i)) = .error e at h
    rw [haxis] at h
    cases h)
  if !b then throw .bounds

-- Source: base/bitarray.jl:688-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function setindex!(B::BitArray, x, i::Int)
--     @boundscheck checkbounds(B, i)
--     unsafe_bitsetindex!(B.chunks, convert(Bool, x), i)
--     return B
-- end
-- /Source
/-- Bool-specialized scalar setter needed by `one`, base/bitarray.jl:688-692.
Arbitrary `convert(Bool,x)` remains outside this closed specialization. The existing
unsafe setter is used for its write effect; its discarded return value is immaterial. -/
def setIndexBool {N : Nat} (B : BitArray N) (x : Bool) (i : I64) :
    BitMutationM (BitArray N) :=
  bitArraySetIndex nativeScalarBounds
    (fun x => pure (JuliaLean.base.number.convertSame x)) B x i

-- Source: base/abstractarray.jl:1463-1492 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
-- function setindex!(A::AbstractArray, v, I...)
--     @_propagate_inbounds_meta
--     error_if_canonical_setindex(IndexStyle(A), A, I...)
--     _setindex!(IndexStyle(A), A, v, to_indices(A, I)...)
-- end
-- function unsafe_setindex!(A::AbstractArray, v, I...)
--     @inline
--     @inbounds r = setindex!(A, v, I...)
--     r
-- end
-- 
-- error_if_canonical_setindex(::IndexLinear, A::AbstractArray, ::Int) =
--     throw(CanonicalIndexError("setindex!", typeof(A)))
-- error_if_canonical_setindex(::IndexCartesian, A::AbstractArray{T,N}, ::Vararg{Int,N}) where {T,N} =
--     throw(CanonicalIndexError("setindex!", typeof(A)))
-- error_if_canonical_setindex(::IndexStyle, ::AbstractArray, ::Any...) = nothing
-- 
-- ## Internal definitions
-- _setindex!(::IndexStyle, A::AbstractArray, v, I...) =
--     error("setindex! for $(typeof(A)) with types $(typeof(I)) is not supported")
-- 
-- ## IndexLinear Scalar indexing
-- _setindex!(::IndexLinear, A::AbstractArray, v, i::Int) = (@_propagate_inbounds_meta; setindex!(A, v, i))
-- function _setindex!(::IndexLinear, A::AbstractArray, v, I::Vararg{Int,M}) where M
--     @inline
--     @boundscheck checkbounds(A, I...)
--     @inbounds r = setindex!(A, v, _to_linear_index(A, I...))
--     r
-- end
-- /Source
/-- Native multidimensional Bool assignment from base/abstractarray.jl:1463-1468,
1487-1492, closing all interface parameters with installed dispatches. -/
def nativeMatrixSet (B : BitMatrix) (x : Bool) (is : List I64) : BitMutationM BitMatrix :=
  JuliaLean.base.abstractarray.setindexArray (fun _ => pure bitArrayIndexStyle)
    (fun style a inds => liftNativeBounds
      (JuliaLean.base.abstractarray.errorCanonicalSetindexOther style a inds)
      (by intro e h; cases h))
    (fun a inds => pure (JuliaLean.base.indices.to_indices_A_Ints a inds))
    (fun _ => JuliaLean.base.abstractarray.setindexLinear
      nativeMatrixCheck nativeMatrixLinear setIndexBool) B x is

-- Source: base/bitarray.jl:419-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function one(x::BitMatrix)
--     m, n = size(x)
--     m == n || throw(DimensionMismatch("multiplicative identity defined only for square matrices"))
--     a = falses(n, n)
--     for i = 1:n
--         a[i,i] = true
--     end
--     return a
-- end
-- /Source
/-- Multiplicative identity of a native BitMatrix, base/bitarray.jl:419-427.
The square check precedes allocation. The varargs falses forwarding method at
base/bitarray.jl:394 passes its native two-element tuple to falsesNative.
Input chunks are never read, including for
empty matrices and matrices whose storage was shortened through an alias. -/
def oneMatrix (runtime : AllocationData) (B : BitMatrix) : BitMutationM BitMatrix := do
  let ds := bitArraySize B
  let m ← liftNativeBounds (JuliaLean.base.abstractarray.tupleGet ds (int 1))
    (tupleGetBounds ds (int 1))
  let n ← liftNativeBounds (JuliaLean.base.abstractarray.tupleGet ds (int 2))
    (tupleGetBounds ds (int 2))
  if m != n then
    throw (.dimensionMismatch "multiplicative identity defined only for square matrices")
  let a ← falsesNative runtime ⟨[n, n], rfl⟩
  for i in intRange (int 1) n do
    let _ ← nativeMatrixSet a true [i, i]
  return a

end JuliaLean.base.bitarray.Models1Group15

namespace JuliaLean.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

-- Source: base/bitarray.jl:429-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto!(dest::BitArray, src::BitArray)
--     length(src) > length(dest) && throw(BoundsError(dest, length(dest)+1))
--     destc = dest.chunks; srcc = src.chunks
--     nc = min(length(destc), length(srcc))
--     nc == 0 && return dest
--     @inbounds begin
--         for i = 1 : nc - 1
--             destc[i] = srcc[i]
--         end
--         if length(src) == length(dest)
--             destc[nc] = srcc[nc]
--         else
--             msk_s = _msk_end(src)
--             msk_d = ~msk_s
--             destc[nc] = (msk_d & destc[nc]) | (msk_s & srcc[nc])
--         end
--     end
--     return dest
-- end
-- /Source
/-- All-rank copyto!, base/bitarray.jl:429-447. The installed method body only reads
chunks and len. Reindexing its unused phantom source rank closes its artificially
same-rank signature without duplicating or altering that faithful existing body. -/
def copyto {N M : Nat} (dest : BitArray N) (src : BitArray M) :
    BitMutationM (BitArray N) :=
  JuliaLean.base.bitarray.bitArrayCopyto dest
    (BitArray.mk src.chunks src.len src.dims)

-- Source: base/bitarray.jl:449-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function unsafe_copyto!(dest::BitArray, doffs::Integer, src::Union{BitArray,Array}, soffs::Integer, n::Integer)
--     copy_to_bitarray_chunks!(dest.chunks, Int(doffs), src, Int(soffs), Int(n))
--     return dest
-- end
-- /Source
/-- Native-Int offsets and packed-source specialization of unsafe_copyto!,
base/bitarray.jl:449-452. Generic Integer conversion and Array sources remain blocked. -/
def unsafeCopytoPacked {N M : Nat} (dest : BitArray N) (doffs : I64)
    (src : BitArray M) (soffs n : I64) : BitMutationM (BitArray N) := do
  let doffs := JuliaLean.base.number.convertSame doffs
  let soffs := JuliaLean.base.number.convertSame soffs
  let n := JuliaLean.base.number.convertSame n
  copyToBitArrayChunks dest.chunks doffs src soffs n
  return dest

-- Source: base/bitarray.jl:456-464 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _copyto_int!(dest::BitArray, doffs::Int, src::Union{BitArray,Array}, soffs::Int, n::Int)
--     n == 0 && return dest
--     n < 0 && throw(ArgumentError("Number of elements to copy must be non-negative."))
--     soffs < 1 && throw(BoundsError(src, soffs))
--     doffs < 1 && throw(BoundsError(dest, doffs))
--     n > length(src) - soffs + 1 && throw(BoundsError(src, length(src)+1))
--     n > length(dest) - doffs + 1 && throw(BoundsError(dest, length(dest)+1))
--     return unsafe_copyto!(dest, doffs, src, soffs, n)
-- end
-- /Source
/-- Packed-source specialization of checked native-offset copying, base/bitarray.jl:456-464.
Every check retains native signed wrapping and Julia's source error order. -/
def copytoPackedInt {N M : Nat} (dest : BitArray N) (doffs : I64)
    (src : BitArray M) (soffs n : I64) : BitMutationM (BitArray N) := do
  if n == int 0 then return dest
  if n < int 0 then throw (.argument "Number of elements to copy must be non-negative.")
  if soffs < int 1 then throw .bounds
  if doffs < int 1 then throw .bounds
  if n > bitArrayLength src - soffs + int 1 then throw .bounds
  if n > bitArrayLength dest - doffs + int 1 then throw .bounds
  unsafeCopytoPacked dest doffs src soffs n

-- Source: base/bitarray.jl:454-455 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- copyto!(dest::BitArray, doffs::Integer, src::Union{BitArray,Array}, soffs::Integer, n::Integer) =
--     _copyto_int!(dest, Int(doffs), src, Int(soffs), Int(n))
-- /Source
/-- Native-Int offsets and packed-source specialization, base/bitarray.jl:454-455.
All three source conversions occur before _copyto_int!'s zero-count short circuit. -/
def copytoPackedOffsets {N M : Nat} (dest : BitArray N) (doffs : I64)
    (src : BitArray M) (soffs n : I64) : BitMutationM (BitArray N) :=
  copytoPackedInt dest (JuliaLean.base.number.convertSame doffs) src
    (JuliaLean.base.number.convertSame soffs) (JuliaLean.base.number.convertSame n)

end JuliaLean.base.bitarray.Models1Group15

namespace JuliaLean.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

-- Source: base/bitarray.jl:24-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct BitArray{N} <: AbstractArray{Bool, N}
--     chunks::Vector{UInt64}
--     len::Int
--     dims::NTuple{N,Int}
-- /Source
/-- Typed identity of a mutable BitArray header (base/bitarray.jl:24-27).
Identity is distinct from the identity of its shared UInt64 chunks vector. -/
structure Ref (rank : Nat) where
  identity : Nat
  deriving Repr, DecidableEq, BEq

-- Source: base/bitarray.jl:24-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct BitArray{N} <: AbstractArray{Bool, N}
--     chunks::Vector{UInt64}
--     len::Int
--     dims::NTuple{N,Int}
-- /Source
/-- Concrete object headers layered over the existing shared chunk-memory store.
The dependent pair retains each header's rank (base/bitarray.jl:24-27).
Heap names are semantic identities, not modeled native pointer values. -/
structure ObjectState where
  memory : MutableMemory U64
  objects : List (Sigma BitArray)

-- Source: base/bitarray.jl:24-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct BitArray{N} <: AbstractArray{Bool, N}
--     chunks::Vector{UInt64}
--     len::Int
--     dims::NTuple{N,Int}
-- /Source
/-- Header and chunk writes survive later exceptions, as in the field assignments
at base/bitarray.jl:752,768,789 and the subsequent copy/write operations. -/
abbrev ObjectM := ExceptT JuliaLean.base.array.Error (StateM ObjectState)

-- Source: base/bitarray.jl:36-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         chunks = Vector{UInt64}(undef, nc)
--         nc > 0 && (chunks[end] = UInt64(0))
--         b = new(chunks, n)
--         N != 1 && (b.dims = dims)
--         return b
-- /Source
/-- Lift a concrete chunk-memory action, preserving its state even when it throws.
This is the local composition of the existing mutation boundary, used by
base/bitarray.jl:36-37,747-748,765-766,786-787. It supplies no missing callee. -/
def liftBit (action : BitMutationM α) : ObjectM α := do
  let before ← get
  let (result, memory) := action.run before.memory
  set { before with memory := memory }
  match result with
  | .ok value => pure value
  | .error error => throw error

-- Source: base/bitarray.jl:24-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct BitArray{N} <: AbstractArray{Bool, N}
--     chunks::Vector{UInt64}
--     len::Int
--     dims::NTuple{N,Int}
-- /Source
/-- Read the fields of a typed mutable header (base/bitarray.jl:24-27).
Missing identities and rank confusion are non-native model states; the bounds
and type errors instrument that representation boundary. Native contracts
quantify valid references and do not present these as extra Julia exceptions. -/
def readObject {N : Nat} (reference : Ref N) : ObjectM (BitArray N) := do
  let state ← get
  match state.objects[reference.identity]? with
  | none => throw .bounds
  | some ⟨rank, header⟩ =>
    if h : rank = N then
      pure (h ▸ header)
    else
      throw (.typeError "BitArray reference rank")

-- Source: base/bitarray.jl:481-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     Br.chunks = B.chunks
--     Br.len = len
--     N != 1 && (Br.dims = dims)
-- /Source
/-- Replace the fields in one existing object slot, preserving its identity and
all other headers (base/bitarray.jl:481-483,752,768,789). -/
def writeObject {N : Nat} (reference : Ref N) (header : BitArray N) : ObjectM Unit := do
  let _ ← readObject reference
  modify fun state =>
    { state with objects := state.objects.set reference.identity ⟨N, header⟩ }

-- Source: base/bitarray.jl:481-481 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     Br.chunks = B.chunks
-- /Source
/-- Concrete header-field assignment used at base/bitarray.jl:481. -/
def setObjectChunks {N : Nat} (reference : Ref N) (chunks : Nat) : ObjectM Unit := do
  let header ← readObject reference
  writeObject reference { header with chunks := chunks }

-- Source: base/bitarray.jl:482-482 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     Br.len = len
-- /Source
/-- Concrete length-field assignment at base/bitarray.jl:482,752,768,789. -/
def setObjectLength {N : Nat} (reference : Ref N) (length : I64) : ObjectM Unit := do
  let header ← readObject reference
  writeObject reference { header with len := length }

-- Source: base/bitarray.jl:483-483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     N != 1 && (Br.dims = dims)
-- /Source
/-- Concrete dims assignment used after the caller's rank branch at
base/bitarray.jl:483. Its argument is a native rank-indexed tuple. -/
def setObjectDims {N : Nat} (reference : Ref N) (dimensions : Dims N) : ObjectM Unit := do
  let header ← readObject reference
  writeObject reference { header with dims := dimensions.val }

-- Source: base/bitarray.jl:38-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         b = new(chunks, n)
--         N != 1 && (b.dims = dims)
--         return b
-- /Source
/-- Register the concrete constructor's completed header under a fresh identity,
base/bitarray.jl:38-40. This allocates only the header; it never copies its chunks.
Resource exhaustion of object allocation is outside the supplied runtime boundary. -/
def registerObject {N : Nat} (header : BitArray N) : ObjectM (Ref N) := do
  let state ← get
  let identity := state.objects.length
  set { state with objects := state.objects ++ [(⟨N, header⟩ : Sigma BitArray)] }
  return ⟨identity⟩

-- Source: base/bitarray.jl:28-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function BitArray{N}(::UndefInitializer, dims::Vararg{Int,N}) where N
--         i = 1
--         for d in dims
--             d >= 0 || throw(ArgumentError("dimension size must be ≥ 0, got $d for dimension $i"))
--             i += 1
--         end
--         n = Core.checked_dims(dims...)
--         nc = num_bit_chunks(n)
--         chunks = Vector{UInt64}(undef, nc)
--         nc > 0 && (chunks[end] = UInt64(0))
--         b = new(chunks, n)
--         N != 1 && (b.dims = dims)
--         return b
--     end
-- /Source
/-- Invoke the completed native constructor at base/bitarray.jl:28-41 and give
its new mutable header an identity. The constructor's new/dims assignments have
no intervening error-producing operations after chunk allocation and zeroing. -/
def undefObject {N : Nat} (runtime : AllocationData) (dimensions : Dims N) :
    ObjectM (Ref N) := do
  let header ← liftBit (Models1Group15.undef runtime dimensions)
  registerObject header

-- Source: base/array.jl:1114-1114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- array_new_memory(mem::Memory, newlen::Int) = typeof(mem)(undef, newlen) # when implemented, this should attempt to first expand mem
-- /Source
-- Source: base/boot.jl:762-762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (self::Type{GenericMemory{kind,T,addrspace}})(::UndefInitializer, m::Int) where {T,addrspace,kind} = memorynew(self, m)
-- /Source
/-- Native UInt64 storage for the `_growend!` calls at base/bitarray.jl:747,765,786.
All installed array operations and metadata are retained. Only the raw allocator
at base/array.jl:1114 / base/boot.jl:762 uses the declared arbitrary isbits words,
so newly allocated chunks cannot spuriously raise UndefRefError. -/
def rawChunkStorage (runtime : AllocationData) :
    Storage BitMutationM Nat Nat (Nat × I64) :=
  { mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout) with
    allocate := fun _ n =>
      JuliaLean.base.array.memoryUndef
        (MemoryLayoutMetadata.ofRuntime uint64Layout).allocation
        (pure runtime.emptyMemory) (allocateRawWords runtime) n }

-- Source: base/array.jl:1171-1223 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _growend_internal!(a::Vector, delta::Int, len::Int)
--     @_terminates_locally_meta
--     ref = a.ref
--     mem = ref.mem
--     memlen = length(mem)
--     newlen = checked_add(len, delta)
--     offset = memoryrefoffset(ref)
--     if offset < 1 || offset - 1 > memlen || len > memlen - (offset - 1)
--         throw(ConcurrencyViolationError("Vector has invalid state. Don't modify internal fields incorrectly, or resize without correct locks"))
--     end
--     newmemlen = checked_add(offset - 1, newlen)
-- 
--     if offset - 1 > newlen && offset - 1 - newlen > div(newlen, 4)
--         # If the offset is far enough that we can copy without resizing
--         # while maintaining proportional spacing on both ends of the array
--         # note that this branch prevents infinite growth when doing combinations
--         # of push! and popfirst! (i.e. when using a Vector as a queue)
--         newmem = mem
--         newoffset = div(newlen, 8) + 1
--     else
--         # grow either by our computed overallocation factor
--         # or exactly the requested size, whichever is larger
--         # TODO we should possibly increase the offset if the current offset is nonzero.
--         newmemlen2 = max(overallocation(memlen), newmemlen)
--         newmem = array_new_memory(mem, newmemlen2)
--         newoffset = offset
--     end
--     newref = @inbounds memoryref(newmem, newoffset)
--     unsafe_copyto!(newref, ref, len)
--     if newmem === mem
--         for j in max(offset, newoffset + len):offset+len-1
--             @inbounds unsetindex!(mem, j)
--         end
--     end
--     if ref !== a.ref
--         @noinline throw(ConcurrencyViolationError("Vector can not be resized concurrently"))
--     end
--     setfield!(a, :ref, newref)
-- return
-- end
-- 
-- function _growend!(a::Vector, delta::Integer)
--     @_noub_meta
--     delta = Int(delta)
--     delta >= 0 || throw(ArgumentError("grow requires delta >= 0"))
--     ref = a.ref
--     len = length(a)
--     if length(ref.mem) - (memoryrefoffset(ref) - 1) - len < delta
--         @noinline _growend_internal!(a, delta, len)
--     end
--     setfield!(a, :size, (len + delta,))
--     return
-- end
-- /Source
/-- Closed native-Int invocation of installed `_growend!` and its internal helper,
base/array.jl:1171-1223, needed at base/bitarray.jl:747,765,786. The existing
checks, arithmetic, mutation order, reallocation and error classes are reused. -/
def growRawChunks (runtime : AllocationData) (chunks : Nat) (delta : I64) :
    BitMutationM Unit :=
  let storage := rawChunkStorage runtime
  JuliaLean.base.array.growend storage (fun d => pure d)
    (JuliaLean.base.array.growendInternal storage) chunks delta

end JuliaLean.base.bitarray.Models1Group15

namespace JuliaLean.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

-- Source: base/bitarray.jl:476-485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _bitreshape(B::BitArray, dims::NTuple{N,Int}) where N
--     len = Core.checked_dims(dims...)
--     len == length(B) ||
--         throw(DimensionMismatch("new dimensions $(dims) must be consistent with array length $(length(B))"))
--     Br = BitArray{N}(undef, ntuple(i->0,Val(N))...)
--     Br.chunks = B.chunks
--     Br.len = len
--     N != 1 && (Br.dims = dims)
--     return Br
-- end
-- /Source
/-- Internal reshape with concrete mutable header identity, base/bitarray.jl:476-485.
The temporary zero-shaped allocation is retained, even though its chunks field is
subsequently replaced. Rank-one dims remain unset. A fresh header shares the exact
source chunks vector, so later resizes are observable through that shared handle. -/
def bitreshape {N R : Nat} (runtime : AllocationData) (source : Ref N)
    (dims : Dims R) : ObjectM (Ref R) := do
  let len ← liftBit (JuliaLean.base.array.checkedDims dims.val)
  let B ← readObject source
  if len != bitArrayLength B then
    throw (.dimensionMismatch "new dimensions must be consistent with array length")
  let zeros : Dims R := ⟨List.replicate R (int 0), by simp⟩
  let reshaped ← undefObject runtime zeros
  setObjectChunks reshaped B.chunks
  setObjectLength reshaped len
  if R != 1 then setObjectDims reshaped dims
  return reshaped

-- Source: base/bitarray.jl:472-474 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function reshape(B::BitArray{N}, dims::NTuple{N,Int}) where N
--     return dims == size(B) ? B : _bitreshape(B, dims)
-- end
-- /Source
/-- Same-rank reshape, base/bitarray.jl:472-474. Equal dimensions return the identical
mutable object reference with no allocations or writes; changed shape creates a new
header through the source-faithful internal reshape above. -/
def reshapeSame {N : Nat} (runtime : AllocationData) (source : Ref N)
    (dims : Dims N) : ObjectM (Ref N) := do
  let B ← readObject source
  if dims.val == bitArraySizeRanked B then
    return source
  else
    bitreshape runtime source dims

-- Source: base/bitarray.jl:475-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- reshape(B::BitArray, dims::Tuple{Vararg{Int}}) = _bitreshape(B, dims)
-- /Source
/-- Different-rank dispatch of reshape, base/bitarray.jl:475. Same-rank callers
select reshapeSame; the inequality records Julia's dispatch partition, not an
assumption about successful execution. -/
def reshapeOther {N R : Nat} (runtime : AllocationData) (source : Ref N)
    (dims : Dims R) (_differentRank : N ≠ R) : ObjectM (Ref R) :=
  bitreshape runtime source dims

end JuliaLean.base.bitarray.Models1Group15

namespace JuliaLean.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

-- Source: base/bitarray.jl:359-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(B::BitArray) = BitArray(undef, size(B))
-- /Source
/-- The completed similar method lifted to mutable header identities, needed by
copy at base/bitarray.jl:535-536. A nonmatching rank is an invalid Lean object
representation, never an additional native Julia case. -/
def similarObject {N : Nat} (runtime : AllocationData) (source : Ref N) :
    ObjectM (Ref N) := do
  let B ← readObject source
  if rank : (bitArraySizeRanked B).length = N then
    let fresh ← liftBit (Models1Group15.similar runtime B rank)
    registerObject fresh
  else
    throw (.typeError "BitArray size tuple rank")

-- Source: base/bitarray.jl:429-447 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copyto!(dest::BitArray, src::BitArray)
--     length(src) > length(dest) && throw(BoundsError(dest, length(dest)+1))
--     destc = dest.chunks; srcc = src.chunks
--     nc = min(length(destc), length(srcc))
--     nc == 0 && return dest
--     @inbounds begin
--         for i = 1 : nc - 1
--             destc[i] = srcc[i]
--         end
--         if length(src) == length(dest)
--             destc[nc] = srcc[nc]
--         else
--             msk_s = _msk_end(src)
--             msk_d = ~msk_s
--             destc[nc] = (msk_d & destc[nc]) | (msk_s & srcc[nc])
--         end
--     end
--     return dest
-- end
-- /Source
/-- Existing concrete copyto! lifted to typed object references, base/bitarray.jl:429-447.
The returned reference is the original destination; no header is replaced. -/
def copytoObject {N M : Nat} (destination : Ref N) (source : Ref M) :
    ObjectM (Ref N) := do
  let dest ← readObject destination
  let src ← readObject source
  let _ ← liftBit (Models1Group15.copyto dest src)
  return destination

-- Source: base/abstractarray.jl:1154-1157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copy(a::AbstractArray)
--     @_propagate_inbounds_meta
--     copymutable(a)
-- end
-- /Source
-- Source: base/abstractarray.jl:1211-1214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copymutable(a::AbstractArray)
--     @_propagate_inbounds_meta
--     copyto!(similar(a), a)
-- end
-- /Source
/-- The actual abstract-array copy/copyMutable callees for base/bitarray.jl:535-536.
Every interface argument is a closed installed or completed method, not a runtime
implementation callback. Fresh object identity and fresh chunk-vector identity
are both retained, including for empty arrays. -/
def copyObject {N : Nat} (runtime : AllocationData) (source : Ref N) : ObjectM (Ref N) :=
  JuliaLean.base.abstractarray.copyArray
    (JuliaLean.base.abstractarray.copyMutableArray
      (similarObject runtime) copytoObject) source

-- Source: base/bitarray.jl:535-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (::Type{T})(x::T) where {T<:BitArray} = copy(x)::T
-- /Source
/-- Same-type BitArray constructor, base/bitarray.jl:535. Static Ref N preserves
Julia's asserted concrete target rank; the source copy allocates fresh identity. -/
def typedCopy {N : Nat} (runtime : AllocationData) (source : Ref N) : ObjectM (Ref N) :=
  copyObject runtime source

-- Source: base/bitarray.jl:536-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- BitArray(x::BitArray) = copy(x)
-- /Source
/-- BitArray(BitArray) copy constructor, base/bitarray.jl:536. -/
def copySame {N : Nat} (runtime : AllocationData) (source : Ref N) : ObjectM (Ref N) :=
  copyObject runtime source

end JuliaLean.base.bitarray.Models1Group15

namespace JuliaLean.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

-- Source: base/bitarray.jl:668-671 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function getindex(B::BitArray, i::Int)
--     @boundscheck checkbounds(B, i)
--     unsafe_bitgetindex(B.chunks, i)
-- end
-- /Source
/-- Scalar getindex with closed native bounds dispatch, base/bitarray.jl:668-671.
The public logical check occurs before the actual packed read. -/
def getIndex {N : Nat} (B : BitArray N) (i : I64) : BitMutationM Bool :=
  bitArrayGetIndex nativeScalarBounds B i

-- Source: base/bitarray.jl:680-686 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function _unsafe_bitsetindex!(Bc::Array{UInt64}, x::Bool, i1::Int, i2::Int)
--     u = UInt64(1) << i2
--     @inbounds begin
--         c = Bc[i1]
--         Bc[i1] = ifelse(x, c | u, c & ~u)
--     end
-- end
-- /Source
/-- The source helper returns the assigned UInt64, base/bitarray.jl:680-686.
Both pure branches of ifelse are evaluated as native UInt64 operations. -/
def unsafeSetIndexAt (bc : Nat) (x : Bool) (i1 i2 : I64) : BitMutationM U64 := do
  let u := shl_Int (u64 1) i2
  let c ← mutableGet bc i1
  let word := JuliaLean.base.int.ifelse x (or_int c u) (and_int c (not_int u))
  mutableSet bc word i1
  return word

-- Source: base/bitarray.jl:675-678 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function unsafe_bitsetindex!(Bc::Array{UInt64}, x::Bool, i::Int)
--     i1, i2 = get_chunks_id(i)
--     _unsafe_bitsetindex!(Bc, x, i1, i2)
-- end
-- /Source
/-- Forward both the write effect and the UInt64 result, base/bitarray.jl:675-678. -/
def unsafeSetIndex (bc : Nat) (x : Bool) (i : I64) : BitMutationM U64 := do
  let (i1, i2) := getChunksId i
  unsafeSetIndexAt bc x i1 i2

end JuliaLean.base.bitarray.Models1Group15

namespace JuliaLean.base.bitarray.Models1Group15

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

-- Source: base/bitarray.jl:739-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function push!(B::BitVector, item)
--     # convert first so we don't grow the bitarray if the assignment won't work
--     item = convert(Bool, item)
-- 
--     Bc = B.chunks
-- 
--     l = _mod64(length(B))
--     if l == 0
--         _growend!(Bc, 1)
--         Bc[end] = UInt64(0)
--     end
--     B.len += 1
--     if item
--         B[end] = true
--     end
--     return B
-- end
-- /Source
/-- Bool-valued push! specialization with actual mutable header identity,
base/bitarray.jl:739-755. Arbitrary convert(Bool,item) remains blocked. Chunk growth
uses raw isbits allocation; the wrapped len update is committed before scalar assignment. -/
def pushBool (runtime : AllocationData) (target : Ref 1) (item : Bool) :
    ObjectM (Ref 1) := do
  let item := JuliaLean.base.number.convertSame item
  let B ← readObject target
  let bc := B.chunks
  let l := mod64 (bitArrayLength B)
  if l == int 0 then
    liftBit (growRawChunks runtime bc (int 1))
    liftBit (do
      let last ← mutableLength bc
      mutableSet bc (u64 0) last)
  let current ← readObject target
  setObjectLength target (current.len + int 1)
  if item then
    let current ← readObject target
    let _ ← liftBit (setIndexBool current true (bitArrayLength current))
  return target

-- Source: base/bitarray.jl:739-755 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
/-- Conversion may mutate captured BitArray objects; the concrete Bool path
reads the target header only after that open dispatch returns. -/
def pushConvert {X : Type} (runtime : AllocationData)
    (convertBool : X → ObjectM Bool) (target : Ref 1) (item : X) : ObjectM (Ref 1) := do
  let item ← convertBool item
  pushBool runtime target item

-- Source: base/bitarray.jl:757-772 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function append!(B::BitVector, items::BitVector)
--     n0 = length(B)
--     n1 = length(items)
--     n1 == 0 && return B
--     n = checked_add(n0, n1)
--     Bc = B.chunks
--     k0 = length(Bc)
--     k1 = num_bit_chunks(n)
--     if k1 > k0
--         _growend!(Bc, k1 - k0)
--         Bc[end] = UInt64(0)
--     end
--     B.len = n
--     copy_chunks!(Bc, n0+1, items.chunks, 1, n1)
--     return B
-- end
-- /Source
/-- Append packed vectors, base/bitarray.jl:757-772. Both old lengths are read
before growth or mutation. The actual target object's len changes before copying,
including when the source is that same object; later failures retain the update. -/
def append (runtime : AllocationData) (target items : Ref 1) : ObjectM (Ref 1) := do
  let B ← readObject target
  let n0 := bitArrayLength B
  let itemsBefore ← readObject items
  let n1 := bitArrayLength itemsBefore
  if n1 == int 0 then return target
  let n ← liftBit ((rawChunkStorage runtime).checkedAdd n0 n1)
  let current ← readObject target
  let bc := current.chunks
  let k0 ← liftBit (mutableLength bc)
  let k1 := numBitChunks n
  if k1 > k0 then
    liftBit (growRawChunks runtime bc (k1 - k0))
    liftBit (do
      let last ← mutableLength bc
      mutableSet bc (u64 0) last)
  setObjectLength target n
  let itemsNow ← readObject items
  liftBit (copyChunks bc (n0 + int 1) itemsNow.chunks (int 1) n1)
  return target

-- Source: base/bitarray.jl:774-774 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def appendIterableConvert {I : Type} (runtime : AllocationData)
    (toBitVector : I → ObjectM (Ref 1)) (target : Ref 1) (items : I) : ObjectM (Ref 1) := do
  let converted ← toBitVector items
  append runtime target converted

-- Source: base/bitarray.jl:777-793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function prepend!(B::BitVector, items::BitVector)
--     n0 = length(B)
--     n1 = length(items)
--     n1 == 0 && return B
--     n = checked_add(n0, n1)
--     Bc = B.chunks
--     k0 = length(Bc)
--     k1 = num_bit_chunks(n)
--     if k1 > k0
--         _growend!(Bc, k1 - k0)
--         Bc[end] = UInt64(0)
--     end
--     B.len = n
--     copy_chunks!(Bc, 1 + n1, Bc, 1, n0)
--     copy_chunks!(Bc, 1, items.chunks, 1, n1)
--     return B
-- end
-- /Source
/-- Prepend packed vectors, base/bitarray.jl:777-793. The two copies run against
live shared storage in Julia order; there is no invented global source snapshot.
Header aliases observe the committed length even if either copy fails. -/
def prepend (runtime : AllocationData) (target items : Ref 1) : ObjectM (Ref 1) := do
  let B ← readObject target
  let n0 := bitArrayLength B
  let itemsBefore ← readObject items
  let n1 := bitArrayLength itemsBefore
  if n1 == int 0 then return target
  let n ← liftBit ((rawChunkStorage runtime).checkedAdd n0 n1)
  let current ← readObject target
  let bc := current.chunks
  let k0 ← liftBit (mutableLength bc)
  let k1 := numBitChunks n
  if k1 > k0 then
    liftBit (growRawChunks runtime bc (k1 - k0))
    liftBit (do
      let last ← mutableLength bc
      mutableSet bc (u64 0) last)
  setObjectLength target n
  liftBit (copyChunks bc (int 1 + n1) bc (int 1) n0)
  let itemsNow ← readObject items
  liftBit (copyChunks bc (int 1) itemsNow.chunks (int 1) n1)
  return target

-- Source: base/bitarray.jl:795 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def prependIterableConvert {I : Type} (runtime : AllocationData)
    (toBitVector : I → ObjectM (Ref 1)) (target : Ref 1) (items : I) : ObjectM (Ref 1) := do
  bitVectorPrependIterableDispatch toBitVector (prepend runtime) target items

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

structure WordAssignment (Raw Converted : Type) where
  asWord : Raw → Option U64
  convert : Raw → ObjectM Converted
  convertedWord : Converted → Option U64

-- Source: base/array.jl:1031-1041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- placed here to break an import cycle with array
def assignMappedWord {Raw Converted : Type} (conversion : WordAssignment Raw Converted)
    (chunks : Nat) (index : I64) (raw : Raw) : ObjectM Unit := do
  let value ← match conversion.asWord raw with
    | some word => pure word
    | none => do
      let converted ← conversion.convert raw
      match conversion.convertedWord converted with
      | some word => pure word
      | none => throw (.typeError "setindex!")
  let _ ← JuliaLean.base.array.setindexTyped
    (fun target i => liftBit (mutableBounds target i))
    (fun target i _ => liftBit (mutableMemoryref target i))
    (fun reference value _ => liftBit (memoryWrite reference.1 reference.2 (some value)))
    chunks value index
  pure ()

-- Source: base/bitarray.jl:1795-1813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitMapUnaryGeneric {D N : Nat} {Raw Converted Masked Tail TailConverted : Type}
    (f : U64 → ObjectM Raw) (andMask : Raw → U64 → ObjectM Masked)
    (orMask : U64 → Masked → ObjectM Tail)
    (assignment : WordAssignment Raw Converted) (tailAssignment : WordAssignment Tail TailConverted)
    (destination : Ref D) (source : Ref N) : ObjectM (Ref D) := do
  let A ← readObject source
  let dest ← readObject destination
  if A.len > dest.len then
    throw (.dimensionMismatch "length of destination must be >= length of collection")
  if A.len == int 0 then return destination
  let destc := dest.chunks
  let Ac := A.chunks
  let lenAc ← liftBit (mutableLength Ac)
  for i in intRange (int 1) (lenAc - int 1) do
    let value ← f (← liftBit (mutableGet Ac i))
    assignMappedWord assignment destc i value
  let destLast ← liftBit (mutableGet destc lenAc)
  let liveA ← readObject source
  let mask := maskEnd liveA.len
  let kept := and_int destLast (not_int mask)
  let value ← f (← liftBit (mutableGet Ac lenAc))
  let masked ← andMask value mask
  let joined ← orMask kept masked
  assignMappedWord tailAssignment destc lenAc joined
  pure destination

-- Source: base/bitarray.jl:1814-1835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitMapBinaryGeneric {D N K : Nat} {Raw Converted Masked Tail TailConverted : Type}
    (f : U64 → U64 → ObjectM Raw) (andMask : Raw → U64 → ObjectM Masked)
    (orMask : U64 → Masked → ObjectM Tail)
    (assignment : WordAssignment Raw Converted) (tailAssignment : WordAssignment Tail TailConverted)
    (destination : Ref D) (left : Ref N) (right : Ref K) : ObjectM (Ref D) := do
  let A ← readObject left
  let B ← readObject right
  let minBitlen := if A.len < B.len then A.len else B.len
  let dest ← readObject destination
  if minBitlen > dest.len then
    throw (.dimensionMismatch "length of destination must be >= length of smallest input collection")
  if A.len == int 0 then return destination
  if B.len == int 0 then return destination
  let destc := dest.chunks
  let Ac := A.chunks
  let Bc := B.chunks
  let lenA ← liftBit (mutableLength Ac)
  let lenB ← liftBit (mutableLength Bc)
  let lenAc := if lenA < lenB then lenA else lenB
  for i in intRange (int 1) (lenAc - int 1) do
    let a ← liftBit (mutableGet Ac i)
    let b ← liftBit (mutableGet Bc i)
    let value ← f a b
    assignMappedWord assignment destc i value
  let destLast ← liftBit (mutableGet destc lenAc)
  let mask := maskEnd minBitlen
  let kept := and_int destLast (not_int mask)
  let a ← liftBit (mutableGet Ac lenAc)
  let b ← liftBit (mutableGet Bc lenAc)
  let value ← f a b
  let masked ← andMask value mask
  let joined ← orMask kept masked
  assignMappedWord tailAssignment destc lenAc joined
  pure destination


/-- Run a pure-header compatibility specialization against the shared chunk store. -/
def withObjectHeaders (headers : List (Sigma BitArray)) (action : ObjectM A) : BitMutationM A :=
  fun memory =>
    let (result, final) := action.run ⟨memory, headers⟩
    (result, final.memory)

private def wordAssignment : WordAssignment U64 U64 :=
  ⟨some, pure, some⟩

end JuliaLean.base.bitarray.Models1Group15


namespace JuliaLean.base.bitarray
open JuliaLean JuliaLean.base.array JuliaLean.base.int Models1Group15

/--
Julia source: base/bitarray.jl:1795-1813 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bit_map!(f::F, dest::BitArray, A::BitArray) where F
    length(A) <= length(dest) || throw(DimensionMismatch("length of destination must be >= length of collection"))
    isempty(A) && return dest
    destc = dest.chunks
    Ac = A.chunks
    len_Ac = length(Ac)
    for i = 1:(len_Ac-1)
        destc[i] = f(Ac[i])
    end
    # the last affected UInt64's original content
    dest_last = destc[len_Ac]
    _msk = _msk_end(A)
    # first zero out the bits mask is going to change
    # then update bits by `or`ing with a masked RHS
    # DO NOT SEPARATE ONTO TWO LINES.
    # Otherwise there will be bugs when Ac aliases destc
    destc[len_Ac] = (dest_last & (~_msk)) | f(Ac[len_Ac]) & _msk
    dest
end
```
-/
def bitArrayMapBangUnary {N : Nat} (f : U64 → U64) (dest A : BitArray N)
    : BitMutationM (BitArray N) :=
  withObjectHeaders [⟨N, dest⟩, ⟨N, A⟩] do
    let _ ← bitMapUnaryGeneric (fun value => pure (f value))
      (fun value mask => pure (and_int value mask))
      (fun kept value => pure (or_int kept value)) wordAssignment wordAssignment
      (⟨0⟩ : Ref N) (⟨1⟩ : Ref N)
    pure dest

/--
Julia source: base/bitarray.jl:1814-1835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function bit_map!(f::F, dest::BitArray, A::BitArray, B::BitArray) where F
    min_bitlen = min(length(A), length(B))
    min_bitlen <= length(dest) || throw(DimensionMismatch("length of destination must be >= length of smallest input collection"))
    isempty(A) && return dest
    isempty(B) && return dest
    destc = dest.chunks
    Ac = A.chunks
    Bc = B.chunks
    len_Ac = min(length(Ac), length(Bc))
    for i = 1:len_Ac-1
        destc[i] = f(Ac[i], Bc[i])
    end
    # the last affected UInt64's original content
    dest_last = destc[len_Ac]
    _msk = _msk_end(min_bitlen)
    # first zero out the bits mask is going to change
    # then update bits by `or`ing with a masked RHS
    # DO NOT SEPARATE ONTO TWO LINES.
    # Otherwise there will be bugs when Ac or Bc aliases destc
    destc[len_Ac] = (dest_last & ~(_msk)) | f(Ac[len_Ac], Bc[len_Ac]) & _msk
    dest
end
```
-/
def bitArrayMapBangBinary {N M : Nat} (f : U64 → U64 → U64)
    (dest : BitArray 1) (A : BitArray N) (B : BitArray M) : BitMutationM (BitArray 1) :=
  withObjectHeaders [⟨1, dest⟩, ⟨N, A⟩, ⟨M, B⟩] do
    let _ ← bitMapBinaryGeneric (fun left right => pure (f left right))
      (fun value mask => pure (and_int value mask))
      (fun kept value => pure (or_int kept value)) wordAssignment wordAssignment
      (⟨0⟩ : Ref 1) (⟨1⟩ : Ref N) (⟨2⟩ : Ref M)
    pure dest

end JuliaLean.base.bitarray

namespace JuliaLean.base.bitarray.Models1Group16

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

/-!
Group 16 additions preserve the bundled model above byte-for-byte.
These definitions use the existing UInt64 mutable-memory boundary. New undefined
isbits slots still have the bundled `none` representation; see NOTES.md.
-/

/-- The installed UInt64 storage interpretation, used by base/bitarray.jl:798. -/
-- Source: base/bitarray.jl:24-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- mutable struct BitArray{N} <: AbstractArray{Bool, N}
--     chunks::Vector{UInt64}
--     len::Int
--     dims::NTuple{N,Int}
-- /Source

def chunkStorage :=
  mutableStorage (α := U64) (MemoryLayoutMetadata.ofRuntime uint64Layout)

/-- Concrete grow-at-front dependency of array.sizehint (base/array.jl:1612).
The BitVector sizehint call uses first=false, but no fake branch is supplied. -/
-- Source: base/array.jl:1151-1169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _growbeg!(a::Vector, delta::Integer)
--     @_noub_meta
--     delta = Int(delta)
--     delta == 0 && return # avoid attempting to index off the end
--     delta >= 0 || throw(ArgumentError("grow requires delta >= 0"))
--     ref = a.ref
--     len = length(a)
--     offset = memoryrefoffset(ref)
--     newlen = checked_add(len, delta)
--     # if offset is far enough advanced to fit data in existing memory without copying
--     if delta <= offset - 1
--         setfield!(a, :ref, @inbounds memoryref(ref, 1 - delta))
--         setfield!(a, :size, (newlen,))
--     else
--         @noinline _growbeg_internal!(a, delta, len)
--         setfield!(a, :size, (newlen,))
--     end
--     return
-- end
-- /Source

def growChunksAtFront (a : Nat) (n : I64) : BitMutationM Unit :=
  JuliaLean.base.array.growbeg chunkStorage pure
    (JuliaLean.base.array.growbegInternal chunkStorage) a n

/-- Concrete sizehint dependency at base/bitarray.jl:799. -/
-- Source: base/array.jl:1612-1643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sizehint!(a::Vector, sz::Integer; first::Bool=false, shrink::Bool=true)
--     len = length(a)
--     ref = a.ref
--     mem = ref.mem
--     memlen = length(mem)
--     sz = max(Int(sz), len)
--     inc = sz - len
--     if sz <= memlen
--         # if we don't save at least 1/8th memlen then its not worth it to shrink
--         if !shrink || memlen - sz <= div(memlen, 8)
--             return a
--         end
--         newmem = array_new_memory(mem, sz)
--         if first && len != 0
--             newref = memoryref(newmem, inc + 1)
--         else
--             newref = memoryref(newmem)
--         end
--         unsafe_copyto!(newref, ref, len)
--         setfield!(a, :ref, newref)
--     elseif first
--         _growbeg!(a, inc)
--         newref = getfield(a, :ref)
--         newref = memoryref(newref, inc + 1)
--         setfield!(a, :size, (len,)) # undo the size change from _growbeg!
--         setfield!(a, :ref, newref) # undo the offset change from _growbeg!
--     else # last
--         _growend!(a, inc)
--         setfield!(a, :size, (len,)) # undo the size change from _growend!
--     end
--     a
-- end
-- /Source

def reserveChunks (a : Nat) (n : I64) : BitMutationM Unit := do
  let _ ← JuliaLean.base.array.sizehint chunkStorage pure growChunksAtFront growChunkVector a n
  pure ()

/-- Native bounds dependency of base/bitarray.jl:827, using the installed OneTo check. -/
-- Source: base/abstractarray.jl:690-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, i)
--     @inline
--     return checkindex(Bool, eachindex(IndexLinear(), A), i)
-- end
-- 
-- /Source

-- Source: base/abstractarray.jl:700-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkbounds(A::AbstractArray, I...)
-- 
-- """
--     checkbounds_indices(Bool, IA, I)
-- 
-- Return `true` if the "requested" indices in the tuple `I` fall within
-- the bounds of the "permitted" indices specified by the tuple
-- /Source

-- Source: base/abstractarray.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkindex(::Type{Bool}, inds::OneTo{T}, i::T) where {T<:BitInteger} = unsigned(i -% one(i)) < unsigned(last(inds))
-- /Source

def checkBounds {N : Nat} (B : BitArray N) (i : I64) : BitMutationM Unit := do
  if !JuliaLean.base.abstractarray.checkindexOneTo B.len i then throw .bounds

/-- Checked conversion, with the existing array-error class. No range failure is
replaced by a wrapping conversion. Used by base/bitarray.jl:803,884,1478,1563. -/
-- Source: base/number.jl:6-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, x::T)      where {T<:Number} = x
-- convert(::Type{T}, x::Number) where {T<:Number} = T(x)::T
-- /Source

-- Source: base/boot.jl:1104-1113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toInt64(x::Int8)      = sext_int(Int64, x)
-- toInt64(x::Int16)     = sext_int(Int64, x)
-- toInt64(x::Int32)     = sext_int(Int64, x)
-- toInt64(x::Int64)     = x
-- toInt64(x::Int128)    = checked_trunc_sint(Int64, x)
-- toInt64(x::UInt8)     = zext_int(Int64, x)
-- toInt64(x::UInt16)    = zext_int(Int64, x)
-- toInt64(x::UInt32)    = zext_int(Int64, x)
-- toInt64(x::UInt64)    = bitcast(Int64, check_sign_bit(Int64, x))
-- toInt64(x::UInt128)   = checked_trunc_sint(Int64, check_sign_bit(Int64, x))
-- /Source

-- Source: base/boot.jl:1187-1187 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Int64(x::BuiltinInts)   = toInt64(x)::Int64
-- /Source

def nativeInteger {t : IntTy} (x : JInt t) : BitMutationM I64 :=
  match JuliaLean.base.int.convert .i64 x with
  | .ok n => pure n
  | .error (.inexactError _) => throw .inexact
  | .error (.overflowError _) => throw .overflow
  | .error .boundsError => throw .bounds
  | .error .divideError => throw .divide
  | .error (.argumentError msg) => throw (.argument msg)
  | .error (.domainError msg) => throw (.argument msg)
  | .error (.methodError name) => throw (.method name)
  | .error .eofError => throw (.method "EOFError")

namespace NativeShift

open JuliaLean.base.bitarray.Models1Group15

-- Source: base/bitarray.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
/-- Native one-dimensional falses with the mutable header created before fill. -/
def falsesVector (runtime : AllocationData) (n : I64) : ObjectM (Ref 1) := do
  let result ← undefObject runtime ⟨[n], rfl⟩
  let array ← readObject result
  let _ ← liftBit (fillBool array false)
  pure result

-- Source: base/int.jl:1092-1100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
/-- The fixed Int64/UInt64 subtraction specialization. Integer promotion uses
remainders into UInt64, rather than checked conversion of a negative Int64. -/
def difference (n : I64) (i : U64) : U64 :=
  match h : JuliaLean.base.int.Generated.sub_Integer
      (Ty := Unit) (V := fun _ => U64) (fun (_ : I64) (_ : U64) => ())
      (fun x _ => pure (JuliaLean.base.int.remT .u64 x))
      (fun x _ => pure (JuliaLean.base.int.remT .u64 x))
      (fun original _ promoted =>
        JuliaLean.base.promotion.notSameTypeDifferent original promoted)
      (fun _ x y => pure (JuliaLean.base.int.sub x y)) n i with
  | .ok value => value
  | .error _ => False.elim (by cases h)

-- Source: base/bitarray.jl:1326-1332 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def leftUnsigned (runtime : AllocationData) (target : Ref 1) (i : U64) :
    ObjectM (Ref 1) := do
  let before ← readObject target
  let n := before.len
  if i == u64 0 then return ← copyObject runtime target
  let result ← falsesVector runtime n
  if JuliaLean.base.int.lt i n then
    let destination ← readObject result
    let source ← readObject target
    let offset ← liftBit (nativeInteger (i + u64 1))
    let count ← liftBit (nativeInteger (difference n i))
    liftBit (Models1Group15.copyChunks destination.chunks (int 1) source.chunks offset count)
  pure result

-- Source: base/bitarray.jl:1334-1340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def rightUnsigned (runtime : AllocationData) (target : Ref 1) (i : U64) :
    ObjectM (Ref 1) := do
  let before ← readObject target
  let n := before.len
  if i == u64 0 then return ← copyObject runtime target
  let result ← falsesVector runtime n
  if JuliaLean.base.int.lt i n then
    let destination ← readObject result
    let source ← readObject target
    let offset ← liftBit (nativeInteger (i + u64 1))
    let count ← liftBit (nativeInteger (difference n i))
    liftBit (Models1Group15.copyChunks destination.chunks offset source.chunks (int 1) count)
  pure result

-- Source: base/bitarray.jl:1415-1415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def leftSigned (runtime : AllocationData) (target : Ref 1) (i : I64) : ObjectM (Ref 1) :=
  if i ≥ int 0 then leftUnsigned runtime target (JuliaLean.base.int.unsigned i)
  else rightUnsigned runtime target (JuliaLean.base.int.unsigned (-i))

-- Source: base/bitarray.jl:1423-1423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def rightSigned (runtime : AllocationData) (target : Ref 1) (i : I64) : ObjectM (Ref 1) :=
  if i ≥ int 0 then rightUnsigned runtime target (JuliaLean.base.int.unsigned i)
  else leftUnsigned runtime target (JuliaLean.base.int.unsigned (-i))

-- Source: base/bitarray.jl:1377-1377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def arithmeticRight (runtime : AllocationData) (target : Ref 1) :
    Sum I64 U64 → ObjectM (Ref 1)
  | .inl count => rightSigned runtime target count
  | .inr count => rightUnsigned runtime target count

end NativeShift

/-- Native scalar access dependency of base/bitarray.jl:1069, with the existing
getter and source bounds-check dispatch (base/bitarray.jl:669-672). -/
-- Source: base/bitarray.jl:669-672 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     @boundscheck checkbounds(B, i)
--     unsafe_bitgetindex(B.chunks, i)
-- end
-- 
-- /Source

def getBit {N : Nat} (B : BitArray N) (i : I64) : BitMutationM Bool :=
  bitArrayGetIndex checkBounds B i

/-- Bool-valued scalar assignment dependency, base/bitarray.jl:688-692. The
identity Bool conversion is the installed convert-same dispatch. -/
-- Source: base/bitarray.jl:688-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline function setindex!(B::BitArray, x, i::Int)
--     @boundscheck checkbounds(B, i)
--     unsafe_bitsetindex!(B.chunks, convert(Bool, x), i)
--     return B
-- end
-- /Source

def setBit {N : Nat} (B : BitArray N) (x : Bool) (i : I64) : BitMutationM (BitArray N) :=
  bitArraySetIndex checkBounds pure B x i


/-!
Local concrete shape dependency bindings needed by assigned methods
(base/bitarray.jl:1177-1189,1783-1787). These close the installed zip/axes/shape models;
no arbitrary shape or constructor implementation is accepted from the caller.
Only DimensionMismatch is reachable from these native metadata calls. The broad
error bridges below keep unsupported classes as failures, but are not advertised
as general error-preserving translations. The formatting buffer is represented
by its accumulated String; no property concerns exception-message formatting.
-/

/-- Concrete shape-error channel for base/bitarray.jl:1784-1785. -/
-- Source: base/bitarray.jl:1783-1787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bit_map(f::F, A::BitArray, B::BitArray) where F
--     AB = zip(A, B)
--     dest = similar(BitArray, _similar_shape(AB, IteratorSize(AB)))
--     bit_map!(f, dest, A, B)
-- end
-- /Source

private abbrev ShapeR := JuliaLean.base.indices.IndexResult
/-- Tagged native Int/range shape entries for the actual mismatch formatter at
base/indices.jl:112-137, including its range-construction branch. -/
-- Source: base/indices.jl:112-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function throw_promote_shape_mismatch(a::Tuple, b::Union{Nothing,Tuple}, i = nothing)
--     if a isa Tuple{Vararg{Base.OneTo}} && (b === nothing || b isa Tuple{Vararg{Base.OneTo}})
--         a = map(lastindex, a)::Dims
--         b === nothing || (b = map(lastindex, b)::Dims)
--     end
--     _has_axes = !(a isa Dims && (b === nothing || b isa Dims))
--     if _has_axes
--         _normalize(d) = map(x -> firstindex(x):lastindex(x), d)
--         a = _normalize(a)
--         b === nothing || (b = _normalize(b))
--         _things = "axes "
--     else
--         _things = "size "
--     end
--     msg = IOBuffer()
--     print(msg, "a has ", _things)
--     print(msg, a)
--     if b ≢ nothing
--         print(msg, ", b has ", _things)
--         print(msg, b)
--     end
--     if i ≢ nothing
--         print(msg, ", mismatch at dim ", i)
--     end
--     throw(DimensionMismatch(takestring!(msg)))
-- end
-- /Source

private abbrev ShapeEntry :=
  JuliaLean.base.indices.IntegerOrRange I64 JuliaLean.base.indices.BaseRange

/-- Source dispatch base/iterators.jl:71-75,503-513 and base/array.jl:700-701. -/
-- Source: base/iterators.jl:71-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- and_iteratorsize(isz::T, ::T) where {T} = isz
-- and_iteratorsize(::HasLength, ::HasShape) = HasLength()
-- and_iteratorsize(::HasShape, ::HasLength) = HasLength()
-- and_iteratorsize(::HasShape{N}, ::HasShape{N}) where {N} = HasShape{N}()
-- and_iteratorsize(::HasShape, ::HasShape) = HasLength()
-- /Source

-- Source: base/iterators.jl:503-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- IteratorSize(::Type{Zip{Is}}) where {N, Is<:Tuple{Vararg{Any, N}}} = zip_iteratorsize(ntuple(n -> IteratorSize(fieldtype(Is, n)), N)...)
-- IteratorEltype(::Type{Zip{Is}}) where {N, Is<:Tuple{Vararg{Any, N}}} = zip_iteratoreltype(ntuple(n -> IteratorEltype(fieldtype(Is, n)), N)...)
-- 
-- zip_iteratorsize() = IsInfinite()
-- zip_iteratorsize(I) = I
-- zip_iteratorsize(a, b) = and_iteratorsize(a,b) # as `and_iteratorsize` but inherit `Union{HasLength,IsInfinite}` of the shorter iterator
-- zip_iteratorsize(::HasLength, ::IsInfinite) = HasLength()
-- zip_iteratorsize(::HasShape, ::IsInfinite) = HasLength()
-- zip_iteratorsize(a::IsInfinite, b) = zip_iteratorsize(b,a)
-- zip_iteratorsize(a::IsInfinite, b::IsInfinite) = IsInfinite()
-- zip_iteratorsize(a, b, tail...) = zip_iteratorsize(a, zip_iteratorsize(b, tail...))
-- /Source

-- Source: base/array.jl:700-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _similar_shape(itr, ::HasLength) = length(itr)::Integer
-- _similar_shape(itr, ::HasShape) = axes(itr)
-- /Source

def binaryRank (N M : Nat) : Nat := if N = M then N else 1

/-- Concrete native min and max from base/operators.jl:555,573. -/
-- Source: base/operators.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- min(x,y) = ifelse(isless(y, x), y, x)
-- /Source

private def binaryMin (a b : I64) : I64 :=
  JuliaLean.base.operators.min JuliaLean.base.int.lt_BitSigned
    JuliaLean.base.essentials.ifelse a b

/-- Native max dependency at base/operators.jl:555. -/
-- Source: base/operators.jl:555-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- max(x, y) = ifelse(isless(y, x), x, y)
-- /Source

private def binaryMax (a b : I64) : I64 :=
  JuliaLean.base.operators.max JuliaLean.base.int.lt_BitSigned
    JuliaLean.base.essentials.ifelse a b

/-- Core throw support for the existing Zip models; catches only the same class. -/
-- Source: base/iterators.jl:379-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- zip(a...) = Zip(a)
-- function length(z::Zip)
--     n = _zip_min_length(z.is)
--     n === nothing && throw(ArgumentError("iterator is of undefined length"))
--     return n
-- end
-- function _zip_min_length(is)
--     i = is[1]
--     n = _zip_min_length(tail(is))
--     if IteratorSize(i) isa IsInfinite
--         return n
--     else
--         return n === nothing ? length(i) : min(n, length(i))
--     end
-- end
-- /Source

local instance : MonadExceptOf JlError ShapeR where
  throw e := .error (.core e)
  tryCatch action handler :=
    match action with
    | .error (.core e) => handler e
    | other => other

/-- The only range callees below are native UnitRange construction/length and
OneTo intersection. They cannot throw the exceptional fallback classes. 
Julia source: base/iterators.jl:414-416. -/
-- Source: base/iterators.jl:414-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _promote_tuple_shape((a,)::Tuple{OneTo}, (b,)::Tuple{OneTo}) = (intersect(a, b),)
-- _promote_tuple_shape((m,)::Tuple{Integer}, (n,)::Tuple{Integer}) = (min(m, n),)
-- _promote_tuple_shape(a, b) = promote_shape(a, b)
-- /Source

private def binaryLiftRange {α : Type} (r : JuliaLean.base.range.JlX α) : ShapeR α :=
  r.mapError fun e => match e with
    | .jl e => .core e
    | .dimensionMismatch msg => .dimensionMismatch msg
    | .inboundsViolation => .boundsError
    | .errorException msg => .argumentError msg
    | .showError _ => .methodError "show" []

/-- axesDefault with ranked size and unchecked_oneto has no error-producing
callee. These cases keep the bridge explicit rather than assuming success. 
Julia source: base/abstractarray.jl:100-103. -/
-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source

private def binaryLiftArray {α : Type}
    (r : JuliaLean.base.abstractarray.Result α) : ShapeR α :=
  r.mapError fun e => match e with
    | .julia e => .core e
    | .dimensionMismatch msg => .dimensionMismatch msg
    | .canonicalIndex f _ => .methodError f []
    | .errorException msg => .argumentError msg
    | .assertionError msg => .argumentError msg
    | .showError _ => .methodError "show" []

-- Source: base/range.jl:485-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct OneTo{T<:Integer} <: AbstractOneTo{T}
--     stop::T # invariant: stop >= zero(stop)
--     function OneTo{T}(stop) where {T<:Integer}
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         T === Bool && throwbool(stop)
--         return new(max(zero(T), stop))
--     end
-- /Source

local instance : JuliaLean.base.range.JType I64 where
  isBool := false
  isSigned := true
  isInteger := true
  isAbstractFloat := false
  bool_eq := by intro h; cases h

-- Source: base/range.jl:488-490 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         T === Bool && throwbool(stop)
--         return new(max(zero(T), stop))
-- /Source

local instance : JuliaLean.base.range.JPrint I64 := ⟨fun n => toString n.val⟩
-- Source: base/range.jl:485-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct OneTo{T<:Integer} <: AbstractOneTo{T}
--     stop::T # invariant: stop >= zero(stop)
--     function OneTo{T}(stop) where {T<:Integer}
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         T === Bool && throwbool(stop)
--         return new(max(zero(T), stop))
--     end
-- /Source

local instance : JuliaLean.base.range.JZero I64 := ⟨int 0⟩
-- Source: base/range.jl:806-806 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(r::OneTo) = Integer(r.stop - zero(r.stop))
-- /Source

local instance : JuliaLean.base.range.JInteger I64 I64 := ⟨pure⟩
-- Source: base/operators.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- min(x,y) = ifelse(isless(y, x), y, x)
-- /Source

local instance : JuliaLean.base.range.JMin I64 I64 I64 :=
  ⟨fun a b => pure (binaryMin a b)⟩
-- Source: base/operators.jl:555-555 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- max(x, y) = ifelse(isless(y, x), x, y)
-- /Source

local instance : JuliaLean.base.range.JMax I64 I64 I64 :=
  ⟨fun a b => pure (binaryMax a b)⟩
-- Source: base/range.jl:485-491 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- struct OneTo{T<:Integer} <: AbstractOneTo{T}
--     stop::T # invariant: stop >= zero(stop)
--     function OneTo{T}(stop) where {T<:Integer}
--         throwbool(r)  = (@noinline; throw(ArgumentError("invalid index: $r of type Bool")))
--         T === Bool && throwbool(stop)
--         return new(max(zero(T), stop))
--     end
-- /Source

local instance : JuliaLean.base.range.JOneToT I64 I64 :=
  ⟨JuliaLean.base.range.OneTo_T_stop⟩
-- Source: base/range.jl:505-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- OneTo(stop::T) where {T<:Integer} = OneTo{T}(stop)
-- /Source

local instance : JuliaLean.base.range.JOneTo1 I64 (JuliaLean.base.range.OneTo I64) :=
  ⟨JuliaLean.base.range.OneTo_stop⟩
-- Source: base/range.jl:867-867 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::OrdinalRange{T}) where {T} = convert(T, r.start)
-- /Source

local instance : JuliaLean.base.range.JFirst (JuliaLean.base.range.UnitRange I64) I64 :=
  ⟨fun r => pure r.start⟩
-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source

local instance : JuliaLean.base.range.JLast (JuliaLean.base.range.UnitRange I64) I64 :=
  ⟨fun r => pure r.stop⟩

/-- Preserve OneTo versus Int while throw_promote_shape_mismatch normalizes its
message arguments. Original input axes are always OneTo values. 
Julia source: base/range.jl:794-806. -/
-- Source: base/range.jl:794-806 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T
--     @inline
--     start, stop = first(r), last(r)
--     a = oneunit(zero(stop) - zero(start))
--     if a isa Signed || stop >= start
--         a += stop - start # Signed are allowed to go negative
--     else
--         a = zero(a) # Unsigned don't necessarily underflow
--     end
--     return Integer(a)
-- end
-- 
-- length(r::OneTo) = Integer(r.stop - zero(r.stop))
-- /Source

private def binaryEntryLastindex : ShapeEntry → ShapeR I64
  | .integer _ => pure (int 1)
  | .range (.oneTo n) =>
      binaryLiftRange (JuliaLean.base.range.length_OneTo
        (T := I64) (D := I64) (I := I64) ⟨n⟩)
  | .range (.unitRange first last) =>
      binaryLiftRange (JuliaLean.base.range.length_AbstractUnitRange
        (R := JuliaLean.base.range.UnitRange I64) (T := I64) (D := I64) (I := I64)
        ⟨first, last⟩)

/-- Text representation used only by the error-buffer binding at
base/indices.jl:125-136. The actual path normalizes OneTo axes to Int first. -/
-- Source: base/indices.jl:125-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     end
--     msg = IOBuffer()
--     print(msg, "a has ", _things)
--     print(msg, a)
--     if b ≢ nothing
--         print(msg, ", b has ", _things)
--         print(msg, b)
--     end
--     if i ≢ nothing
--         print(msg, ", mismatch at dim ", i)
--     end
--     throw(DimensionMismatch(takestring!(msg)))
-- /Source

private def binaryEntryText : ShapeEntry → String
  | .integer n => toString n.val
  | .range (.oneTo n) => "Base.OneTo(" ++ toString n.val ++ ")"
  | .range (.unitRange a b) => toString a.val ++ ":" ++ toString b.val

/-- Tuple punctuation for the concrete IOBuffer printing dependency at
base/indices.jl:125-136; an empty tuple and a singleton retain Julia punctuation. -/
-- Source: base/indices.jl:125-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     end
--     msg = IOBuffer()
--     print(msg, "a has ", _things)
--     print(msg, a)
--     if b ≢ nothing
--         print(msg, ", b has ", _things)
--         print(msg, b)
--     end
--     if i ≢ nothing
--         print(msg, ", mismatch at dim ", i)
--     end
--     throw(DimensionMismatch(takestring!(msg)))
-- /Source

private def binaryTupleText (xs : List ShapeEntry) : String :=
  "(" ++ String.intercalate ", " (xs.map binaryEntryText) ++
    (if xs.length = 1 then ",)" else ")")

/-- Concrete source-dependency binding for indices.jl:109-137. The colon callee
is the supplied native UnitRange constructor; no arbitrary shape callback is
accepted. The mismatch path for actual OneTo axes normalizes them to Ints. 
Julia source: base/indices.jl:112-137. -/
-- Source: base/indices.jl:112-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function throw_promote_shape_mismatch(a::Tuple, b::Union{Nothing,Tuple}, i = nothing)
--     if a isa Tuple{Vararg{Base.OneTo}} && (b === nothing || b isa Tuple{Vararg{Base.OneTo}})
--         a = map(lastindex, a)::Dims
--         b === nothing || (b = map(lastindex, b)::Dims)
--     end
--     _has_axes = !(a isa Dims && (b === nothing || b isa Dims))
--     if _has_axes
--         _normalize(d) = map(x -> firstindex(x):lastindex(x), d)
--         a = _normalize(a)
--         b === nothing || (b = _normalize(b))
--         _things = "axes "
--     else
--         _things = "size "
--     end
--     msg = IOBuffer()
--     print(msg, "a has ", _things)
--     print(msg, a)
--     if b ≢ nothing
--         print(msg, ", b has ", _things)
--         print(msg, b)
--     end
--     if i ≢ nothing
--         print(msg, ", mismatch at dim ", i)
--     end
--     throw(DimensionMismatch(takestring!(msg)))
-- end
-- /Source

private def binaryShapeCalls : JuliaLean.base.indices.ShapeCallees ShapeEntry String where
  isOneTo
    | .range (.oneTo _) => true
    | _ => false
  isInt
    | .integer _ => true
    | _ => false
  ofInt := .integer
  lastindex := binaryEntryLastindex
  firstindex := fun _ => pure (int 1)
  colon a b := do
    let r ← binaryLiftRange (JuliaLean.base.range.colon_T_T_Real (T := I64) a b)
    pure (.range (.unitRange r.start r.stop))
  IOBuffer := ""
  printString := String.append
  printTuple := fun buffer xs => buffer ++ binaryTupleText xs
  printInt := fun buffer i => buffer ++ toString i.val
  takestring := id

/-- A range's actual start/stop metadata. Used only for comparing the optional
trailing unit axis; both original zip inputs have equal ranks on this path. 
Julia source: base/range.jl:1163-1166. -/
-- Source: base/range.jl:1163-1166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(r::AbstractUnitRange, s::AbstractUnitRange) =
--     (isempty(r) & isempty(s)) | ((first(r) == first(s)) & (last(r) == last(s)))
-- 
-- ==(r::OneTo, s::OneTo) = last(r) == last(s)
-- /Source

private def binaryRangeEndpoints : JuliaLean.base.indices.BaseRange → I64 × I64
  | .oneTo n => (int 1, n)
  | .unitRange a b => (a, b)

/-- Native OneTo equality is stop equality (range.jl:1166). For a trailing
1:1 check the native AbstractUnitRange equality is used (1163-1165). 
Julia source: base/range.jl:1163-1166. -/
-- Source: base/range.jl:1163-1166 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- ==(r::AbstractUnitRange, s::AbstractUnitRange) =
--     (isempty(r) & isempty(s)) | ((first(r) == first(s)) & (last(r) == last(s)))
-- 
-- ==(r::OneTo, s::OneTo) = last(r) == last(s)
-- /Source

private def binaryEntryEq (a b : ShapeEntry) : Bool :=
  match a, b with
  | .integer a, .integer b => JuliaLean.base.int.eq_int a b
  | .range (.oneTo a), .range (.oneTo b) => JuliaLean.base.int.eq_int a b
  | .range a, .range b =>
      let a := binaryRangeEndpoints a
      let b := binaryRangeEndpoints b
      (JuliaLean.base.int.lt_BitSigned a.2 a.1 &&
       JuliaLean.base.int.lt_BitSigned b.2 b.1) ||
      (JuliaLean.base.int.eq_int a.1 b.1 && JuliaLean.base.int.eq_int a.2 b.2)
  | _, _ => false

/-- Reuse the installed ordered comparison loops. A genuine argument element
supplies Inhabited for the existing get! notation, never an invented default;
the existing loop ranges keep every access within its tuple. 
Julia source: base/indices.jl:192-204. -/
-- Source: base/indices.jl:108-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_shape(::Tuple{}, ::Tuple{}) = ()
-- /Source

-- Source: base/indices.jl:192-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function promote_shape(a::Indices, b::Indices)
--     if length(a) < length(b)
--         return promote_shape(b, a)
--     end
--     for i=1:length(b)
--         a[i] != b[i] && throw_promote_shape_mismatch(a, b, i)
--     end
--     for i=length(b)+1:length(a)
--         a[i] != 1:1 && throw_promote_shape_mismatch(a, nothing, i)
--     end
--     return a
-- end
-- 
-- /Source

private def binaryPromoteGeneral (a b : List ShapeEntry) : ShapeR (List ShapeEntry) :=
  match a, b with
  | [], [] => pure JuliaLean.base.indices.promote_shape_Tuple0_Tuple0
  | first :: _, _ =>
      letI : Inhabited ShapeEntry := ⟨first⟩
      JuliaLean.base.indices.promote_shape_Indices binaryShapeCalls binaryEntryEq a b
  | [], first :: _ =>
      letI : Inhabited ShapeEntry := ⟨first⟩
      JuliaLean.base.indices.promote_shape_Indices binaryShapeCalls binaryEntryEq a b

/-- The exact _promote_tuple_shape dispatch of iterators.jl:414-416. Singleton
OneTo tuples intersect; all other ranks call the installed promote_shape body. 
Julia source: base/range.jl:1206. -/
-- Source: base/iterators.jl:414-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _promote_tuple_shape((a,)::Tuple{OneTo}, (b,)::Tuple{OneTo}) = (intersect(a, b),)
-- _promote_tuple_shape((m,)::Tuple{Integer}, (n,)::Tuple{Integer}) = (min(m, n),)
-- _promote_tuple_shape(a, b) = promote_shape(a, b)
-- /Source

-- Source: base/range.jl:1206-1206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- intersect(r::OneTo, s::OneTo) = OneTo(min(r.stop,s.stop))
-- /Source

private def binaryPromoteAxes (a b : List ShapeEntry) : ShapeR (List ShapeEntry) :=
  JuliaLean.base.iterators.promoteTupleShape2
    (fun x => match x with
      | .range (.oneTo n) => some (JuliaLean.base.range.unchecked_oneto n)
      | _ => none)
    (fun r : JuliaLean.base.range.OneTo I64 => .range (.oneTo r.stop))
    (fun r s => binaryLiftRange
      (JuliaLean.base.range.intersect_OneTo_OneTo
        (T := I64) (U := I64) (M := I64) (ρ := JuliaLean.base.range.OneTo I64) r s))
    (fun x => match x with | .integer n => some n | _ => none)
    (fun n => (.integer n : ShapeEntry))
    (fun x y => pure (binaryMin x y))
    binaryPromoteGeneral a b

/-- Actual BitArray axes, including BitVector's len-based size and rank zero. 
Julia source: base/abstractarray.jl:100-103. -/
-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source

private def binaryAxes (rank : Nat) (B : BitArray rank) : ShapeR (List ShapeEntry) := do
  let axes ← binaryLiftArray (JuliaLean.base.abstractarray.axesDefault
    (fun value : BitArray rank => pure (bitArraySizeRanked value))
    (JuliaLean.base.range.unchecked_oneto (T := I64)) B)
  pure (axes.map fun axis => .range (.oneTo axis.stop))

/-- to_shape on the entries that the two-BitArray zip can actually return.
A OneTo uses its stop; no mathematical size arithmetic replaces native Int. 
Julia source: base/abstractarray.jl:836-845. -/
-- Source: base/abstractarray.jl:836-845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- to_shape(::Tuple{}) = ()
-- to_shape(dims::Dims) = dims
-- to_shape(dims::DimsOrInds) = map(to_shape, dims)::DimsOrInds
-- # each dimension
-- to_shape(i::Int) = i
-- to_shape(i::Integer) = Int(i)
-- to_shape(r::AbstractOneTo) = _to_shape(last(r))
-- _to_shape(x::Integer) = to_shape(x)
-- _to_shape(x) = Int(x)
-- to_shape(r::AbstractUnitRange) = r
-- /Source

private def binaryToDimension : ShapeEntry → ShapeR I64
  | .integer n => pure (JuliaLean.base.abstractarray.toShapeInt n)
  | .range (.oneTo n) =>
      JuliaLean.base.abstractarray.toShapeOneTo
        (fun r : JuliaLean.base.range.OneTo I64 => pure r.stop)
        (fun i => JuliaLean.base.abstractarray.toShapeIntegerHelper
          (fun x => pure (JuliaLean.base.abstractarray.toShapeInt x)) i)
        (JuliaLean.base.range.unchecked_oneto n)
  | .range (.unitRange _ _) => .error (.methodError "BitArray: non-OneTo dimensions" [])

/-- Explicit shape error bridge. The only error produced by concrete native
metadata/shape calls here is DimensionMismatch. Broad unsupported Core classes
are retained as failures and never replaced by a value. 
Julia source: base/indices.jl:112-137. -/
-- Source: base/indices.jl:112-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function throw_promote_shape_mismatch(a::Tuple, b::Union{Nothing,Tuple}, i = nothing)
--     if a isa Tuple{Vararg{Base.OneTo}} && (b === nothing || b isa Tuple{Vararg{Base.OneTo}})
--         a = map(lastindex, a)::Dims
--         b === nothing || (b = map(lastindex, b)::Dims)
--     end
--     _has_axes = !(a isa Dims && (b === nothing || b isa Dims))
--     if _has_axes
--         _normalize(d) = map(x -> firstindex(x):lastindex(x), d)
--         a = _normalize(a)
--         b === nothing || (b = _normalize(b))
--         _things = "axes "
--     else
--         _things = "size "
--     end
--     msg = IOBuffer()
--     print(msg, "a has ", _things)
--     print(msg, a)
--     if b ≢ nothing
--         print(msg, ", b has ", _things)
--         print(msg, b)
--     end
--     if i ≢ nothing
--         print(msg, ", mismatch at dim ", i)
--     end
--     throw(DimensionMismatch(takestring!(msg)))
-- end
-- /Source

private def binaryShapeError : JuliaLean.base.indices.IndexError → JuliaLean.base.array.Error
  | .argumentError msg => .argument msg
  | .dimensionMismatch msg => .dimensionMismatch msg
  | .boundsError => .bounds
  | .methodError f _ => .method f
  | .core (.argumentError msg) => .argument msg
  | .core (.overflowError _) => .overflow
  | .core .boundsError => .bounds
  | .core (.inexactError _) => .inexact
  | .core .divideError => .divide
  | .core (.methodError f) => .method f
  | .core (.domainError msg) => .argument msg
  | .core .eofError => .method "EOFError"


/-- Dispatch quotient of the Integer argument at base/bitarray.jl:798.
The only pinned num_bit_chunks method accepts Int. Every other Integer type fails
method dispatch before its numeric value is inspected, so its value is irrelevant.
This is pinned Base dispatch, not a model of user-added num_bit_chunks methods. -/
-- Source: base/bitarray.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- num_bit_chunks(n::Int) = _div64(n) + !iszero(_mod64(n))
-- /Source

-- Source: base/bitarray.jl:798-801 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sizehint!(B::BitVector, sz::Integer)
--     sizehint!(B.chunks, num_bit_chunks(sz))
--     return B
-- end
-- /Source

inductive SizeHintArgument where
  | native (value : I64)
  | otherInteger (typeName : String)

/-- base/bitarray.jl:798: preserves the source's num_bit_chunks dispatch, then calls
the installed array.sizehint implementation with its actual defaults. -/
-- Source: base/bitarray.jl:798-801 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function sizehint!(B::BitVector, sz::Integer)
--     sizehint!(B.chunks, num_bit_chunks(sz))
--     return B
-- end
-- /Source

def sizehint (B : BitVector) (sz : SizeHintArgument) : BitMutationM BitVector :=
  match sz with
  | .native n => bitVectorSizehint reserveChunks B n
  | .otherInteger _ => throw (.method "num_bit_chunks")


section ResizeNativeRange

-- Source: base/range.jl:794-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T
--     @inline
--     start, stop = first(r), last(r)
--     a = oneunit(zero(stop) - zero(start))
--     if a isa Signed || stop >= start
--         a += stop - start # Signed are allowed to go negative
--     else
--         a = zero(a) # Unsigned don't necessarily underflow
--     end
--     return Integer(a)
-- end
-- /Source
local instance : JuliaLean.base.range.JType I64 where
  isBool := false
  isSigned := true
  isInteger := true
  isAbstractFloat := false
  bool_eq := by intro h; cases h

-- Source: base/range.jl:797-797 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     a = oneunit(zero(stop) - zero(start))
-- /Source
local instance : JuliaLean.base.range.JZero I64 := ⟨int 0⟩
-- Source: base/range.jl:803-803 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     return Integer(a)
-- /Source
local instance : JuliaLean.base.range.JInteger I64 I64 :=
  ⟨fun x => JuliaLean.base.range.liftJl (JuliaLean.base.int.convert .i64 x)⟩
-- Source: base/range.jl:867-867 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::OrdinalRange{T}) where {T} = convert(T, r.start)
-- /Source
local instance : JuliaLean.base.range.JEltype (JuliaLean.base.range.UnitRange I64) I64 := ⟨⟩
-- Source: base/range.jl:867-867 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::OrdinalRange{T}) where {T} = convert(T, r.start)
-- /Source
local instance : JuliaLean.base.range.JFieldStart (JuliaLean.base.range.UnitRange I64) I64 :=
  ⟨JuliaLean.base.range.UnitRange.start⟩
-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source
local instance : JuliaLean.base.range.JFieldStop (JuliaLean.base.range.UnitRange I64) I64 :=
  ⟨JuliaLean.base.range.UnitRange.stop⟩
-- Source: base/range.jl:867-867 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::OrdinalRange{T}) where {T} = convert(T, r.start)
-- /Source
local instance : JuliaLean.base.range.JFirst (JuliaLean.base.range.UnitRange I64) I64 :=
  ⟨JuliaLean.base.range.first_OrdinalRange⟩
-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source
local instance : JuliaLean.base.range.JLast (JuliaLean.base.range.UnitRange I64) I64 :=
  ⟨JuliaLean.base.range.last_OrdinalRange⟩

/-- Error bridge for the concrete native-range callees at base/bitarray.jl:810.
Only same-type Int construction/conversion and native arithmetic occur; the
exceptional non-Julia branches cannot be produced by these callees. -/
-- Source: base/bitarray.jl:804-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _resize_int!(B::BitVector, n::Int, first::Bool)
--     n0 = length(B)
--     n == n0 && return B
--     n >= 0 || throw(BoundsError(B, n))
--     if n < n0
--         r = first ? (1:n0-n) : (n+1:n0)
--         deleteat!(B, r)
--         return B
--     end
--     Bc = B.chunks
--     k0 = length(Bc)
--     k1 = num_bit_chunks(n)
--     if k1 > k0
--         _growend!(Bc, k1 - k0)
--         Bc[end] = UInt64(0)
--     end
--     if first
--         copy_chunks!(Bc, 1 + n - n0, Bc, 1, n0)
--     end
--     B.len = n
--     return B
-- end
-- /Source
def resizeLiftRange {α : Type} (r : JuliaLean.base.range.JlX α) : BitMutationM α :=
  match r with
  | .ok value => pure value
  | .error (.jl (.argumentError msg)) => throw (.argument msg)
  | .error (.jl .boundsError) => throw .bounds
  | .error (.jl (.inexactError _)) => throw .inexact
  | .error (.jl (.overflowError _)) => throw .overflow
  | .error (.jl .divideError) => throw .divide
  | .error (.jl (.domainError msg)) => throw (.argument msg)
  | .error (.jl (.methodError name)) => throw (.method name)
  | .error (.jl .eofError) => throw (.method "EOFError")
  | .error (.dimensionMismatch msg) => throw (.dimensionMismatch msg)
  | .error (.errorException msg) => throw (.argument msg)
  | .error (.showError e) => throw (.showError e)
  | .error .inboundsViolation => throw .bounds

/-- Actual native UnitRange length callee at base/range.jl:794-804.
The native Int specialization is selected by the installed proof-file dispatch
`lengthUnit`; that proof module is not imported here. -/
-- Source: base/range.jl:794-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T
--     @inline
--     start, stop = first(r), last(r)
--     a = oneunit(zero(stop) - zero(start))
--     if a isa Signed || stop >= start
--         a += stop - start # Signed are allowed to go negative
--     else
--         a = zero(a) # Unsigned don't necessarily underflow
--     end
--     return Integer(a)
-- end
-- /Source
def nativeUnitRangeLength (r : JuliaLean.base.range.UnitRange I64) : BitMutationM I64 :=
  resizeLiftRange (JuliaLean.base.range.length_AbstractUnitRange
    (R := JuliaLean.base.range.UnitRange I64) (T := I64) (D := I64) (I := I64) r)

/-- Concrete native UnitRange instance of base/bitarray.jl:955-977, used only for
tail deletion. Callers supply the actual native range; this wrapper preserves
both endpoint checks before evaluating length(r), then closes the bundled pure
length interface with that computed value. No arbitrary range behavior is an
input. Calling the bundled body repeats only the already-passed pure checks.

This is usable for a tail r with r.stop=B.len. In that domain copyChunks receives
n-i_l=0 and returns before reading any word. Do not claim a faithful arbitrary
range model: positive-count copyChunks has the frozen source167 defect. -/
-- Source: base/bitarray.jl:955-977 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function deleteat!(B::BitVector, r::AbstractUnitRange{Int})
--     n = length(B)
--     i_f = first(r)
--     i_l = last(r)
--     1 <= i_f || throw(BoundsError(B, i_f))
--     i_l <= n || throw(BoundsError(B, n+1))
-- 
--     Bc = B.chunks
--     new_l = length(B) - length(r)
--     delta_k = num_bit_chunks(new_l) - length(Bc)
-- 
--     copy_chunks!(Bc, i_f, Bc, i_l+1, n-i_l)
-- 
--     delta_k < 0 && _deleteend!(Bc, -delta_k)
-- 
--     B.len = new_l
-- 
--     if new_l > 0
--         Bc[end] &= _msk_end(new_l)
--     end
-- 
--     return B
-- end
-- /Source
private def deleteNativeTailRange (B : BitVector) (r : JuliaLean.base.range.UnitRange I64) :
    BitMutationM BitVector := do
  let iF ← resizeLiftRange (JuliaLean.base.range.first_OrdinalRange r)
  let iL ← resizeLiftRange (JuliaLean.base.range.last_OrdinalRange r)
  if iF < int 1 then throw .bounds
  if iL > B.len then throw .bounds
  let count ← nativeUnitRangeLength r
  bitVectorDeleteRange (fun _ => count) B ⟨iF, iL⟩

/-- Complete first=false specialization of base/bitarray.jl:804-825, retaining
all native lengths, capacity states and shared chunks. The source's first=true
branch remains outside this explicitly partial row. Growing may expose undefined
slots; only a newly appended final chunk is zeroed, exactly as in source. -/
-- Source: base/bitarray.jl:804-825 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _resize_int!(B::BitVector, n::Int, first::Bool)
--     n0 = length(B)
--     n == n0 && return B
--     n >= 0 || throw(BoundsError(B, n))
--     if n < n0
--         r = first ? (1:n0-n) : (n+1:n0)
--         deleteat!(B, r)
--         return B
--     end
--     Bc = B.chunks
--     k0 = length(Bc)
--     k1 = num_bit_chunks(n)
--     if k1 > k0
--         _growend!(Bc, k1 - k0)
--         Bc[end] = UInt64(0)
--     end
--     if first
--         copy_chunks!(Bc, 1 + n - n0, Bc, 1, n0)
--     end
--     B.len = n
--     return B
-- end
-- /Source
def resizeLast (B : BitVector) (n : I64) : BitMutationM BitVector := do
  let n0 := B.len
  if n == n0 then return B
  if n < int 0 then throw .bounds
  if n < n0 then
    let r ← resizeLiftRange (JuliaLean.base.range.colon_T_T_Real (n + int 1) n0)
    return ← deleteNativeTailRange B r
  let Bc := B.chunks
  let k0 ← mutableLength Bc
  let k1 := numBitChunks n
  if k1 > k0 then
    growChunkVector Bc (k1 - k0)
    mutableSet Bc (u64 0) (← mutableLength Bc)
  return { B with len := n }

/-- Default-first=false public specialization of base/bitarray.jl:803 for every
value of all ten built-in non-Bool machine integer types. Native conversion is
fallible and occurs before any size check or mutation. -/
-- Source: base/bitarray.jl:803-803 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- resize!(B::BitVector, n::Integer; first::Bool=false) = _resize_int!(B, Int(n), first)
-- /Source
def resizeLastMachine {t : IntTy} (B : BitVector) (n : JInt t) : BitMutationM BitVector := do
  let n ← nativeInteger n
  resizeLast B n

end ResizeNativeRange

/-- Concrete represented scalar family for base/bitarray.jl:839,885. This covers
Bool and all ten machine Integer types, without pretending to implement every
possible Julia value or a user-defined convert(Bool, item) method. -/
-- Source: base/bitarray.jl:839-840 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function pushfirst!(B::BitVector, item)
--     item = convert(Bool, item)
-- /Source

-- Source: base/bitarray.jl:885-889 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _insert_int!(B::BitVector, i::Int, item)
--     i = Int(i)
--     n = length(B)
--     1 <= i <= n+1 || throw(BoundsError(B, i))
--     item = convert(Bool, item)
-- /Source

inductive ScalarItem where
  | boolean (value : Bool)
  | integer (type : IntTy) (value : JInt type)

/-- Actual number.convert dispatch and Bool(::Real) for the represented scalar
family, including the ordered comparisons to native Int zero and one.
Only InexactError is reachable from these concrete conversions.
Julia source: base/number.jl:6-7; base/bool.jl:170. -/
-- Source: base/number.jl:6-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, x::T)      where {T<:Number} = x
-- convert(::Type{T}, x::Number) where {T<:Number} = T(x)::T
-- /Source

-- Source: base/bool.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Bool(x::Real) = x==0 ? false : x==1 ? true : throw(InexactError(:Bool, Bool, x))
-- /Source

def scalarToBool (item : ScalarItem) : BitMutationM Bool :=
  match item with
  | .boolean value => pure (JuliaLean.base.number.convertSame value)
  | .integer _ value =>
      match JuliaLean.base.number.convertNumber
        (JuliaLean.base.bool.boolFromReal
          (fun x n => pure (JuliaLean.base.int.eq x (int n)))) value with
      | .ok value => pure value
      | .error _ => throw .inexact

/-- base/bitarray.jl:839, concrete Bool/machine-Integer item specialization.
The installed source body performs conversion before any mutation, preserves
the descending chunk-write order, and returns the updated BitVector header. -/
-- Source: base/bitarray.jl:839-859 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function pushfirst!(B::BitVector, item)
--     item = convert(Bool, item)
-- 
--     Bc = B.chunks
-- 
--     l = _mod64(length(B))
--     if l == 0
--         _growend!(Bc, 1)
--         Bc[end] = UInt64(0)
--     end
--     B.len += 1
--     if B.len == 1
--         Bc[1] = item
--         return B
--     end
--     for i = length(Bc) : -1 : 2
--         Bc[i] = (Bc[i] << 1) | (Bc[i-1] >>> 63)
--     end
--     Bc[1] = UInt64(item) | (Bc[1] << 1)
--     return B
-- end
-- /Source

def pushFirstScalar (B : BitVector) (item : ScalarItem) : BitMutationM BitVector :=
  bitVectorPushfirst scalarToBool B item

/-- base/bitarray.jl:885, concrete Bool/machine-Integer item specialization.
The final public scalar assignment retains its bounds check after B.len changes;
the frozen template suppresses this check. This additive body leaves that
template unchanged, and retains both source reads of the partially shifted word. -/
-- Source: base/bitarray.jl:885-911 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _insert_int!(B::BitVector, i::Int, item)
--     i = Int(i)
--     n = length(B)
--     1 <= i <= n+1 || throw(BoundsError(B, i))
--     item = convert(Bool, item)
-- 
--     Bc = B.chunks
-- 
--     k, j = get_chunks_id(i)
-- 
--     l = _mod64(length(B))
--     if l == 0
--         _growend!(Bc, 1)
--         Bc[end] = UInt64(0)
--     end
--     B.len += 1
-- 
--     for t = length(Bc) : -1 : k + 1
--         Bc[t] = (Bc[t] << 1) | (Bc[t - 1] >>> 63)
--     end
-- 
--     msk_aft = (_msk64 << j)
--     msk_bef = ~msk_aft
--     Bc[k] = (msk_bef & Bc[k]) | ((msk_aft & Bc[k]) << 1)
--     B[i] = item
--     B
-- end
-- /Source

def insertIntScalar (B : BitVector) (i : I64) (item : ScalarItem) :
    BitMutationM BitVector := do
  let i ← nativeInteger i
  let n := B.len
  if !(int 1 ≤ i ∧ i ≤ n + int 1) then throw .bounds
  let item ← scalarToBool item
  let Bc := B.chunks
  let (k, j) := getChunksId i
  let l := mod64 B.len
  if l == int 0 then
    growChunkVector Bc (int 1)
    mutableSet Bc (u64 0) (← mutableLength Bc)
  let B := { B with len := B.len + int 1 }
  for t in (intRange (k + int 1) (← mutableLength Bc)).reverse do
    let current ← mutableGet Bc t
    let previous ← mutableGet Bc (t - int 1)
    mutableSet Bc (or_int (shl_int current (int 1)) (lshr_int previous (int 63))) t
  let maskAfter := shl_int u64Max j
  let maskBefore := not_int maskAfter
  let before ← mutableGet Bc k
  let after ← mutableGet Bc k
  mutableSet Bc
    (or_int (and_int maskBefore before) (shl_int (and_int maskAfter after) (int 1))) k
  let _ ← setBit B item i
  pure B

/-- base/bitarray.jl:884, checked machine-Integer index conversion precedes the
native insertion method and its item conversion. The public Integer/Any method
has further types outside this explicitly represented specialization. -/
-- Source: base/bitarray.jl:884-884 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- insert!(B::BitVector, i::Integer, item) = _insert_int!(B, Int(i), item)
-- /Source

def insertMachineScalar {t : IntTy} (B : BitVector) (i : JInt t) (item : ScalarItem) :
    BitMutationM BitVector := do
  insertIntScalar B (← nativeInteger i) item


/-- base/bitarray.jl:913: retain the source's two distinct writes to Bc[k].
The original declaration remains unchanged, including its combined-write behavior. -/
-- Source: base/bitarray.jl:913-944 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _deleteat!(B::BitVector, i::Int)
--     k, j = get_chunks_id(i)
-- 
--     msk_bef = _msk64 >>> (63 - j)
--     msk_aft = ~msk_bef
--     msk_bef >>>= 1
-- 
--     Bc = B.chunks
-- 
--     @inbounds begin
--         Bc[k] = (msk_bef & Bc[k]) | ((msk_aft & Bc[k]) >> 1)
--         if length(Bc) > k
--             Bc[k] |= (Bc[k + 1] << 63)
--         end
-- 
--         for t = k + 1 : length(Bc) - 1
--             Bc[t] = (Bc[t] >>> 1) | (Bc[t + 1] << 63)
--         end
-- 
--         l = _mod64(length(B))
-- 
--         if l == 1
--             _deleteend!(Bc, 1)
--         elseif length(Bc) > k
--             Bc[end] >>>= 1
--         end
--     end
-- 
--     B.len -= 1
-- 
--     return B
-- end
-- /Source

def deleteAtInt (B : BitVector) (i : I64) : BitMutationM BitVector := do
  let (k, j) := getChunksId i
  let mskBef := lshr_int u64Max (int 63 - j)
  let mskAft := not_int mskBef
  let mskBef := lshr_int mskBef (int 1)
  let Bc := B.chunks
  let before ← mutableGet Bc k
  let after ← mutableGet Bc k
  mutableSet Bc (or_int (and_int mskBef before)
    (lshr_int (and_int mskAft after) (int 1))) k
  if (← mutableLength Bc) > k then
    let current ← mutableGet Bc k
    let next ← mutableGet Bc (k + int 1)
    mutableSet Bc (or_int current (shl_int next (int 63))) k
  for t in intRange (k + int 1) ((← mutableLength Bc) - int 1) do
    let current ← mutableGet Bc t
    let next ← mutableGet Bc (t + int 1)
    mutableSet Bc (or_int (lshr_int current (int 1)) (shl_int next (int 63))) t
  let l := mod64 B.len
  if l == int 1 then
    deleteChunkEnd Bc (int 1)
  else if (← mutableLength Bc) > k then
    let last ← mutableLength Bc
    mutableSet Bc (lshr_int (← mutableGet Bc last) (int 1)) last
  return { B with len := B.len - int 1 }

/-- base/bitarray.jl:946, all ten non-Bool machine Integer types. The full Bool
deprecation runtime is not represented; this is explicitly a partial specialization. -/
-- Source: base/bitarray.jl:946-953 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function deleteat!(B::BitVector, i::Integer)
--     i isa Bool && depwarn("passing Bool as an index is deprecated", :deleteat!)
--     i = Int(i)
--     n = length(B)
--     1 <= i <= n || throw(BoundsError(B, i))
-- 
--     return _deleteat!(B, i)
-- end
-- /Source

def deleteAtMachine {t : IntTy} (B : BitVector) (i : JInt t) : BitMutationM BitVector := do
  let i ← nativeInteger i
  let n := B.len
  if !(int 1 ≤ i ∧ i ≤ n) then throw .bounds
  deleteAtInt B i

/-- base/bitarray.jl:1066, non-Bool machine Integer specialization. Returning the
updated header alongside the removed Boolean is the established pop! convention. -/
-- Source: base/bitarray.jl:1066-1078 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function splice!(B::BitVector, i::Integer)
--     # TODO: after deprecation remove the four lines below
--     #       as v = B[i] is enough to do both bounds checking
--     #       and Bool check then just pass Int(i) to _deleteat!
--     i isa Bool && depwarn("passing Bool as an index is deprecated", :splice!)
--     i = Int(i)
--     n = length(B)
--     1 <= i <= n || throw(BoundsError(B, i))
-- 
--     v = B[i]   # TODO: change to a copy if/when subscripting becomes an ArrayView
--     _deleteat!(B, i)
--     return v
-- end
-- /Source

def spliceMachine {t : IntTy} (B : BitVector) (i : JInt t) :
    BitMutationM (BitVector × Bool) := do
  let i ← nativeInteger i
  let n := B.len
  if !(int 1 ≤ i ∧ i ≤ n) then throw .bounds
  let item ← getBit B i
  let updated ← deleteAtInt B i
  pure (updated, item)


section KeepAtBindings

/-- Concrete abstract-array result channel used by base/bitarray.jl:1063-1064. -/
-- Source: base/bitarray.jl:1063-1064 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keepat!(B::BitVector, inds) = _keepat!(B, inds)
-- keepat!(B::BitVector, inds::AbstractVector{Bool}) = _keepat!(B, inds)
-- /Source

private abbrev KeepArrayResult := JuliaLean.base.abstractarray.Result
/-- Native vector axis representation for base/abstractarray.jl:396. -/
-- Source: base/abstractarray.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexLinear, A::AbstractVector) = (@inline; axes1(A))
-- /Source

private abbrev KeepAxis := JuliaLean.base.range.OneTo I64
/-- Native tail-range representation for base/abstractarray.jl:3713,3728. -/
-- Source: base/abstractarray.jl:3713-3713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     deleteat!(a, i:lastindex(a))
-- /Source

private abbrev KeepRange := JuliaLean.base.range.UnitRange I64
/-- Error-channel composition used by the existing _keepat! implementation,
base/abstractarray.jl:3699-3729, while retaining underlying heap writes on error. -/
-- Source: base/bitarray.jl:1063-1064 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keepat!(B::BitVector, inds) = _keepat!(B, inds)
-- keepat!(B::BitVector, inds::AbstractVector{Bool}) = _keepat!(B, inds)
-- /Source

private abbrev KeepM := ExceptT JuliaLean.base.abstractarray.ArrayError BitMutationM
/-- Method-local object-header state for base/abstractarray.jl:3713-3714.
It represents the same source object before and after tail deletion. -/
-- Source: base/abstractarray.jl:3713-3714 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     deleteat!(a, i:lastindex(a))
--     return a
-- /Source

private abbrev KeepHeaderM := StateT BitVector KeepM

-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source
local instance : JuliaLean.base.range.JEltype KeepAxis I64 := ⟨⟩
-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source
local instance : JuliaLean.base.range.JFieldStop KeepAxis I64 :=
  ⟨JuliaLean.base.range.OneTo.stop⟩
-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source
local instance : JuliaLean.base.range.JLast KeepAxis I64 :=
  ⟨JuliaLean.base.range.last_OrdinalRange⟩
-- Source: base/range.jl:1141-1141 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- show(io::IO, r::OneTo) = print(io, "Base.OneTo(", r.stop, ")")
-- /Source
local instance : JuliaLean.base.range.JPrint I64 := ⟨fun n => toString n.val⟩

/-- Native range metadata bridge for base/abstractarray.jl:429.
Every native callee below is total; no unsupported exception branch is reachable.
The bridge preserves all actually reachable classes without inventing a value. -/
-- Source: base/abstractarray.jl:429-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- lastindex(a::AbstractArray) = (@inline; last(eachindex(IndexLinear(), a)))
-- /Source
private def keepRangeResult {α : Type} (r : JuliaLean.base.range.JlX α) : KeepArrayResult α :=
  r.mapError fun e => match e with
    | .jl e => .julia e
    | .dimensionMismatch msg => .dimensionMismatch msg
    | .errorException msg => .errorException msg
    | .showError e => .showError e
    | .inboundsViolation => .julia .boundsError

/-- Source error bridge for the two concrete _keepat! calls.
Only BoundsError, the explicit sorted-indices ArgumentError and a possible
native metadata error can arise from the abstractarray layer here. 
Julia source: base/abstractarray.jl:3699-3729. -/
-- Source: base/abstractarray.jl:3699-3729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _keepat!(a::AbstractVector, inds)
--     local prev
--     i = firstindex(a)
--     for k in inds
--         if @isdefined(prev)
--             prev < k || throw(ArgumentError("indices must be unique and sorted"))
--         end
--         ak = a[k] # must happen even when i==k for bounds checking
--         if i != k
--             @inbounds a[i] = ak # k > i, so a[i] is inbounds
--         end
--         prev = k
--         i = nextind(a, i)
--     end
--     deleteat!(a, i:lastindex(a))
--     return a
-- end
-- 
-- function _keepat!(a::AbstractVector, m::AbstractVector{Bool})
--     length(m) == length(a) || throw(BoundsError(a, m))
--     j = firstindex(a)
--     for i in eachindex(a, m)
--         @inbounds begin
--             if m[i]
--                 i == j || (a[j] = a[i])
--                 j = nextind(a, j)
--             end
--         end
--     end
--     deleteat!(a, j:lastindex(a))
-- end
-- /Source
private def keepError : JuliaLean.base.abstractarray.ArrayError → JuliaLean.base.array.Error
  | .julia (.argumentError msg) => .argument msg
  | .julia .boundsError => .bounds
  | .julia (.inexactError _) => .inexact
  | .julia (.overflowError _) => .overflow
  | .julia .divideError => .divide
  | .julia (.domainError msg) => .argument msg
  | .julia (.methodError name) => .method name
  | .julia .eofError => .method "EOFError"
  | .dimensionMismatch msg => .dimensionMismatch msg
  | .canonicalIndex f _ => .method f
  | .errorException msg => .argument msg
  | .assertionError msg => .assertion msg
  | .showError e => .showError e

/-- Adapter preserving underlying mutation errors and all writes made before a
later _keepat! error, base/abstractarray.jl:3699-3729. -/
-- Source: base/abstractarray.jl:3699-3729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _keepat!(a::AbstractVector, inds)
--     local prev
--     i = firstindex(a)
--     for k in inds
--         if @isdefined(prev)
--             prev < k || throw(ArgumentError("indices must be unique and sorted"))
--         end
--         ak = a[k] # must happen even when i==k for bounds checking
--         if i != k
--             @inbounds a[i] = ak # k > i, so a[i] is inbounds
--         end
--         prev = k
--         i = nextind(a, i)
--     end
--     deleteat!(a, i:lastindex(a))
--     return a
-- end
-- 
-- function _keepat!(a::AbstractVector, m::AbstractVector{Bool})
--     length(m) == length(a) || throw(BoundsError(a, m))
--     j = firstindex(a)
--     for i in eachindex(a, m)
--         @inbounds begin
--             if m[i]
--                 i == j || (a[j] = a[i])
--                 j = nextind(a, j)
--             end
--         end
--     end
--     deleteat!(a, j:lastindex(a))
-- end
-- /Source
private def keepRun {α : Type} (action : KeepM α) : BitMutationM α := do
  match ← action.run with
  | .ok value => return value
  | .error error => throw (keepError error)

/-- Lift concrete metadata results for base/abstractarray.jl:3699-3729 into the local error channel. -/
-- Source: base/abstractarray.jl:3699-3729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _keepat!(a::AbstractVector, inds)
--     local prev
--     i = firstindex(a)
--     for k in inds
--         if @isdefined(prev)
--             prev < k || throw(ArgumentError("indices must be unique and sorted"))
--         end
--         ak = a[k] # must happen even when i==k for bounds checking
--         if i != k
--             @inbounds a[i] = ak # k > i, so a[i] is inbounds
--         end
--         prev = k
--         i = nextind(a, i)
--     end
--     deleteat!(a, i:lastindex(a))
--     return a
-- end
-- 
-- function _keepat!(a::AbstractVector, m::AbstractVector{Bool})
--     length(m) == length(a) || throw(BoundsError(a, m))
--     j = firstindex(a)
--     for i in eachindex(a, m)
--         @inbounds begin
--             if m[i]
--                 i == j || (a[j] = a[i])
--                 j = nextind(a, j)
--             end
--         end
--     end
--     deleteat!(a, j:lastindex(a))
-- end
-- /Source
private def keepLiftArray {α : Type} (r : KeepArrayResult α) : KeepM α :=
  ExceptT.mk (pure r)

/-- Lift actual shared-heap operations for base/abstractarray.jl:3699-3729 without rolling back earlier writes. -/
-- Source: base/abstractarray.jl:3699-3729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _keepat!(a::AbstractVector, inds)
--     local prev
--     i = firstindex(a)
--     for k in inds
--         if @isdefined(prev)
--             prev < k || throw(ArgumentError("indices must be unique and sorted"))
--         end
--         ak = a[k] # must happen even when i==k for bounds checking
--         if i != k
--             @inbounds a[i] = ak # k > i, so a[i] is inbounds
--         end
--         prev = k
--         i = nextind(a, i)
--     end
--     deleteat!(a, i:lastindex(a))
--     return a
-- end
-- 
-- function _keepat!(a::AbstractVector, m::AbstractVector{Bool})
--     length(m) == length(a) || throw(BoundsError(a, m))
--     j = firstindex(a)
--     for i in eachindex(a, m)
--         @inbounds begin
--             if m[i]
--                 i == j || (a[j] = a[i])
--                 j = nextind(a, j)
--             end
--         end
--     end
--     deleteat!(a, j:lastindex(a))
-- end
-- /Source
private def keepLiftMutation {α : Type} (action : BitMutationM α) : KeepM α :=
  ExceptT.mk (do return .ok (← action))

/-- Local object-header state gives the immutable BitVector representation the
source's updated header after `_keepat!` returns `a`, base/abstractarray.jl:3714.
The actual UInt64 storage remains the existing shared mutable heap. -/
-- Source: base/abstractarray.jl:3713-3714 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     deleteat!(a, i:lastindex(a))
--     return a
-- /Source
private def keepHeaderLift {α : Type} (action : KeepM α) : KeepHeaderM α :=
  fun header => do
    let value ← action
    return (value, header)

/-- Actual axes/eachindex chain for a BitVector, base/abstractarray.jl:396.
The ranked size callee reads len, including vectors whose unused dims is stale. -/
-- Source: base/abstractarray.jl:396-396 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexLinear, A::AbstractVector) = (@inline; axes1(A))
-- /Source
private def keepAxis (B : BitVector) : KeepArrayResult KeepAxis :=
  JuliaLean.base.abstractarray.eachindexLinearVector
    (JuliaLean.base.abstractarray.axes1
      (JuliaLean.base.abstractarray.axesDefault
        (fun (B : BitVector) => pure (bitArraySizeRanked B))
        JuliaLean.base.range.unchecked_oneto)) B

/-- Concrete firstindex dependency at base/abstractarray.jl:452. -/
-- Source: base/abstractarray.jl:452-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- firstindex(a::AbstractArray) = (@inline; first(eachindex(IndexLinear(), a)))
-- /Source
private def keepFirstindex (B : BitVector) : KeepArrayResult I64 :=
  JuliaLean.base.abstractarray.firstindexArray keepAxis
    (fun r => pure (JuliaLean.base.range.first_OneTo r)) B

/-- Concrete lastindex dependency at base/abstractarray.jl:429. -/
-- Source: base/abstractarray.jl:429-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- lastindex(a::AbstractArray) = (@inline; last(eachindex(IndexLinear(), a)))
-- /Source
private def keepLastindex (B : BitVector) : KeepArrayResult I64 :=
  JuliaLean.base.abstractarray.lastindexArray keepAxis
    (fun r => keepRangeResult (JuliaLean.base.range.last_OrdinalRange r)) B

/-- Concrete nextind dependency at base/abstractarray.jl:220, retaining native wrapping addition. -/
-- Source: base/abstractarray.jl:220-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- nextind(::AbstractArray, i::Integer) = Int(i)+1
-- /Source
private def keepNextindex (B : BitVector) (i : I64) : KeepArrayResult I64 :=
  JuliaLean.base.abstractarray.nextind
    (fun x => JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .i64 x)) B i

/-- Concrete nonempty _join_comma_and arities from base/abstractarray.jl:329-330. -/
-- Source: base/abstractarray.jl:329-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _join_comma_and(indsA, indsB) = LazyString(indsA, " and ", indsB)
-- _join_comma_and(indsA, indsB, indsC...) = LazyString(indsA, ", ", _join_comma_and(indsB, indsC...))
-- /Source
private def keepJoinMany (a b : String) : List String → String
  | [] => JuliaLean.base.abstractarray.joinCommaAndTwo a b
  | c :: cs => JuliaLean.base.abstractarray.joinCommaAndMany
      (fun next _ => keepJoinMany next c cs) a b (c :: cs)

/-- The singleton other-axis case used by eachindex(A,mask); the list shape is
fixed by the two arguments, and no generic formatting callback is a model input. 
Julia source: base/abstractarray.jl:329-335. -/
-- Source: base/abstractarray.jl:329-335 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _join_comma_and(indsA, indsB) = LazyString(indsA, " and ", indsB)
-- _join_comma_and(indsA, indsB, indsC...) = LazyString(indsA, ", ", _join_comma_and(indsB, indsC...))
-- @noinline function throw_eachindex_mismatch_indices(indices_str, indsA, indsBs...)
--     throw(DimensionMismatch(
--             LazyString("all inputs to eachindex must have the same ", indices_str, ", got ",
--                 _join_comma_and(indsA, indsBs...))))
-- end
-- /Source
private def keepAxisMismatch (a : KeepAxis) (bs : List KeepAxis) : KeepArrayResult KeepAxis := do
  let text ← keepRangeResult (JuliaLean.base.range.show_OneTo ⟨⟩ a)
  let texts ← bs.mapM (fun r => keepRangeResult (JuliaLean.base.range.show_OneTo ⟨⟩ r))
  match texts with
  | [] => throw (.julia (.methodError "_join_comma_and"))
  | other :: others =>
      JuliaLean.base.abstractarray.throwEachindexMismatch
        (fun first _ => keepJoinMany first other others) "indices" text texts

/-- Source eachindex(IndexLinear(),A,mask), base/abstractarray.jl:397-404.
The prior length equality check in _keepat! makes the mismatch path unreachable,
but it is still bound to an actual throwing callee rather than a success value. -/
-- Source: base/abstractarray.jl:397-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function eachindex(::IndexLinear, A::AbstractArray, B::AbstractArray...)
--     @inline
--     indsA = eachindex(IndexLinear(), A)
--     indsBs = map(X -> eachindex(IndexLinear(), X), B)
--     all(==(indsA), indsBs) ||
--         throw_eachindex_mismatch_indices("indices", indsA, indsBs...)
--     indsA
-- end
-- /Source
private def keepEachindex (B mask : BitVector) : KeepArrayResult (List I64) := do
  let axis ← JuliaLean.base.abstractarray.eachindexLinearMany
    (A := BitVector) (n := 1) (B := fun _ => BitVector)
    keepAxis (fun _ => keepAxis)
    (fun a b => JuliaLean.base.int.eq_int a.stop b.stop)
    keepAxisMismatch B (fun _ => mask)
  return intRange (int 1) axis.stop

/-- Concrete `_keepat!(a, inds)` instance at base/abstractarray.jl:3699-3715,
where inds is an immutable Julia tuple of native Int indices, represented by a
machine-sized List. Source for-loop traversal is represented by ForIn, as in the
installed callee; tuple elements have no effects or overrides.

The local BitVector header state is essential: the installed callee returns its
original object reference after deleteat!, so a plain immutable-header binding
would return the old len. All content accesses use the current shared heap. -/
-- Source: base/abstractarray.jl:3699-3715 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _keepat!(a::AbstractVector, inds)
--     local prev
--     i = firstindex(a)
--     for k in inds
--         if @isdefined(prev)
--             prev < k || throw(ArgumentError("indices must be unique and sorted"))
--         end
--         ak = a[k] # must happen even when i==k for bounds checking
--         if i != k
--             @inbounds a[i] = ak # k > i, so a[i] is inbounds
--         end
--         prev = k
--         i = nextind(a, i)
--     end
--     deleteat!(a, i:lastindex(a))
--     return a
-- end
-- /Source
private def keepNativeTupleBody (B : BitVector) (indices : List I64) : BitMutationM BitVector := do
  let action : KeepHeaderM Unit :=
    JuliaLean.base.abstractarray.keepAtIndices
      (m := KeepHeaderM) (A := Unit) (I := I64) (K := I64) (E := Bool)
      (Range := KeepRange) (Ret := BitVector)
      (fun _ => do
        let header : BitVector ← get
        keepHeaderLift (keepLiftArray (keepFirstindex header)))
      (fun _ => do
        let header : BitVector ← get
        keepHeaderLift (keepLiftArray (keepLastindex header)))
      (fun a b => pure (JuliaLean.base.int.lt_BitSigned a b))
      (fun a b => pure (JuliaLean.base.int.eq_int a b))
      (fun _ i => do
        let header : BitVector ← get
        keepHeaderLift (keepLiftMutation (getBit header i)))
      (fun _ i value => do
        let header : BitVector ← get
        keepHeaderLift (keepLiftMutation (unsafeBitSetIndex header.chunks value i)))
      (fun _ i => do
        let header : BitVector ← get
        keepHeaderLift (keepLiftArray (keepNextindex header i)))
      (fun first last => keepHeaderLift (keepLiftMutation
        (resizeLiftRange (JuliaLean.base.range.colon_T_T_Real first last))))
      (fun _ r => do
        let header : BitVector ← get
        let updated ← keepHeaderLift (keepLiftMutation (deleteNativeTailRange header r))
        set updated
        return updated)
      () indices
  let (_, updated) ← keepRun (action.run B)
  return updated

/-- Usable native-Int-tuple specialization of base/bitarray.jl:1063.
The full generic iterable row remains blocked on its other dispatch/effect domains. -/
-- Source: base/bitarray.jl:1063-1063 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keepat!(B::BitVector, inds) = _keepat!(B, inds)
-- /Source
def keepNativeTuple (B : BitVector) (indices : List I64) : BitMutationM BitVector :=
  bitVectorKeepAt keepNativeTupleBody B indices

/-- Concrete BitVector-mask instance of base/abstractarray.jl:3717-3729.
Every mask test is a live read, including when B and mask partially overlap in
shared storage. Scalar writes preserve their other chunk bits. The installed
callee returns the actual shortened BitVector from the tail delete operation. -/
-- Source: base/abstractarray.jl:3717-3729 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _keepat!(a::AbstractVector, m::AbstractVector{Bool})
--     length(m) == length(a) || throw(BoundsError(a, m))
--     j = firstindex(a)
--     for i in eachindex(a, m)
--         @inbounds begin
--             if m[i]
--                 i == j || (a[j] = a[i])
--                 j = nextind(a, j)
--             end
--         end
--     end
--     deleteat!(a, j:lastindex(a))
-- end
-- /Source
private def keepBitMaskBody (B mask : BitVector) : BitMutationM BitVector :=
  keepRun (JuliaLean.base.abstractarray.keepAtMask
    (m := KeepM) (A := BitVector) (Mask := BitVector) (I := I64) (E := Bool)
    (Indices := List I64) (Range := KeepRange) (Ret := BitVector)
    (fun a => pure a.len) (fun a => pure a.len)
    (fun a => keepLiftArray (keepFirstindex a))
    (fun a => keepLiftArray (keepLastindex a))
    (fun a m => keepLiftArray (keepEachindex a m))
    (fun m i => keepLiftMutation (unsafeBitGetIndex m.chunks i))
    (fun a i => keepLiftMutation (unsafeBitGetIndex a.chunks i))
    (fun a i value => keepLiftMutation (unsafeBitSetIndex a.chunks value i))
    (fun a i => keepLiftArray (keepNextindex a i))
    (fun first last => keepLiftMutation
      (resizeLiftRange (JuliaLean.base.range.colon_T_T_Real first last)))
    (fun a r => keepLiftMutation (deleteNativeTailRange a r)) B mask)

/-- Usable live-BitVector-mask specialization of base/bitarray.jl:1064.
Other AbstractVector{Bool} implementations, including offset indexing and custom
accessors, remain outside this explicitly partial row. -/
-- Source: base/bitarray.jl:1064-1064 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keepat!(B::BitVector, inds::AbstractVector{Bool}) = _keepat!(B, inds)
-- /Source
def keepBitMask (B mask : BitVector) : BitMutationM BitVector :=
  bitVectorKeepAtMask keepBitMaskBody B mask

end KeepAtBindings

/-- Read-only source storage paired with the existing mutable native-Int store.
This is a composition of supplied heap models at their explicit primitive boundary,
not an extra caller-supplied implementation. The assigned source never writes its
UInt64 input and always creates fresh Int output storage. Hence cross-type aliases
among pre-existing arrays cannot be observed by this method. Partial output writes
survive an exception because MutationM is ExceptT outside StateM.
Julia source: base/bitarray.jl:1145-1172. -/
-- Source: base/bitarray.jl:1145-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function (-)(B::BitArray)
--     A = zeros(Int, size(B))
--     l = length(B)
--     l == 0 && return A
--     Bc = B.chunks
--     ind = 1
--     for i = 1:length(Bc)-1
--         u = UInt64(1)
--         c = Bc[i]
--         for _ = 1:64
--             if c & u != 0
--                 A[ind] = -1
--             end
--             ind += 1
--             u <<= 1
--         end
--     end
--     u = UInt64(1)
--     c = Bc[end]
--     for _ = 0:_mod64(l-1)
--         if c & u != 0
--             A[ind] = -1
--         end
--         ind += 1
--         u <<= 1
--     end
--     return A
-- end
-- /Source

abbrev UnaryMinusM := ReaderT (JuliaLean.base.array.MutableMemory U64)
  (JuliaLean.base.array.MutationM I64)

/-- The supplied typed mutable getter, projected into the read-only input component.
This specific primitive never modifies its state; no arbitrary action is accepted.
Julia source: base/bitarray.jl:1153,1163. -/
-- Source: base/bitarray.jl:1151-1153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     for i = 1:length(Bc)-1
--         u = UInt64(1)
--         c = Bc[i]
-- /Source

-- Source: base/bitarray.jl:1162-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     u = UInt64(1)
--     c = Bc[end]
-- /Source

private def unaryMinusRead (input : JuliaLean.base.array.MutableMemory U64)
    (handle : Nat) (i : I64) : JuliaLean.base.array.MutationM I64 U64 :=
  match (JuliaLean.base.array.mutableGet (α := U64) handle i).run input with
  | (.ok value, _) => pure value
  | (.error error, _) => throw error

/-- Source chunk length, using the installed header primitive on the read-only
input store. Julia source: base/bitarray.jl:1151,1163. -/
-- Source: base/bitarray.jl:1151-1151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     for i = 1:length(Bc)-1
-- /Source

-- Source: base/bitarray.jl:1163-1163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     c = Bc[end]
-- /Source

private def unaryMinusChunkLength (input : JuliaLean.base.array.MutableMemory U64)
    (handle : Nat) : JuliaLean.base.array.MutationM I64 I64 :=
  match (JuliaLean.base.array.mutableLength (α := U64) handle).run input with
  | (.ok value, _) => pure value
  | (.error error, _) => throw error

/-- Native Int allocation metadata at the existing array.MemoryLayout boundary:
eight inline, non-union bytes. Signedness changes values, not these allocation
fields. Julia source: base/boot.jl:286; base/bitarray.jl:1146. -/
-- Source: base/boot.jl:286-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- #primitive type Int64   <: Signed   64 end
-- #primitive type UInt64  <: Unsigned 64 end
-- /Source

-- Source: base/bitarray.jl:1146-1146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     A = zeros(Int, size(B))
-- /Source

private def unaryMinusIntLayout : JuliaLean.base.array.MemoryLayout :=
  ⟨JuliaLean.base.int.sizeofT .i64, false, false⟩

/-- Actual Array{Int,N}(undef, dims) constructor dispatch, including checked_dims
and the supplied GenericMemory allocation limit. The existing HeapArray metadata
records rank and axes, while MutableVector records the underlying linear window.
The constructor's explicit `header` boundary appends the fresh header. Its length
comes from the allocated memory request, with no repeated dimension arithmetic.
Julia source: base/boot.jl:821-845; base/array.jl:638. -/
-- Source: base/boot.jl:821-845 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eval(Core, :(function (self::Type{Array{T,1}})(::UndefInitializer, m::Int) where {T}
--     mem = fieldtype(fieldtype(self, :ref), :mem)(undef, m)
--     return $(Expr(:new, :self, :(memoryref(mem)), :((m,))))
-- end))
-- eval(Core, :(function (self::Type{Array{T,2}})(::UndefInitializer, m::Int, n::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n))), :((m, n))))
-- end))
-- eval(Core, :(function (self::Type{Array{T,3}})(::UndefInitializer, m::Int, n::Int, o::Int) where {T}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(m, n, o))), :((m, n, o))))
-- end))
-- eval(Core, :(function (self::Type{Array{T, N}})(::UndefInitializer, d::Vararg{Int, N}) where {T, N}
--     return $(Expr(:new, :self, :(new_as_memoryref(fieldtype(self, :ref), checked_dims(d...))), :d))
-- end))
-- # type and dimensionality specified, accepting dims as tuples of Ints
-- (self::Type{Array{T,1}})(::UndefInitializer, d::NTuple{1, Int}) where {T} = self(undef, getfield(d, 1))
-- (self::Type{Array{T,2}})(::UndefInitializer, d::NTuple{2, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2))
-- (self::Type{Array{T,3}})(::UndefInitializer, d::NTuple{3, Int}) where {T} = self(undef, getfield(d, 1), getfield(d, 2), getfield(d, 3))
-- (self::Type{Array{T,N}})(::UndefInitializer, d::NTuple{N, Int}) where {T, N} = self(undef, d...)
-- # type but not dimensionality specified
-- Array{T}(::UndefInitializer, m::Int) where {T} = Array{T, 1}(undef, m)
-- Array{T}(::UndefInitializer, m::Int, n::Int) where {T} = Array{T, 2}(undef, m, n)
-- Array{T}(::UndefInitializer, m::Int, n::Int, o::Int) where {T} = Array{T, 3}(undef, m, n, o)
-- # Guard against invalidations due to spurious `Tuple{}` intersections
-- Array{T}(::UndefInitializer, ::Tuple{}) where {T} = Array{T, 0}(undef)
-- Array{T}(::UndefInitializer, d::NTuple{N, Int}) where {T, N} = Array{T, N}(undef, d)
-- /Source

-- Source: base/array.jl:637-641 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         function $fname(::Type{T}, dims::NTuple{N, Integer}) where {T,N}
--             a = Array{T,N}(undef, dims)
--             fill!(a, $felt(T))
--             return a
--         end
-- /Source

private def unaryMinusAllocate (dims : List I64) :
    JuliaLean.base.array.MutationM I64 (JuliaLean.base.array.HeapArray IntTy) :=
  JuliaLean.base.array.arrayUndef (some unaryMinusIntLayout)
    (do
      let memory ← JuliaLean.base.array.mutableFreshMemory (α := I64) 0
      pure (memory, int 0))
    (fun count : Nat => do
      let memory ← JuliaLean.base.array.mutableFreshMemory (α := I64) count
      pure (memory, int (count : Int)))
    (fun allocation ds => do
      let state ← get
      let handle := state.arrays.length
      set { state with arrays := state.arrays ++
        [JuliaLean.base.array.MutableVector.mk (allocation.1, int 1) allocation.2] }
      pure ⟨handle, .i64, ds.map (fun d => d.val.toNat),
        ds.map (fun d => ((1 : Int), d.val.toNat))⟩)
    dims

/-- Public native-Int scalar assignment selects its already-typed branch, then
the supplied checked mutable setter. It retains BoundsError if an excess source
chunk causes unary minus to write beyond the logical output.
Julia source: base/array.jl:1031-1041; base/bitarray.jl:1156,1166. -/
-- Source: base/array.jl:1031-1041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function setindex!(A::Array{T}, x, i::Int) where {T}
--     @_propagate_inbounds_meta
--     x = x isa T ? x : convert(T, x)::T
--     return _setindex!(A, x, i)
-- end
-- function _setindex!(A::Array{T}, x::T, i::Int) where {T}
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefset!(memoryrefnew(A.ref, i, false), x, :not_atomic, false)
--     return A
-- end
-- /Source

private def unaryMinusSet (A : JuliaLean.base.array.HeapArray IntTy) (value : I64)
    (i : I64) : JuliaLean.base.array.MutationM I64 Unit := do
  let _ ← JuliaLean.base.array.setindexScalar (fun _ : I64 => true) (fun x => x)
    pure (JuliaLean.base.array.mutableTypedSet (α := I64)) A.handle value i
  pure ()

/-- Native Int zero uses the installed zero(::Type) and same-number conversion.
The closed call succeeds; the explicit error cases keep the bridge total without
inventing a fallback value. Julia source: base/number.jl:6,364. -/
-- Source: base/number.jl:6-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, x::T)      where {T<:Number} = x
-- /Source

-- Source: base/number.jl:364-364 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- zero(::Type{T}) where {T<:Number} = convert(T,0)
-- /Source

private def unaryMinusZero : JuliaLean.base.array.MutationM I64 I64 :=
  match JuliaLean.base.number.zeroType
    (fun _ : Unit => fun n => pure (JuliaLean.base.number.convertSame (int n))) () with
  | .ok value => pure value
  | .error (.inexactError _) => throw .inexact
  | .error (.overflowError _) => throw .overflow
  | .error .boundsError => throw .bounds
  | .error .divideError => throw .divide
  | .error (.argumentError message) => throw (.argument message)
  | .error (.domainError message) => throw (.argument message)
  | .error (.methodError name) => throw (.method name)
  | .error .eofError => throw (.method "EOFError")

/-- Actual fill! / _fill! with the native Int value and dense linear indices.
The zero fill occurs once, before the bit scan, as in zeros(Int, size(B)).
Julia source: base/array.jl:368-378; base/abstractarray.jl:394. -/
-- Source: base/array.jl:368-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill!(A::AbstractArray{T}, x) where T
--     @inline
--     xT = x isa T ? x : convert(T, x)::T
--     return _fill!(A, xT)
-- end
-- function _fill!(A::AbstractArray{T}, x::T) where T
--     for i in eachindex(A)
--         A[i] = x
--     end
--     return A
-- end
-- /Source

-- Source: base/abstractarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexLinear, A::Union{Array, Memory}) = unchecked_oneto(length(A))
-- /Source

private def unaryMinusFill (A : JuliaLean.base.array.HeapArray IntTy) (value : I64) :
    JuliaLean.base.array.MutationM I64 (JuliaLean.base.array.HeapArray IntTy) :=
  JuliaLean.base.array.fillBang (fun _ : I64 => true) (fun x => x) pure
    (fun array element => JuliaLean.base.array.fillTyped
      (fun array => do
        let axis ← JuliaLean.base.abstractarray.eachindexDense
          (fun array : JuliaLean.base.array.HeapArray IntTy =>
            JuliaLean.base.array.mutableLength (α := I64) array.handle)
          (JuliaLean.base.range.unchecked_oneto (T := I64)) array
        pure (intRange (int 1) axis.stop))
      unaryMinusSet array element)
    A value

/-- The generated zeros methods, selecting the explicit empty-tuple method at
rank zero. Every constructor/fill callee is concrete and already source-modelled.
Julia source: base/array.jl:631-646; base/bitarray.jl:1146. -/
-- Source: base/array.jl:631-653 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (fname, felt) in ((:zeros, :zero), (:ones, :one))
--     @eval begin
--         $fname(dims::DimOrInd...) = $fname(dims)
--         $fname(::Type{T}, dims::DimOrInd...) where {T} = $fname(T, dims)
--         $fname(dims::Tuple{Vararg{DimOrInd}}) = $fname(Float64, dims)
--         $fname(::Type{T}, dims::NTuple{N, Union{Integer, OneTo}}) where {T,N} = $fname(T, map(to_dim, dims))
--         function $fname(::Type{T}, dims::NTuple{N, Integer}) where {T,N}
--             a = Array{T,N}(undef, dims)
--             fill!(a, $felt(T))
--             return a
--         end
--         function $fname(::Type{T}, dims::Tuple{}) where {T}
--             a = Array{T}(undef)
--             fill!(a, $felt(T))
--             return a
--         end
--         function $fname(::Type{T}, dims::NTuple{N, DimOrInd}) where {T,N}
--             a = similar(Array{T,N}, dims)
--             fill!(a, $felt(T))
--             return a
--         end
--     end
-- end
-- /Source

private def unaryMinusZeros (dims : List I64) :
    JuliaLean.base.array.MutationM I64 (JuliaLean.base.array.HeapArray IntTy) :=
  match dims with
  | [] => JuliaLean.base.array.constant642 unaryMinusAllocate unaryMinusZero unaryMinusFill []
  | _ => JuliaLean.base.array.constant637 unaryMinusAllocate unaryMinusZero unaryMinusFill dims

/-- Unary minus for every BitArray rank. Reuses native zeros/Array allocation and
typed setters, reads source length, uses rank-correct size, and retains the exact
conditional -1 writes. The frozen template's unconditional zero writes and raw
rank-one dims are not used. The state composition boundary is UnaryMinusM above.
Julia source: base/bitarray.jl:1145-1172. -/
-- Source: base/bitarray.jl:1145-1172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function (-)(B::BitArray)
--     A = zeros(Int, size(B))
--     l = length(B)
--     l == 0 && return A
--     Bc = B.chunks
--     ind = 1
--     for i = 1:length(Bc)-1
--         u = UInt64(1)
--         c = Bc[i]
--         for _ = 1:64
--             if c & u != 0
--                 A[ind] = -1
--             end
--             ind += 1
--             u <<= 1
--         end
--     end
--     u = UInt64(1)
--     c = Bc[end]
--     for _ = 0:_mod64(l-1)
--         if c & u != 0
--             A[ind] = -1
--         end
--         ind += 1
--         u <<= 1
--     end
--     return A
-- end
-- /Source

def unaryMinus {N : Nat} (B : BitArray N) :
    UnaryMinusM (JuliaLean.base.array.HeapArray IntTy) := fun input => do
  let A ← unaryMinusZeros (bitArraySizeRanked B)
  let l := bitArrayLength B
  if l == int 0 then return A
  let Bc := B.chunks
  let mut ind := int 1
  for i in intRange (int 1) ((← unaryMinusChunkLength input Bc) - int 1) do
    let mut u := u64 1
    let c ← unaryMinusRead input Bc i
    for _ in intRange (int 1) (int 64) do
      if JuliaLean.base.operators.notEqual JuliaLean.base.int.eq Bool.not
          (and_int c u) (int 0) then
        unaryMinusSet A (int (-1)) ind
      ind := ind + int 1
      u := JuliaLean.base.int.shl_Int u (int 1)
  let mut u := u64 1
  let c ← unaryMinusRead input Bc (← unaryMinusChunkLength input Bc)
  for _ in intRange (int 0) (mod64 (l - int 1)) do
    if JuliaLean.base.operators.notEqual JuliaLean.base.int.eq Bool.not
        (and_int c u) (int 0) then
      unaryMinusSet A (int (-1)) ind
    ind := ind + int 1
    u := JuliaLean.base.int.shl_Int u (int 1)
  pure A

/-- The two functions generated at base/bitarray.jl:1176-1190. A finite dispatch
tag replaces only the Julia function singleton, never an implementation callback. -/
-- Source: base/bitarray.jl:1176-1190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for f in (:+, :-)
--     @eval function ($f)(A::BitArray, B::BitArray)
--         r = Array{Int}(undef, promote_shape(size(A), size(B)))
--         ay, by = iterate(A), iterate(B)
--         ri = 1
--         # promote_shape guarantees that A and B have the
--         # same iteration space
--         while ay !== nothing
--             @inbounds r[ri] = ($f)(ay[1], by[1])
--             ri += 1
--             ay, by = iterate(A, ay[2]), iterate(B, by[2])
--         end
--         return r
--     end
-- end
-- /Source

inductive ArithmeticFunction where
  | add
  | subtract

/-- Actual Bool arithmetic returns native Int, through the installed Bool methods.
Julia source: base/bool.jl:145-146; base/bitarray.jl:1184. -/
-- Source: base/bool.jl:145-146 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- +(x::Bool, y::Bool) = Int(x) +% Int(y)
-- -(x::Bool, y::Bool) = Int(x) -% Int(y)
-- /Source

-- Source: base/bitarray.jl:1183-1186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         while ay !== nothing
--             @inbounds r[ri] = ($f)(ay[1], by[1])
--             ri += 1
--             ay, by = iterate(A, ay[2]), iterate(B, by[2])
-- /Source

private def arithmeticNative (f : ArithmeticFunction) (a b : Bool) : I64 :=
  match f with
  | .add => JuliaLean.base.bool.addBool a b
  | .subtract => JuliaLean.base.bool.subBool a b

/-- The installed shape-mismatch function over its full Int/range value family.
The existing Dims promotion templates require ShapeCallees I64, whose colon field
cannot represent a UnitRange; this additive interface repair retains the actual
throw callee instead of supplying a fake unreachable colon. All input entries
here are native Int dimensions, and the existing tuple printer preserves their
Julia punctuation. Julia source: base/indices.jl:112-137. -/
-- Source: base/indices.jl:112-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function throw_promote_shape_mismatch(a::Tuple, b::Union{Nothing,Tuple}, i = nothing)
--     if a isa Tuple{Vararg{Base.OneTo}} && (b === nothing || b isa Tuple{Vararg{Base.OneTo}})
--         a = map(lastindex, a)::Dims
--         b === nothing || (b = map(lastindex, b)::Dims)
--     end
--     _has_axes = !(a isa Dims && (b === nothing || b isa Dims))
--     if _has_axes
--         _normalize(d) = map(x -> firstindex(x):lastindex(x), d)
--         a = _normalize(a)
--         b === nothing || (b = _normalize(b))
--         _things = "axes "
--     else
--         _things = "size "
--     end
--     msg = IOBuffer()
--     print(msg, "a has ", _things)
--     print(msg, a)
--     if b ≢ nothing
--         print(msg, ", b has ", _things)
--         print(msg, b)
--     end
--     if i ≢ nothing
--         print(msg, ", mismatch at dim ", i)
--     end
--     throw(DimensionMismatch(takestring!(msg)))
-- end
-- /Source

private def arithmeticShapeMismatch (a : List I64) (b : Option (List I64))
    (dimension : Option I64 := none) : ShapeR Unit :=
  JuliaLean.base.indices.throw_promote_shape_mismatch binaryShapeCalls
    (a.map fun n => (.integer n : ShapeEntry))
    (b.map fun dims => dims.map fun n => (.integer n : ShapeEntry)) dimension

/-- Exact singleton Dims promotion after repairing only the mismatch interface.
Julia source: base/indices.jl:139-142. -/
-- Source: base/indices.jl:139-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function promote_shape(a::Tuple{Int,}, b::Tuple{Int,})
--     a[1] != b[1] && throw_promote_shape_mismatch(a, b)
--     return a
-- end
-- /Source

private def arithmeticPromoteOneOne (a b : I64) : ShapeR (List I64) := do
  if a ≠ b then arithmeticShapeMismatch [a] (some [b])
  pure [a]

/-- Exact two-dimension/one-dimension specialization, including short-circuit
comparison and its mismatch without a dimension suffix.
Julia source: base/indices.jl:144-147. -/
-- Source: base/indices.jl:144-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function promote_shape(a::Tuple{Int,Int}, b::Tuple{Int,})
--     (a[1] != b[1] || a[2] != 1) && throw_promote_shape_mismatch(a, b)
--     return a
-- end
-- /Source

private def arithmeticPromoteTwoOne (a b : I64) (c : I64) : ShapeR (List I64) := do
  if a ≠ c ∨ b ≠ int 1 then arithmeticShapeMismatch [a, b] (some [c])
  pure [a, b]

/-- Exact two-dimension/two-dimension specialization, retaining its source
error point and tuple order. Julia source: base/indices.jl:151-154. -/
-- Source: base/indices.jl:151-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function promote_shape(a::Tuple{Int, Int}, b::Tuple{Int, Int})
--     (a[1] != b[1] || a[2] != b[2]) && throw_promote_shape_mismatch(a, b)
--     return a
-- end
-- /Source

private def arithmeticPromoteTwoTwo (a b c d : I64) : ShapeR (List I64) := do
  if a ≠ c ∨ b ≠ d then arithmeticShapeMismatch [a, b] (some [c, d])
  pure [a, b]

/-- The supplied tuple length observation, carried as Julia's native Int before
comparison or arithmetic. Readable ties this tuple length to a rank below 2^63.
Julia source: base/tuple.jl:28; base/indices.jl:176,179,182. -/
-- Source: base/tuple.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(@nospecialize t::Tuple) = nfields(t)
-- /Source

-- Source: base/indices.jl:175-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function promote_shape(a::Dims, b::Dims)
--     if length(a) < length(b)
--         return promote_shape(b, a)
--     end
--     for i=1:length(b)
--         a[i] != b[i] && throw_promote_shape_mismatch(a, b, i)
--     end
--     for i=length(b)+1:length(a)
--         a[i] != 1 && throw_promote_shape_mismatch(a, nothing, i)
--     end
--     return a
-- end
-- /Source

private def arithmeticTupleLength (dims : List I64) : I64 :=
  int (JuliaLean.base.tuple.lengthTuple dims)

/-- Checked native tuple indexing at the supplied abstractarray tuple boundary.
Its only failure is BoundsError, retained by the class-preserving bridge. No
get! default is used, including after native loop-bound overflow.
Julia source: base/tuple.jl:33; base/indices.jl:180,183. -/
-- Source: base/tuple.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- getindex(@nospecialize(t::Tuple), i::Int) = getfield(t, i, @_boundscheck)
-- /Source

-- Source: base/indices.jl:179-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     for i=1:length(b)
--         a[i] != b[i] && throw_promote_shape_mismatch(a, b, i)
--     end
--     for i=length(b)+1:length(a)
--         a[i] != 1 && throw_promote_shape_mismatch(a, nothing, i)
--     end
-- /Source

private def arithmeticTupleGet (dims : List I64) (i : I64) : ShapeR I64 :=
  binaryLiftArray (JuliaLean.base.abstractarray.tupleGet dims i)

/-- Source Dims loop with only the unusable mismatch-callee carrier repaired.
Unlike the axes variant, a trailing dimension is compared with native Int one.
Both ranges, the second range's +1, and tuple-length comparisons use native Int.
The actual tuple getter preserves the error from any wrapped or invalid index.
The sole recursive swap terminates because strict native order is asymmetric.
Julia source: base/indices.jl:175-186. -/
-- Source: base/indices.jl:175-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function promote_shape(a::Dims, b::Dims)
--     if length(a) < length(b)
--         return promote_shape(b, a)
--     end
--     for i=1:length(b)
--         a[i] != b[i] && throw_promote_shape_mismatch(a, b, i)
--     end
--     for i=length(b)+1:length(a)
--         a[i] != 1 && throw_promote_shape_mismatch(a, nothing, i)
--     end
--     return a
-- end
-- /Source

private def arithmeticPromoteDimsGeneral (a b : List I64) : ShapeR (List I64) :=
  if h : arithmeticTupleLength a < arithmeticTupleLength b then
    arithmeticPromoteDimsGeneral b a
  else do
    for i in intRange (int 1) (arithmeticTupleLength b) do
      let ai ← arithmeticTupleGet a i
      let bi ← arithmeticTupleGet b i
      if ai ≠ bi then arithmeticShapeMismatch a (some b) (some i)
    for i in intRange (arithmeticTupleLength b + int 1) (arithmeticTupleLength a) do
      let ai ← arithmeticTupleGet a i
      if ai ≠ int 1 then arithmeticShapeMismatch a none (some i)
    pure a
termination_by if arithmeticTupleLength a < arithmeticTupleLength b then 1 else 0
decreasing_by
  have reverseFalse : ¬ arithmeticTupleLength b < arithmeticTupleLength a := by
    change ¬ (arithmeticTupleLength b).val < (arithmeticTupleLength a).val
    have forward : (arithmeticTupleLength a).val < (arithmeticTupleLength b).val := h
    omega
  simp_all

/-- Actual promote_shape Dims dispatch, including the four small-tuple methods
and empty-tuple method. The tuple entries stay Ints throughout; this does not use
zip shape rules or replace Dims by axes. Julia source: base/indices.jl:108,139-186. -/
-- Source: base/indices.jl:108-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- promote_shape(::Tuple{}, ::Tuple{}) = ()
-- /Source

-- Source: base/indices.jl:139-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function promote_shape(a::Tuple{Int,}, b::Tuple{Int,})
--     a[1] != b[1] && throw_promote_shape_mismatch(a, b)
--     return a
-- end
-- 
-- function promote_shape(a::Tuple{Int,Int}, b::Tuple{Int,})
--     (a[1] != b[1] || a[2] != 1) && throw_promote_shape_mismatch(a, b)
--     return a
-- end
-- 
-- promote_shape(a::Tuple{Int,}, b::Tuple{Int,Int}) = promote_shape(b, a)
-- 
-- function promote_shape(a::Tuple{Int, Int}, b::Tuple{Int, Int})
--     (a[1] != b[1] || a[2] != b[2]) && throw_promote_shape_mismatch(a, b)
--     return a
-- end
-- 
-- """
--     promote_shape(s1, s2)
-- 
-- Check two array shapes for compatibility, allowing trailing singleton dimensions, and return
-- whichever shape has more dimensions.
-- 
-- # Examples
-- ```jldoctest
-- julia> a = fill(1, (3,4,1,1,1));
-- 
-- julia> b = fill(1, (3,4));
-- 
-- julia> promote_shape(a,b)
-- (Base.OneTo(3), Base.OneTo(4), Base.OneTo(1), Base.OneTo(1), Base.OneTo(1))
-- 
-- julia> promote_shape((2,3,1,4), (2, 3, 1, 4, 1))
-- (2, 3, 1, 4, 1)
-- ```
-- """
-- function promote_shape(a::Dims, b::Dims)
--     if length(a) < length(b)
--         return promote_shape(b, a)
--     end
--     for i=1:length(b)
--         a[i] != b[i] && throw_promote_shape_mismatch(a, b, i)
--     end
--     for i=length(b)+1:length(a)
--         a[i] != 1 && throw_promote_shape_mismatch(a, nothing, i)
--     end
--     return a
-- end
-- /Source

private def arithmeticPromoteDims (a b : List I64) : ShapeR (List I64) :=
  match a, b with
  | [], [] => pure JuliaLean.base.indices.promote_shape_Tuple0_Tuple0
  | [a], [b] => arithmeticPromoteOneOne a b
  | [a, b], [c] => arithmeticPromoteTwoOne a b c
  | [a], [b, c] => arithmeticPromoteTwoOne b c a
  | [a, b], [c, d] => arithmeticPromoteTwoTwo a b c d
  | _, _ => arithmeticPromoteDimsGeneral a b

/-- Existing custom BitArray iteration, evaluated on the read-only UInt64 store.
This is the actual dispatch selected for BitArray, ahead of AbstractArray's
generic iterator. No mathematical list iteration or arbitrary callee is used.
Julia source: base/bitarray.jl:352-355,1179,1186. -/
-- Source: base/bitarray.jl:352-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function iterate(B::BitArray, i::Int=0)
--     i >= length(B) && return nothing
--     (B.chunks[_div64(i)+1] & (UInt64(1)<<_mod64(i)) != 0, i+1)
-- end
-- /Source

private def arithmeticIterate {N : Nat} (input : JuliaLean.base.array.MutableMemory U64)
    (A : BitArray N) (state : I64 := int 0) :
    JuliaLean.base.array.MutationM I64 (Option (Bool × I64)) :=
  match (bitArrayIterate A state).run input with
  | (.ok value, _) => pure value
  | (.error error, _) => throw error

/-- Native Int public assignment with the source's explicit @inbounds context.
Only the @boundscheck block of the supplied typed setter is erased; memory
reference construction and the existing memory write primitive are retained.
Julia source: base/array.jl:1031-1041; base/bitarray.jl:1184. -/
-- Source: base/array.jl:1031-1041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function setindex!(A::Array{T}, x, i::Int) where {T}
--     @_propagate_inbounds_meta
--     x = x isa T ? x : convert(T, x)::T
--     return _setindex!(A, x, i)
-- end
-- function _setindex!(A::Array{T}, x::T, i::Int) where {T}
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefset!(memoryrefnew(A.ref, i, false), x, :not_atomic, false)
--     return A
-- end
-- /Source

-- Source: base/bitarray.jl:1184-1184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--             @inbounds r[ri] = ($f)(ay[1], by[1])
-- /Source

private def arithmeticSet (A : JuliaLean.base.array.HeapArray IntTy) (value : I64)
    (i : I64) : JuliaLean.base.array.MutationM I64 Unit := do
  let typedSet := fun (handle : Nat) (value : I64) (index : I64) =>
    JuliaLean.base.array.setindexTyped
      (fun (_ : Nat) (_ : I64) => pure ())
      (fun handle index _ => JuliaLean.base.array.mutableMemoryref (α := I64) handle index)
      (fun reference value _ => JuliaLean.base.array.memoryWrite reference.1 reference.2
        (some value)) handle value index
  let _ ← JuliaLean.base.array.setindexScalar (fun _ : I64 => true) (fun x => x)
    pure typedSet A.handle value i
  pure ()

/-- Both generated arithmetic methods, for all input ranks. Dims promotion is
completed before allocating native Int output; the actual custom iterators then
advance left before right in every source tuple assignment. Fresh output uses the
same explicit existing-store composition as unary minus. The impossible early
right-iterator exhaustion is represented by the actual getindex(Nothing, Int)
MethodError rather than an invented value or the frozen template's BoundsError.
Julia source: base/bitarray.jl:1176-1190. -/
-- Source: base/bitarray.jl:1176-1190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for f in (:+, :-)
--     @eval function ($f)(A::BitArray, B::BitArray)
--         r = Array{Int}(undef, promote_shape(size(A), size(B)))
--         ay, by = iterate(A), iterate(B)
--         ri = 1
--         # promote_shape guarantees that A and B have the
--         # same iteration space
--         while ay !== nothing
--             @inbounds r[ri] = ($f)(ay[1], by[1])
--             ri += 1
--             ay, by = iterate(A, ay[2]), iterate(B, by[2])
--         end
--         return r
--     end
-- end
-- /Source

def binaryArithmetic {N K : Nat} (f : ArithmeticFunction) (A : BitArray N) (B : BitArray K) :
    UnaryMinusM (JuliaLean.base.array.HeapArray IntTy) := fun input => do
  let shape ← match arithmeticPromoteDims (bitArraySizeRanked A) (bitArraySizeRanked B) with
    | .ok shape => pure shape
    | .error error => throw (binaryShapeError error)
  let result ← unaryMinusAllocate shape
  let mut ay ← arithmeticIterate input A
  let mut byValue ← arithmeticIterate input B
  let mut ri := int 1
  while ay.isSome do
    match ay, byValue with
    | some (x, stateA), some (y, stateB) =>
        arithmeticSet result (arithmeticNative f x y) ri
        ri := ri + int 1
        ay ← arithmeticIterate input A stateA
        byValue ← arithmeticIterate input B stateB
    | some _, none => throw (.method "getindex")
    | none, _ => return result
  pure result

/-- base/bitarray.jl:1448, a concrete specialization for all ten BitInteger init
types. The addition has Julia's promoted intermediate type; reduction back to T
uses the installed `% Type` dispatch. Arbitrary non-BitInteger T remains blocked. -/
-- Source: base/bitarray.jl:1448-1454 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bitcount(Bc::Vector{UInt64}; init::T=0) where {T}
--     n::T = init
--     @inbounds for i = 1:length(Bc)
--         n = (n + count_ones(Bc[i])) % T
--     end
--     return n
-- end
-- /Source

def bitcountMachine {t : IntTy} (Bc : Nat) (init : JInt t) : BitMutationM (JInt t) := do
  let mut n := init
  for i in intRange (int 1) (← mutableLength Bc) do
    let count := JuliaLean.base.int.count_ones (← mutableGet Bc i)
    let promoted := IntTy.promote t .i64
    let nPromoted := JuliaLean.base.int.remT promoted n
    let countPromoted := JuliaLean.base.int.remT promoted count
    let total := JuliaLean.base.int.add nPromoted countPromoted
    n := JuliaLean.base.int.remT t total
  return n

/-- base/bitarray.jl:1456, machine-integer init specialization. -/
-- Source: base/bitarray.jl:1456-1456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _count(::typeof(identity), B::BitArray, ::Colon, init) = bitcount(B.chunks; init)
-- /Source

def countMachine {N : Nat} {t : IntTy} (B : BitArray N) (init : JInt t) :
    BitMutationM (JInt t) :=
  bitArrayCountIdentity bitcountMachine B init


/-- base/bitarray.jl:1478, all machine Integer starts, with fallible native
conversion evaluated before the two source range checks. Other Integer families
remain blocked; the UInt64 scan is the existing callable implementation. -/
-- Source: base/bitarray.jl:1478-1483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findnext(B::BitArray, start::Integer)
--     start = Int(start)
--     start > 0 || throw(BoundsError(B, start))
--     start > length(B) && return nothing
--     unsafe_bitfindnext(B.chunks, start)
-- end
-- /Source

def findNextMachine {N : Nat} {t : IntTy} (B : BitArray N) (start : JInt t) :
    BitMutationM (Option I64) := do
  let start ← nativeInteger start
  bitArrayFindNext (fun i => i) (unsafeBitFindNext JuliaLean.base.int.trailing_zeros) B start

/-- base/bitarray.jl:1520: `value` is pred.x, for either == or isequal Fix2
dispatch. Its Bool payload is complete; starts are the ten machine Integer types.
The false branch performs Int(start) at the source call site, while the true
branch invokes the checked public true-bit search. -/
-- Source: base/bitarray.jl:1520-1526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findnext(pred::Fix2{<:Union{typeof(isequal),typeof(==)},Bool},
--                   B::BitArray, start::Integer)
--     v = pred.x
--     v == false && return findnextnot(B, Int(start))
--     v == true && return findnext(B, start)
--     return nothing
-- end
-- /Source

def findNextFixedMachine {N : Nat} {t : IntTy} (value : Bool) (B : BitArray N)
    (start : JInt t) : BitMutationM (Option I64) := do
  let v := value
  if v == false then
    let start ← nativeInteger start
    return ← bitArrayFindNextNot
      (JuliaLean.base.int.trailing_ones_Integer JuliaLean.base.int.trailing_zeros
        JuliaLean.base.int.not_int) B start
  if v == true then return ← findNextMachine B start
  return none

/-- base/bitarray.jl:1563, all machine Integer starts, preserving conversion,
nonpositive-start return, and upper BoundsError in precisely that order. -/
-- Source: base/bitarray.jl:1563-1568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findprev(B::BitArray, start::Integer)
--     start = Int(start)
--     start > 0 || return nothing
--     start > length(B) && throw(BoundsError(B, start))
--     unsafe_bitfindprev(B.chunks, start)
-- end
-- /Source

def findPrevMachine {N : Nat} {t : IntTy} (B : BitArray N) (start : JInt t) :
    BitMutationM (Option I64) := do
  let start ← nativeInteger start
  bitArrayFindPrev (fun i => i) (unsafeBitFindPrev JuliaLean.base.int.top_set_bit) B start

/-- base/bitarray.jl:1596, Bool Fix2 payload for == or isequal, with all machine
Integer starts. Other Integer families retain the recorded dispatch blocker. -/
-- Source: base/bitarray.jl:1596-1602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findprev(pred::Fix2{<:Union{typeof(isequal),typeof(==)},Bool},
--                   B::BitArray, start::Integer)
--     v = pred.x
--     v == false && return findprevnot(B, Int(start))
--     v == true && return findprev(B, start)
--     return nothing
-- end
-- /Source

def findPrevFixedMachine {N : Nat} {t : IntTy} (value : Bool) (B : BitArray N)
    (start : JInt t) : BitMutationM (Option I64) := do
  let v := value
  if v == false then
    let start ← nativeInteger start
    return ← bitArrayFindPrevNot
      (JuliaLean.base.int.leading_ones_Integer JuliaLean.base.int.leading_zeros
        JuliaLean.base.int.not_int) B start
  if v == true then return ← findPrevMachine B start
  return none


/-- Error-channel adapter for concrete indices.jl key constructors/indexing.
All IndexError classes have a class-preserving abstractarray representation.
Needed by base/bitarray.jl:1628,1630,1646-1647. -/
-- Source: base/indices.jl:483-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- LinearIndices(inds::NTuple{N,AbstractUnitRange{<:Integer}}) where {N} =
--     LinearIndices(map(r->convert(AbstractUnitRange{Int}, r), inds))
-- LinearIndices(inds::NTuple{N,Union{<:Integer,AbstractUnitRange{<:Integer}}}) where {N} =
--     LinearIndices(map(_convert2ind, inds))
-- LinearIndices(A::Union{AbstractArray,SimpleVector}) = LinearIndices(axes(A))
-- /Source

private def extremaIndexResult {α : Type}
    (r : JuliaLean.base.indices.IndexResult α) : JuliaLean.base.abstractarray.Result α :=
  r.mapError fun e => match e with
    | .methodError f _ => .julia (.methodError f)
    | .argumentError msg => .julia (.argumentError msg)
    | .dimensionMismatch msg => .dimensionMismatch msg
    | .boundsError => .julia .boundsError
    | .core e => .julia e

/-- Concrete keys(::BitVector) route: ranked axes, then the installed
LinearIndices(array) and native AbstractUnitRange constructor. Conversion to
AbstractUnitRange{Int} is the existing identity convert for this OneTo{Int}.
No user-supplied callee or key law is accepted. 
Julia source: base/indices.jl:483-487. -/
-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source

-- Source: base/abstractarray.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- keys(a::AbstractVector) = LinearIndices(a)
-- /Source

-- Source: base/abstractarray.jl:16-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- convert(::Type{T}, a::T) where {T<:AbstractArray} = a
-- /Source

-- Source: base/indices.jl:483-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- LinearIndices(inds::NTuple{N,AbstractUnitRange{<:Integer}}) where {N} =
--     LinearIndices(map(r->convert(AbstractUnitRange{Int}, r), inds))
-- LinearIndices(inds::NTuple{N,Union{<:Integer,AbstractUnitRange{<:Integer}}}) where {N} =
--     LinearIndices(map(_convert2ind, inds))
-- LinearIndices(A::Union{AbstractArray,SimpleVector}) = LinearIndices(axes(A))
-- /Source

private def extremaVectorKeys (A : BitVector) :
    JuliaLean.base.abstractarray.Result
      (JuliaLean.base.indices.LinearIndices (JuliaLean.base.range.OneTo I64)) :=
  JuliaLean.base.abstractarray.keysVector
    (fun value : BitVector => do
      let axes ← JuliaLean.base.abstractarray.axesDefault
        (fun B : BitVector => pure (bitArraySizeRanked B))
        (JuliaLean.base.range.unchecked_oneto (T := I64)) value
      extremaIndexResult (JuliaLean.base.indices.LinearIndices_AbstractArray
        (fun _ : BitVector => axes)
        (JuliaLean.base.indices.LinearIndices_AbstractUnitRanges
          (fun r : JuliaLean.base.range.OneTo I64 =>
            pure (JuliaLean.base.abstractarray.convertSame r))) value)) A

/-- At the two extrema call sites the source explicitly uses `@inbounds`.
The installed LinearIndices getter is called with its @boundscheck block erased,
so an invalid computed key is returned unchanged; the independent extrema
contracts below require valid keys and can detect that source failure.
The unit callback is erasure of this specific check, not a missing implementation.
The concrete metadata and getter calls cannot produce ArrayError fallback
classes; the total adapter keeps such impossible outcomes as failures. 
Julia source: base/bitarray.jl:1646-1647. -/
-- Source: base/indices.jl:509-513 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(iter::LinearIndices, i::Int)
--     @inline
--     @boundscheck checkbounds(iter, i)
--     i
-- end
-- /Source

-- Source: base/bitarray.jl:1628-1630 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--         k == 64 || return (true, @inbounds keys(a)[ti])
--     end
--     return m, @inbounds keys(a)[mi]
-- /Source

-- Source: base/bitarray.jl:1646-1647 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     k == l || return (false, @inbounds keys(a)[ti])
--     return (m, @inbounds keys(a)[mi])
-- /Source

private def extremaVectorKey (A : BitVector) (i : I64) : BitMutationM I64 := do
  let result : JuliaLean.base.abstractarray.Result I64 := do
    let keys ← extremaVectorKeys A
    extremaIndexResult (JuliaLean.base.indices.getindex_LinearIndices_Int
      (fun _ _ => pure ()) keys i)
  match result with
  | .ok value => pure value
  | .error (.julia (.argumentError msg)) => throw (.argument msg)
  | .error (.julia (.overflowError _)) => throw .overflow
  | .error (.julia .boundsError) => throw .bounds
  | .error (.julia (.inexactError _)) => throw .inexact
  | .error (.julia .divideError) => throw .divide
  | .error (.julia (.methodError f)) => throw (.method f)
  | .error (.julia (.domainError msg)) => throw (.argument msg)
  | .error (.julia .eofError) => throw (.method "EOFError")
  | .error (.dimensionMismatch msg) => throw (.dimensionMismatch msg)
  | .error (.canonicalIndex f _) => throw (.method f)
  | .error (.errorException msg) => throw (.argument msg)
  | .error (.assertionError msg) => throw (.assertion msg)
  | .error (.showError e) => throw (.showError e)

/-- base/bitarray.jl:1620: complete BitVector specialization of the installed
findmax scan, including empty ArgumentError, machine index arithmetic, and the
actual unchecked LinearIndices key route. Higher-rank Cartesian keys remain
blocked on unavailable prebuilt multidimensional imports. -/
-- Source: base/bitarray.jl:1620-1631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findmax(a::BitArray)
--     isempty(a) && throw(ArgumentError("BitArray must be non-empty"))
--     m, mi = false, 1
--     ti = 1
--     ac = a.chunks
--     for i = 1:length(ac)
--         @inbounds k = trailing_zeros(ac[i])
--         ti += k
--         k == 64 || return (true, @inbounds keys(a)[ti])
--     end
--     return m, @inbounds keys(a)[mi]
-- end
-- /Source

def findMaxVector (A : BitVector) : BitMutationM (Bool × I64) :=
  bitArrayFindMax JuliaLean.base.int.trailing_zeros extremaVectorKey A

/-- base/bitarray.jl:1633: complete BitVector specialization of the installed
findmin scan with native trailing_ones and the same source key route. -/
-- Source: base/bitarray.jl:1633-1648 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function findmin(a::BitArray)
--     isempty(a) && throw(ArgumentError("BitArray must be non-empty"))
--     m, mi = true, 1
--     ti = 1
--     ac = a.chunks
--     for i = 1:length(ac)-1
--         @inbounds k = trailing_ones(ac[i])
--         ti += k
--         k == 64 || return (false, @inbounds keys(a)[ti])
--     end
--     l = Base._mod64(length(a)-1) + 1
--     @inbounds k = trailing_ones(ac[end] & Base._msk_end(l))
--     ti += k
--     k == l || return (false, @inbounds keys(a)[ti])
--     return (m, @inbounds keys(a)[mi])
-- end
-- /Source

def findMinVector (A : BitVector) : BitMutationM (Bool × I64) :=
  bitArrayFindMin
    (JuliaLean.base.int.trailing_ones_Integer JuliaLean.base.int.trailing_zeros
      JuliaLean.base.int.not_int) extremaVectorKey A

/-- base/bitarray.jl:1674: the empty-tuple branch never inspects the scalar or
size argument. Keep both fully polymorphic, and enforce the actual Tuple{}
shape through Unit. This extends the frozen native-only specialization without
changing it or substituting behavior for any arithmetic callee. -/
-- Source: base/bitarray.jl:1674-1674 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _overflowind(i1, irest::Tuple{}, size) = (i1, irest)
-- /Source

def overflowIndEmptyAny {I S : Type} (i1 : I) (irest : Unit) (_size : S) : I × Unit :=
  (i1, irest)

/-- base/bitarray.jl:1685: return the actual scalar payload for any value type.
The source neither constructs a CartesianIndex nor wraps the return value;
the empty tuple is enforced by the input representation. -/
-- Source: base/bitarray.jl:1685-1685 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _toind(i1, irest::Tuple{}) = i1
-- /Source

def toIndEmptyAny {I : Type} (i1 : I) (_irest : Unit) : I := i1


/-- base/bitarray.jl:1722: default count uses native Int init=0. The generic
init-type limitation of bitcount does not apply to this selected dispatch. -/
-- Source: base/bitarray.jl:1722-1722 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _sum(B::BitArray, ::Colon) = count(B)
-- /Source

def sumColon {N : Nat} (B : BitArray N) : BitMutationM I64 :=
  bitArraySumColon (fun value => countMachine value (int 0)) B


/-- Concrete constructor binding needed by assigned map methods at
base/bitarray.jl:1756-1759,1776. Core.checked_dims and UInt64 allocation are the
existing implementations, including their errors. No extra initialization is
introduced for undef storage. This is a dependency binding, not new coverage of
the unassigned constructor row. -/
-- Source: base/bitarray.jl:28-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     function BitArray{N}(::UndefInitializer, dims::Vararg{Int,N}) where N
--         i = 1
--         for d in dims
--             d >= 0 || throw(ArgumentError("dimension size must be ≥ 0, got $d for dimension $i"))
--             i += 1
--         end
--         n = Core.checked_dims(dims...)
--         nc = num_bit_chunks(n)
--         chunks = Vector{UInt64}(undef, nc)
--         nc > 0 && (chunks[end] = UInt64(0))
--         b = new(chunks, n)
--         N != 1 && (b.dims = dims)
--         return b
--     end
-- /Source

def allocate {N : Nat} (dims : List I64) : BitMutationM (BitArray N) :=
  BitArrayUndef (N := N) (JuliaLean.base.array.checkedDims (m := BitMutationM))
    (fun count : Nat => JuliaLean.base.array.mutableAllocate (α := U64)
      (some (JuliaLean.base.array.allocationSummary uint64Layout)) 0 (int (count : Int))) dims

/-- Rank-correct similar dependency for assigned map methods. The frozen
one-argument similar template reads raw dims even at rank one; use the existing
dimension-taking constructor route with the actual installed size dispatch.
The source object's fields and shared chunks are not modified. 
Julia source: base/bitarray.jl:359-361. -/
-- Source: base/bitarray.jl:359-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(B::BitArray) = BitArray(undef, size(B))
-- similar(B::BitArray, dims::Int...) = BitArray(undef, dims)
-- similar(B::BitArray, dims::Dims) = BitArray(undef, dims...)
-- /Source

def similarRanked {N : Nat} (A : BitArray N) : BitMutationM (BitArray N) :=
  similarBitArrayDimsTuple allocate (bitArraySizeRanked A)

/-- Native UInt64 vector fill binding for base/bitarray.jl:373-375. The frozen
fillBitArray interface normalizes both source arguments to UInt64. Recover the
actual Int-zero dispatch in its false branch, including convert(UInt64, 0),
and the already-UInt64 dispatch in its all-ones branch. Eachindex is obtained
from the actual dense-array length/OneTo implementation. -/
-- Source: base/bitarray.jl:368-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill!(B::BitArray, x)
--     y = convert(Bool, x)
--     isempty(B) && return B
--     Bc = B.chunks
--     if !y
--         fill!(Bc, 0)
--     else
--         fill!(Bc, _msk64)
--         Bc[end] &= _msk_end(B)
--     end
--     return B
-- end
-- /Source

-- Source: base/array.jl:368-378 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill!(A::AbstractArray{T}, x) where T
--     @inline
--     xT = x isa T ? x : convert(T, x)::T
--     return _fill!(A, xT)
-- end
-- function _fill!(A::AbstractArray{T}, x::T) where T
--     for i in eachindex(A)
--         A[i] = x
--     end
--     return A
-- end
-- /Source

def fillWords (chunks : Nat) (value : U64) : BitMutationM Unit := do
  let fill := fun (a : Nat) (x : U64) =>
    JuliaLean.base.array.fillTyped
      (fun handle => do
        let axis ← JuliaLean.base.abstractarray.eachindexDense mutableLength
          (JuliaLean.base.range.unchecked_oneto (T := I64)) handle
        pure (intRange (int 1) axis.stop)) mutableSet a x
  if value == u64 0 then
    let _ ← JuliaLean.base.array.fillBang
      (fun _ : I64 => false) (fun _ : I64 => u64 0)
      (fun x => match JuliaLean.base.int.convert .u64 x with
        | .ok word => pure word
        | .error _ => throw .inexact)
      fill chunks (int 0)
    pure ()
  else
    let _ ← JuliaLean.base.array.fillBang (fun _ : U64 => true) (fun x => x) pure fill chunks value
    pure ()

/-- Required Bool-valued fill! dependency for assigned map(one) at
base/bitarray.jl:1758. The frozen generic fillBitArray writes its final mask at
index one, so it is not a faithful callable for this source branch. This narrow
additive binding retains that declaration unchanged and reuses actual conversion,
vector fill and mutable primitives. No coverage is claimed for the unassigned
generic-item fill! row. -/
-- Source: base/bitarray.jl:368-379 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fill!(B::BitArray, x)
--     y = convert(Bool, x)
--     isempty(B) && return B
--     Bc = B.chunks
--     if !y
--         fill!(Bc, 0)
--     else
--         fill!(Bc, _msk64)
--         Bc[end] &= _msk_end(B)
--     end
--     return B
-- end
-- /Source

def fillBoolForMap {N : Nat} (B : BitArray N) (x : Bool) : BitMutationM (BitArray N) := do
  let y := JuliaLean.base.number.convertSame x
  if B.len == int 0 then return B
  let Bc := B.chunks
  if !y then
    fillWords Bc (u64 0)
  else
    fillWords Bc u64Max
    let lastIndex ← mutableLength Bc
    let last ← mutableGet Bc lastIndex
    mutableSet Bc (and_int last (maskEndArray B)) lastIndex
  return B

/-- Concrete copy path for assigned map(identity). This uses the BitArray
copyto! specialization, which is distinct from the defective copyChunks helper.
The return has a fresh constructor-allocated chunk-vector header. 
Julia source: base/abstractarray.jl:1211-1214. -/
-- Source: base/abstractarray.jl:1154-1157 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copy(a::AbstractArray)
--     @_propagate_inbounds_meta
--     copymutable(a)
-- end
-- /Source

-- Source: base/abstractarray.jl:1211-1214 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copymutable(a::AbstractArray)
--     @_propagate_inbounds_meta
--     copyto!(similar(a), a)
-- end
-- /Source

def copyRanked {N : Nat} (A : BitArray N) : BitMutationM (BitArray N) :=
  JuliaLean.base.abstractarray.copyArray
    (JuliaLean.base.abstractarray.copyMutableArray similarRanked bitArrayCopyto) A

/-- Only the phantom rank changes in this internal view; chunks, logical length,
and stored dims are copied literally. The assigned map! callees never inspect
the phantom rank. This retains shared-memory aliasing without allocating. 
Julia source: base/bitarray.jl:1761-1764. -/
-- Source: base/bitarray.jl:1761-1764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map!(::Union{typeof(~), typeof(!)}, dest::BitArray, A::BitArray) = bit_map!(~, dest, A)
-- map!(::typeof(zero), dest::BitArray, A::BitArray) = bit_map_constant!(dest, A, false)
-- map!(::typeof(one), dest::BitArray, A::BitArray) = bit_map_constant!(dest, A, true)
-- map!(::typeof(identity), dest::BitArray, A::BitArray) = copyto!(dest, A)
-- /Source

def rankView {N K : Nat} (A : BitArray N) : BitArray K :=
  ⟨A.chunks, A.len, A.dims⟩


/-- base/bitarray.jl:1756: actual ranked-size allocation followed by the installed
chunkwise complement. Both public function tags ! and ~ select this body. -/
-- Source: base/bitarray.jl:1756-1756 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map(::Union{typeof(~), typeof(!)}, A::BitArray) = bit_map!(~, similar(A), A)
-- /Source

def mapNot {N : Nat} (A : BitArray N) : BitMutationM (BitArray N) :=
  bitArrayMapNot similarRanked (bitArrayMapBangUnary JuliaLean.base.int.not_int) A

/-- base/bitarray.jl:1757: only the false fill branch is used. The separate frozen
true-fill masking defect is neither changed nor invoked. -/
-- Source: base/bitarray.jl:1757-1757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map(::typeof(zero), A::BitArray) = fill!(similar(A), false)
-- /Source

def mapZero {N : Nat} (A : BitArray N) : BitMutationM (BitArray N) :=
  bitArrayMapZero similarRanked (fillBitArray pure fillWords) A

/-- base/bitarray.jl:1758: actual ranked allocation followed by the required
faithful Bool-valued fill dependency. The frozen generic fill model is unchanged. -/
-- Source: base/bitarray.jl:1758-1758 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map(::typeof(one), A::BitArray) = fill!(similar(A), true)
-- /Source

def mapOne {N : Nat} (A : BitArray N) : BitMutationM (BitArray N) :=
  bitArrayMapOne similarRanked fillBoolForMap A

/-- base/bitarray.jl:1759: reuse the actual copy/copyto path at every rank. -/
-- Source: base/bitarray.jl:1759-1759 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map(::typeof(identity), A::BitArray) = copy(A)
-- /Source

def mapIdentity {N : Nat} (A : BitArray N) : BitMutationM (BitArray N) :=
  bitArrayMapIdentity copyRanked A

/-- base/bitarray.jl:1761: independently ranked source and destination, with the
source's alias-sensitive final read preceding its write. -/
-- Source: base/bitarray.jl:1761-1761 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map!(::Union{typeof(~), typeof(!)}, dest::BitArray, A::BitArray) = bit_map!(~, dest, A)
-- /Source

def mapNotBang {D N : Nat} (dest : BitArray D) (A : BitArray N) :
    BitMutationM (BitArray D) :=
  bitArrayMapBangNot (bitArrayMapBangUnary JuliaLean.base.int.not_int) dest (rankView A)

/-- base/bitarray.jl:1762: concrete fill_chunks! callee with native length check. -/
-- Source: base/bitarray.jl:1762-1762 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map!(::typeof(zero), dest::BitArray, A::BitArray) = bit_map_constant!(dest, A, false)
-- /Source

def mapZeroBang {D N : Nat} (dest : BitArray D) (A : BitArray N) :
    BitMutationM (BitArray D) :=
  bitArrayMapBangZero (bitArrayMapBangConstant fillChunks) dest (rankView A)

/-- base/bitarray.jl:1763: the constant bit-map route uses fill_chunks!, not the
frozen fillBitArray true branch. -/
-- Source: base/bitarray.jl:1763-1763 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map!(::typeof(one), dest::BitArray, A::BitArray) = bit_map_constant!(dest, A, true)
-- /Source

def mapOneBang {D N : Nat} (dest : BitArray D) (A : BitArray N) :
    BitMutationM (BitArray D) :=
  bitArrayMapBangOne (bitArrayMapBangConstant fillChunks) dest (rankView A)

/-- base/bitarray.jl:1764: preserve copyto!'s BoundsError (not map's
DimensionMismatch) and support independent ranks without changing metadata. -/
-- Source: base/bitarray.jl:1764-1764 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- map!(::typeof(identity), dest::BitArray, A::BitArray) = copyto!(dest, A)
-- /Source

def mapIdentityBang {D N : Nat} (dest : BitArray D) (A : BitArray N) :
    BitMutationM (BitArray D) :=
  bitArrayMapBangIdentity bitArrayCopyto dest (rankView A)


/-- The fifteen public function tags covered by the ten generator cases at
base/bitarray.jl:1766-1778. Function identity determines the concrete chunk op;
there is no supplied replacement implementation or correctness law. -/
-- Source: base/bitarray.jl:1766-1778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (T, f) in ((:(Union{typeof(&), typeof(*), typeof(min)}), :(&)),
--                (:(Union{typeof(|), typeof(max)}),            :(|)),
--                (:(Union{typeof(xor), typeof(!=)}),           :xor),
--                (:(typeof(nand)),                             :nand),
--                (:(typeof(nor)),                              :nor),
--                (:(Union{typeof(>=), typeof(^)}),             :((p, q) -> p | ~q)),
--                (:(typeof(<=)),                               :((p, q) -> ~p | q)),
--                (:(typeof(==)),                               :((p, q) -> ~xor(p, q))),
--                (:(typeof(<)),                                :((p, q) -> ~p & q)),
--                (:(typeof(>)),                                :((p, q) -> p & ~q)))
--     @eval map(::$T, A::BitArray, B::BitArray) = bit_map($f, A, B)
--     @eval map!(::$T, dest::BitArray, A::BitArray, B::BitArray) = bit_map!($f, dest, A, B)
-- end
-- /Source

inductive BinaryFunction where
  | bitAnd | multiply | minimum | bitOr | maximum | bitXor | notEqual
  | nand | nor | greaterEqual | power | lessEqual | equal | less | greater
  deriving Repr, DecidableEq

/-- Exact generated UInt64 operations. nand/nor expand their installed one-line
definitions from base/bool.jl:83,121 into the installed and/or/not intrinsics.
All operands and intermediates remain UInt64. -/
-- Source: base/bitarray.jl:1766-1778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (T, f) in ((:(Union{typeof(&), typeof(*), typeof(min)}), :(&)),
--                (:(Union{typeof(|), typeof(max)}),            :(|)),
--                (:(Union{typeof(xor), typeof(!=)}),           :xor),
--                (:(typeof(nand)),                             :nand),
--                (:(typeof(nor)),                              :nor),
--                (:(Union{typeof(>=), typeof(^)}),             :((p, q) -> p | ~q)),
--                (:(typeof(<=)),                               :((p, q) -> ~p | q)),
--                (:(typeof(==)),                               :((p, q) -> ~xor(p, q))),
--                (:(typeof(<)),                                :((p, q) -> ~p & q)),
--                (:(typeof(>)),                                :((p, q) -> p & ~q)))
--     @eval map(::$T, A::BitArray, B::BitArray) = bit_map($f, A, B)
--     @eval map!(::$T, dest::BitArray, A::BitArray, B::BitArray) = bit_map!($f, dest, A, B)
-- end
-- /Source

-- Source: base/bool.jl:83-83 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- nand(x...) = ~(&)(x...)
-- /Source

-- Source: base/bool.jl:121-121 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- nor(x...) = ~(|)(x...)
-- /Source

def wordBinary (f : BinaryFunction) (p q : U64) : U64 :=
  match f with
  | .bitAnd | .multiply | .minimum => and_int p q
  | .bitOr | .maximum => or_int p q
  | .bitXor | .notEqual => xor_int p q
  | .nand => not_int (and_int p q)
  | .nor => not_int (or_int p q)
  | .greaterEqual | .power => or_int p (not_int q)
  | .lessEqual => or_int (not_int p) q
  | .equal => not_int (xor_int p q)
  | .less => and_int (not_int p) q
  | .greater => and_int p (not_int q)

/-- Concrete generated-operation binding to the existing alias-sensitive
binary loop (base/bitarray.jl:1814). The loop never reads phantom rank or dims.
No user-supplied arbitrary F is claimed to be implemented by this finite tag type. -/
-- Source: base/bitarray.jl:1814-1835 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bit_map!(f::F, dest::BitArray, A::BitArray, B::BitArray) where F
--     min_bitlen = min(length(A), length(B))
--     min_bitlen <= length(dest) || throw(DimensionMismatch("length of destination must be >= length of smallest input collection"))
--     isempty(A) && return dest
--     isempty(B) && return dest
--     destc = dest.chunks
--     Ac = A.chunks
--     Bc = B.chunks
--     len_Ac = min(length(Ac), length(Bc))
--     for i = 1:len_Ac-1
--         destc[i] = f(Ac[i], Bc[i])
--     end
--     # the last affected UInt64's original content
--     dest_last = destc[len_Ac]
--     _msk = _msk_end(min_bitlen)
--     # first zero out the bits mask is going to change
--     # then update bits by `or`ing with a masked RHS
--     # DO NOT SEPARATE ONTO TWO LINES.
--     # Otherwise there will be bugs when Ac or Bc aliases destc
--     destc[len_Ac] = (dest_last & ~(_msk)) | f(Ac[len_Ac], Bc[len_Ac]) & _msk
--     dest
-- end
-- /Source

def binaryInto {D N K : Nat} (f : BinaryFunction) (dest : BitArray D)
    (A : BitArray N) (B : BitArray K) : BitMutationM (BitArray D) := do
  let _ ← bitArrayMapBangBinary (wordBinary f) (rankView (K := 1) dest) A B
  pure dest


/-- _similar_shape(zip(A,B), IteratorSize(zip(A,B))) at bitarray.jl:1784-1785.
Two HasShape traits produce only HasLength or HasShape. Thus testing HasLength
is exhaustive for this concrete input domain; no other-trait default is used.
Shape queries run before allocation and before reading either input's chunks. 
Julia source: base/array.jl:700-701. -/
-- Source: base/bitarray.jl:1783-1787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bit_map(f::F, A::BitArray, B::BitArray) where F
--     AB = zip(A, B)
--     dest = similar(BitArray, _similar_shape(AB, IteratorSize(AB)))
--     bit_map!(f, dest, A, B)
-- end
-- /Source

-- Source: base/iterators.jl:413-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- axes(z::Zip) = _promote_tuple_shape(Base.map(axes, z.is)...)
-- _promote_tuple_shape((a,)::Tuple{OneTo}, (b,)::Tuple{OneTo}) = (intersect(a, b),)
-- _promote_tuple_shape((m,)::Tuple{Integer}, (n,)::Tuple{Integer}) = (min(m, n),)
-- _promote_tuple_shape(a, b) = promote_shape(a, b)
-- /Source

-- Source: base/array.jl:700-701 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _similar_shape(itr, ::HasLength) = length(itr)::Integer
-- _similar_shape(itr, ::HasShape) = axes(itr)
-- /Source

def binaryShape {N M : Nat} (A : BitArray N) (B : BitArray M) : ShapeR (List I64) := do
  let inputs : JuliaLean.base.iterators.TupleVals BitArray [N, M] :=
    .cons A (.cons B .nil)
  let zipped := JuliaLean.base.iterators.zipModel inputs
  let trait := JuliaLean.base.iterators.zipIteratorSizeDispatch2 (.hasShape N) (.hasShape M)
  if trait == .hasLength then
    let length ← JuliaLean.base.array.similarShapeLength
      (fun z => JuliaLean.base.iterators.zipLength
        (fun rank (_ : BitArray rank) => pure (.hasShape rank))
        (fun _ value => pure value.len)
        (fun n m => pure (binaryMin n m)) z) zipped
    pure [length]
  else
    let axes ← JuliaLean.base.array.similarShapeAxes
      (fun z => JuliaLean.base.iterators.sourceMethod413 binaryAxes binaryPromoteAxes z)
      zipped
    JuliaLean.base.abstractarray.toShapeMixed binaryToDimension axes

/-- Concrete allocating step of base/bitarray.jl:1785. Shape dispatch and any
DimensionMismatch occur before the existing BitArray constructor is called. -/
-- Source: base/bitarray.jl:1783-1787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bit_map(f::F, A::BitArray, B::BitArray) where F
--     AB = zip(A, B)
--     dest = similar(BitArray, _similar_shape(AB, IteratorSize(AB)))
--     bit_map!(f, dest, A, B)
-- end
-- /Source

def allocateBinary {N M : Nat} (A : BitArray N) (B : BitArray M) :
    BitMutationM (BitArray (binaryRank N M)) := do
  let shape ← match binaryShape A B with
    | .ok shape => pure shape
    | .error e => throw (binaryShapeError e)
  allocate (N := binaryRank N M) shape

/-- base/bitarray.jl:1776: every generated Boolean operation. The concrete
zip/axes shape path runs before allocation, then the existing source loop writes
the newly allocated packed destination. All input ranks and unequal lengths are
retained; same-rank multidimensional shape disagreement throws first. -/
-- Source: base/bitarray.jl:1766-1778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (T, f) in ((:(Union{typeof(&), typeof(*), typeof(min)}), :(&)),
--                (:(Union{typeof(|), typeof(max)}),            :(|)),
--                (:(Union{typeof(xor), typeof(!=)}),           :xor),
--                (:(typeof(nand)),                             :nand),
--                (:(typeof(nor)),                              :nor),
--                (:(Union{typeof(>=), typeof(^)}),             :((p, q) -> p | ~q)),
--                (:(typeof(<=)),                               :((p, q) -> ~p | q)),
--                (:(typeof(==)),                               :((p, q) -> ~xor(p, q))),
--                (:(typeof(<)),                                :((p, q) -> ~p & q)),
--                (:(typeof(>)),                                :((p, q) -> p & ~q)))
--     @eval map(::$T, A::BitArray, B::BitArray) = bit_map($f, A, B)
--     @eval map!(::$T, dest::BitArray, A::BitArray, B::BitArray) = bit_map!($f, dest, A, B)
-- end
-- /Source

-- Source: base/bitarray.jl:1783-1787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bit_map(f::F, A::BitArray, B::BitArray) where F
--     AB = zip(A, B)
--     dest = similar(BitArray, _similar_shape(AB, IteratorSize(AB)))
--     bit_map!(f, dest, A, B)
-- end
-- /Source

def mapBinary {N K : Nat} (f : BinaryFunction) (A : BitArray N) (B : BitArray K) :
    BitMutationM (BitArray (binaryRank N K)) := do
  let dest ← allocateBinary A B
  binaryInto f dest A B

/-- base/bitarray.jl:1777: every generated public function tag, with independent
destination and input ranks. Full generator context is retained below. -/
-- Source: base/bitarray.jl:1766-1778 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- for (T, f) in ((:(Union{typeof(&), typeof(*), typeof(min)}), :(&)),
--                (:(Union{typeof(|), typeof(max)}),            :(|)),
--                (:(Union{typeof(xor), typeof(!=)}),           :xor),
--                (:(typeof(nand)),                             :nand),
--                (:(typeof(nor)),                              :nor),
--                (:(Union{typeof(>=), typeof(^)}),             :((p, q) -> p | ~q)),
--                (:(typeof(<=)),                               :((p, q) -> ~p | q)),
--                (:(typeof(==)),                               :((p, q) -> ~xor(p, q))),
--                (:(typeof(<)),                                :((p, q) -> ~p & q)),
--                (:(typeof(>)),                                :((p, q) -> p & ~q)))
--     @eval map(::$T, A::BitArray, B::BitArray) = bit_map($f, A, B)
--     @eval map!(::$T, dest::BitArray, A::BitArray, B::BitArray) = bit_map!($f, dest, A, B)
-- end
-- /Source

def mapBinaryBang {D N K : Nat} (f : BinaryFunction) (dest : BitArray D)
    (A : BitArray N) (B : BitArray K) : BitMutationM (BitArray D) :=
  binaryInto f dest A B

/-- base/bitarray.jl:1789: the full constant helper with independent ranks and
concrete fill_chunks!, including no-op zero length and its source check order. -/
-- Source: base/bitarray.jl:1789-1793 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function bit_map_constant!(dest::BitArray, A::BitArray, x::Bool)
--     length(A) <= length(dest) || throw(DimensionMismatch("length of destination must be >= length of collection"))
--     fill_chunks!(dest.chunks, x, 1, length(A))
--     return dest
-- end
-- /Source

def bitMapConstant {D N : Nat} (dest : BitArray D) (A : BitArray N) (x : Bool) :
    BitMutationM (BitArray D) :=
  bitArrayMapBangConstant fillChunks dest (rankView A) x


/-- Closed adapter of the existing length check, base/tuple.jl:255-259.
A live Vector has a nonnegative native header length. Its Nat observation is used
only at the existing tuple-model boundary: this callee does comparison and string
formatting, not arithmetic. Its only error branch is the source ArgumentError,
whose exact message is retained here. This is not a generic TupleError bridge. -/
-- Source: base/tuple.jl:255-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _check_length_split_rest(len, n)
--     len < n && throw(ArgumentError(
--         "The iterator only contains $len elements, but at least $n were requested."
--     ))
-- end
-- /Source

private def splitRestCheckLength (len n : I64) : BitMutationM Unit :=
  match JuliaLean.base.tuple.checkLengthSplitRest len.val.toNat n.val with
  | .ok _ => pure ()
  | .error _ => throw (.argument
      s!"The iterator only contains {len.val.toNat} elements, but at least {n.val} were requested.")

/-- Concrete native colon dependency, base/range.jl:5,428,437-441.
The installed constructor normalizes empty UnitRanges and retains wrapping Int
arithmetic. Only the already closed native range-error adapter is used. -/
-- Source: base/range.jl:5-5 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- (:)(start::T, stop::T) where {T<:Real} = UnitRange{T}(start, stop)
-- /Source

-- Source: base/range.jl:428-428 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     UnitRange{T}(start::T, stop::T) where {T<:Real} = new(start, unitrange_last(start, stop))
-- /Source

-- Source: base/range.jl:437-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # if stop and start are integral, we know that their difference is a multiple of 1
-- unitrange_last(start::Integer, stop::Integer) =
--     stop >= start ? stop : convert(typeof(stop),
--         _range_wrapping_sub(start, oneunit(_range_wrapping_sub(start, stop))))
-- /Source

private def splitRestNativeRange (first last : I64) :
    BitMutationM (JuliaLean.base.range.UnitRange I64) :=
  match binaryLiftRange (JuliaLean.base.range.colon_T_T_Real first last) with
  | .ok r => pure r
  | .error e => throw (binaryShapeError e)

/-- Native UnitRange length, base/range.jl:794-804. In particular this is wrapping
1+(stop-start), not a mathematical nonnegative subtraction. -/
-- Source: base/range.jl:794-804 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function length(r::AbstractUnitRange{T}) where T
--     @inline
--     start, stop = first(r), last(r)
--     a = oneunit(zero(stop) - zero(start))
--     if a isa Signed || stop >= start
--         a += stop - start # Signed are allowed to go negative
--     else
--         a = zero(a) # Unsigned don't necessarily underflow
--     end
--     return Integer(a)
-- end
-- /Source

private def splitRestRangeLength (r : JuliaLean.base.range.UnitRange I64) : BitMutationM I64 :=
  match binaryLiftRange (JuliaLean.base.range.length_AbstractUnitRange
      (R := JuliaLean.base.range.UnitRange I64) (T := I64) (D := I64) (I := I64) r) with
  | .ok n => pure n
  | .error e => throw (binaryShapeError e)

/-- Native Vector range bounds at base/abstractarray.jl:690-706,753,756-757.
The installed range checker evaluates empty/first/last in source order. Its
callbacks are the concrete Int UnitRange field and OneTo-index methods. -/
-- Source: base/abstractarray.jl:690-706 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function checkbounds(::Type{Bool}, A::AbstractArray, i)
--     @inline
--     return checkindex(Bool, eachindex(IndexLinear(), A), i)
-- end
-- 
-- """
--     checkbounds(A, I...)
-- 
-- Throw an error if the specified indices `I` are not in bounds for the given array `A`.
-- """
-- checkbounds(A::AbstractArray, I...)
-- 
-- """
--     checkbounds_indices(Bool, IA, I)
-- 
-- Return `true` if the "requested" indices in the tuple `I` fall within
-- the bounds of the "permitted" indices specified by the tuple
-- /Source

-- Source: base/abstractarray.jl:753-753 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkindex(::Type{Bool}, inds::OneTo{T}, i::T) where {T<:BitInteger} = unsigned(i -% one(i)) < unsigned(last(inds))
-- /Source

-- Source: base/abstractarray.jl:756-757 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- checkindex(::Type{Bool}, inds::AbstractUnitRange, i::AbstractRange) =
--     isempty(i) | (checkindex(Bool, inds, first(i)) & checkindex(Bool, inds, last(i)))
-- /Source

private def splitRestRangeBounds (a : Nat) (r : JuliaLean.base.range.UnitRange I64) :
    BitMutationM Unit := do
  let len ← mutableLength a
  let checked := JuliaLean.base.abstractarray.checkindexRange
    (fun r : JuliaLean.base.range.UnitRange I64 => pure (decide (r.start > r.stop)))
    (fun r => pure r.start) (fun r => pure r.stop)
    (fun len i => pure (JuliaLean.base.abstractarray.checkindexOneTo len i)) len r
  let accepted ← match binaryLiftArray checked with
    | .ok value => pure value
    | .error e => throw (binaryShapeError e)
  if !accepted then throw .bounds

/-- The rank-one range axes at base/range.jl:706-707 and
base/abstractarray.jl:100-103. A one-element tuple stays a Tuple1, and its single
axis is the installed unchecked_oneto constructor. Length is evaluated again,
as in size(I), rather than reusing the earlier lI read in getindex. -/
-- Source: base/range.jl:706-707 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(r::AbstractRange) = (@inline; (length(r),))
-- 
-- /Source

-- Source: base/abstractarray.jl:100-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function axes(A)
--     @inline
--     map(unchecked_oneto, size(A))
-- end
-- /Source

private def splitRestRangeAxes (r : JuliaLean.base.range.UnitRange I64) :
    BitMutationM (JuliaLean.base.range.Tuple1 (JuliaLean.base.range.OneTo I64)) :=
  letI : JuliaLean.base.range.JLength (JuliaLean.base.range.UnitRange I64) I64 :=
    ⟨fun r => JuliaLean.base.range.length_AbstractUnitRange
      (R := JuliaLean.base.range.UnitRange I64) (T := I64) (D := I64) (I := I64) r⟩
  do
    let dims ← match binaryLiftRange (JuliaLean.base.range.size_AbstractRange r) with
      | .ok dims => pure dims
      | .error e => throw (binaryShapeError e)
    pure ⟨JuliaLean.base.range.unchecked_oneto dims._1⟩

/-- Complete similar(A, axes(I)) dispatch for a Vector{UInt64} and a singleton
OneTo tuple: abstractarray.jl:821,832,842-843 followed by array.jl:419.
The element type is fixed by this specialization, and the final constructor is
the supplied UInt64 mutableAllocate with the actual eight-byte runtime layout. 
Julia source: base/array.jl:419. -/
-- Source: base/abstractarray.jl:821-821 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(a::AbstractArray{T}, dims::Tuple) where {T}                = similar(a, T, dims)
-- /Source

-- Source: base/abstractarray.jl:832-843 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(a::AbstractArray, ::Type{T}, dims::Tuple{Union{Integer, OneTo}, Vararg{Union{Integer, OneTo}}}) where {T} = similar(a, T, to_shape(dims))
-- # similar creates an Array by default
-- similar(a::AbstractArray, ::Type{T}, dims::Dims{N}) where {T,N}    = Array{T,N}(undef, dims)
-- 
-- to_shape(::Tuple{}) = ()
-- to_shape(dims::Dims) = dims
-- to_shape(dims::DimsOrInds) = map(to_shape, dims)::DimsOrInds
-- # each dimension
-- to_shape(i::Int) = i
-- to_shape(i::Integer) = Int(i)
-- to_shape(r::AbstractOneTo) = _to_shape(last(r))
-- _to_shape(x::Integer) = to_shape(x)
-- /Source

-- Source: base/array.jl:419-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- similar(a::Array, T::Type, dims::Dims{N}) where {N} = Array{T,N}(undef, dims)
-- /Source

private def splitRestSimilarUInt64 (a : Nat)
    (axes : JuliaLean.base.range.Tuple1 (JuliaLean.base.range.OneTo I64)) :
    BitMutationM Nat :=
  JuliaLean.base.abstractarray.similarDims
    (fun a _element axes =>
      JuliaLean.base.abstractarray.similarLegacyOneTo
        (fun axes : JuliaLean.base.range.Tuple1 (JuliaLean.base.range.OneTo I64) => do
          let dim ← JuliaLean.base.abstractarray.toShapeOneTo
            (fun axis : JuliaLean.base.range.OneTo I64 => pure axis.stop)
            (fun n => JuliaLean.base.abstractarray.toShapeIntegerHelper
              (fun n => pure (JuliaLean.base.abstractarray.toShapeInt n)) n) axes._1
          pure (JuliaLean.base.range.Tuple1.mk dim))
        (fun a _element dims => JuliaLean.base.array.similar419
          (fun ds : JuliaLean.base.range.Tuple1 I64 =>
            mutableAllocate (MemoryLayoutMetadata.ofRuntime uint64Layout).allocation a ds._1)
          a dims)
        a U64 axes)
    U64 a axes

/-- Concrete one-based Vector firstindex, base/abstractarray.jl:394,452.
The header/axis is observed before taking the installed OneTo first element. -/
-- Source: base/abstractarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexLinear, A::Union{Array, Memory}) = unchecked_oneto(length(A))
-- /Source

-- Source: base/abstractarray.jl:452-452 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- firstindex(a::AbstractArray) = (@inline; first(eachindex(IndexLinear(), a)))
-- /Source

-- Source: base/range.jl:868-868 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(r::OneTo{T}) where {T} = oneunit(T)
-- /Source

private def splitRestFirstindex (a : Nat) : BitMutationM I64 := do
  let len ← mutableLength a
  let value := JuliaLean.base.abstractarray.firstindexArray
    (JuliaLean.base.abstractarray.eachindexDense
      (fun _ : Nat => pure len) JuliaLean.base.range.unchecked_oneto)
    (fun axis => pure (JuliaLean.base.range.first_OneTo axis)) a
  match binaryLiftArray value with
  | .ok n => pure n
  | .error e => throw (binaryShapeError e)

/-- Concrete Vector lastindex, base/abstractarray.jl:429.
The native OneTo last endpoint is the vector header length. -/
-- Source: base/abstractarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- eachindex(::IndexLinear, A::Union{Array, Memory}) = unchecked_oneto(length(A))
-- /Source

-- Source: base/abstractarray.jl:429-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- lastindex(a::AbstractArray) = (@inline; last(eachindex(IndexLinear(), a)))
-- /Source

-- Source: base/range.jl:877-877 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- last(r::OrdinalRange{T}) where {T} = convert(T, r.stop) # via steprange_last
-- /Source

private def splitRestLastindex (a : Nat) : BitMutationM I64 := do
  let len ← mutableLength a
  let value := JuliaLean.base.abstractarray.lastindexArray
    (JuliaLean.base.abstractarray.eachindexDense
      (fun _ : Nat => pure len) JuliaLean.base.range.unchecked_oneto)
    (fun axis : JuliaLean.base.range.OneTo I64 => pure axis.stop) a
  match binaryLiftArray value with
  | .ok n => pure n
  | .error e => throw (binaryShapeError e)

/-- The actual array.jl:981-990 slice implementation, with every callable closed.
Raw UInt64 copying uses mutableCopyto, so no fresh uninitialized destination cell
is read as a UInt64 value before being overwritten. 
Julia source: base/array.jl:981-990. -/
-- Source: base/array.jl:981-990 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(A::Array, I::AbstractUnitRange{<:Integer})
--     @inline
--     @boundscheck checkbounds(A, I)
--     lI = length(I)
--     X = similar(A, axes(I))
--     if lI > 0
--         copyto!(X, firstindex(X), A, first(I), lI)
--     end
--     return X
-- end
-- /Source

def splitRestSliceUInt64 (a : Nat) (r : JuliaLean.base.range.UnitRange I64) : BitMutationM Nat :=
  JuliaLean.base.array.getindexUnitRange
    (fun n : I64 => pure (decide (n > int 0))) splitRestRangeBounds
    splitRestRangeLength splitRestRangeAxes splitRestSimilarUInt64
    splitRestFirstindex (fun r => pure r.start) mutableCopyto a r

/-- UInt64 Vector resize at base/array.jl:1559-1574, with the actual installed
UInt64 grow/delete storage operations. All four branches are real bindings, even
though this source caller uses first=false. The source header is mutated in place. -/
-- Source: base/array.jl:1559-1574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function resize!(a::Vector, nl_::Integer; first::Bool=false)
--     nl = Int(nl_)::Int
--     l = length(a)
--     if nl > l
--         # Since l is positive, if nl > l, both are positive, and so nl-l is also
--         # positive. But the compiler does not know that, so we mask out top bit.
--         # This allows the compiler to skip the check
--         first ? _growbeg!(a, (nl-l) & typemax(Int)) : _growend!(a, (nl-l) & typemax(Int))
--     elseif nl != l
--         if nl < 0
--             _throw_argerror("new length must be ≥ 0")
--         end
--         first ? _deletebeg!(a, l-nl) : _deleteend!(a, l-nl)
--     end
--     return a
-- end
-- /Source

def splitRestResizeUInt64 (a : Nat) (n : I64) : BitMutationM Nat :=
  JuliaLean.base.array.resize pure mutableLength and_int
    growChunksAtFront growChunkVector
    (JuliaLean.base.array.deletebeg chunkStorage pure) deleteChunkEnd a n false

/-- Vector{UInt64} specialization only of base/bitarray.jl:1941-1946.
The separate end occurrences each query lastindex before slicing. The source is
resized after the fresh suffix has been copied, preserving direct and backing-store
aliases. Negative n is deliberately accepted by the source check; native overflow,
range BoundsError, allocation errors, and possible growth retain their source order.
The BitVector arm and arbitrary element layouts are not claimed by this model. -/
-- Source: base/bitarray.jl:1941-1946 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _split_rest(a::Union{Vector, BitVector}, n::Int)
--     _check_length_split_rest(length(a), n)
--     last_n = a[end-n+1:end]
--     resize!(a, length(a) - n)
--     return a, last_n
-- end
-- /Source

def splitRestUInt64 (a : Nat) (n : I64) : BitMutationM (Nat × Nat) := do
  splitRestCheckLength (← mutableLength a) n
  let first := (← splitRestLastindex a) - n + int 1
  let last ← splitRestLastindex a
  let r ← splitRestNativeRange first last
  let suffix ← splitRestSliceUInt64 a r
  let _ ← splitRestResizeUInt64 a ((← mutableLength a) - n)
  pure (a, suffix)


end JuliaLean.base.bitarray.Models1Group16


namespace JuliaLean.base.bitarray.Models2Group11

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

/-- Native UInt64 storage together with the raw address bits stored in each
GenericMemory.ptr field, indexed by the same memory identity as memories.
The equal table lengths are a native representation invariant used by the
properties. The table contains field data, not a dataids implementation or a
callable correctness oracle. Distinct Array headers can share one memory row.
Julia source: base/abstractarray.jl:1627-1628; base/bitarray.jl:110. -/
-- Source: base/abstractarray.jl:1627-1628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- dataids(A::Memory) = (UInt(A.ptr),)
-- dataids(A::Array) = dataids(A.ref.mem)
-- /Source
structure DataIdState where
  memory : MutableMemory U64
  pointers : List U64

/-- State/error carrier for the concrete field reads behind
base/bitarray.jl:110. Invalid instrumented handles report the existing bounds
error; an actual Julia object always has its referenced fields. -/
-- Source: base/bitarray.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- dataids(B::BitArray) = dataids(B.chunks)
-- /Source
abbrev DataIdM := ExceptT JuliaLean.base.array.Error (StateM DataIdState)

/-- Lift the installed concrete UInt64 Array-header read, preserving its error
state. Pointer-field data remain unchanged. No runtime operation is supplied by
the caller of this adapter. Julia source: base/abstractarray.jl:1628. -/
-- Source: base/abstractarray.jl:1628-1628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- dataids(A::Array) = dataids(A.ref.mem)
-- /Source
def liftDataIdMemory {A : Type} (action : BitMutationM A) : DataIdM A := do
  let before ← get
  let (result, memory) := action.run before.memory
  set { before with memory := memory }
  match result with
  | .ok value => pure value
  | .error error => throw error

/-- Concrete Memory dataids at base/abstractarray.jl:1627. The stored pointer
field is read from the addressed memory row. The installed dataidsMemory body
constructs its singleton tuple; UInt(ptr) preserves these exact native address
bits (base/boot.jl:1198), without an address-conversion callback. No memory
contents, array offset, or array length contributes to the identifier. -/
-- Source: base/abstractarray.jl:1627-1627 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- dataids(A::Memory) = (UInt(A.ptr),)
-- /Source
-- Source: base/boot.jl:1198-1198 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- UInt(x::Ptr) = bitcast(UInt, x)
-- /Source
def memoryDataIds (memoryIdentity : Nat) : DataIdM (List U64) := do
  match (← get).pointers[memoryIdentity]? with
  | none => throw .bounds
  | some address =>
      JuliaLean.base.abstractarray.dataidsMemory
        (fun value : U64 => value) (fun value => pure value) address

/-- Concrete Vector{UInt64} dataids required by base/bitarray.jl:110. The real
Array header supplies ref, ref supplies the backing memory identity, and the
closed Memory method reads that memory's stored pointer. This reuses both
installed Base bodies and never confuses a chunk-array handle with its backing
memory address. Julia source: base/abstractarray.jl:1628. -/
-- Source: base/abstractarray.jl:1628-1628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- dataids(A::Array) = dataids(A.ref.mem)
-- /Source
def chunkVectorDataIds (chunks : Nat) : DataIdM (List U64) := do
  let header ← liftDataIdMemory (mutableVector chunks)
  JuliaLean.base.abstractarray.dataidsDense
    MutableVector.reference (fun reference : Nat × I64 => reference.1)
    memoryDataIds header

/-- Complete dataids(B::BitArray), base/bitarray.jl:110. Every rank and all
stored lengths/dimensions are admitted. Its known Vector{UInt64} callee is
closed over the installed concrete Array/Memory chain and stored pointer data.
Aliased chunk headers follow the same memory row and return the same UInt. -/
-- Source: base/bitarray.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- dataids(B::BitArray) = dataids(B.chunks)
-- /Source
def dataIds {N : Nat} (B : BitArray N) : DataIdM (List U64) :=
  bitArrayDataIds chunkVectorDataIds B

end JuliaLean.base.bitarray.Models2Group11


namespace JuliaLean.base.bitarray.Models2Group11

open JuliaLean JuliaLean.base.bitarray

/-- The selected right-shift callee for the completely untyped input at
base/bitarray.jl:115. Input/result types may be arbitrary Julia tagged values;
the effect monad retains custom dispatch, errors, mutation and nonreturn.
This field models the operator >>, not a supplied implementation of _div64. -/
-- Source: base/bitarray.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _div64(l) = l >> 6
-- /Source
structure Div64Ops (m : Type → Type) (A R : Type) where
  shiftRight : A → I64 → m R

/-- Complete generic _div64 at base/bitarray.jl:115. The source's literal is a
native Int and the selected operator receives the original input unchanged.
Concrete Base instantiations use the installed shr_Int operator model. -/
-- Source: base/bitarray.jl:115-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _div64(l) = l >> 6
-- /Source
def div64Generic {m : Type → Type} [Monad m] {A R : Type}
    (ops : Div64Ops m A R) (value : A) : m R :=
  ops.shiftRight value (int 6)

/-- The selected mixed-argument & operation at base/bitarray.jl:116. Any
promotion or custom behavior belongs to that genuinely open operator dispatch;
neither its result type nor its effects are restricted to native integers. -/
-- Source: base/bitarray.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _mod64(l) = l & 63
-- /Source
structure Mod64Ops (m : Type → Type) (A R : Type) where
  bitAnd : A → I64 → m R

/-- Complete generic _mod64 at base/bitarray.jl:116. Pass the actual source
literal Int(63), preserving the open operand's original type and identity. -/
-- Source: base/bitarray.jl:116-116 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _mod64(l) = l & 63
-- /Source
def mod64Generic {m : Type → Type} [Monad m] {A R : Type}
    (ops : Mod64Ops m A R) (value : A) : m R :=
  ops.bitAnd value (int 63)

/-- Independently selected subtraction and bitwise-and operators for the
untyped input at base/bitarray.jl:117. Subtraction may change the intermediate
type. A single tagged type can represent heterogeneous results when needed.
No correctness, purity, type-preservation, or termination law is assumed. -/
-- Source: base/bitarray.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _blsr(x)= x & (x-1) #zeros the last set bit. Has native instruction on many archs. needed in multidimensional.jl
-- /Source
structure BlsrOps (m : Type → Type) (A Difference R : Type) where
  subtract : A → I64 → m Difference
  bitAnd : A → Difference → m R

/-- Complete generic _blsr at base/bitarray.jl:117. Evaluate subtraction
using the native literal one before selecting/calling & on the original x and
the exact returned intermediate value. Subtraction failure prevents the & call;
subtraction mutations remain visible to it. -/
-- Source: base/bitarray.jl:117-117 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @inline _blsr(x)= x & (x-1) #zeros the last set bit. Has native instruction on many archs. needed in multidimensional.jl
-- /Source
def blsrGeneric {m : Type → Type} [Monad m] {A Difference R : Type}
    (ops : BlsrOps m A Difference R) (value : A) : m R := do
  let difference ← ops.subtract value (int 1)
  ops.bitAnd value difference

end JuliaLean.base.bitarray.Models2Group11


namespace JuliaLean.base.bitarray.Models2Group11

open JuliaLean

set_option maxRecDepth 10000

-- Source: base/boot.jl:287-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- #primitive type UInt64  <: Unsigned 64 end
-- /Source
/-- Native little-endian eight-byte representation of the `UInt64` type
documented at `base/boot.jl:287`, required by `base/bitarray.jl:306-311`
and the concrete `pointerref` invoked at
`base/pointer.jl:151`. This encodes the existing 64-bit unsigned representation,
without a user-supplied byte-decoding callback. -/
def littleEndianU64Encode (value : JInt .u64) : List (JInt .u8) :=
  [JInt.wrap .u8 (value.val / 256 ^ 0),
   JInt.wrap .u8 (value.val / 256 ^ 1),
   JInt.wrap .u8 (value.val / 256 ^ 2),
   JInt.wrap .u8 (value.val / 256 ^ 3),
   JInt.wrap .u8 (value.val / 256 ^ 4),
   JInt.wrap .u8 (value.val / 256 ^ 5),
   JInt.wrap .u8 (value.val / 256 ^ 6),
   JInt.wrap .u8 (value.val / 256 ^ 7)]

-- Source: base/pointer.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_load(p::Ptr, i::Integer=1) = pointerref(p, Int(i), 1)
-- /Source
/-- Decode native little-endian bytes for the `UInt64` load at
`base/bitarray.jl:311`, using the concrete runtime representation behind
`base/pointer.jl:151`. Actual pointer loads pass exactly eight bytes;
the total definition reduces any supplied byte string modulo `2^64`. -/
def littleEndianU64Decode (bytes : List (JInt .u8)) : JInt .u64 :=
  JInt.wrap .u64 (bytes.foldr (fun byte accumulated => byte.val + 256 * accumulated) 0)

/-- Euclidean base-256 reconstruction used only to establish the concrete
runtime representation's roundtrip field. -/
private theorem littleEndianU64Step (x divisor : Int) (h : 0 ≤ divisor) :
    (x / divisor) % 256 + 256 * (x / (divisor * 256)) = x / divisor := by
  have heq := Int.emod_add_mul_ediv (x / divisor) 256
  rw [Int.ediv_ediv_of_nonneg h] at heq
  exact heq

-- Source: base/pointer.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_load(p::Ptr, i::Integer=1) = pointerref(p, Int(i), 1)
-- /Source
/-- Concrete native `UInt64` byte layout for the installed `unsafeLoad` model
of `base/pointer.jl:151`. The small proofs discharge representation fields of
`ByteCodec`; they do not prove a public method property or assume a decoder law.
The target is the packet's 64-bit little-endian platform. -/
def littleEndianU64Codec : JuliaLean.base.pointer.ByteCodec (JInt .u64) where
  elementSize := JInt.wrap .i64 8
  size_nonnegative := by decide
  encode := littleEndianU64Encode
  decode := littleEndianU64Decode
  encode_length value := by
    simp [littleEndianU64Encode, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
  decode_encode value := by
    apply Subtype.ext
    have hrange := value.property
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hrange
    simp [littleEndianU64Decode, littleEndianU64Encode, List.foldr,
      JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]
    have h7 : value.val / 72057594037927936 % 256 =
        value.val / 72057594037927936 := by omega
    have h6 : value.val / 281474976710656 % 256 +
        256 * (value.val / 72057594037927936) = value.val / 281474976710656 := by
      simpa using littleEndianU64Step value.val 281474976710656 (by decide)
    have h5 : value.val / 1099511627776 % 256 +
        256 * (value.val / 281474976710656) = value.val / 1099511627776 := by
      simpa using littleEndianU64Step value.val 1099511627776 (by decide)
    have h4 : value.val / 4294967296 % 256 +
        256 * (value.val / 1099511627776) = value.val / 4294967296 := by
      simpa using littleEndianU64Step value.val 4294967296 (by decide)
    have h3 : value.val / 16777216 % 256 +
        256 * (value.val / 4294967296) = value.val / 16777216 := by
      simpa using littleEndianU64Step value.val 16777216 (by decide)
    have h2 : value.val / 65536 % 256 +
        256 * (value.val / 16777216) = value.val / 65536 := by
      simpa using littleEndianU64Step value.val 65536 (by decide)
    have h1 : value.val / 256 % 256 +
        256 * (value.val / 65536) = value.val / 256 := by
      simpa using littleEndianU64Step value.val 256 (by decide)
    rw [h7, h6, h5, h4, h3, h2, h1, Int.emod_add_mul_ediv]
    omega

end JuliaLean.base.bitarray.Models2Group11


namespace JuliaLean.base.bitarray.Models2Group11

open JuliaLean
open JuliaLean.base.int

/-!
Concrete runtime boundary for `base/bitarray.jl:274-337`:
`Array{Bool}` and `Vector{UInt64}` retain their native size tuple and the
installed MemoryRef pointer representation. Both access one shared byte heap.
The platform is the packet's 64-bit little-endian native platform. The access
log records the obligations of unchecked array/pointer operations and Bool's
0/1 representation. Failed obligations do not synthesize Julia exceptions:
the source uses `@inbounds`; valid native executions require those obligations,
live/provenant references, and Julia's documented aliasing restrictions
(`doc/src/devdocs/ub.md:38-48`). Raw heap execution remains total outside that
boundary, without claiming defined Julia behavior there. The array headers
are immutable snapshots during this call; all element reads and writes use
the live heap, including possible shared addresses.
-/

-- Source: base/boot.jl:80-85 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- #end
--
-- #mutable struct Array{T,N} <: DenseArray{T,N}
-- #  ref::MemoryRef{T}
-- #  size::NTuple{N,Int}
-- #end
-- /Source
/-- Concrete native Array header fields at `base/boot.jl:82-85`, retaining
its actual MemoryRef and a machine-sized dimension tuple. -/
structure BoolCopyArray (T : Type) (N : Nat) where
  reference : JuliaLean.base.pointer.PointerMemoryRef T
  dimensions : JuliaLean.base.pointer.TupleN I64 N
  rankFits : N ≤ IntTy.i64.max.toNat

-- Source: base/bitarray.jl:291-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     ind = pos_s
--     @inbounds if ld0 > 0
--         c = UInt64(0)
--         for j = ld0:lt0
--             c |= (UInt64(C[ind]) << j)
--             ind += 1
--         end
--         Bc[kd0] = (Bc[kd0] & msk_d0) | (c & ~msk_d0)
--         bind += 1
--     end
--
-- /Source
/-- Observable heap-access categories for the unchecked accesses at
`base/bitarray.jl:291-301` and the pointer loads at line 311. -/
inductive BoolCopyAccessKind where
  | boolRead | chunkRead | chunkWrite | wordLoad
  deriving DecidableEq, Repr

-- Source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(A::Array, i::Int)
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
-- end
-- /Source
/-- Ghost obligation emitted by the unchecked read at `base/essentials.jl:1076`
and corresponding native stores. canonicalBool is checked only for scalar
Bool reads; a wordLoad is a UInt64 load and does not validate eight Bools. -/
structure BoolCopyAccess where
  kind : BoolCopyAccessKind
  address : U64
  width : Nat
  index : I64
  arrayLength : Option I64
  withinArray : Bool
  validBytes : Bool
  canonicalBool : Bool
  deriving Repr

-- Source: base/bitarray.jl:274-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copy_to_bitarray_chunks!(Bc::Vector{UInt64}, pos_d::Int, C::Array{Bool}, pos_s::Int, numbits::Int)
-- /Source
/-- Shared heap and observational access log for `base/bitarray.jl:274`.
Header snapshots are arguments; every element access observes this live heap. -/
structure BoolCopyState where
  heap : JuliaLean.base.pointer.ByteHeap
  accesses : List BoolCopyAccess

-- Source: base/bitarray.jl:327-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
--     end
--     @inbounds if bind ≤ kd1
--         @assert bind == kd1 "bind != kd1"
--         c = UInt64(0)
--         for j = 0:ld1
--             c |= (UInt64(C[ind]) << j)
--             ind += 1
--         end
--         Bc[kd1] = (Bc[kd1] & msk_d1) | (c & ~msk_d1)
--     end
-- end
-- /Source
/-- Source exceptions preserve all preceding heap effects at
`base/bitarray.jl:328`, using the installed Array Error type. -/
abbrev BoolCopyM := ExceptT JuliaLean.base.array.Error (StateM BoolCopyState)

-- Source: base/essentials.jl:12-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- size(a::Array) = getfield(a, :size)
-- length(t::AbstractArray) = (@inline; prod(size(t)))
-- /Source
/-- Native Array length observer for `base/essentials.jl:13`; multiplication
uses the installed native-Int shape product. The tuple is machine-sized. -/
def boolCopyArrayLength {T : Type} {N : Nat} (a : BoolCopyArray T N) : I64 :=
  JuliaLean.base.essentials.prodDims a.dimensions.values

-- Source: base/abstractarray.jl:1279-1279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- pointer(x::AbstractArray{T}) where {T} = unsafe_convert(Ptr{T}, cconvert(Ptr{T}, x))
-- /Source
/-- Closed Array pointer conversion at `base/abstractarray.jl:1279`, composed
from the installed cconvert and MemoryRef unsafe-conversion methods. -/
def boolCopyDataPointer {T : Type} {N : Nat}
    (a : BoolCopyArray T N) : JuliaLean.base.pointer.Ptr T :=
  match h : JuliaLean.base.abstractarray.pointerArray
      (fun a : BoolCopyArray T N => pure
        (JuliaLean.base.pointer.cconvertArray BoolCopyArray.reference a))
      (fun reference => pure (JuliaLean.base.pointer.unsafeConvertMemoryRef
        (S := T) reference)) a with
  | .ok p => p
  | .error _ => False.elim (by
      simp [JuliaLean.base.abstractarray.pointerArray] at h
      cases h)

-- Source: base/indices.jl:526-527 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- first(iter::LinearIndices) = 1
-- first(iter::LinearIndices{1}) = (@inline; first(axes1(iter.indices[1])))
-- /Source
/-- Native Array linear-index origin at `base/indices.jl:526-527`.
The vector branch has a native OneTo axis; its axes1 is the same OneTo. -/
def boolCopyLinearFirst {T : Type} {N : Nat} (a : BoolCopyArray T N) : I64 :=
  letI : JuliaLean.base.range.JOneunit I64 := ⟨int 1⟩
  letI : Inhabited (JuliaLean.base.range.OneTo I64) :=
    ⟨JuliaLean.base.range.unchecked_oneto (int 0)⟩
  match a.dimensions.values with
  | [length] =>
    JuliaLean.base.indices.first_LinearIndices_1 (m := Id)
      (fun axis : JuliaLean.base.range.OneTo I64 => pure axis)
      (fun axis : JuliaLean.base.range.OneTo I64 =>
        pure (JuliaLean.base.range.first_OneTo (T := I64) axis))
      ⟨[JuliaLean.base.range.unchecked_oneto length]⟩
  | _ => JuliaLean.base.indices.first_LinearIndices
      (R := I64) ⟨a.dimensions.values⟩

-- Source: base/abstractarray.jl:1280-1286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function pointer(x::AbstractArray{T}, i::Integer) where T
--     @inline
--     pointer(x) + Int(_memory_offset(x, i))::Int
-- end
--
-- # The distance from pointer(x) to the element at x[I...] in bytes
-- _memory_offset(x::DenseArray, I::Vararg{Any,N}) where {N} = (_to_linear_index(x, I...) - first(LinearIndices(x)))*elsize(x)
-- /Source
/-- Closed concrete Bool-Array `pointer(C,i)` at `base/abstractarray.jl:1280`.
The installed DenseArray offset body receives native scalar indexing, native
OneTo origin, Bool's one-byte elsize, and wrapping Int arithmetic. -/
def boolCopyPointer {N : Nat} (a : BoolCopyArray Bool N) (i : I64) :
    JuliaLean.base.pointer.Ptr Bool :=
  match h : JuliaLean.base.abstractarray.pointerIndex
      (fun a => pure (boolCopyDataPointer a))
      (fun a i => JuliaLean.base.abstractarray.memoryOffsetDense
        (fun a i => pure (JuliaLean.base.abstractarray.toLinearScalar a i))
        (fun a => pure a)
        (fun a => pure (boolCopyLinearFirst a))
        (fun i origin => pure (i - origin))
        (fun _ => pure (int 1))
        (fun difference size => pure (difference * size)) a i)
      (fun offset => pure (JuliaLean.base.number.convertSame offset))
      (fun p offset => pure (JuliaLean.base.pointer.ptrAddI64 p offset)) a i with
  | .ok p => p
  | .error _ => False.elim (by
      simp [JuliaLean.base.abstractarray.pointerIndex,
        JuliaLean.base.abstractarray.memoryOffsetDense] at h
      cases h)

-- Source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(A::Array, i::Int)
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
-- end
-- /Source
/-- Decidable raw-byte accessibility recorded for the unchecked access at
`base/essentials.jl:1076`; it is the installed validRange predicate's finite form. -/
def boolCopyByteRangeValid (heap : JuliaLean.base.pointer.ByteHeap)
    (address : U64) (width : Nat) : Bool :=
  decide (address.val.toNat + width ≤ 2 ^ 64) &&
    (List.range width).all (fun offset =>
      heap.validByte (JuliaLean.base.pointer.addressMod (address.val.toNat + offset)))

-- Source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(A::Array, i::Int)
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
-- end
-- /Source
/-- Ghost access obligations for `base/essentials.jl:1076`. Source @inbounds
elides the boundscheck; recording an unmet obligation does not throw. -/
def boolCopyRecord (kind : BoolCopyAccessKind) (address : U64) (width : Nat)
    (index : I64) (length : Option I64) (canonicalBool : Bool := true) : BoolCopyM Unit := do
  let state ← get
  let event : BoolCopyAccess :=
    { kind, address, width, index, arrayLength := length
      withinArray := match length with
        | none => true
        | some n => decide (1 ≤ index.val ∧ index.val ≤ n.val)
      validBytes := boolCopyByteRangeValid state.heap address width
      canonicalBool }
  set { state with accesses := state.accesses ++ [event] }

-- Source: base/boot.jl:1169-1169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- toUInt64(x::Bool)     = zext_int(UInt64, x)
-- /Source
/-- Native `UInt64(C[i])` used at `base/bitarray.jl:295`, with
`base/boot.jl:1169` zero extension. Bool storage is exactly byte 0 or byte 1;
raw noncanonical bytes are only an instrumented undefined execution. -/
def boolCopyReadBoolWord {N : Nat} (a : BoolCopyArray Bool N) (i : I64) : BoolCopyM U64 := do
  let address := (JuliaLean.base.pointer.ptrAddI64
    (boolCopyDataPointer a) (i - int 1)).address
  let state ← get
  let byte := state.heap.readByte address.val.toNat
  boolCopyRecord .boolRead address 1 i (some (boolCopyArrayLength a))
    (byte.val == 0 || byte.val == 1)
  pure (JuliaLean.base.int.widenTo .u64 byte)

-- Source: base/pointer.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_load(p::Ptr, i::Integer=1) = pointerref(p, Int(i), 1)
-- /Source
/-- The closed native-Int `unsafe_load` at `base/pointer.jl:151`:
Int conversion is identity and the installed pointerref uses alignment one. -/
def boolCopyNativeWord (heap : JuliaLean.base.pointer.ByteHeap)
    (p : JuliaLean.base.pointer.Ptr U64) (i : I64) : U64 :=
  match h : JuliaLean.base.pointer.unsafeLoad littleEndianU64Codec
      (fun i : I64 => pure (JuliaLean.base.number.convertSame i)) p heap i with
  | .ok word => word
  | .error _ => False.elim (by
      simp [JuliaLean.base.pointer.unsafeLoad] at h
      cases h)

-- Source: base/essentials.jl:1073-1077 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function getindex(A::Array, i::Int)
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefget(memoryrefnew(getfield(A, :ref), i, false), :not_atomic, false)
-- end
-- /Source
/-- Concrete native UInt64 Array read at `base/essentials.jl:1076`.
The source's memoryrefnew offset and byte load are the same installed indexed
pointer primitive; the inbounds check is represented only in the access log. -/
def boolCopyReadChunk (a : BoolCopyArray U64 1) (i : I64) : BoolCopyM U64 := do
  let p := boolCopyDataPointer a
  let address := (JuliaLean.base.pointer.indexedPointer littleEndianU64Codec p i).address
  boolCopyRecord .chunkRead address 8 i (some (boolCopyArrayLength a))
  let state ← get
  pure (boolCopyNativeWord state.heap p i)

-- Source: base/array.jl:1036-1041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function _setindex!(A::Array{T}, x::T, i::Int) where {T}
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefset!(memoryrefnew(A.ref, i, false), x, :not_atomic, false)
--     return A
-- end
-- /Source
/-- Native UInt64 memoryrefset at `base/array.jl:1039`, on the shared heap.
Pointer arithmetic and the eight-byte store use the installed pointerSet. -/
def boolCopyStoreChunkBytes (a : BoolCopyArray U64 1) (i : I64) (word : U64) :
    BoolCopyM Unit := do
  let p := boolCopyDataPointer a
  let address := (JuliaLean.base.pointer.indexedPointer littleEndianU64Codec p i).address
  boolCopyRecord .chunkWrite address 8 i (some (boolCopyArrayLength a))
  modify fun state => { state with heap :=
    (JuliaLean.base.pointer.pointerSet littleEndianU64Codec state.heap p word i (int 1)).1 }

-- Source: base/array.jl:1031-1041 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function setindex!(A::Array{T}, x, i::Int) where {T}
--     @_propagate_inbounds_meta
--     x = x isa T ? x : convert(T, x)::T
--     return _setindex!(A, x, i)
-- end
-- function _setindex!(A::Array{T}, x::T, i::Int) where {T}
--     @_noub_if_noinbounds_meta
--     @boundscheck checkbounds(A, i)
--     memoryrefset!(memoryrefnew(A.ref, i, false), x, :not_atomic, false)
--     return A
-- end
-- /Source
/-- Concrete `setindex!` and `_setindex!` at `base/array.jl:1031-1041`.
The value is already UInt64; boundschecks are elided by the caller's @inbounds.
The returned Array is discarded by the source assignment syntax. -/
def boolCopyWriteChunk (a : BoolCopyArray U64 1) (i : I64) (word : U64) :
    BoolCopyM Unit := do
  let _ ← JuliaLean.base.array.setindexScalar
    (fun _ : U64 => true) (fun word => word) (fun word => pure word)
    (fun a word i => JuliaLean.base.array.setindexTyped
      (fun _ _ => pure ())
      (fun a i _ => pure (a, i))
      (fun (a, i) word _ => boolCopyStoreChunkBytes a i word)
      a word i) a word i
  pure ()

-- Source: base/pointer.jl:151-151 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_load(p::Ptr, i::Integer=1) = pointerref(p, Int(i), 1)
-- /Source
/-- The cached P8 load at `base/bitarray.jl:311`, using `base/pointer.jl:151`.
It reads the current shared heap, so earlier chunk writes are visible. -/
def boolCopyLoadWord (p : JuliaLean.base.pointer.Ptr U64) (i : I64) : BoolCopyM U64 := do
  let address := (JuliaLean.base.pointer.indexedPointer littleEndianU64Codec p i).address
  boolCopyRecord .wordLoad address 8 i none
  let state ← get
  pure (boolCopyNativeWord state.heap p i)

-- Source: base/bitarray.jl:274-337 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function copy_to_bitarray_chunks!(Bc::Vector{UInt64}, pos_d::Int, C::Array{Bool}, pos_s::Int, numbits::Int)
--     kd0, ld0 = get_chunks_id(pos_d)
--     kd1, ld1 = get_chunks_id(pos_d + numbits - 1)
--
--     delta_kd = kd1 - kd0
--
--     u = _msk64
--     if delta_kd == 0
--         msk_d0 = msk_d1 = ~(u << ld0) | (u << (ld1+1))
--         lt0 = ld1
--     else
--         msk_d0 = ~(u << ld0)
--         msk_d1 = (u << (ld1+1))
--         lt0 = 63
--     end
--
--     bind = kd0
--     ind = pos_s
--     @inbounds if ld0 > 0
--         c = UInt64(0)
--         for j = ld0:lt0
--             c |= (UInt64(C[ind]) << j)
--             ind += 1
--         end
--         Bc[kd0] = (Bc[kd0] & msk_d0) | (c & ~msk_d0)
--         bind += 1
--     end
--
--     nc = _div64(numbits - ind + pos_s)
--     nc8 = (nc >>> 3) << 3
--     if nc8 > 0
--         ind8 = 1
--         P8 = Ptr{UInt64}(pointer(C, ind)) # unaligned i64 pointer
--         @inbounds for _ = 1:nc8
--             c = UInt64(0)
--             for j = 0:7
--                 # unaligned load
--                 c |= (pack8bools(unsafe_load(P8, ind8)) << (j<<3))
--                 ind8 += 1
--             end
--             Bc[bind] = c
--             bind += 1
--         end
--         ind += (ind8-1) << 3
--     end
--     @inbounds for _ = (nc8+1):nc
--         c = UInt64(0)
--         for j = 0:63
--             c |= (UInt64(C[ind]) << j)
--             ind += 1
--         end
--         Bc[bind] = c
--         bind += 1
--     end
--     @inbounds if bind ≤ kd1
--         @assert bind == kd1 "bind != kd1"
--         c = UInt64(0)
--         for j = 0:ld1
--             c |= (UInt64(C[ind]) << j)
--             ind += 1
--         end
--         Bc[kd1] = (Bc[kd1] & msk_d1) | (c & ~msk_d1)
--     end
-- end
-- /Source
/-- Complete concrete Bool-Array chunk copy at `base/bitarray.jl:274-337`.
Every counter, range endpoint, mask, offset and shift is a wrapping native Int
or UInt64 operation. The raw-byte loads are live and the P8 pointer is captured
once. Zero and negative counts follow the source without an added guard.
The result is the final assignment's UInt64, or Julia `nothing`, respectively.
Only the source assertion throws; unchecked-access obligations are logged. -/
def copyBoolChunks {N : Nat} (bc : BoolCopyArray U64 1) (posD : I64)
    (src : BoolCopyArray Bool N) (posS numbits : I64) : BoolCopyM (Option U64) := do
  let (kd0, ld0) := getChunksId posD
  let (kd1, ld1) := getChunksId (posD + numbits - int 1)
  let deltaKd := kd1 - kd0
  let u := u64Max
  let (mskD0, mskD1, lt0) :=
    if deltaKd == int 0 then
      let mask := or_int (not_int (shl_Int u ld0)) (shl_Int u (ld1 + int 1))
      (mask, mask, ld1)
    else
      (not_int (shl_Int u ld0), shl_Int u (ld1 + int 1), int 63)
  let mut bind := kd0
  let mut ind := posS
  if ld0 > int 0 then
    let mut c := u64 0
    for j in JuliaLean.base.array.intRange ld0 lt0 do
      c := or_int c (shl_Int (← boolCopyReadBoolWord src ind) j)
      ind := ind + int 1
    let old ← boolCopyReadChunk bc kd0
    boolCopyWriteChunk bc kd0 (or_int (and_int old mskD0) (and_int c (not_int mskD0)))
    bind := bind + int 1
  let nc := div64 (numbits - ind + posS)
  let nc8 := shl_Int (lshr_Int nc (int 3)) (int 3)
  if nc8 > int 0 then
    let mut ind8 := int 1
    let p8 : JuliaLean.base.pointer.Ptr U64 :=
      JuliaLean.base.pointer.convertPtrType (boolCopyPointer src ind)
    for _ in JuliaLean.base.array.intRange (int 1) nc8 do
      let mut c := u64 0
      for j in JuliaLean.base.array.intRange (int 0) (int 7) do
        c := or_int c (shl_Int
          (Models1Group15.pack8bools (← boolCopyLoadWord p8 ind8))
          (shl_Int j (int 3)))
        ind8 := ind8 + int 1
      boolCopyWriteChunk bc bind c
      bind := bind + int 1
    ind := ind + shl_Int (ind8 - int 1) (int 3)
  for _ in JuliaLean.base.array.intRange (nc8 + int 1) nc do
    let mut c := u64 0
    for j in JuliaLean.base.array.intRange (int 0) (int 63) do
      c := or_int c (shl_Int (← boolCopyReadBoolWord src ind) j)
      ind := ind + int 1
    boolCopyWriteChunk bc bind c
    bind := bind + int 1
  if bind ≤ kd1 then
    if bind != kd1 then throw (.assertion "bind != kd1")
    let mut c := u64 0
    for j in JuliaLean.base.array.intRange (int 0) ld1 do
      c := or_int c (shl_Int (← boolCopyReadBoolWord src ind) j)
      ind := ind + int 1
    let old ← boolCopyReadChunk bc kd1
    let result := or_int (and_int old mskD1) (and_int c (not_int mskD1))
    boolCopyWriteChunk bc kd1 result
    pure (some result)
  else pure none

end JuliaLean.base.bitarray.Models2Group11


namespace JuliaLean.base.bitarray.Models2Group11

open JuliaLean
open JuliaLean.base.int

-- Source: base/essentials.jl:1296-1296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- length(a::Array{T,1}) where {T} = getfield(getfield(a, :size), 1)
-- /Source
/-- Concrete vector length at `base/essentials.jl:1296`. The installed
method projects the sole native-Int size field; no product, conversion,
allocation, callback, or out-of-bounds default is used. -/
def boolCopyVectorLength {T : Type} (a : BoolCopyArray T 1) : I64 :=
  JuliaLean.base.essentials.lengthArray1
    (fun a _ => a.dimensions)
    (fun dimensions _ => dimensions.values[0]'(by rw [dimensions.length_eq]; decide)) a

-- Source: base/promotion.jl:677-677 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- min(x::T, y::T) where {T<:Real} = ifelse(y < x, y, x)
-- /Source
/-- Native signed-Int min at `base/promotion.jl:677`, closed through the
installed same-type min body and the installed signed comparison primitive. -/
def boolCopyNativeMin (x y : I64) : I64 :=
  match h : JuliaLean.base.promotion.minSameType
      (fun a b : I64 => pure (JuliaLean.base.int.lt_BitSigned a b)) x y with
  | .ok result => result
  | .error _ => False.elim (by
      simp [JuliaLean.base.promotion.minSameType] at h
      cases h)

-- Source: base/bitarray.jl:347-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- dumpbitcache(Bc::Vector{UInt64}, bind::Int, C::Vector{Bool}) =
--     copy_to_bitarray_chunks!(Bc, ((bind - 1) << 6) + 1, C, 1, min(bitcache_size, (length(Bc)-bind+1) << 6))
-- /Source
/-- Complete cache dump at `base/bitarray.jl:347-348`. Both shifts and every
intermediate use native wrapping Int arithmetic. Capacity is converted from
chunks to bits before min, and the exact UInt64-or-nothing result and effects
of the concrete Bool copy are preserved. Its documented raw-memory boundary
is the same as copyBoolChunks, including all machine-valued bind arguments. -/
def dumpBoolCache (bc : BoolCopyArray U64 1) (bind : I64)
    (src : BoolCopyArray Bool 1) : BoolCopyM (Option U64) :=
  copyBoolChunks bc (shl_Int (bind - int 1) (int 6) + int 1) src (int 1)
    (boolCopyNativeMin bitCacheSize
      (shl_Int (boolCopyVectorLength bc - bind + int 1) (int 6)))

end JuliaLean.base.bitarray.Models2Group11

namespace JuliaLean.base.bitarray.Dispatch

open JuliaLean JuliaLean.base.bitarray

-- Source: base/bitarray.jl:1478-1483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
/-- Int(start) dispatch depends on the open Integer subtype. The native scan,
its length checks, and its UInt64 bit intrinsic are closed Base callees. -/
def findNext {N : Nat} {I : Type} (toInt : I → BitMutationM I64)
    (B : BitArray N) (start : I) : BitMutationM (Option I64) := do
  let start ← toInt start
  bitArrayFindNext id (unsafeBitFindNext JuliaLean.base.int.trailing_zeros) B start

-- Source: base/bitarray.jl:1563-1568 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def findPrev {N : Nat} {I : Type} (toInt : I → BitMutationM I64)
    (B : BitArray N) (start : I) : BitMutationM (Option I64) := do
  let start ← toInt start
  bitArrayFindPrev id (unsafeBitFindPrev JuliaLean.base.int.top_set_bit) B start

-- Source: base/bitarray.jl:1520-1526 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def findNextFixed {N : Nat} {I : Type} (toInt : I → BitMutationM I64)
    (value : Bool) (B : BitArray N) (start : I) : BitMutationM (Option I64) := do
  let v := value
  if v == false then
    let start ← toInt start
    return ← bitArrayFindNextNot
      (JuliaLean.base.int.trailing_ones_Integer JuliaLean.base.int.trailing_zeros
        JuliaLean.base.int.not_int) B start
  if v == true then return ← findNext toInt B start
  return none

-- Source: base/bitarray.jl:1596-1602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def findPrevFixed {N : Nat} {I : Type} (toInt : I → BitMutationM I64)
    (value : Bool) (B : BitArray N) (start : I) : BitMutationM (Option I64) := do
  let v := value
  if v == false then
    let start ← toInt start
    return ← bitArrayFindPrevNot
      (JuliaLean.base.int.leading_ones_Integer JuliaLean.base.int.leading_zeros
        JuliaLean.base.int.not_int) B start
  if v == true then return ← findPrev toInt B start
  return none

-- Source: base/bitarray.jl:1531-1541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
/-- Each typed local converts its arbitrary predicate result to Bool before
the next call. The supplied functions represent only these two open dispatches. -/
-- Source: base/bitarray.jl:1532-1533,1608-1609 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def checkedPredicateBool {F V C : Type}
    (test : F → Bool → BitMutationM V) (convertBool : V → BitMutationM C)
    (asBool : C → Option Bool) (functionName : String) (testf : F) (value : Bool) :
    BitMutationM Bool := do
  let result ← convertBool (← test testf value)
  match asBool result with
  | some result => pure result
  | none => throw (.typeError (functionName ++ if value then ": f1" else ": f0"))

-- Source: base/bitarray.jl:1531-1541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def findNextIntChecked {N : Nat} {F V C : Type}
    (test : F → Bool → BitMutationM V) (convertBool : V → BitMutationM C)
    (asBool : C → Option Bool) (testf : F) (B : BitArray N) (start : I64) :
    BitMutationM (Option I64) :=
  bitArrayFindNextInt (checkedPredicateBool test convertBool asBool "_findnext_int")
    (findNext pure)
    (bitArrayFindNextNot
      (JuliaLean.base.int.trailing_ones_Integer JuliaLean.base.int.trailing_zeros
        JuliaLean.base.int.not_int)) testf B start

-- Source: base/bitarray.jl:1607-1617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def findPrevIntChecked {N : Nat} {F V C : Type}
    (test : F → Bool → BitMutationM V) (convertBool : V → BitMutationM C)
    (asBool : C → Option Bool) (testf : F) (B : BitArray N) (start : I64) :
    BitMutationM (Option I64) :=
  bitArrayFindPrevInt (checkedPredicateBool test convertBool asBool "_findprev_int")
    (findPrev pure)
    (bitArrayFindPrevNot
      (JuliaLean.base.int.leading_ones_Integer JuliaLean.base.int.leading_zeros
        JuliaLean.base.int.not_int)) testf B start

-- Source: base/bitarray.jl:1530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def findNextFunctionChecked {N : Nat} {F V C I : Type}
    (toInt : I → BitMutationM I64) (test : F → Bool → BitMutationM V)
    (convertBool : V → BitMutationM C) (asBool : C → Option Bool)
    (testf : F) (B : BitArray N) (start : I) : BitMutationM (Option I64) := do
  let start ← toInt start
  findNextIntChecked test convertBool asBool testf B start

-- Source: base/bitarray.jl:1606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def findPrevFunctionChecked {N : Nat} {F V C I : Type}
    (toInt : I → BitMutationM I64) (test : F → Bool → BitMutationM V)
    (convertBool : V → BitMutationM C) (asBool : C → Option Bool)
    (testf : F) (B : BitArray N) (start : I) : BitMutationM (Option I64) := do
  let start ← toInt start
  findPrevIntChecked test convertBool asBool testf B start

def findNextInt {N : Nat} {F V : Type}
    (test : F → Bool → BitMutationM V) (convertBool : V → BitMutationM Bool)
    (testf : F) (B : BitArray N) (start : I64) : BitMutationM (Option I64) :=
  findNextIntChecked test convertBool some testf B start

-- Source: base/bitarray.jl:1607-1617 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def findPrevInt {N : Nat} {F V : Type}
    (test : F → Bool → BitMutationM V) (convertBool : V → BitMutationM Bool)
    (testf : F) (B : BitArray N) (start : I64) : BitMutationM (Option I64) :=
  findPrevIntChecked test convertBool some testf B start

-- Source: base/bitarray.jl:1530-1530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def findNextFunction {N : Nat} {F V I : Type}
    (toInt : I → BitMutationM I64) (test : F → Bool → BitMutationM V)
    (convertBool : V → BitMutationM Bool) (testf : F) (B : BitArray N) (start : I) :
    BitMutationM (Option I64) := do
  let start ← toInt start
  findNextInt test convertBool testf B start

-- Source: base/bitarray.jl:1606-1606 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def findPrevFunction {N : Nat} {F V I : Type}
    (toInt : I → BitMutationM I64) (test : F → Bool → BitMutationM V)
    (convertBool : V → BitMutationM Bool) (testf : F) (B : BitArray N) (start : I) :
    BitMutationM (Option I64) := do
  let start ← toInt start
  findPrevInt test convertBool testf B start

-- Source: base/bitarray.jl:688-692 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def setIndex {N : Nat} {X : Type} (convertBool : X → BitMutationM Bool)
    (B : BitArray N) (x : X) (i : I64) : BitMutationM (BitArray N) := do
  Models1Group15.nativeScalarBounds B i
  let value ← convertBool x
  let _ ← Models1Group15.unsafeSetIndex B.chunks value i
  pure B

end JuliaLean.base.bitarray.Dispatch

namespace JuliaLean.base.bitarray.Models1Group15
open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
-- Source: base/bitarray.jl:1783-1787 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def bitMapGeneric {N K : Nat} {F R : Type} (runtime : AllocationData)
    (mapBang : F → (rank : Nat) → Ref rank → Ref N → Ref K → ObjectM R)
    (f : F) (left : Ref N) (right : Ref K) : ObjectM R := do
  let A ← readObject left
  let B ← readObject right
  let shape ← match Models1Group16.binaryShape A B with
    | .ok shape => pure shape
    | .error error => throw (Models1Group16.binaryShapeError error)
  let destination ← undefObject runtime (⟨shape, rfl⟩ : Dims shape.length)
  mapBang f shape.length destination left right
end JuliaLean.base.bitarray.Models1Group15
/-!
# BitArray chunk storage (`base/bitarray.jl`, master `bbfa0ce4150`)

A `BitArray` stores its elements in `chunks::Vector{UInt64}`: element `k`
(1-based) is bit `(k-1) % 64` of chunk `(k-1) ÷ 64 + 1`. The unused high bits of
the last chunk must always be zero (`base/bitarray.jl:5-6`); `count`, `==`,
`hash`, `any` and `all` read whole chunks and rely on that.

Modelling conventions of this area:

* A chunk is `U64 := BitVec 64`. Julia's `x << n` and `x >>> n` on `UInt64`
  for `0 ≤ n` are `BitVec` shifts by a `Nat`: both give zero once `n ≥ 64`,
  exactly like Julia. Every shift count in these functions is in `0:64`.
* A chunk vector is a `List U64`; `cget cs k` and `cset cs k v` are Julia's
  1-based `cs[k]` and `cs[k] = v`. All modelled reads are in bounds on valid
  inputs; `cget` returns `0` for an index Julia would read with `@inbounds`
  outside the vector (undefined behaviour in Julia), so a model that reaches it
  shows memory unsafety, which the properties detect through the chunk count.
* Element positions inside the chunk helpers are `Nat`. They are derived from
  lengths of existing BitArrays (at most `2^62` elements, since the chunks must
  fit in memory) and from user arguments that were range-checked first, so the
  Julia `Int` arithmetic on them never wraps. User-supplied indices and shifts
  are `JInt64` (Core) and every operation on them mirrors Julia's wrapping.
* `_growend!(chunks, k)` appends `k` uninitialised chunks. The model appends
  copies of an arbitrary `dirty : U64`; properties quantify over it.
-/

namespace JuliaLean.BitArrays

abbrev U64 := BitVec 64

/-- Chunk loop of `cmp(::BitVector, ::BitVector)`, `base/bitarray.jl:1211-1218`.
The low set bit of the xor identifies the first differing element. -/
def cmpChunks : List U64 → List U64 → Nat → Nat → Int
  | a :: as, b :: bs, na, nb =>
    let d := a ^^^ b
    if d = 0 then cmpChunks as bs na nb
    else if (b &&& d &&& -d) = 0 then 1 else -1
  | _, _, na, nb => if na < nb then -1 else if nb < na then 1 else 0


/-- `_msk64 = ~UInt64(0)`, `base/bitarray.jl:114`. -/
def msk64 : U64 := BitVec.allOnes 64

/-- `_div64(l) = l >> 6`, `base/bitarray.jl:115`. -/
def div64 (l : Nat) : Nat := l / 64

/-- `_mod64(l) = l & 63`, `base/bitarray.jl:116`. -/
def mod64 (l : Nat) : Nat := l % 64

/-- `_msk_end(l) = _msk64 >>> _mod64(-l)`, `base/bitarray.jl:118`; `(-l) & 63`
is `(64 - l % 64) % 64` for `l ≥ 0`. -/
def mskEnd (l : Nat) : U64 := msk64 >>> ((64 - l % 64) % 64)

/-- `num_bit_chunks(n) = _div64(n) + !iszero(_mod64(n))`, `base/bitarray.jl:120`. -/
def numBitChunks (n : Nat) : Nat := div64 n + (if mod64 n = 0 then 0 else 1)

/-- `get_chunks_id(i) = _div64(i-1)+1, _mod64(i-1)`, `base/bitarray.jl:122`
(called with `i ≥ 1`). -/
def getChunksId (i : Nat) : Nat × Nat := (div64 (i - 1) + 1, mod64 (i - 1))

/-- 1-based `cs[k]`. -/
def cget (cs : List U64) (k : Nat) : U64 := cs.getD (k - 1) 0

/-- 1-based `cs[k] = v`. -/
def cset (cs : List U64) (k : Nat) (v : U64) : List U64 := cs.set (k - 1) v

/-- `_growend!(cs, k)`: `k` uninitialised chunks at the end. -/
def growend (cs : List U64) (k : Nat) (dirty : U64) : List U64 := cs ++ List.replicate k dirty

/-- `_deleteend!(cs, k)`. -/
def deleteend (cs : List U64) (k : Nat) : List U64 := cs.take (cs.length - k)

/-- `cs[end]` and `cs[end] = v`. -/
def cgetEnd (cs : List U64) : U64 := cget cs cs.length
def csetEnd (cs : List U64) (v : U64) : List U64 := cset cs cs.length v

/-- `UInt64(b)` for a `Bool`. -/
def ofBool (b : Bool) : U64 := if b then 1 else 0

/-- `glue_src_bitchunks`, `base/bitarray.jl:124-133`. -/
def glue (src : List U64) (k ks1 : Nat) (mskS0 : U64) (ls0 : Nat) : U64 :=
  let chunk := (cget src k &&& mskS0) >>> ls0
  if ks1 > k ∧ ls0 > 0 then
    chunk ||| ((cget src (k + 1) &&& ~~~mskS0) <<< (64 - ls0))
  else chunk

/-- The source of `copy_chunks!`: a different vector, or the destination itself
(`dest === src`), whose reads see the writes already made. -/
inductive Src where
  | other (cs : List U64)
  | self

def Src.read : Src → List U64 → List U64
  | .other cs, _ => cs
  | .self, dest => dest

/-- Inner loop of `copy_chunks!`, `base/bitarray.jl:166-174`: runs the
iterations `i, i+1, …, i+fuel-1`; iteration `i` glues source chunk `ks0 + i`
and writes `dest[kd0 + i]`. Returns the destination and the last `chunk_s1`. -/
def copyLoop (src : Src) (kd0 ld0 ks0 ks1 ls0 : Nat) (mskS0 : U64) :
    Nat → Nat → List U64 → U64 → List U64 × U64
  | _, 0, dest, c0 => (dest, c0)
  | i, fuel + 1, dest, c0 =>
    let c1 := glue (src.read dest) (ks0 + i) ks1 mskS0 ls0
    let cs := (c0 >>> (64 - ld0)) ||| (c1 <<< ld0)
    copyLoop src kd0 ld0 ks0 ks1 ls0 mskS0 (i + 1) fuel (cset dest (kd0 + i) cs) c1

/-- `copy_chunks!(dest, pos_d, src, pos_s, numbits)` for `dest !== src` or
`pos_d ≤ pos_s`, `base/bitarray.jl:141-186` (the part after the dispatch on
line 137). -/
def copyChunksLtoR (dest : List U64) (posD : Nat) (src : Src) (posS numbits : Nat) : List U64 :=
  let (kd0, ld0) := getChunksId posD
  let (kd1, ld1) := getChunksId (posD + numbits - 1)
  let (ks0, ls0) := getChunksId posS
  let (ks1, ls1) := getChunksId (posS + numbits - 1)
  let deltaKd := kd1 - kd0
  let deltaKs := ks1 - ks0
  let u := msk64
  let mskD0 := ~~~(u <<< ld0)
  let mskD1 := u <<< (ld1 + 1)
  let mskD0 := if deltaKd = 0 then mskD0 ||| mskD1 else mskD0
  let mskS0 := u <<< ls0
  let mskS0 := if deltaKs = 0 then mskS0 &&& ~~~(u <<< (ls1 + 1)) else mskS0
  let chunkS0 := glue (src.read dest) ks0 ks1 mskS0 ls0
  let dest := cset dest kd0 ((cget dest kd0 &&& mskD0) ||| ((chunkS0 <<< ld0) &&& ~~~mskD0))
  if deltaKd = 0 then dest else
  let (dest, chunkS0) := copyLoop src kd0 ld0 ks0 ks1 ls0 mskS0 1 (kd1 - kd0 - 1) dest chunkS0
  let chunkS1 := if ks1 ≥ ks0 + deltaKd then glue (src.read dest) (ks0 + deltaKd) ks1 mskS0 ls0 else 0
  let chunkS := (chunkS0 >>> (64 - ld0)) ||| (chunkS1 <<< ld0)
  cset dest kd1 ((cget dest kd1 &&& mskD1) ||| (chunkS &&& ~~~mskD1))

/-- Loop of `copy_chunks_rtol!`, `base/bitarray.jl:193-232`: copies blocks of at
most 64 bits from the high end down. `fuel` bounds the iterations. -/
def rtolLoop (posD posS : Nat) : Nat → Nat → List U64 → List U64
  | 0, _, chunks => chunks
  | fuel + 1, left, chunks =>
    if left = 0 then chunks else
    let s := min left 64
    let b := left - s
    let ps := posS + b
    let pd := posD + b
    let u := msk64
    let (kd0, ld0) := getChunksId pd
    let (kd1, ld1) := getChunksId (pd + s - 1)
    let (ks0, ls0) := getChunksId ps
    let (ks1, ls1) := getChunksId (ps + s - 1)
    let deltaKd := kd1 - kd0
    let deltaKs := ks1 - ks0
    let mskD0 := ~~~(u <<< ld0)
    let mskD1 := u <<< (ld1 + 1)
    let mskD0 := if deltaKd = 0 then mskD0 ||| mskD1 else mskD0
    let mskS0 := u <<< ls0
    let mskS0 := if deltaKs = 0 then mskS0 &&& ~~~(u <<< (ls1 + 1)) else mskS0
    let chunkS0 := glue chunks ks0 ks1 mskS0 ls0 &&& ~~~(u <<< s)
    let chunks := cset chunks kd0 ((cget chunks kd0 &&& mskD0) ||| ((chunkS0 <<< ld0) &&& ~~~mskD0))
    let chunks := if deltaKd ≠ 0 then
        let chunkS := chunkS0 >>> (64 - ld0)
        cset chunks kd1 ((cget chunks kd1 &&& mskD1) ||| (chunkS &&& ~~~mskD1))
      else chunks
    rtolLoop posD posS fuel (left - s) chunks

/-- `copy_chunks_rtol!(chunks, pos_d, pos_s, numbits)`, `base/bitarray.jl:189-233`. -/
def copyChunksRtol (chunks : List U64) (posD posS numbits : Nat) : List U64 :=
  if posD = posS then chunks
  else if posD < posS then copyChunksLtoR chunks posD .self posS numbits
  else rtolLoop posD posS numbits numbits chunks

/-- `copy_chunks!(dest, pos_d, src, pos_s, numbits)`, `base/bitarray.jl:135-187`. -/
def copyChunks (dest : List U64) (posD : Nat) (src : Src) (posS numbits : Nat) : List U64 :=
  if numbits = 0 then dest
  else match src with
    | .self => if posD > posS then copyChunksRtol dest posD posS numbits
               else copyChunksLtoR dest posD .self posS numbits
    | .other cs => copyChunksLtoR dest posD (.other cs) posS numbits

/-- `fill_chunks!(Bc, x, pos, numbits)`, `base/bitarray.jl:235-259`. -/
def fillChunks (bc : List U64) (x : Bool) (pos numbits : Nat) : List U64 :=
  if numbits = 0 then bc else
  let (k0, l0) := getChunksId pos
  let (k1, l1) := getChunksId (pos + numbits - 1)
  let u := msk64
  let msk0 := u <<< l0
  let msk1 := ~~~(u <<< (l1 + 1))
  let msk0 := if k1 = k0 then msk0 &&& msk1 else msk0
  let mid (v : U64) (cs : List U64) : List U64 :=
    (List.range (k1 - k0 - 1)).foldl (fun cs j => cset cs (k0 + 1 + j) v) cs
  if x then
    let bc := cset bc k0 (cget bc k0 ||| msk0)
    let bc := mid u bc
    if k1 > k0 then cset bc k1 (cget bc k1 ||| msk1) else bc
  else
    let bc := cset bc k0 (cget bc k0 &&& ~~~msk0)
    let bc := mid 0 bc
    if k1 > k0 then cset bc k1 (cget bc k1 &&& ~~~msk1) else bc

/-! ## Abstraction: elements of a chunk vector -/

/-- Element `k + 1` (0-based bit `k`) of a chunk vector. -/
def bitOf (cs : List U64) (k : Nat) : Bool := (cs.getD (k / 64) 0).getLsbD (k % 64)

/-- Chunk `c` (0-based) of the canonical packing of `l`: bit `j` is `l[64c+j]`. -/
def chunkAt (l : List Bool) (c : Nat) : U64 :=
  (List.range 64).foldl
    (fun acc j => if l.getD (64 * c + j) false then acc ||| BitVec.twoPow 64 j else acc) 0

/-- The chunks of a valid `BitVector` holding `l`: `num_bit_chunks(length(l))`
chunks, unused bits zero. -/
def pack (l : List Bool) : List U64 := (List.range (numBitChunks l.length)).map (chunkAt l)

/-- The elements `1:len` of a chunk vector. -/
def unpack (cs : List U64) (len : Nat) : List Bool := (List.range len).map (bitOf cs)

end JuliaLean.BitArrays

/-!
# `BitVector` operations (`base/bitarray.jl`, master `bbfa0ce4150`)

`BV` is the state of a `BitVector`: its `chunks` and `len` fields. Mutating
methods return the new state; methods that also return a value return a pair.
Bit-level helpers on `UInt64` (`count_ones`, `trailing_zeros`, ...) are at the top.
-/

namespace JuliaLean.BitArrays

/-! ## `UInt64` bit counts (`base/int.jl`) -/

/-- `count_ones(x)`. -/
def countOnes (x : U64) : Nat := ((List.range 64).filter (fun j => x.getLsbD j)).length

/-- `trailing_zeros(x)`: index of the lowest set bit, `64` for zero. -/
def trailingZeros (x : U64) : Nat := ((List.range 64).find? (fun j => x.getLsbD j)).getD 64

/-- `trailing_ones(x) = trailing_zeros(~x)`. -/
def trailingOnes (x : U64) : Nat := trailingZeros (~~~x)

/-- `top_set_bit(x) = 64 - leading_zeros(x)`: one more than the index of the
highest set bit, `0` for zero. -/
def topSetBit (x : U64) : Nat :=
  ((List.range 64).reverse.find? (fun j => x.getLsbD j)).elim 0 (· + 1)

/-- `leading_ones(x)`: number of set bits above the highest clear bit. -/
def leadingOnes (x : U64) : Nat := 64 - topSetBit (~~~x)

/-- `bitreverse(x)`. -/
def bitreverse (x : U64) : U64 := x.reverse

/-- The chunkwise form of a Boolean function: bit `j` of the result is
`g(x[j], y[j])` (the functions `&`, `|`, `xor`, `nand`, `nor`, `(p,q)->p|~q`, …
of `base/bitarray.jl:1757-1766` are of this form). -/
def liftBits (g : Bool → Bool → Bool) (x y : U64) : U64 :=
  (List.range 64).foldl
    (fun acc j => if g (x.getLsbD j) (y.getLsbD j) then acc ||| BitVec.twoPow 64 j else acc) 0

/-! ## The `BitVector` state -/

/-- Fields `chunks` and `len` of a `BitVector`, `base/bitarray.jl:24-42`. -/
structure BV where
  chunks : List U64
  len : Nat
  deriving DecidableEq, Repr

namespace BV

/-- The valid `BitVector` holding `l` (what `BitVector(l)` builds). -/
def ofList (l : List Bool) : BV := ⟨pack l, l.length⟩

/-- The elements `B[1:end]`. -/
def toList (B : BV) : List Bool := unpack B.chunks B.len

/-- `BitVector(undef, n)`, `base/bitarray.jl:28-41`: `num_bit_chunks(n)` chunks,
the last one zeroed, the others uninitialised (`dirty`). -/
def undef (n : Nat) (dirty : U64) : BV :=
  let nc := numBitChunks n
  let cs := List.replicate nc dirty
  ⟨if nc > 0 then csetEnd cs 0 else cs, n⟩

/-- `falses(n)`, `base/bitarray.jl:396` and `fill!` at `:368-379`. -/
def falses (n : Nat) : BV := ⟨List.replicate (numBitChunks n) 0, n⟩

end BV

/-! ## Indexing -/

/-- `unsafe_bitgetindex(Bc, i)`, `base/bitarray.jl:661-666`. -/
def unsafeBitget (bc : List U64) (i : Nat) : Bool :=
  let (i1, i2) := getChunksId i
  (cget bc i1 &&& ((1 : U64) <<< i2)) != 0

/-- `_unsafe_bitsetindex!(Bc, x, i1, i2)`, `base/bitarray.jl:680-686`. -/
def unsafeBitsetAt (bc : List U64) (x : Bool) (i1 i2 : Nat) : List U64 :=
  let u := (1 : U64) <<< i2
  let c := cget bc i1
  cset bc i1 (if x then c ||| u else c &&& ~~~u)

/-- `unsafe_bitsetindex!(Bc, x, i)`, `base/bitarray.jl:675-678`. -/
def unsafeBitset (bc : List U64) (x : Bool) (i : Nat) : List U64 :=
  let (i1, i2) := getChunksId i
  unsafeBitsetAt bc x i1 i2

/-- `checkbounds(B, i)` for an `Int` index. -/
def inBounds (B : BV) (i : JInt64) : Bool := decide (1 ≤ i.val ∧ i.val ≤ B.len)

/-- `getindex(B, i::Int)`, `base/bitarray.jl:668-671`. -/
def getindex (B : BV) (i : JInt64) : Jl Bool :=
  if inBounds B i then .ok (unsafeBitget B.chunks i.val.toNat) else .error .boundsError

/-- `setindex!(B, x::Bool, i::Int)`, `base/bitarray.jl:688-692`. -/
def setindex (B : BV) (x : Bool) (i : JInt64) : Jl BV :=
  if inBounds B i then .ok { B with chunks := unsafeBitset B.chunks x i.val.toNat }
  else .error .boundsError

/-- `B[end] = x` on a nonempty vector (always in bounds). -/
def setEnd (B : BV) (x : Bool) : BV := { B with chunks := unsafeBitset B.chunks x B.len }

/-! ## Dequeue functionality, `base/bitarray.jl:737-1141` -/

/-- `push!(B, item::Bool)`, `base/bitarray.jl:739-755`. -/
def push (B : BV) (item : Bool) (dirty : U64) : BV :=
  let l := mod64 B.len
  let bc := if l = 0 then csetEnd (growend B.chunks 1 dirty) 0 else B.chunks
  let B := ⟨bc, B.len + 1⟩
  if item then setEnd B true else B

/-- `pop!(B)`, `base/bitarray.jl:827-837`. -/
def pop (B : BV) : Jl (BV × Bool) :=
  if B.len = 0 then .error (.argumentError "argument must not be empty") else
  let item := unsafeBitget B.chunks B.len
  let B := setEnd B false
  let l := mod64 B.len
  let bc := if l = 1 then deleteend B.chunks 1 else B.chunks
  .ok (⟨bc, B.len - 1⟩, item)

/-- Loop `for i = length(Bc):-1:lo; Bc[i] = (Bc[i] << 1) | (Bc[i-1] >>> 63); end`
(`base/bitarray.jl:854-856, 902-904`), run on `i = hi, hi-1, …, hi-fuel+1`. -/
def shiftUpLoop : Nat → Nat → List U64 → List U64
  | _, 0, bc => bc
  | i, fuel + 1, bc =>
    shiftUpLoop (i - 1) fuel (cset bc i ((cget bc i <<< 1) ||| (cget bc (i - 1) >>> 63)))

/-- Loop `for i = lo:hi; Bc[i] = (Bc[i] >>> 1) | (Bc[i+1] << 63); end`
(`base/bitarray.jl:868-870, 928-930`), run on `i = lo, …, lo+fuel-1`. -/
def shiftDownLoop : Nat → Nat → List U64 → List U64
  | _, 0, bc => bc
  | i, fuel + 1, bc =>
    shiftDownLoop (i + 1) fuel (cset bc i ((cget bc i >>> 1) ||| (cget bc (i + 1) <<< 63)))

/-- `pushfirst!(B, item::Bool)`, `base/bitarray.jl:839-859`. -/
def pushfirst (B : BV) (item : Bool) (dirty : U64) : BV :=
  let l := mod64 B.len
  let bc := if l = 0 then csetEnd (growend B.chunks 1 dirty) 0 else B.chunks
  let len := B.len + 1
  if len = 1 then ⟨cset bc 1 (ofBool item), len⟩ else
  let bc := shiftUpLoop bc.length (bc.length - 1) bc
  ⟨cset bc 1 (ofBool item ||| (cget bc 1 <<< 1)), len⟩

/-- `popfirst!(B)`, `base/bitarray.jl:861-882`. -/
def popfirst (B : BV) : Jl (BV × Bool) :=
  if B.len = 0 then .error (.argumentError "argument must not be empty") else
  let item := unsafeBitget B.chunks 1
  let bc := shiftDownLoop 1 (B.chunks.length - 1) B.chunks
  let l := mod64 B.len
  let bc := if l = 1 then deleteend bc 1 else csetEnd bc (cgetEnd bc >>> 1)
  .ok (⟨bc, B.len - 1⟩, item)

/-- `insert!(B, i, item::Bool)` with `i::Int`, `base/bitarray.jl:884-911`. -/
def insert (B : BV) (i : JInt64) (item : Bool) (dirty : U64) : Jl BV :=
  let n := B.len
  if ¬ (1 ≤ i.val ∧ i.val ≤ n + 1) then .error .boundsError else
  let i := i.val.toNat
  let (k, j) := getChunksId i
  let l := mod64 B.len
  let bc := if l = 0 then csetEnd (growend B.chunks 1 dirty) 0 else B.chunks
  let len := B.len + 1
  let bc := shiftUpLoop bc.length (bc.length - k) bc
  let mskAft := msk64 <<< j
  let mskBef := ~~~mskAft
  let bc := cset bc k ((mskBef &&& cget bc k) ||| ((mskAft &&& cget bc k) <<< 1))
  .ok ⟨unsafeBitset bc item i, len⟩

/-- `_deleteat!(B, i::Int)`, `base/bitarray.jl:913-944`. -/
def deleteatUnsafe (B : BV) (i : Nat) : BV :=
  let (k, j) := getChunksId i
  let mskBef := msk64 >>> (63 - j)
  let mskAft := ~~~mskBef
  let mskBef := mskBef >>> 1
  let bc := B.chunks
  let bc := cset bc k ((mskBef &&& cget bc k) ||| ((mskAft &&& cget bc k) >>> 1))
  let bc := if bc.length > k then cset bc k (cget bc k ||| (cget bc (k + 1) <<< 63)) else bc
  let bc := shiftDownLoop (k + 1) (bc.length - 1 - k) bc
  let l := mod64 B.len
  let bc := if l = 1 then deleteend bc 1
    else if bc.length > k then csetEnd bc (cgetEnd bc >>> 1) else bc
  ⟨bc, B.len - 1⟩

/-- `deleteat!(B, i::Int)`, `base/bitarray.jl:946-953`. -/
def deleteat (B : BV) (i : JInt64) : Jl BV :=
  if 1 ≤ i.val ∧ i.val ≤ B.len then .ok (deleteatUnsafe B i.val.toNat) else .error .boundsError

/-- A `UnitRange{Int}` `f:l`, stored normalised (`l ≥ f - 1`). -/
structure URange where
  first : JInt64
  last : JInt64
  deriving DecidableEq, Repr

def URange.length (r : URange) : Int := r.last.val - r.first.val + 1

/-- `deleteat!(B, r::AbstractUnitRange{Int})`, `base/bitarray.jl:955-977`. -/
def deleteatRange (B : BV) (r : URange) : Jl BV :=
  let n := B.len
  if ¬ (1 ≤ r.first.val) then .error .boundsError else
  if ¬ (r.last.val ≤ n) then .error .boundsError else
  let iF := r.first.val.toNat
  let iL := r.last.val.toNat
  let newL := n - r.length.toNat
  let bc := copyChunks B.chunks iF .self (iL + 1) (n - iL)
  let bc := if numBitChunks newL < bc.length then deleteend bc (bc.length - numBitChunks newL) else bc
  let bc := if newL > 0 then csetEnd bc (cgetEnd bc &&& mskEnd newL) else bc
  .ok ⟨bc, newL⟩

/-- `B[r]` for `r::UnitRange{Int}`: `getindex` through
`_unsafe_getindex!(X, B, I0::AbstractUnitRange)`, `base/multidimensional.jl:1374-1377`,
into `X = BitVector(undef, length(r))`. -/
def getindexRange (B : BV) (r : URange) (dirty : U64) : Jl BV :=
  if r.length = 0 then .ok (BV.undef 0 dirty) else
  if ¬ (1 ≤ r.first.val ∧ r.last.val ≤ B.len) then .error .boundsError else
  let X := BV.undef r.length.toNat dirty
  .ok { X with chunks := copyChunks X.chunks 1 (.other B.chunks) r.first.val.toNat r.length.toNat }

/-- `append!(B, items::BitVector)`, `base/bitarray.jl:757-772`; `items = none`
means `items === B`. -/
def append (B : BV) (items : Option BV) (dirty : U64) : BV :=
  let it := items.getD B
  let n0 := B.len
  let n1 := it.len
  if n1 = 0 then B else
  let n := n0 + n1
  let k0 := B.chunks.length
  let k1 := numBitChunks n
  let bc := if k1 > k0 then csetEnd (growend B.chunks (k1 - k0) dirty) 0 else B.chunks
  let src := match items with | some it => Src.other it.chunks | none => Src.self
  ⟨copyChunks bc (n0 + 1) src 1 n1, n⟩

/-- `prepend!(B, items::BitVector)`, `base/bitarray.jl:777-793`; `items = none`
means `items === B`. -/
def prepend (B : BV) (items : Option BV) (dirty : U64) : BV :=
  let it := items.getD B
  let n0 := B.len
  let n1 := it.len
  if n1 = 0 then B else
  let n := n0 + n1
  let k0 := B.chunks.length
  let k1 := numBitChunks n
  let bc := if k1 > k0 then csetEnd (growend B.chunks (k1 - k0) dirty) 0 else B.chunks
  let bc := copyChunks bc (1 + n1) .self 1 n0
  let src := match items with | some it => Src.other it.chunks | none => Src.self
  ⟨copyChunks bc 1 src 1 n1, n⟩

/-- `splice!(B, r::UnitRange{Int}, ins::BitVector)`, `base/bitarray.jl:1082-1124`
(`ins` distinct from `B`). Returns the new state and the removed elements. -/
def splice (B : BV) (r : URange) (ins : BV) (dirty : U64) : Jl (BV × BV) :=
  let n := B.len
  if ¬ (1 ≤ r.first.val ∧ r.first.val ≤ n + 1) then .error .boundsError else
  if ¬ (r.last.val ≤ n) then .error .boundsError else
  if r.first.val > n then .ok (append B (some ins) dirty, BV.undef 0 dirty) else
  match getindexRange B r dirty with
  | .error e => .error e
  | .ok v =>
    let iF := r.first.val.toNat
    let iL := r.last.val.toNat
    let lins := ins.len
    let ldel := r.length.toNat
    let newL := n + lins - ldel
    let bc := B.chunks
    let k := numBitChunks newL
    let bc := if k > bc.length then growend bc (k - bc.length) dirty else bc
    let bc := copyChunks bc (iF + lins) .self (iL + 1) (n - iL)
    let bc := copyChunks bc iF (.other ins.chunks) 1 lins
    let bc := if k < bc.length then deleteend bc (bc.length - k) else bc
    let bc := if newL > 0 then csetEnd bc (cgetEnd bc &&& mskEnd newL) else bc
    .ok (⟨bc, newL⟩, v)

/-- `resize!(B, n; first)`, `base/bitarray.jl:803-825` (the `first` keyword is
new on master; 1.13.2 has only `first = false`). -/
def resize (B : BV) (n : JInt64) (first : Bool) (dirty : U64) : Jl BV :=
  let n0 := B.len
  if n.val = n0 then .ok B else
  if ¬ (n.val ≥ 0) then .error .boundsError else
  let m := n.val.toNat
  if m < n0 then
    deleteatRange B (if first then ⟨JInt.lit .i64 1, JInt.lit .i64 (n0 - m)⟩
      else ⟨JInt.lit .i64 (m + 1), JInt.lit .i64 n0⟩)
  else
  let k0 := B.chunks.length
  let k1 := numBitChunks m
  let bc := if k1 > k0 then csetEnd (growend B.chunks (k1 - k0) dirty) 0 else B.chunks
  let bc := if first then copyChunks bc (1 + m - n0) .self 1 n0 else bc
  .ok ⟨bc, m⟩

/-- `fill!(B, x::Bool)`, `base/bitarray.jl:368-379`. -/
def fill (B : BV) (y : Bool) : BV :=
  if B.len = 0 then B else
  if ¬ y then ⟨B.chunks.map (fun _ => 0), B.len⟩
  else ⟨csetEnd (B.chunks.map (fun _ => msk64)) (cgetEnd (B.chunks.map (fun _ => msk64)) &&& mskEnd B.len), B.len⟩

/-- `empty!(B)`, `base/bitarray.jl:1137-1141`. -/
def empty (B : BV) : BV := ⟨deleteend B.chunks B.chunks.length, 0⟩

/-! ## Shifts and rotation -/

/-- `copy(B)`. -/
def copy (B : BV) : BV := B

/-- `B << i` for `i::UInt`, `base/bitarray.jl:1317-1323`. -/
def shlU (B : BV) (i : JInt .u64) : BV :=
  let n := B.len
  if i.val = 0 then copy B else
  let A := BV.falses n
  if i.val < n then { A with chunks := copyChunks A.chunks 1 (.other B.chunks) (i.val.toNat + 1) (n - i.val.toNat) }
  else A

/-- `B >>> i` for `i::UInt`, `base/bitarray.jl:1325-1331`. -/
def shrU (B : BV) (i : JInt .u64) : BV :=
  let n := B.len
  if i.val = 0 then copy B else
  let A := BV.falses n
  if i.val < n then { A with chunks := copyChunks A.chunks (i.val.toNat + 1) (.other B.chunks) 1 (n - i.val.toNat) }
  else A

/-- `unsigned(i)` for `i::Int`. -/
def unsignedI (i : JInt64) : JInt .u64 := JInt.rem .u64 i

/-- `B << i` for `i::Int`, `base/bitarray.jl:1406`. -/
def shl (B : BV) (i : JInt64) : BV :=
  if i.val ≥ 0 then shlU B (unsignedI i) else shrU B (unsignedI (-i))

/-- `B >>> i` (and `B >> i`) for `i::Int`, `base/bitarray.jl:1368, 1414`. -/
def shr (B : BV) (i : JInt64) : BV :=
  if i.val ≥ 0 then shrU B (unsignedI i) else shlU B (unsignedI (-i))

/-- `copyto!(dest::BitArray, src::BitArray)` for vectors, `base/bitarray.jl:429-447`. -/
def copyto (dest src : BV) : Jl BV :=
  if src.len > dest.len then .error .boundsError else
  let nc := min dest.chunks.length src.chunks.length
  if nc = 0 then .ok dest else
  let destc := (List.range (nc - 1)).foldl (fun d j => cset d (j + 1) (cget src.chunks (j + 1))) dest.chunks
  let destc := if src.len = dest.len then cset destc nc (cget src.chunks nc)
    else
      let mskS := mskEnd src.len
      let mskD := ~~~mskS
      cset destc nc ((mskD &&& cget destc nc) ||| (mskS &&& cget src.chunks nc))
  .ok { dest with chunks := destc }

/-- `circshift!(dest, src, i)` with `i::Int`, `base/bitarray.jl:1416-1433`;
`src = none` means `src === dest` (the one-argument `circshift!(B, i)`, `:1435`). -/
def circshift (dest : BV) (src : Option BV) (i : JInt64) : Jl BV := do
  let s := src.getD dest
  if dest.len ≠ s.len then throw (.argumentError "destination and source should be of same size")
  let n := dest.len
  let i ← JInt.remInt i (JInt.lit .i64 n)
  if i.val = 0 then
    match src with
    | none => return dest
    | some s => return (← copyto dest s)
  let bc := s.chunks  -- `copy(src.chunks)` when aliased: a snapshot
  if i.val > 0 then
    let k := i.val.toNat
    let d := copyChunks dest.chunks (k + 1) (.other bc) 1 (n - k)
    return ⟨copyChunks d 1 (.other bc) (n - k + 1) k, n⟩
  else
    let k := (-i.val).toNat
    let d := copyChunks dest.chunks 1 (.other bc) (k + 1) (n - k)
    return ⟨copyChunks d (n - k + 1) (.other bc) 1 k, n⟩

/-! ## count, any, all, find -/

/-- `bitcount(Bc; init::T)`, `base/bitarray.jl:1439-1445`: `(n + count_ones(c)) % T`. -/
def bitcount {t : IntTy} (bc : List U64) (init : JInt t) : JInt t :=
  bc.foldl (fun n c => JInt.wrap t (n.val + countOnes c)) init

/-- `count(B; init)`, `base/bitarray.jl:1447`. -/
def count {t : IntTy} (B : BV) (init : JInt t) : JInt t := bitcount B.chunks init

/-- `all(B)`, `base/bitarray.jl:1715-1725`. -/
def all (B : BV) : Bool :=
  if B.len = 0 then true else
  (List.range (B.chunks.length - 1)).all (fun j => cget B.chunks (j + 1) == msk64) &&
    cgetEnd B.chunks == mskEnd B.len

/-- `any(B)`, `base/bitarray.jl:1727-1736`. -/
def any (B : BV) : Bool :=
  if B.len = 0 then false else B.chunks.any (· != 0)

/-- `unsafe_bitfindnext(Bc, start)`, `base/bitarray.jl:1449-1466`. -/
def unsafeBitfindnext (bc : List U64) (start : Nat) : Option Nat :=
  let chunkStart := div64 (start - 1) + 1
  let within := mod64 (start - 1)
  let mask := msk64 <<< within
  if cget bc chunkStart &&& mask != 0 then
    some ((chunkStart - 1) * 64 + trailingZeros (cget bc chunkStart &&& mask) + 1)
  else
    ((List.range (bc.length - chunkStart)).find? (fun j => cget bc (chunkStart + 1 + j) != 0)).map
      (fun j => (chunkStart + j) * 64 + trailingZeros (cget bc (chunkStart + 1 + j)) + 1)

/-- `findnext(B, start)` for `start::Int`, `base/bitarray.jl:1469-1474`. -/
def findnext (B : BV) (start : JInt64) : Jl (Option Nat) :=
  if ¬ (start.val > 0) then .error .boundsError
  else if start.val > B.len then .ok none
  else .ok (unsafeBitfindnext B.chunks start.val.toNat)

/-- `unsafe_bitfindprev(Bc, start)`, `base/bitarray.jl:1535-1551`. -/
def unsafeBitfindprev (bc : List U64) (start : Nat) : Option Nat :=
  let chunkStart := div64 (start - 1) + 1
  let mask := mskEnd start
  if cget bc chunkStart &&& mask != 0 then
    some ((chunkStart - 1) * 64 + topSetBit (cget bc chunkStart &&& mask))
  else
    ((List.range (chunkStart - 1)).find? (fun j => cget bc (chunkStart - 1 - j) != 0)).map
      (fun j => (chunkStart - 2 - j) * 64 + topSetBit (cget bc (chunkStart - 1 - j)))

/-- `findprev(B, start)` for `start::Int`, `base/bitarray.jl:1554-1559`. -/
def findprev (B : BV) (start : JInt64) : Jl (Option Nat) :=
  if ¬ (start.val > 0) then .ok none
  else if start.val > B.len then .error .boundsError
  else .ok (unsafeBitfindprev B.chunks start.val.toNat)

/-- `findnextnot(B, start)`, `base/bitarray.jl:1479-1507`. -/
def findnextnot (B : BV) (start : JInt64) : Jl (Option Nat) :=
  if ¬ (start.val > 0) then .error .boundsError
  else if start.val > B.len then .ok none else
  let bc := B.chunks
  let l := bc.length
  if l = 0 then .ok none else
  let st := start.val.toNat
  let chunkStart := div64 (st - 1) + 1
  let within := mod64 (st - 1)
  let mask := ~~~(msk64 <<< within)
  if chunkStart < l then
    if cget bc chunkStart ||| mask != msk64 then
      .ok (some ((chunkStart - 1) * 64 + trailingOnes (cget bc chunkStart ||| mask) + 1))
    else match (List.range (l - 1 - chunkStart)).find? (fun j => cget bc (chunkStart + 1 + j) != msk64) with
      | some j => .ok (some ((chunkStart + j) * 64 + trailingOnes (cget bc (chunkStart + 1 + j)) + 1))
      | none =>
        if cget bc l != mskEnd B.len then .ok (some ((l - 1) * 64 + trailingOnes (cget bc l) + 1))
        else .ok none
  else if cget bc l ||| mask != mskEnd B.len then
    .ok (some ((l - 1) * 64 + trailingOnes (cget bc l ||| mask) + 1))
  else .ok none

/-- `findprevnot(B, start)`, `base/bitarray.jl:1561-1583`. -/
def findprevnot (B : BV) (start : JInt64) : Jl (Option Nat) :=
  if ¬ (start.val > 0) then .ok none
  else if start.val > B.len then .error .boundsError else
  let bc := B.chunks
  let st := start.val.toNat
  let chunkStart := div64 (st - 1) + 1
  let mask := ~~~(mskEnd st)
  if cget bc chunkStart ||| mask != msk64 then
    .ok (some ((chunkStart - 1) * 64 + (64 - leadingOnes (cget bc chunkStart ||| mask))))
  else
    .ok (((List.range (chunkStart - 1)).find? (fun j => cget bc (chunkStart - 1 - j) != msk64)).map
      (fun j => (chunkStart - 2 - j) * 64 + (64 - leadingOnes (cget bc (chunkStart - 1 - j)))))

/-! ## Reversal -/

/-- Loop of `_reverse!(B, ::Colon)`, `base/bitarray.jl:1288-1306`. -/
def reverseLoop (k h : Nat) : Nat → Nat → Nat → U64 → U64 → List U64 → Nat × Nat × U64 × U64 × List U64
  | 0, i, j, u, v, bc => (i, j, u, v, bc)
  | fuel + 1, i, j, u, v, bc =>
    let i := i + 1
    if i = j then (i, j, u, v, bc) else
    let u := bitreverse (cget bc i)
    let bc := cset bc i 0
    let bc := cset bc j (cget bc j ||| (u >>> h))
    let bc := cset bc i (cget bc i ||| (v >>> h))
    let j := j - 1
    if i = j then (i, j, u, v, bc) else
    let v := bitreverse (cget bc j)
    let bc := cset bc j 0
    let bc := cset bc i (cget bc i ||| (v <<< k))
    let bc := cset bc j (cget bc j ||| (u <<< k))
    reverseLoop k h fuel i j u v bc

/-- `reverse!(B::BitVector)`, `_reverse!(B, ::Colon)`, `base/bitarray.jl:1263-1315`. -/
def reverse (B : BV) : BV :=
  let n := B.len
  if n = 0 then B else
  let k := mod64 (n + 63) + 1
  let h := 64 - k
  let j := B.chunks.length
  let v := bitreverse (cget B.chunks j)
  let bc := cset B.chunks j 0
  let (i, _, u, v, bc) := reverseLoop k h (B.chunks.length + 1) 0 j 0 v bc
  let bc := if B.chunks.length % 2 = 1 then cset bc i (cget bc i ||| (v >>> h))
    else cset bc i (cget bc i ||| (u <<< k))
  ⟨bc, n⟩

/-- `j = start:step:stop` with `step ≠ 0` as the list of its elements; a zero step
throws `ArgumentError("step cannot be zero")` (`StepRange` constructor,
`base/range.jl`). -/
def stepRange (start step stop : Int) : Jl (List Int) :=
  if step = 0 then .error (.argumentError "step cannot be zero") else
  if step > 0 then
    .ok (if stop < start then [] else
      (List.range ((stop - start) / step + 1).toNat).map (fun (t : Nat) => start + step * (t : Int)))
  else
    .ok (if stop > start then [] else
      (List.range ((start - stop) / (-step) + 1).toNat).map (fun (t : Nat) => start + step * (t : Int)))

/-- `_reverse(A::BitArray, d::Int)`, `base/bitarray.jl:1217-1261`, i.e.
`reverse(A; dims=d)`, for an array with element state `A` and size `dims`.
`similar(A)` gives `num_bit_chunks(length(A))` uninitialised chunks with the last
one zeroed (`dirty` elsewhere). Elements are read and written with the scalar
`getindex`/`setindex!` (always in bounds here). -/
def reverseDims (A : BV) (dims : List Nat) (d : JInt64) (dirty : U64) : Jl BV := do
  let nd := dims.length
  if ¬ (1 ≤ d.val ∧ d.val ≤ nd) then throw (.argumentError "dimension out of range")
  let d := d.val.toNat
  let sd := dims.getD (d - 1) 0
  if sd = 1 then return copy A
  let B := BV.undef A.len dirty
  let nnd := ((List.range nd).filter (fun i => dims.getD i 0 = 1 ∨ i + 1 = d)).length
  if nnd = nd then
    return (List.range sd).foldl (fun B i =>
      { B with chunks := unsafeBitset B.chunks (unsafeBitget A.chunks (sd - i)) (i + 1) }) B
  let M := (dims.take (d - 1)).foldl (· * ·) 1
  let N := A.len
  let stride := M * sd
  if M = 1 then
    let js ← stepRange 0 stride (N - stride : Int)
    return js.foldl (fun B j => (List.range sd).foldl (fun B i =>
      let ri := sd - i
      { B with chunks := unsafeBitset B.chunks (unsafeBitget A.chunks (j.toNat + i + 1)) (j.toNat + ri) }) B) B
  else
    (List.range sd).foldlM (fun B i => do
      let ri := sd - i
      let js ← stepRange 0 stride (N - stride : Int)
      return js.foldl (fun B j =>
        let offs := j.toNat + 1 + i * M
        let boffs := j.toNat + 1 + (ri - 1) * M
        { B with chunks := copyChunks B.chunks boffs (.other A.chunks) offs M }) B) B

/-! ## Chunkwise `map!`, `base/bitarray.jl:1747-1826` -/

/-- `bit_map!(f, dest, A)`, `base/bitarray.jl:1786-1804`; `A = none` means
`A === dest`. -/
def bitMap1 (f : U64 → U64) (dest : BV) (A : Option BV) : Jl BV :=
  let a := A.getD dest
  if ¬ (a.len ≤ dest.len) then .error (.argumentError "DimensionMismatch") else
  if a.len = 0 then .ok dest else
  let lenAc := a.chunks.length
  let destc := (List.range (lenAc - 1)).foldl
    (fun d j => cset d (j + 1) (f (cget (A.elim d BV.chunks) (j + 1)))) dest.chunks
  let destLast := cget destc lenAc
  let msk := mskEnd a.len
  .ok { dest with chunks := cset destc lenAc ((destLast &&& ~~~msk) ||| (f (cget (A.elim destc BV.chunks) lenAc) &&& msk)) }

/-- `bit_map!(f, dest, A, B)`, `base/bitarray.jl:1805-1826` (`A`, `B` distinct
from `dest`). -/
def bitMap2 (f : U64 → U64 → U64) (dest A B : BV) : Jl BV :=
  let minBitlen := min A.len B.len
  if ¬ (minBitlen ≤ dest.len) then .error (.argumentError "DimensionMismatch") else
  if A.len = 0 then .ok dest else
  if B.len = 0 then .ok dest else
  let lenAc := min A.chunks.length B.chunks.length
  let destc := (List.range (lenAc - 1)).foldl
    (fun d j => cset d (j + 1) (f (cget A.chunks (j + 1)) (cget B.chunks (j + 1)))) dest.chunks
  let destLast := cget destc lenAc
  let msk := mskEnd minBitlen
  .ok { dest with chunks := cset destc lenAc ((destLast &&& ~~~msk) ||| (f (cget A.chunks lenAc) (cget B.chunks lenAc) &&& msk)) }

/-! ## Logical-mask assignment -/

/-- Inner loop of `_unsafe_setindex!(B, X, I::BitArray)`, `base/bitarray.jl:721-730`:
the bits `u = 1 << b` for `b = b0, …` of one chunk. State: chunk `C`, the
number `c` of `X` elements consumed. A `DimensionMismatch` aborts with the chunk
vector as written so far (the current chunk is not stored). -/
def maskBitsLoop (X : List Bool) (imsk : U64) : Nat → Nat → U64 → Nat → Except Unit (U64 × Nat)
  | _, 0, C, c => .ok (C, c)
  | b, fuel + 1, C, c =>
    if imsk.getLsbD b then
      if c = X.length then .error () else
      let x := X.getD c false
      let u := (1 : U64) <<< b
      maskBitsLoop X imsk (b + 1) fuel (if x then C ||| u else C &&& ~~~u) (c + 1)
    else maskBitsLoop X imsk (b + 1) fuel C c

/-- Outer loop over chunks `i = i0, …` of `_unsafe_setindex!`, `base/bitarray.jl:717-732`.
Returns the chunk vector and either the consumed count or a mismatch. -/
def maskChunksLoop (X : List Bool) (ic : List U64) (lc lastChunkLen : Nat) :
    Nat → Nat → List U64 → Nat → List U64 × Option Nat
  | _, 0, bc, c => (bc, some c)
  | i, fuel + 1, bc, c =>
    match maskBitsLoop X (cget ic i) 0 (if i < lc then 64 else lastChunkLen) (cget bc i) c with
    | .error () => (bc, none)
    | .ok (C, c) => maskChunksLoop X ic lc lastChunkLen (i + 1) fuel (cset bc i C) c

/-- `setindex!(B, X::AbstractArray, I::BitArray)` for vectors (`B[I] = X`),
`base/bitarray.jl:703-735`. The result carries the chunk state also when a
`DimensionMismatch` is thrown, to expose writes made before the throw. -/
def setindexMask (B : BV) (X : List Bool) (I : BV) : BV × Option JlError :=
  if B.len ≠ I.len then (B, some .boundsError) else
  let lc := B.chunks.length
  let lastChunkLen := mod64 (B.len - 1) + 1
  match maskChunksLoop X I.chunks lc lastChunkLen 1 lc B.chunks 0 with
  | (bc, none) => (⟨bc, B.len⟩, some (.argumentError "DimensionMismatch"))
  | (bc, some c) => if c = X.length then (⟨bc, B.len⟩, none)
    else (⟨bc, B.len⟩, some (.argumentError "DimensionMismatch"))

end JuliaLean.BitArrays

namespace JuliaLean.BitArrays

/-! ## `vec(M)` aliasing (`reshape`, `base/bitarray.jl:475-485`) -/

/-- A `BitArray` `M` and `v = reshape(M, length(M))` (or `vec(M)`): two headers
sharing one `chunks::Vector{UInt64}` object. `_bitreshape` assigns
`Br.chunks = B.chunks` (`base/bitarray.jl:481`). -/
structure Aliased where
  chunks : List U64
  lenM : Nat
  lenV : Nat
  deriving DecidableEq, Repr

namespace Aliased

/-- `v = vec(M)` for `M` with the state `M`. -/
def vecOf (M : BV) : Aliased := ⟨M.chunks, M.len, M.len⟩

/-- The state of `M`. -/
def parent (a : Aliased) : BV := ⟨a.chunks, a.lenM⟩

/-- Run a `BitVector` method on `v`. Every mutating `BitVector` method in
`base/bitarray.jl` updates `B.chunks` in place (`_growend!`, `_deleteend!`,
element stores) and assigns `B.len`, so `M` sees the new chunks with its own length. -/
def onVec (a : Aliased) (f : BV → BV) : Aliased :=
  let v := f ⟨a.chunks, a.lenV⟩
  ⟨v.chunks, a.lenM, v.len⟩

end Aliased

/-- `==(A::BitArray, B::BitArray)`, `base/bitarray.jl:1206-1209` (for equal sizes). -/
def bitEq (A B : BV) : Bool := A.len == B.len && A.chunks == B.chunks

end JuliaLean.BitArrays

/-!
# Remaining `base/bitarray.jl` method models

`BA` adds Julia's dimension tuple to the existing faithful packed `BV` model.
The chunk-level methods reuse `JuliaLean.BitArrays.Chunks`; mutation, resize,
find, reverse, count, and map paths reuse the existing `BV` implementations.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays

namespace BARows

def dimProduct (dims : List Nat) : Nat := dims.foldl (· * ·) 1

structure BA where
  dims : List Nat
  data : BV
  deriving DecidableEq

def valid (a : BA) : Prop := a.data.len = dimProduct a.dims

/-- `BitArray{N}(undef, dims)`, lines 28-41. -/
def undef (dims : List Nat) (dirty : U64) : BA := ⟨dims, BV.undef (dimProduct dims) dirty⟩
def undefIntegers (dims : List Nat) (dirty : U64) : BA := undef dims dirty
def emptyVector : BA := undef [0] 0
def fromTuple (xs : List Bool) : BA := ⟨[xs.length], BV.ofList xs⟩
def length (a : BA) : Nat := a.data.len
def sizeVector (a : BA) : List Nat := [a.data.len]
def size (a : BA) : List Nat := a.dims
def isassigned (a : BA) (i : Nat) : Bool := decide (1 ≤ i && i ≤ a.data.len)
def indexStyle : Bool := true
def dataids (a : BA) : Nat := a.data.chunks.length

/-- Lines 115-133. -/
def div64Row (l : Nat) : Nat := div64 l
def mod64Row (l : Nat) : Nat := mod64 l
def blsrRow (x : U64) : U64 := x &&& (x - 1)
def mskEndRow (l : Nat) : U64 := mskEnd l
def mskEndArray (a : BA) : U64 := mskEnd a.data.len
def numChunksRow (n : Nat) : Nat := numBitChunks n
def chunksIdRow (i : Nat) : Nat × Nat := getChunksId i
def glueRow (src : List U64) (k ks1 : Nat) (mask : U64) (shift : Nat) : U64 :=
  glue src k ks1 mask shift

/-- Lines 235-355. -/
def fillChunksRow (chunks : List U64) (x : Bool) (pos n : Nat) : List U64 :=
  fillChunks chunks x pos n
def copyBitChunksRow (dest : List U64) (posD : Nat) (src : BV) (posS n : Nat) : List U64 :=
  copyChunks dest posD (.other src.chunks) posS n
def pack8bools (bits : List Bool) : U64 := chunkAt (bits.take 8) 0
def copyBoolChunksRow (dest : List U64) (posD : Nat) (src : List Bool) (posS n : Nat) : List U64 :=
  copyChunks dest posD (.other (pack src)) posS n
def dumpbitcache (dest : List U64) (index : Nat) (cache : List Bool) : List U64 :=
  copyBoolChunksRow dest (8 * index + 1) cache 1 cache.length
def iterate (a : BA) (i : Nat := 0) : Option (Bool × Nat) :=
  if i < a.data.len then some (unsafeBitget a.data.chunks (i + 1), i + 1) else none

/-- Lines 359-536. -/
def similar (a : BA) : BA := undef a.dims 0
def similarDims (dims : List Nat) : BA := undef dims 0
def similarBool (dims : List Nat) : BA := undef dims 0
def similarOther (dims : List Nat) : List Bool := List.replicate (dimProduct dims) false
def falses (dims : List Nat) : BA := ⟨dims, BV.falses (dimProduct dims)⟩
def trues (dims : List Nat) : BA := ⟨dims, JuliaLean.BitArrays.fill (BV.falses (dimProduct dims)) true⟩
def oneMatrix (n m : Nat) : BA :=
  let xs := (List.range (n * m)).map (fun k => decide (k / n = k % n))
  ⟨[n, m], BV.ofList xs⟩
def copytoBits (dest src : BA) : Option BA :=
  match JuliaLean.BitArrays.copyto dest.data src.data with
  | .ok data => some ⟨dest.dims, data⟩
  | .error _ => none
def unsafeCopyto (dest : BA) (doffs : Nat) (src : List Bool) (soffs n : Nat) : BA :=
  let chunks := copyChunks dest.data.chunks doffs (.other (pack src)) soffs n
  ⟨dest.dims, ⟨chunks, dest.data.len⟩⟩
def copytoChecked (dest : BA) (doffs : Nat) (src : List Bool) (soffs n : Nat) : Option BA :=
  if 1 ≤ doffs && doffs + n - 1 ≤ dest.data.len && 1 ≤ soffs && soffs + n - 1 ≤ src.length
  then some (unsafeCopyto dest doffs src soffs n) else none
def copytoArray (src : List Bool) : BA := ⟨[src.length], BV.ofList src⟩
def reshape (a : BA) (dims : List Nat) : Option BA :=
  if dimProduct dims = a.data.len then some ⟨dims, a.data⟩ else none
def toArray (a : BA) : List Bool := a.data.toList
def fromArray (dims : List Nat) (xs : List Bool) : Option BA :=
  if dimProduct dims = xs.length then some ⟨dims, BV.ofList xs⟩ else none
def sameType (a : BA) : BA := a

/-- Lines 566-656. -/
def fromIterator (xs : List Bool) : BA := copytoArray xs
def fromIteratorN (rank : Nat) (dims : List Nat) (xs : List Bool) : Option BA :=
  if dims.length = rank && dimProduct dims = xs.length then fromArray dims xs else none
def genBitarray (hasShape : Bool) (dims : List Nat) (xs : List Bool) : Option BA :=
  if hasShape then fromArray dims xs else some (fromIterator xs)
def fillFromIterator (a : BA) (xs : List Bool) : Option BA :=
  if xs.length = a.data.len then some ⟨a.dims, BV.ofList xs⟩ else none

/-- Lines 694-699. -/
def indexoffset (firstIndex : Nat) : Nat := firstIndex - 1
def indexoffsetColon : Nat := 0
def setindexRange (a : BA) (xs : List Bool) (first : Nat) : Option BA :=
  if first = 0 || first + xs.length - 1 > a.data.len then none
  else some ⟨a.dims, ⟨copyChunks a.data.chunks first (.other (pack xs)) 1 xs.length, a.data.len⟩⟩

def emptyBang (a : BA) : BA := ⟨[0], JuliaLean.BitArrays.empty a.data⟩

/-- Lines 979-1134. The source validates increasing indices before its
copy loops; Boolean masks select or delete at each true position; splice
returns the removed segment and replaces it by `ins`. -/
def strictlyIncreasing : List Nat → Bool
  | [] | [_] => true
  | x :: y :: xs => decide (x < y) && strictlyIncreasing (y :: xs)

def deleteatIndices (a : BA) (inds : List Nat) : Option BA :=
  if strictlyIncreasing inds && inds.all (fun i => decide (1 ≤ i && i ≤ a.data.len)) then
    some (copytoArray ((List.zip (List.range a.data.len) a.data.toList).filterMap fun p =>
      if p.1 + 1 ∈ inds then none else some p.2))
  else none

def deleteatMask (a : BA) (mask : List Bool) : Option BA :=
  if mask.length = a.data.len then
    some (copytoArray ((List.zip a.data.toList mask).filterMap fun p => if p.2 then none else some p.1))
  else none

def keepatIndices (a : BA) (inds : List Nat) : Option BA :=
  if strictlyIncreasing inds && inds.all (fun i => decide (1 ≤ i && i ≤ a.data.len)) then
    some (copytoArray (inds.map fun i => a.data.toList.getD (i - 1) false))
  else none

def keepatMask (a : BA) (mask : List Bool) : Option BA :=
  if mask.length = a.data.len then
    some (copytoArray ((List.zip a.data.toList mask).filterMap fun p => if p.2 then some p.1 else none))
  else none

def spliceRange (a : BA) (first count : Nat) (ins : List Bool) : Option (BA × BA) :=
  if first = 0 || first + count - 1 > a.data.len then none
  else
    let xs := a.data.toList
    let removed := copytoArray ((xs.drop (first - 1)).take count)
    let result := copytoArray (xs.take (first - 1) ++ ins ++ xs.drop (first - 1 + count))
    some (removed, result)

def spliceIndex (a : BA) (i : Nat) : Option (Bool × BA) :=
  match spliceRange a i 1 [] with
  | some (old, result) => some (old.data.toList.headD false, result)
  | none => none

/-- Lines 1145-1216. -/
def negate (a : BA) : List Int := a.data.toList.map (fun b => if b then -1 else 0)
def bitBinary (f : Bool → Bool → Bool) (a b : BA) : BA :=
  let xs := List.zipWith f a.data.toList b.data.toList
  ⟨a.dims, BV.ofList xs⟩
def matrixBinary (f : Bool → Bool → Bool) (a b : BA) : BA := bitBinary f a b
def divRight (a : BA) (x : Int) : List Int := a.data.toList.map (fun b => (if b then 1 else 0) / x)
def divLeft (x : Int) (a : BA) : List Int := a.data.toList.map (fun b => x / (if b then 1 else 0))
def bitarrayEq (a b : BA) : Bool := decide (a.dims = b.dims) && bitEq a.data b.data
def reverseDim (a : BA) (dim : JInt64) (dirty : U64) : Option BA :=
  match JuliaLean.BitArrays.reverseDims a.data a.dims dim dirty with
  | .ok data => some ⟨a.dims, data⟩
  | .error _ => none

/-- Lines 1611-1739. -/
def findmax (a : BA) : Option (Bool × Nat) :=
  if a.data.len = 0 then none
  else match JuliaLean.BitArrays.findnext a.data ⟨1, by decide⟩ with
    | .ok (some i) => some (true, i)
    | _ => some (false, 1)
def findmin (a : BA) : Option (Bool × Nat) :=
  if a.data.len = 0 then none
  else match JuliaLean.BitArrays.findnextnot a.data ⟨1, by decide⟩ with
    | .ok (some i) => some (false, i)
    | _ => some (true, 1)
def allindices (a : BA) : List Nat := List.range a.data.len |>.map (fun i => i + 1)
def allindicesVector (a : BA) : List Nat := allindices a
def allindicesMatrix (a : BA) : List (Nat × Nat) :=
  (List.range (a.dims.getD 0 0)).flatMap (fun i =>
    (List.range (a.dims.getD 1 0)).map (fun j => (i + 1, j + 1)))
def overflowind (i : Nat) (rest size : List Nat) : Nat :=
  (List.zip rest size).foldl (fun out p => out + p.1 * p.2) i
def toind (i : Nat) (rest : List Nat) : Nat := rest.foldl (· + ·) i
def findall (a : BA) : List Nat := allindices a |>.filter (fun i => unsafeBitget a.data.chunks i)
def findallNotZero (a : BA) : List Nat := findall a
def sumDims (a : BA) (_dims : List Nat) : Nat := (a.data.toList.filter id).length
def sumAll (a : BA) : Nat := sumDims a []
def minimum (a : BA) : Option Bool := if a.data.len = 0 then none else some (JuliaLean.BitArrays.all a.data)
def maximum (a : BA) : Option Bool := if a.data.len = 0 then none else some (JuliaLean.BitArrays.any a.data)

/-- Lines 1747-1826. -/
def mapUnary (f : Bool → Bool) (a : BA) : BA := ⟨a.dims, BV.ofList (a.data.toList.map f)⟩
def mapUnaryBang (f : Bool → Bool) (dest a : BA) : BA :=
  ⟨dest.dims, BV.ofList ((a.data.toList.map f) ++ (dest.data.toList.drop a.data.len))⟩
def mapBinary (f : Bool → Bool → Bool) (a b : BA) : BA := bitBinary f a b
def mapBinaryBang (f : Bool → Bool → Bool) (dest a b : BA) : BA :=
  let xs := List.zipWith f a.data.toList b.data.toList
  ⟨dest.dims, BV.ofList (xs ++ dest.data.toList.drop xs.length)⟩
def bitMap (f : Bool → Bool → Bool) (a b : BA) : BA := mapBinary f a b
def bitMapConstant (f : Bool → Bool → Bool) (a : BA) (x : Bool) : BA := mapUnary (fun y => f y x) a
def filter (f : Bool → Bool) (a : BA) : BA := copytoArray (a.data.toList.filter f)

/-- Lines 1838-1930. -/
def hcatVectors (as : List BA) : BA :=
  let rows := (as.head?.map (fun a => a.data.len)).getD 0
  let xs := as.flatMap (fun a => a.data.toList)
  ⟨[rows, as.length], BV.ofList xs⟩
def vcatVectors (as : List BA) : BA := copytoArray (as.flatMap (fun a => a.data.toList))
def hcatArrays (as : List BA) : BA := hcatVectors as
def vcatMatrices (as : List BA) : BA := vcatVectors as
def cat (dim : Nat) (as : List BA) : BA := if dim = 1 then vcatVectors as else hcatVectors as
def sizeof (a : BA) : Nat := 8 * a.data.chunks.length

end BARows

end JuliaLean.BitSetsCov

namespace JuliaLean.BitSetsCov.Bugs

inductive SizehintOutcome where
  | ok
  | methodError
  deriving DecidableEq

/-- `sizehint!(::BitVector, sz::Integer)`, `base/bitarray.jl:798-801`, passes
`_div64(sz + 63)` to `_resize_int!(..., ::Int, ...)` without converting it. -/
def bitSizehint (isMachineInt : Bool) (_n : Nat) : SizehintOutcome :=
  if isMachineInt then .ok else .methodError

end JuliaLean.BitSetsCov.Bugs

namespace JuliaLean.AbstractArraySpecs

/-- The element loop of `_copyto_bitarray!(B, A)` (base/bitarray.jl:513-531): starting from
`Ai = first(eachindex(A))`, bit `k` of `B` (element `k` of the 1-based `B`) becomes
`A[Ai]` and `Ai = nextind(A, Ai)` advances through `eachindex(A)`; the chunk masks keep
the other bits of `B`. -/
def bitLoop {α : Type} (A : Arr α) : Nat → Arr α → I64 → IterState → R (Arr α)
  | 0, B, _, _ => .ok B
  | n + 1, B, k, st =>
    match eachindexStep A st with
    | none => .ok B
    | some (I, st') => do
        let v ← getindex A I
        let B' ← setindex B v [k]
        bitLoop A n B' (k + i64 1) st'

/-- `_copyto_bitarray!(B::BitArray, A::AbstractArray)` (base/bitarray.jl:507-532). -/
def copytoBitarray {α : Type} (B A : Arr α) : R (Arr α) :=
  let l := lengthA A
  if l == i64 0 then .ok B
  else if lengthA B < l then .error .boundsError
  else bitLoop A (fuelOf A) B (i64 1) (eachStart A)

end JuliaLean.AbstractArraySpecs

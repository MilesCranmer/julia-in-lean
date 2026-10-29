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

def growChunkVector (chunks : Nat) (delta : I64) : BitMutationM Unit :=
  growend mutableStorage (fun d => pure d) (growendInternal mutableStorage) chunks delta

def deleteChunkEnd (chunks : Nat) (delta : I64) : BitMutationM Unit :=
  deleteend mutableStorage (fun d => pure d) chunks delta

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
def similarBitArrayBool {N : Nat} (allocate : List I64 → BitMutationM (BitArray N))
    (_B : BitArray N) (dims : List I64) : BitMutationM (BitArray N) := allocate dims

/--
Julia source: base/bitarray.jl:366-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
similar(B::BitArray, T::Type, dims::Dims) = Array{T}(undef, dims)
```
-/
def similarBitArrayOther {N : Nat} {T A : Type} (allocate : List I64 → BitMutationM A)
    (B : BitArray N) (_typeToken : T) (dims : List I64) : BitMutationM A := allocate dims

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
def bitVectorPrependIterable {I : Type} (convert : I → BitMutationM BitVector)
    (prepend : BitVector → BitVector → BitMutationM BitVector) (B : BitVector) (items : I) : BitMutationM BitVector := do
  prepend B (← convert items)

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
def bitArrayReshapeInternal {N : Nat} (checkedDims : List I64 → BitMutationM I64)
    (allocate : List I64 → BitMutationM (BitArray N)) (B : BitArray N) (dims : List I64) : BitMutationM (BitArray N) := do
  let len ← checkedDims dims
  if len != B.len then throw (.dimensionMismatch "new dimensions must be consistent with array length")
  let Br ← allocate (List.replicate N (int 0))
  return { Br with chunks := B.chunks, len := len, dims := if N != 1 then dims else Br.dims }

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
def bitArrayFromAbstract {N : Nat} {A : Type}
    (construct : A → BitMutationM (BitArray N)) (a : A) : BitMutationM (BitArray N) := construct a

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
def falsesAxes {N : Nat} {D A : Type} (similar : D → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N)) (dims : D) : BitMutationM (BitArray N) := do
  fill (← similar dims) false

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
def truesAxes {N : Nat} {D A : Type} (similar : D → BitMutationM (BitArray N))
    (fill : BitArray N → Bool → BitMutationM (BitArray N)) (dims : D) : BitMutationM (BitArray N) := do
  fill (← similar dims) true

/--
Julia source: base/bitarray.jl:394-394 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
falses(dims::DimOrInd...) = falses(dims)
```
-/
def falsesVarargs {N : Nat} {D : Type} (dispatch : List D → BitMutationM (BitArray N))
    (dims : List D) : BitMutationM (BitArray N) := dispatch dims

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
def truesVarargs {N : Nat} {D : Type} (dispatch : List D → BitMutationM (BitArray N))
    (dims : List D) : BitMutationM (BitArray N) := dispatch dims

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
def genBitArrayUnknown {I S C P : Type} (checkedDims : List I64 → BitMutationM I64)
    (allocateChunks : Nat → BitMutationM Nat) (allocateCache : Nat → BitMutationM C)
    (iterate : I → Option S → BitMutationM (Option (Bool × S)))
    (cacheSet : C → Bool → I64 → BitMutationM Unit)
    (cacheFillFalse : C → I64 → I64 → BitMutationM Unit)
    (getBool : C → I64 → BitMutationM Bool) (pointer : C → I64 → P)
    (unsafeLoad : P → I64 → BitMutationM U64) (lengthChunks : Nat → BitMutationM I64)
    (toInt : I64 → I64) (rangeLength : BitRange → I64)
    (itr : I) : BitMutationM BitVector :=
  genBitArrayFromIterator checkedDims allocateChunks allocateCache iterate cacheSet cacheFillFalse
    getBool pointer unsafeLoad lengthChunks toInt rangeLength itr

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
def genBitArrayNVector {I : Type} (gen : BitIteratorSize → I → BitMutationM BitVector)
    (itsz : BitIteratorSize) (itr : I) : BitMutationM BitVector := gen itsz itr

/--
Julia source: base/bitarray.jl:597-597 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gen_bitarrayN(::Type{BitVector}, itsz::HasShape{1}, itr)           = gen_bitarray(itsz, itr)
```
-/
def genBitArrayNVectorShapeOne {I : Type} (gen : BitIteratorSize → I → BitMutationM BitVector)
    (itsz : BitIteratorSize) (itr : I) : BitMutationM BitVector := gen itsz itr

/--
Julia source: base/bitarray.jl:598-598 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
gen_bitarrayN(::Type{BitArray{N}}, itsz::HasShape{N}, itr) where N = gen_bitarray(itsz, itr)
```
-/
def genBitArrayNRank {N : Nat} {I : Type} (gen : BitIteratorSize → I → BitMutationM (BitArray N))
    (itsz : BitIteratorSize) (itr : I) : BitMutationM (BitArray N) := gen itsz itr

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
  if dims == B.dims then pure B else bitArrayReshapeInternal checkedDims allocate B dims

/--
Julia source: base/bitarray.jl:475-475 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
reshape(B::BitArray, dims::Tuple{Vararg{Int}}) = _bitreshape(B, dims)
```
-/
def bitArrayReshapeAny {N : Nat} (checkedDims : List I64 → BitMutationM I64)
    (allocate : List I64 → BitMutationM (BitArray N)) (B : BitArray N) (dims : List I64) : BitMutationM (BitArray N) :=
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
def bitArrayFromIterator {I S : Type} {N : Nat} (iteratorSize : I → S) (gen : S → I → BitMutationM (BitArray N)) (itr : I) : BitMutationM (BitArray N) :=
  gen (iteratorSize itr) itr

/--
Julia source: base/bitarray.jl:567-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitArray{N}(itr) where N = gen_bitarrayN(BitArray{N}, IteratorSize(itr), itr)
```
-/
def bitArrayNFromIterator {N : Nat} {I S : Type} (iteratorSize : I → S)
    (gen : Nat → S → I → BitMutationM (BitArray N)) (itr : I) : BitMutationM (BitArray N) :=
  gen N (iteratorSize itr) itr

/--
Julia source: base/bitarray.jl:569-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{T}, a::AbstractArray) where {T<:BitArray} = a isa T ? a : T(a)::T
```
-/
def convertToBitArray {N : Nat} {A T : Type}
    (isa : A → T → Bool) (asTarget : A → T → BitArray N)
    (construct : T → A → BitMutationM (BitArray N)) (target : T) (a : A) : BitMutationM (BitArray N) :=
  if isa a target then pure (asTarget a target) else construct target a

/--
Julia source: base/bitarray.jl:694-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
indexoffset(i) = first(i)-1
```
-/
def indexOffset {R : Type} (first : R → I64) (i : R) : I64 := first i - int 1

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
def bitArraySetIndexRange {N : Nat} {X J : Type} (setindex : JuliaLean.base.indices.IndexStyle → BitArray N → X → J → BitMutationM (BitArray N))
    (toIndices : BitArray N → J → BitMutationM J) (B : BitArray N) (x : X) (j0 : J) : BitMutationM (BitArray N) := do
  setindex (bitArrayIndexStyle) B x (← toIndices B j0)

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
def bitArrayEqual {N M : Nat} (chunkEqual : Nat → Nat → BitMutationM Bool)
    (a : BitArray N) (b : BitArray M) : BitMutationM Bool := do
  if a.dims != b.dims then return false
  chunkEqual a.chunks b.chunks

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
def bitArrayReverseTuple {N : Nat} (reverseDim : BitArray N → I64 → BitMutationM (BitArray N))
    (a : BitArray N) (dims : List I64) : BitMutationM (BitArray N) :=
  reverseDim a (dims.getD 0 (int 0))

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
def bitcount {T : Type} (addCount : T → I64 → T) (remCount : T → T)
    (countOnes : U64 → I64) (init : T) (bc : Nat) : BitMutationM T := do
  let mut n := init
  let nc ← mutableLength bc
  for i in intRange (int 1) nc do
    n := remCount (addCount n (countOnes (← mutableGet bc i)))
  return n

/--
Julia source: base/bitarray.jl:1456-1456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_count(::typeof(identity), B::BitArray, ::Colon, init) = bitcount(B.chunks; init)
```
-/
def bitArrayCountIdentity {N : Nat} {T : Type} (bitcount : Nat → T → BitMutationM T)
    (B : BitArray N) (init : T) : BitMutationM T := bitcount B.chunks init

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
    : BitMutationM (BitArray N) := do
  if A.len > dest.len then throw (.dimensionMismatch "length of destination must be >= length of collection")
  if A.len == int 0 then return dest
  let destc := dest.chunks
  let Ac := A.chunks
  let lenAc ← mutableLength Ac
  for i in intRange (int 1) (lenAc - int 1) do mutableSet destc (f (← mutableGet Ac i)) i
  let destLast ← mutableGet destc lenAc
  let mask := maskEndArray A
  let sourceLast := f (← mutableGet Ac lenAc)
  mutableSet destc (or_int (and_int destLast (not_int mask)) (and_int sourceLast mask)) lenAc
  return dest

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
    (dest : BitArray 1) (A : BitArray N) (B : BitArray M) : BitMutationM (BitArray 1) := do
  let minBitlen := if A.len < B.len then A.len else B.len
  if minBitlen > dest.len then throw (.dimensionMismatch "length of destination must be >= length of smallest input collection")
  if A.len == int 0 || B.len == int 0 then return dest
  let destc := dest.chunks
  let Ac := A.chunks
  let Bc := B.chunks
  let lenAc ← mutableLength Ac
  let lenBc ← mutableLength Bc
  let lenChunks := if lenAc < lenBc then lenAc else lenBc
  for i in intRange (int 1) (lenChunks - int 1) do
    mutableSet destc (f (← mutableGet Ac i) (← mutableGet Bc i)) i
  let destLast ← mutableGet destc lenChunks
  let mask := maskEnd minBitlen
  let sourceLast := f (← mutableGet Ac lenChunks) (← mutableGet Bc lenChunks)
  mutableSet destc (or_int (and_int destLast (not_int mask)) (and_int sourceLast mask)) lenChunks
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

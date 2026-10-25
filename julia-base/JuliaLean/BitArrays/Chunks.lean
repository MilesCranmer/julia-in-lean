import JuliaLean.Core

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

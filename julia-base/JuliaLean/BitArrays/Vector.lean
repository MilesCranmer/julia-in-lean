import JuliaLean.BitArrays.Chunks

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

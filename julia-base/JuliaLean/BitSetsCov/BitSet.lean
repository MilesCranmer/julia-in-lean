import JuliaLean.BitSetsCov.Basic
import JuliaLean.BitArrays.Vector

/-!
# `BitSet`, `base/bitset.jl` (master `bbfa0ce4150`)

The state is `BitArrays.BitSetS` (fields `bits` and `offset`); `_setint!`,
`_bits_getindex` (`BitSetS.contains`) and the `UInt64` bit counts come from the
`BitArrays` area. Every other method of the file is mirrored here.

* `offset` and the chunk indices are `Int`s in `-2^60:2^57` (`bitset.jl:6-9`),
  so the `Int` arithmetic on them never wraps and the model uses `Int`; values
  that reach user code (`intoffset`, iteration, `first`, `last`) are built with
  Julia's wrapping `<<` and `+` (`shl6`, `JInt.wrap`).
* `Integer` arguments are mathematical integers; `Int(n)` is `toInt`.
* Fresh memory from `resize!`/`_growend!`/`_growbeg!` holds `dirty`.
* The four functions passed to `_matched_map!` (`|`, `&`, `(p, q) -> p & ~q`,
  `xor`) are `MapOp`; Julia applies them to `Bool`s (the two flags) and to
  `UInt64` chunks.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays

namespace BS

/-- Membership of the integer `x` in the chunk store (the bit `_bits_getindex` reads). -/
def mem (s : BitSetS) (x : Int) : Bool := BitSetProof.G s.bits s.offset (x / 64) (x % 64).toNat

/-- Type invariant (`base/bitset.jl:6-9`): no chunks while the offset is
`NO_OFFSET`; otherwise the chunks cover only `Int` elements. -/
def WF (s : BitSetS) : Prop :=
  (s.offset = noOffset → s.bits = []) ∧
  (s.offset ≠ noOffset → -(2 ^ 57) ≤ s.offset ∧ s.offset + s.bits.length ≤ 2 ^ 57)

/-- `BitSet()`, `base/bitset.jl:18-22`: a `Vector{UInt64}(undef, 4)` whose size is
set to `(0,)`, and `NO_OFFSET`. -/
def new : BitSetS := ⟨[], noOffset⟩

/-- `push!(s, n::Integer) = _setint!(s, Int(n), true)`, `base/bitset.jl:255`. -/
def push (s : BitSetS) (n : Int) : R BitSetS := do
  let i ← toInt n
  pure (s.setint i true)

/-- `union!(s::BitSet, itr)`, `base/bitset.jl:36-41`: `push!` every element. -/
def unionItr (s : BitSetS) (itr : List Int) : R BitSetS := itr.foldlM push s

/-- `BitSet(itr) = union!(BitSet(), itr)`, `base/bitset.jl:33`. -/
def ofItr (itr : List Int) : R BitSetS := unionItr new itr

/-- `push!(s::BitSet, ns::Integer...)`, `base/bitset.jl:257`. -/
def pushMany (s : BitSetS) (ns : List Int) : R BitSetS := ns.foldlM push s

/-- `intoffset(s) = s.offset << 6`, `base/bitset.jl:43`. -/
def intoffset (s : BitSetS) : JInt64 := shl6 s.offset

/-- `empty(s::BitSet, Int)` and `emptymutable(s::BitSet, Int)`, `base/bitset.jl:45-46`. -/
def empty (_s : BitSetS) : BitSetS := new
def emptymutable (_s : BitSetS) : BitSetS := new

/-- `copy!(dest::BitSet, src::BitSet)`, `base/bitset.jl:51-56`. -/
def copyBang (dest src : BitSetS) (dirty : U64) : R BitSetS := do
  let bits := vresize dest.bits src.bits.length dirty
  let bits ← vcopyto bits src.bits
  pure ⟨bits, src.offset⟩

/-- `copy(s1) = copy!(BitSet(), s1)` and `copymutable(s) = copy(s)`, `base/bitset.jl:48-49`. -/
def copy (s : BitSetS) (dirty : U64) : R BitSetS := copyBang new s dirty
def copymutable (s : BitSetS) (dirty : U64) : R BitSetS := copy s dirty

/-- `sizehint!(v::Vector, sz::Integer)` (`base/array.jl:1617-1622`): `Int(sz)`,
then the elements are kept (only the capacity changes). -/
def vsizehint (v : List U64) (sz : Int) : R (List U64) := do
  let _ ← toInt sz
  pure v

/-- `sizehint!(s, n; first, shrink)`, `base/bitset.jl:58-61`: `(n + 63) >> 6` is
computed in `n`'s type (wrapping `+`, arithmetic shift). -/
def sizehint {t : IntTy} (s : BitSetS) (n : JInt t) : R BitSetS := do
  let sz : JInt t := n + JInt.lit t 63
  let bits ← vsizehint s.bits (sz.val / 64)
  pure ⟨bits, s.offset⟩

/-- `_bits_getindex(b, n, offset)`, `base/bitset.jl:63-68` (= `BitSetS.contains`). -/
def bitsGetindex (b : List U64) (n : JInt64) (offset : Int) : Bool := BitSetS.contains ⟨b, offset⟩ n

/-- `_bits_findnext(b, start)`, `base/bitset.jl:70-76` (0-based `start ≥ 0`). -/
def bitsFindnext (b : List U64) (start : Nat) : Int :=
  if start / 64 + 1 > b.length then -1
  else match unsafeBitfindnext b (start + 1) with
    | none => -1
    | some ind => (ind : Int) - 1

/-- `_bits_findprev(b, start)`, `base/bitset.jl:78-84` (0-based `start ≤ 64 length(b) - 1`). -/
def bitsFindprev (b : List U64) (start : Int) : Int :=
  if ¬ start ≥ 0 then -1
  else match unsafeBitfindprev b (start + 1).toNat with
    | none => -1
    | some ind => (ind : Int) - 1

/-- `_growend0!(b, nchunks)`, `base/bitset.jl:116-122`. -/
def growend0 (b : List U64) (nchunks : Nat) (dirty : U64) : List U64 :=
  let len := b.length
  let b := growend b nchunks dirty
  (List.range (b.length - len)).foldl (fun b k => vset b (len + 1 + k) 0) b

/-- `_growbeg0!(b, nchunks)`, `base/bitset.jl:124-129`. -/
def growbeg0 (b : List U64) (nchunks : Nat) (dirty : U64) : List U64 :=
  let b := growbeg b nchunks dirty
  (List.range nchunks).foldl (fun b k => vset b (1 + k) 0) b

/-- `s.bits[i] |= m` -/
def orAt (b : List U64) (i : Nat) (m : U64) : List U64 := vset b i (vget b i ||| m)

/-- The body of `union!(s::BitSet, r)` after `a = Int(first(r))` and
`b = Int(last(r))`, `base/bitset.jl:134-166`. -/
def unionRangeBits (s : BitSetS) (a b : JInt64) (dirty : U64) : BitSetS :=
  let cidxa := a.val / 64
  let cidxb := b.val / 64
  let off := if s.offset = noOffset then cidxa else s.offset
  let len : Int := s.bits.length
  let diffa := cidxa - off
  let diffb := cidxb - off
  let bits := if diffb ≥ len then growend0 s.bits (diffb - len + 1).toNat dirty else s.bits
  let (bits, off, diffa, diffb) :=
    if diffa < 0 then (growbeg0 bits (-diffa).toNat dirty, cidxa, (0 : Int), diffb - diffa)
    else (bits, off, diffa, diffb)
  let i := (a.val % 64).toNat
  let j := (b.val % 64).toNat
  let u : U64 := ~~~0
  let bits :=
    if diffa = diffb then
      orAt bits (diffa + 1).toNat (((u >>> i) <<< (i + 63 - j)) >>> (63 - j))
    else
      let bits := orAt bits (diffa + 1).toNat ((u >>> i) <<< i)
      let bits := orAt bits (diffb + 1).toNat ((u <<< (63 - j)) >>> (63 - j))
      (List.range (diffb - diffa - 1).toNat).foldl (fun bits (k : Nat) => vset bits (diffa + 2 + (k : Int)).toNat u) bits
  ⟨bits, off⟩

/-- `union!(s::BitSet, r::AbstractUnitRange{<:Integer})`, `base/bitset.jl:131-167`,
for `r = a0:b0`: `isempty(r) && return s`, then the two `Int` conversions. -/
def unionRange (s : BitSetS) (a0 b0 : Int) (dirty : U64) : R BitSetS :=
  if b0 < a0 then .ok s else do
    let a ← toInt a0
    let b ← toInt b0
    pure (unionRangeBits s a b dirty)

/-- The functions handed to `_matched_map!`: `|` (`union!`), `&` (`intersect!`),
`(p, q) -> p & ~q` (`setdiff!`) and `xor` (`symdiff!`). -/
inductive MapOp where
  | or | and | andNot | xor
  deriving Repr, DecidableEq

def MapOp.bool : MapOp → Bool → Bool → Bool
  | .or, p, q => p || q
  | .and, p, q => p && q
  | .andNot, p, q => p && !q
  | .xor, p, q => p ^^ q

def MapOp.chunk : MapOp → U64 → U64 → U64
  | .or, p, q => p ||| q
  | .and, p, q => p &&& q
  | .andNot, p, q => p &&& ~~~q
  | .xor, p, q => p ^^^ q

/-- `for i = lo:hi; a1[i] = f(a1[i], a2[i - bdiff]); end` -/
def mapCommon (f : MapOp) (a1 a2 : List U64) (bdiff lo hi : Int) : List U64 :=
  (List.range (hi - lo + 1).toNat).foldl
    (fun a (k : Nat) => vset a (lo + (k : Int)).toNat
      (f.chunk (vget a (lo + (k : Int)).toNat) (vget a2 (lo + (k : Int) - bdiff).toNat))) a1

/-- `for i = lo:hi; a[i] = CHK0; end` -/
def zeroRange (a : List U64) (lo hi : Int) : List U64 :=
  (List.range (hi - lo + 1).toNat).foldl (fun a (k : Nat) => vset a (lo + (k : Int)).toNat 0) a

/-- The `Bits` method `_matched_map!(f, a1, b1, a2, b2, lff, rff)`,
`base/bitset.jl:189-253`: the new chunks of `a1` and the new offset. `a2` is
read as it was on entry; when `a1 === a2` (e.g. `union!(s, s)`) the offsets are
equal and each `a2[i]` is read before `a1[i]` is written. -/
def matchedMapBits (f : MapOp) (a1 : List U64) (b1 : Int) (a2 : List U64) (b2 : Int)
    (lff rff : Bool) (dirty : U64) : List U64 × Int :=
  let l1 : Int := a1.length
  let l2 : Int := a2.length
  let bdiff := b2 - b1
  let e1 := l1 + b1
  let e2 := l2 + b2
  let ediff := e2 - e1
  let a1 := mapCommon f a1 a2 bdiff (max 1 (1 + bdiff)) (min l1 (l2 + bdiff))
  let (a1, l1) :=
    if ediff > 0 then
      if lff then (a1, l1)
      else
        let a1 := growend a1 ediff.toNat dirty
        -- `for outer l1 = l1+1:bdiff; a1[l1] = CHK0; end`
        let (a1, l1) := if l1 + 1 ≤ bdiff then (zeroRange a1 (l1 + 1) bdiff, bdiff) else (a1, l1)
        let ediff := e2 - l1 - b1
        let a1 := vunsafeCopyto a1 (l1 + 1).toNat a2 (l2 + 1 - ediff).toNat ediff.toNat
        (a1, (a1.length : Int))
    else if ediff < 0 then
      if rff then (deleteend a1 (min l1 (-ediff)).toNat, l1) else (a1, l1)
    else (a1, l1)
  if bdiff < 0 then
    if lff then (a1, b1)
    else
      let a1 := growbeg a1 (-bdiff).toNat dirty
      let a1 := zeroRange a1 (l2 + 1) (-bdiff)
      let b1 := b1 + bdiff
      (vunsafeCopyto a1 1 a2 1 (min (-bdiff) l2).toNat, b1)
  else if bdiff > 0 then
    if rff then (deletebeg a1 (min l1 bdiff).toNat, b1 + bdiff) else (a1, b1)
  else (a1, b1)

/-- `empty!(s::BitSet)`, `base/bitset.jl:285-289`. -/
def emptyBang (_s : BitSetS) : BitSetS := ⟨[], noOffset⟩

/-- The `BitSet` method `_matched_map!(f, s1, s2)`, `base/bitset.jl:169-184`. -/
def matchedMap (f : MapOp) (s1 s2 : BitSetS) (dirty : U64) : R BitSetS :=
  let lff := f.bool false false == f.bool false true && f.bool false true == false
  let rff := f.bool false false == f.bool true false && f.bool true false == false
  if s1.offset = noOffset then (if lff then pure s1 else copyBang s1 s2 dirty)
  else if s2.offset = noOffset then pure (if rff then emptyBang s1 else s1)
  else
    let r := matchedMapBits f s1.bits s1.offset s2.bits s2.offset lff rff dirty
    pure ⟨r.1, r.2⟩

/-- `union!(s1::BitSet, s2::BitSet)`, `base/bitset.jl:296`. -/
def unionBS (s1 s2 : BitSetS) (dirty : U64) : R BitSetS := matchedMap .or s1 s2 dirty
/-- `intersect!(s1::BitSet, s2::BitSet)`, `base/bitset.jl:301`. -/
def intersectBang (s1 s2 : BitSetS) (dirty : U64) : R BitSetS := matchedMap .and s1 s2 dirty
/-- `setdiff!(s1::BitSet, s2::BitSet)`, `base/bitset.jl:303`. -/
def setdiffBang (s1 s2 : BitSetS) (dirty : U64) : R BitSetS := matchedMap .andNot s1 s2 dirty
/-- `symdiff!(s1::BitSet, s2::BitSet)`, `base/bitset.jl:326`. -/
def symdiffBS (s1 s2 : BitSetS) (dirty : U64) : R BitSetS := matchedMap .xor s1 s2 dirty

/-- `intersect(s1::BitSet, s2::BitSet)`, `base/bitset.jl:298-299`. -/
def intersect (s1 s2 : BitSetS) (dirty : U64) : R BitSetS :=
  if s1.bits.length < s2.bits.length then do intersectBang (← copy s1 dirty) s2 dirty
  else do intersectBang (← copy s2 dirty) s1 dirty

/-- An argument of `union(s::BitSet, sets...)`: a `BitSet`, an
`AbstractUnitRange{<:Integer}` `a:b`, or another iterable of `Integer`s. -/
inductive Arg where
  | bitset (t : BitSetS)
  | range (a b : Int)
  | itr (xs : List Int)

/-- `union!(s::BitSet, x)` for one argument, by dispatch. -/
def unionOne (s : BitSetS) (dirty : U64) : Arg → R BitSetS
  | .bitset t => unionBS s t dirty
  | .range a b => unionRange s a b dirty
  | .itr xs => unionItr s xs

/-- `union(s::BitSet, sets...) = union!(copy(s), sets...)`, `base/bitset.jl:295`
(the generic `union!(s, sets...)` loop, `base/abstractset.jl:85-90`). -/
def union (s : BitSetS) (sets : List Arg) (dirty : U64) : R BitSetS := do
  sets.foldlM (fun c a => unionOne c dirty a) (← copy s dirty)

/-- `in(n::Int, s::BitSet)`, `base/bitset.jl:330`. -/
def inInt (n : JInt64) (s : BitSetS) : Bool := bitsGetindex s.bits n s.offset

/-- `_is_convertible_Int(n)`, `base/bitset.jl:279`. -/
def isConvertibleInt (n : Int) : Bool := decide (inIntRange n)

/-- `in(n::Integer, s::BitSet)`, `base/bitset.jl:331`. -/
def inInteger (n : Int) (s : BitSetS) : Bool :=
  if h : inIntRange n then inInt ⟨n, (inIntRange_iff n).mp h⟩ s else false

/-- `delete!(s::BitSet, n::Int) = _setint!(s, n, false)`, `base/bitset.jl:280`. -/
def deleteInt (s : BitSetS) (n : JInt64) : BitSetS := s.setint n false

/-- `delete!(s::BitSet, n::Integer)`, `base/bitset.jl:281`. -/
def deleteInteger (s : BitSetS) (n : Int) : BitSetS :=
  if h : inIntRange n then deleteInt s ⟨n, (inIntRange_iff n).mp h⟩ else s

/-- `pop!(s::BitSet, n::Integer)`, `base/bitset.jl:261-268`. -/
def popKey (s : BitSetS) (n : Int) : R (Int × BitSetS) :=
  if inInteger n s then .ok (n, deleteInteger s n) else .error .keyError

/-- `pop!(s::BitSet, n::Integer, default)`, `base/bitset.jl:270-277`; `none` is `default`. -/
def popDefault (s : BitSetS) (n : Int) : Option Int × BitSetS :=
  if inInteger n s then (some n, deleteInteger s n) else (none, s)

/-- `int_symdiff!(s, n::Integer)`, `base/bitset.jl:319-324`. -/
def intSymdiff (s : BitSetS) (n : Int) : R BitSetS := do
  let n0 ← toInt n
  let val := !(inInt n0 s)
  pure (s.setint n0 val)

/-- `symdiff!(s::BitSet, ns::AbstractSet)`, `base/bitset.jl:312-317`, for a set of
`Integer`s listed in iteration order. -/
def symdiffSet (s : BitSetS) (ns : List Int) : R BitSetS := ns.foldlM intSymdiff s

/-- `_blsr(x) = x & (x - 1)`, `base/bitarray.jl:117`. -/
def blsr (x : U64) : U64 := x &&& (x - 1)

/-- The `while word == 0` loop of `iterate(s::BitSet, (word, idx))`,
`base/bitset.jl:333-340`, reading the current chunks; `fuel` bounds the loop. -/
def iterStep (s : BitSetS) : Nat → U64 → Nat → Option (JInt64 × U64 × Nat)
  | fuel, word, idx =>
    if word ≠ 0 then
      some (JInt.wrap .i64 (trailingZeros word + (shl6 ((idx : Int) - 1 + s.offset)).val), blsr word, idx)
    else match fuel with
      | 0 => none
      | fuel + 1 =>
        if idx = s.bits.length then none
        else iterStep s fuel (vget s.bits (idx + 1)) (idx + 1)

/-- `iterate(s, state)` with the default state `(CHK0, 0)`. -/
def iterate (s : BitSetS) (st : U64 × Nat) : Option (JInt64 × U64 × Nat) :=
  iterStep s (s.bits.length + 1) st.1 st.2

/-- Iteration from `state` to exhaustion (`fuel` bounds the number of elements). -/
def iterFrom (s : BitSetS) : Nat → U64 × Nat → List JInt64
  | 0, _ => []
  | fuel + 1, st =>
    match iterate s st with
    | none => []
    | some (x, w, i) => x :: iterFrom s fuel (w, i)

/-- The elements `for n in s` visits. -/
def elems (s : BitSetS) : List JInt64 := iterFrom s (64 * s.bits.length + 1) (0, 0)

/-- `unsafe_filter!(f, s) = mapfilter(!f, delete!, s, s)`
(`base/abstractset.jl:633-641`): the loop iterates `s` while deleting from it;
every step reads the current chunks. -/
def filterLoop (f : JInt64 → Bool) : Nat → BitSetS → U64 × Nat → BitSetS
  | 0, s, _ => s
  | fuel + 1, s, st =>
    match iterate s st with
    | none => s
    | some (x, w, i) =>
      let s := if !(f x) then deleteInt s x else s
      filterLoop f fuel s (w, i)

/-- `filter!(f, s::BitSet) = unsafe_filter!(f, s)`, `base/bitset.jl:328`. -/
def filterBang (f : JInt64 → Bool) (s : BitSetS) : BitSetS :=
  filterLoop f (64 * s.bits.length + 1) s (0, 0)

/-- `_throw_bitset_notempty_error()`, `base/bitset.jl:342-343`. -/
def throwNotempty {α : Type} : R α := .error .argumentError

/-- `first(s::BitSet)`, `base/bitset.jl:345-348`. -/
def first (s : BitSetS) : R JInt64 :=
  let idx := bitsFindnext s.bits 0
  if idx = -1 then throwNotempty else .ok (JInt.wrap .i64 (idx + (intoffset s).val))

/-- `last(s::BitSet)`, `base/bitset.jl:350-353`. -/
def last (s : BitSetS) : R JInt64 :=
  let idx := bitsFindprev s.bits ((shl6 s.bits.length).val - 1)
  if idx = -1 then throwNotempty else .ok (JInt.wrap .i64 (idx + (intoffset s).val))

/-- `length(s::BitSet) = bitcount(s.bits)`, `base/bitset.jl:355`. -/
def length (s : BitSetS) : JInt64 := bitcount s.bits (JInt.lit .i64 0)

/-- `pop!(s::BitSet) = pop!(s, last(s))`, `base/bitset.jl:259`. -/
def pop (s : BitSetS) : R (Int × BitSetS) := do popKey s (← last s).val

/-- `popfirst!(s::BitSet) = pop!(s, first(s))`, `base/bitset.jl:283`. -/
def popfirst (s : BitSetS) : R (Int × BitSetS) := do popKey s (← first s).val

/-- `show(io, s::BitSet)`, `base/bitset.jl:357-366`: the printed text. -/
def showStr (s : BitSetS) : String :=
  let body := (elems s).foldl (fun (acc : String × Bool) n =>
    ((if !acc.2 then acc.1 ++ ", " else acc.1) ++ toString n.val, false)) ("", true)
  "BitSet([" ++ body.1 ++ "])"

/-- `_check0(a, b, e)`, `base/bitset.jl:368-373`. -/
def check0 (a : List U64) (b e : Int) : Bool :=
  (List.range (e - b + 1).toNat).all (fun (k : Nat) => vget a (b + (k : Int)).toNat == 0)

/-- `isempty(s::BitSet)`, `base/bitset.jl:291`. -/
def isempty (s : BitSetS) : Bool := check0 s.bits 1 s.bits.length

/-- `memcmp(pointer(a1, i), pointer(a2), n << 3) == 0` on chunk vectors. -/
def memeq (a1 : List U64) (i : Int) (a2 : List U64) (n : Int) : Bool :=
  (List.range n.toNat).all (fun (k : Nat) => vget a1 (i + (k : Int)).toNat == vget a2 (1 + k))

/-- `==(s1::BitSet, s2::BitSet)`, `base/bitset.jl:375-407`. -/
def eq (s1 s2 : BitSetS) : Bool :=
  let (s1, s2) := if s1.offset > s2.offset then (s2, s1) else (s1, s2)
  let a1 := s1.bits
  let a2 := s2.bits
  let b1 := s1.offset
  let b2 := s2.offset
  let l1 : Int := a1.length
  let l2 : Int := a2.length
  let e1 := l1 + b1
  let overlap0 := max 0 (e1 - b2)
  let included := decide (overlap0 ≥ l2)
  let overlap := if included then l2 else overlap0
  if !check0 a1 1 (l1 - overlap0) then false
  else if (if included then !check0 a1 (b2 - b1 + l2 + 1) l1 else !check0 a2 (1 + overlap) l2) then false
  else if overlap > 0 then memeq a1 (b2 - b1 + 1) a2 overlap
  else true

/-- `f(a, b) = a == a & b`, `base/bitset.jl:414`. -/
def subChunk (a b : U64) : Bool := a == (a &&& b)

/-- `issubset(a::BitSet, b::BitSet)`, `base/bitset.jl:409-419`. -/
def issubset (a b : BitSetS) : Bool :=
  let n : Int := a.bits.length
  let shift := b.offset - a.offset
  let i := shift
  let j := shift + b.bits.length
  let rng (lo hi : Int) : List Int := (List.range (hi - lo + 1).toNat).map (fun (k : Nat) => lo + (k : Int))
  (rng 1 (min n i)).all (fun k => vget a.bits k.toNat == 0) &&
  (rng (max 1 (i + 1)) (min n j)).all (fun k => subChunk (vget a.bits k.toNat) (vget b.bits (k - shift).toNat)) &&
  (rng (max 1 (j + 1)) n).all (fun k => vget a.bits k.toNat == 0)

/-- `⊊(a::BitSet, b::BitSet) = a <= b && a != b`, `base/bitset.jl:420`
(`<=` is `⊆`, `base/abstractset.jl:626`). -/
def psubset (a b : BitSetS) : Bool := issubset a b && !(eq a b)

/-- `minimum`, `maximum`, `extrema`, `issorted` of a `BitSet`, `base/bitset.jl:423-426`. -/
def minimum (s : BitSetS) : R JInt64 := first s
def maximum (s : BitSetS) : R JInt64 := last s
def extrema (s : BitSetS) : R (JInt64 × JInt64) := do pure (← first s, ← last s)
def issorted (_s : BitSetS) : Bool := true

end BS

end JuliaLean.BitSetsCov

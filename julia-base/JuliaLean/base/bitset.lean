import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.bitarray
import JuliaLean.base.range
import JuliaLean.base.abstractset
import JuliaLean.Registry.Types

/-!
# Source-mirrored model of `base/bitset.jl`

`BitSet` is represented by its UInt64 chunks and chunk offset. Vector capacity is
not observable through this API, so the model records only initialized contents.
The chunk primitives use the typed integer and bit-array models; all Integer
arguments remain mathematical integers until Julia's explicit `Int` conversion.
-/

namespace JuliaLean.base.bitset

open JuliaLean

abbrev I64 := JInt .i64
abbrev U64 := JInt .u64

def int64 (x : Int) : I64 := JInt.lit .i64 x
def uint64 (x : Int) : U64 := JInt.lit .u64 x
def zero64 : U64 := uint64 0
def noOffset : Int := -(2 ^ 60)

def div64 (x : Int) : Int := (JuliaLean.base.bitarray.div64 (int64 x)).val
def mod64 (x : Int) : Nat := (JuliaLean.base.bitarray.mod64 (int64 x)).val.toNat

def intRange (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map (fun k => lo + Int.ofNat k)

def bitsGet (bits : List U64) (i : Nat) : U64 := bits.getD (i - 1) zero64
def bitsSet (bits : List U64) (i : Nat) (x : U64) : List U64 := bits.set (i - 1) x
def bitsGrowEnd (bits : List U64) (n : Nat) (dirty : U64) : List U64 :=
  bits ++ List.replicate n dirty
def bitsGrowBeg (bits : List U64) (n : Nat) (dirty : U64) : List U64 :=
  List.replicate n dirty ++ bits
def bitsDeleteEnd (bits : List U64) (n : Nat) : List U64 := bits.take (bits.length - n)
def bitsDeleteBeg (bits : List U64) (n : Nat) : List U64 := bits.drop n

def copyChunks (dest : List U64) (destStart : Nat) (src : List U64) (srcStart n : Nat) : List U64 :=
  (List.range n).foldl (fun out k => bitsSet out (destStart + k) (bitsGet src (srcStart + k))) dest

def bitAt (word : U64) (bit : Nat) : Bool :=
  JuliaLean.base.int.and_int word (JuliaLean.base.int.shl_int (uint64 1) (int64 bit)) != zero64

def setBit (bits : List U64) (value : Bool) (chunk bit : Nat) : List U64 :=
  let mask := JuliaLean.base.int.shl_int (uint64 1) (int64 bit)
  let old := bitsGet bits chunk
  bitsSet bits chunk (if value then JuliaLean.base.int.or_int old mask else
    JuliaLean.base.int.and_int old (JuliaLean.base.int.not_int mask))

inductive Error where
  | julia (error : JlError)
  | range (error : JuliaLean.base.range.Exc)
  | keyError (key : Int)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

def toInt (n : Int) : Result I64 :=
  match JInt.convert .i64 n with
  | .ok x => .ok x
  | .error e => .error (.julia e)

structure BitSet where
  bits : List U64
  offset : Int
  deriving DecidableEq, Repr

structure UnitRangeI64 where
  first : I64
  last : I64
  deriving DecidableEq, Repr

instance : JuliaLean.base.range.JIsempty UnitRangeI64 where
  isempty r := .ok (r.first.val > r.last.val)

instance : JuliaLean.base.range.JFirst UnitRangeI64 I64 where
  first r := .ok r.first

instance : JuliaLean.base.range.JLast UnitRangeI64 I64 where
  last r := .ok r.last

instance : JuliaLean.base.range.JCtor I64 I64 where
  ctor x := .ok x

inductive UnionArg where
  | bitset (value : BitSet)
  | range (first last : I64)
  | iterator (values : List Int)
  deriving Repr

mutual

/--
Julia source: base/bitset.jl:13-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct BitSet <: AbstractSet{Int}
    const bits::Vector{UInt64}
    # 1st stored Int equals 64*offset
    offset::Int

    function BitSet()
        a = Vector{UInt64}(undef, 4) # start with some initial space for holding 0:255 without additional allocations later
        setfield!(a, :size, (0,)) # aka `empty!(a)` inlined
        return new(a, NO_OFFSET)
   end
end
```
-/
def new : BitSet := ⟨[], noOffset⟩

/--
Julia source: base/bitset.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
BitSet(itr) = union!(BitSet(), itr)
```
-/
def ofIterator (xs : List Int) : Result BitSet := unionIterator new xs

/--
Julia source: base/bitset.jl:36-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function union!(s::BitSet, itr)
    for x in itr
        push!(s, x)
    end
    return s
end
```
-/
def unionIterator (s : BitSet) (xs : List Int) : Result BitSet := do
  let mut out := s
  for x in xs do
    out ← push out x
  pure out

/--
Julia source: base/bitset.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline intoffset(s::BitSet) = s.offset << 6
```
-/
def intoffset (s : BitSet) : I64 := JuliaLean.base.int.shl_int (int64 s.offset) (int64 6)

/--
Julia source: base/bitset.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
empty(s::BitSet, ::Type{Int}=Int) = BitSet()
```
-/
def empty (_s : BitSet) : BitSet := new

/--
Julia source: base/bitset.jl:46-46 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
emptymutable(s::BitSet, ::Type{Int}=Int) = BitSet()
```
-/
def emptymutable (_s : BitSet) : BitSet := new

/--
Julia source: base/bitset.jl:48-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(s1::BitSet) = copy!(BitSet(), s1)
```
-/
def copy (s : BitSet) : BitSet := copyBang new s

/--
Julia source: base/bitset.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copymutable(s::BitSet) = copy(s)
```
-/
def copymutable (s : BitSet) : BitSet := copy s

/--
Julia source: base/bitset.jl:51-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy!(dest::BitSet, src::BitSet)
    resize!(dest.bits, length(src.bits))
    copyto!(dest.bits, src.bits)
    dest.offset = src.offset
    dest
end
```
-/
def copyBang (dest src : BitSet) : BitSet := { dest with bits := src.bits, offset := src.offset }

/--
Julia source: base/bitset.jl:58-61 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sizehint!(s::BitSet, n::Integer; first::Bool=false, shrink::Bool=true)
    sizehint!(s.bits, (n+63) >> 6; first, shrink)
    s
end
```
-/
def sizehint {t : IntTy} (s : BitSet) (n : JInt t) (first : Bool := false)
    (shrink : Bool := true) : Result BitSet := do
  let adjusted := n + JInt.lit t 63
  let chunks := if t.signed then
    JuliaLean.base.int.ashr_int adjusted (JInt.lit t 6)
  else
    JuliaLean.base.int.lshr_int adjusted (JInt.lit t 6)
  let _ ← toInt chunks.val
  let _ := first
  let _ := shrink
  pure s

/--
Julia source: base/bitset.jl:63-68 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _bits_getindex(b::Bits, n::Int, offset::Int)
    ci = _div64(n) - offset + 1
    1 <= ci <= length(b) || return false
    @inbounds r = (b[ci] & (one(UInt64) << _mod64(n))) != 0
    r
end
```
-/
def bitsGetindex (b : List U64) (n : I64) (offset : Int) : Bool :=
  let ci := div64 n.val - offset + 1
  if 1 ≤ ci ∧ ci ≤ b.length then bitAt (bitsGet b ci.toNat) (mod64 n.val) else false

/--
Julia source: base/bitset.jl:70-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _bits_findnext(b::Bits, start::Int)
    # start is 0-based
    # @assert start >= 0
    _div64(start) + 1 > length(b) && return -1
    ind = unsafe_bitfindnext(b, start+1)
    ind === nothing ? -1 : ind - 1
end
```
-/
def bitsFindnext (b : List U64) (start : Int) : Int :=
  match ((List.range (b.length * 64) : List Nat).find? (fun (p : Nat) =>
      start ≤ (p : Int) ∧ bitAt (bitsGet b (p / 64 + 1)) (p % 64))) with
  | some p => p
  | none => -1

/--
Julia source: base/bitset.jl:78-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _bits_findprev(b::Bits, start::Int)
    # start is 0-based
    # @assert start <= 64 * length(b) - 1
    start >= 0 || return -1
    ind = unsafe_bitfindprev(b, start+1)
    ind === nothing ? -1 : ind - 1
end
```
-/
def bitsFindprev (b : List U64) (start : Int) : Int :=
  match ((List.range (b.length * 64) : List Nat).reverse.find? (fun (p : Nat) =>
      (p : Int) ≤ start ∧ bitAt (bitsGet b (p / 64 + 1)) (p % 64))) with
  | some p => p
  | none => -1

/--
Julia source: base/bitset.jl:87-111 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _setint!(s::BitSet, idx::Int, b::Bool)
    cidx = _div64(idx)
    len = length(s.bits)
    diff = cidx - s.offset
    if diff >= len
        b || return s # setting a bit to zero outside the set's bits is a no-op

        # we put the following test within one of the two branches,
        # with the NO_OFFSET trick, to avoid having to perform it at
        # each and every call to _setint!
        if s.offset == NO_OFFSET # initialize the offset
            # we assume isempty(s.bits)
            s.offset = cidx
            diff = 0
        end
        _growend0!(s.bits, diff - len + 1)
    elseif diff < 0
        b || return s
        _growbeg0!(s.bits, -diff)
        s.offset += diff
        diff = 0
    end
    _unsafe_bitsetindex!(s.bits, b, diff+1, _mod64(idx))
    s
end
```
-/
def setint (s : BitSet) (idx : I64) (value : Bool) : BitSet :=
  let cidx := div64 idx.val
  let len : Int := s.bits.length
  let diff := cidx - s.offset
  if diff ≥ len then
    if !value then s else
      let (offset, diff) := if s.offset = noOffset then (cidx, (0 : Int)) else (s.offset, diff)
      let bits := growend0 s.bits (diff - len + 1).toNat
      { bits := setBit bits value (diff + 1).toNat (mod64 idx.val), offset := offset }
  else if diff < 0 then
    if !value then s else
      let bits := growbeg0 s.bits (-diff).toNat
      let offset := s.offset + diff
      { bits := setBit bits value 1 (mod64 idx.val), offset := offset }
  else
    { s with bits := setBit s.bits value (diff + 1).toNat (mod64 idx.val) }

/--
Julia source: base/bitset.jl:116-122 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _growend0!(b::Bits, nchunks::Int)
    len = length(b)
    _growend!(b, nchunks)
    for i in len+1:length(b)
        @inbounds b[i] = CHK0 # resize! gives dirty memory
    end
end
```
-/
def growend0 (b : List U64) (nchunks : Nat) : List U64 :=
  let len := b.length
  let grown := bitsGrowEnd b nchunks zero64
  (intRange (len + 1) grown.length).foldl
    (fun out i => bitsSet out i.toNat zero64) grown

/--
Julia source: base/bitset.jl:124-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function _growbeg0!(b::Bits, nchunks::Int)
    _growbeg!(b, nchunks)
    for i in 1:nchunks
        @inbounds b[i] = CHK0
    end
end
```
-/
def growbeg0 (b : List U64) (nchunks : Nat) : List U64 :=
  let grown := bitsGrowBeg b nchunks zero64
  (intRange 1 nchunks).foldl
    (fun out i => bitsSet out i.toNat zero64) grown

def unionRangeBits (s : BitSet) (a b : I64) : BitSet :=
  let cidxa := div64 a.val
  let cidxb := div64 b.val
  let offset := if s.offset = noOffset then cidxa else s.offset
  let len : Int := s.bits.length
  let diffa := cidxa - offset
  let diffb := cidxb - offset
  let bits := if diffb ≥ len then growend0 s.bits (diffb - len + 1).toNat else s.bits
  let (bits, offset, diffa, diffb) :=
    if diffa < 0 then
      (growbeg0 bits (-diffa).toNat, cidxa, (0 : Int), diffb - diffa)
    else (bits, offset, diffa, diffb)
  let i := mod64 a.val
  let j := mod64 b.val
  let ones := JuliaLean.base.int.not_int zero64
  let bits :=
    if diffa = diffb then
      let mask := JuliaLean.base.int.lshr_int
        (JuliaLean.base.int.shl_int (JuliaLean.base.int.lshr_int ones (int64 i))
          (int64 (i + 63 - j))) (int64 (63 - j))
      bitsSet bits (diffa + 1).toNat (JuliaLean.base.int.or_int (bitsGet bits (diffa + 1).toNat) mask)
    else
      let firstMask := JuliaLean.base.int.shl_int (JuliaLean.base.int.lshr_int ones (int64 i)) (int64 i)
      let lastMask := JuliaLean.base.int.lshr_int
        (JuliaLean.base.int.shl_int ones (int64 (63 - j))) (int64 (63 - j))
      let bits := bitsSet bits (diffa + 1).toNat
        (JuliaLean.base.int.or_int (bitsGet bits (diffa + 1).toNat) firstMask)
      let bits := bitsSet bits (diffb + 1).toNat
        (JuliaLean.base.int.or_int (bitsGet bits (diffb + 1).toNat) lastMask)
      (intRange (diffa + 1) (diffb - 1)).foldl
        (fun out n => bitsSet out (n + 1).toNat ones) bits
  ⟨bits, offset⟩

/--
Julia source: base/bitset.jl:131-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function union!(s::BitSet, r::AbstractUnitRange{<:Integer})
    isempty(r) && return s
    a, b = Int(first(r)), Int(last(r))
    cidxa = _div64(a)
    cidxb = _div64(b)
    if s.offset == NO_OFFSET
        s.offset = cidxa
    end
    len = length(s.bits)
    diffa = cidxa - s.offset
    diffb = cidxb - s.offset

    # grow s.bits as necessary
    if diffb >= len
        _growend0!(s.bits, diffb - len + 1)
    end
    if diffa < 0
        _growbeg0!(s.bits, -diffa)
        s.offset = cidxa # s.offset += diffa
        diffb -= diffa
        diffa = 0
    end

    # update s.bits
    i = _mod64(a)
    j = _mod64(b)
    @inbounds if diffa == diffb
        s.bits[diffa + 1] |= (((~CHK0) >> i) << (i+63-j)) >> (63-j)
    else
        s.bits[diffa + 1] |= ((~CHK0) >> i) << i
        s.bits[diffb + 1] |= (~CHK0  << (63-j)) >> (63-j)
        for n = diffa+1:diffb-1
            s.bits[n+1] = ~CHK0
        end
    end
    s
end
```
-/
def unionRange {R T : Type} [JuliaLean.base.range.JIsempty R]
    [JuliaLean.base.range.JFirst R T] [JuliaLean.base.range.JLast R T]
    [JuliaLean.base.range.JCtor I64 T] (s : BitSet) (r : R) : Result BitSet := do
  let empty ← Except.mapError Error.range (JuliaLean.base.range.JIsempty.isempty r)
  if empty then return s
  let firstValue ← Except.mapError Error.range (JuliaLean.base.range.JFirst.first r)
  let lastValue ← Except.mapError Error.range (JuliaLean.base.range.JLast.last r)
  let firstInt ← Except.mapError Error.range (JuliaLean.base.range.JCtor.ctor (T := I64) firstValue)
  let lastInt ← Except.mapError Error.range (JuliaLean.base.range.JCtor.ctor (T := I64) lastValue)
  pure (unionRangeBits s firstInt lastInt)

/--
Julia source: base/bitset.jl:169-184 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _matched_map!(f, s1::BitSet, s2::BitSet)
    left_false_is_false = f(false, false) == f(false, true) == false
    right_false_is_false = f(false, false) == f(true, false) == false

    # we must first handle the NO_OFFSET case; we could test for
    # isempty(s1) but it can be costly, so the user has to call
    # empty!(s1) themselves before-hand to re-initialize to NO_OFFSET
    if s1.offset == NO_OFFSET
        return left_false_is_false ? s1 : copy!(s1, s2)
    elseif s2.offset == NO_OFFSET
        return right_false_is_false ? empty!(s1) : s1
    end
    s1.offset = _matched_map!(f, s1.bits, s1.offset, s2.bits, s2.offset,
                              left_false_is_false, right_false_is_false)
    s1
end
```
-/
def matchedMap (fBool : Bool → Bool → Bool) (fBits : U64 → U64 → U64)
    (s1 s2 : BitSet) : BitSet :=
  let leftFalseIsFalse := fBool false false == fBool false true && fBool false true == false
  let rightFalseIsFalse := fBool false false == fBool true false && fBool true false == false
  if s1.offset = noOffset then
    if leftFalseIsFalse then s1 else copyBang s1 s2
  else if s2.offset = noOffset then
    if rightFalseIsFalse then emptyBang s1 else s1
  else
    let (bits, offset) := matchedMapBits fBits s1.bits s1.offset s2.bits s2.offset
      leftFalseIsFalse rightFalseIsFalse
    ⟨bits, offset⟩

/--
Julia source: base/bitset.jl:189-253 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _matched_map!(f, a1::Bits, b1::Int, a2::Bits, b2::Int,
                       left_false_is_false::Bool, right_false_is_false::Bool)
    l1, l2 = length(a1), length(a2)
    bdiff = b2 - b1
    e1, e2 = l1+b1, l2+b2
    ediff = e2 - e1

    # map! over the common indices
    @inbounds for i = max(1, 1+bdiff):min(l1, l2+bdiff)
        a1[i] = f(a1[i], a2[i-bdiff])
    end

    if ediff > 0
        if left_false_is_false
            # We don't need to worry about the trailing bits — they're all false
        else # @assert f(false, x) == x
            _growend!(a1, ediff)
            # if a1 and a2 are not overlapping, we infer implied "false" values from a2
            for outer l1 = l1+1:bdiff
                @inbounds a1[l1] = CHK0
            end
            # update ediff in case l1 was updated
            ediff = e2 - l1 - b1
            # copy actual chunks from a2
            unsafe_copyto!(a1, l1+1, a2, l2+1-ediff, ediff)
            l1 = length(a1)
        end
    elseif ediff < 0
        if right_false_is_false
            # We don't need to worry about the trailing bits — they're all false
            _deleteend!(a1, min(l1, -ediff))
            # no need to update l1, as if bdiff > 0 (case below), then bdiff will
            # be smaller anyway than an updated l1
        else # @assert f(x, false) == x
            # We don't need to worry about the trailing bits — they already have the
            # correct value
        end
    end

    if bdiff < 0
        if left_false_is_false
            # We don't need to worry about the leading bits — they're all false
        else # @assert f(false, x) == x
            _growbeg!(a1, -bdiff)
            # if a1 and a2 are not overlapping, we infer implied "false" values from a2
            for i = l2+1:-bdiff
                @inbounds a1[i] = CHK0
            end
            b1 += bdiff # updated return value

            # copy actual chunks from a2
            unsafe_copyto!(a1, 1, a2, 1, min(-bdiff, l2))
        end
    elseif bdiff > 0
        if right_false_is_false
            # We don't need to worry about the trailing bits — they're all false
            _deletebeg!(a1, min(l1, bdiff))
            b1 += bdiff
        else # @assert f(x, false) == x
            # We don't need to worry about the trailing bits — they already have the
            # correct value
        end
    end
    b1 # the new offset
end
```
-/
def matchedMapBits (fBits : U64 → U64 → U64)
    (a1 : List U64) (b1 : Int) (a2 : List U64) (b2 : Int)
    (leftFalseIsFalse rightFalseIsFalse : Bool) : List U64 × Int :=
  let l1 : Int := a1.length
  let l2 : Int := a2.length
  let bdiff := b2 - b1
  let e1 := l1 + b1
  let e2 := l2 + b2
  let ediff := e2 - e1
  let a1 := (intRange (max 1 (1 + bdiff)) (min l1 (l2 + bdiff))).foldl
    (fun a i => bitsSet a i.toNat (fBits (bitsGet a i.toNat) (bitsGet a2 (i - bdiff).toNat))) a1
  let (a1, l1) :=
    if ediff > 0 then
      if leftFalseIsFalse then (a1, l1) else
        let a1 := bitsGrowEnd a1 ediff.toNat zero64
        let (a1, l1) := if l1 + 1 ≤ bdiff then
          ((intRange (l1 + 1) bdiff).foldl (fun a i => bitsSet a i.toNat zero64) a1, bdiff)
          else (a1, l1)
        let ediff := e2 - l1 - b1
        let a1 := copyChunks a1 (l1 + 1).toNat a2 (l2 + 1 - ediff).toNat ediff.toNat
        (a1, a1.length)
    else if ediff < 0 then
      if rightFalseIsFalse then (bitsDeleteEnd a1 (min l1 (-ediff)).toNat, l1) else (a1, l1)
    else (a1, l1)
  if bdiff < 0 then
    if leftFalseIsFalse then (a1, b1) else
      let a1 := bitsGrowBeg a1 (-bdiff).toNat zero64
      let a1 := (intRange (l2 + 1) (-bdiff)).foldl
        (fun a i => bitsSet a i.toNat zero64) a1
      let b1 := b1 + bdiff
      (copyChunks a1 1 a2 1 (min (-bdiff) l2).toNat, b1)
  else if bdiff > 0 then
    if rightFalseIsFalse then (bitsDeleteBeg a1 (min l1 bdiff).toNat, b1 + bdiff) else (a1, b1)
  else (a1, b1)

/--
Julia source: base/bitset.jl:255-255 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline push!(s::BitSet, n::Integer) = _setint!(s, Int(n), true)
```
-/
def push (s : BitSet) (n : Int) : Result BitSet := do
  let index ← toInt n
  pure (setint s index true)

/--
Julia source: base/bitset.jl:257-257 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
push!(s::BitSet, ns::Integer...) = (for n in ns; push!(s, n); end; s)
```
-/
def pushMany (s : BitSet) (ns : List Int) : Result BitSet := do
  let mut out := s
  for n in ns do
    out ← push out n
  pure out

/--
Julia source: base/bitset.jl:259-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline pop!(s::BitSet) = pop!(s, last(s))
```
-/
def popLast (s : BitSet) : Result (Int × BitSet) := do
  let n ← last s
  popKey s n.val

/--
Julia source: base/bitset.jl:261-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function pop!(s::BitSet, n::Integer)
    if n in s
        delete!(s, n)
        n
    else
        throw(KeyError(n))
    end
end
```
-/
def popKey (s : BitSet) (n : Int) : Result (Int × BitSet) :=
  if inInteger n s then .ok (n, deleteInteger s n) else .error (.keyError n)

/--
Julia source: base/bitset.jl:270-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline function pop!(s::BitSet, n::Integer, default)
    if n in s
        delete!(s, n)
        n
    else
        default
    end
end
```
-/
def popDefault {α : Type} (s : BitSet) (n : Int) (default : α) : (Int ⊕ α) × BitSet :=
  if inInteger n s then (.inl n, deleteInteger s n) else (.inr default, s)

/--
Julia source: base/bitset.jl:279-279 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline _is_convertible_Int(n) = typemin(Int) <= n <= typemax(Int)
```
-/
def isConvertibleInt (n : Int) : Bool := decide (IntTy.i64.min ≤ n ∧ n ≤ IntTy.i64.max)

/--
Julia source: base/bitset.jl:280-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline delete!(s::BitSet, n::Int) = _setint!(s, n, false)
```
-/
def deleteInt (s : BitSet) (n : I64) : BitSet := setint s n false

/--
Julia source: base/bitset.jl:281-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline delete!(s::BitSet, n::Integer) = _is_convertible_Int(n) ? delete!(s, Int(n)) : s
```
-/
def deleteInteger (s : BitSet) (n : Int) : BitSet :=
  if isConvertibleInt n then deleteInt s (int64 n) else s

/--
Julia source: base/bitset.jl:283-283 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
popfirst!(s::BitSet) = pop!(s, first(s))
```
-/
def popfirst (s : BitSet) : Result (Int × BitSet) := do
  let n ← first s
  popKey s n.val

/--
Julia source: base/bitset.jl:285-289 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function empty!(s::BitSet)
    empty!(s.bits)
    s.offset = NO_OFFSET
    s
end
```
-/
def emptyBang (_s : BitSet) : BitSet := new

/--
Julia source: base/bitset.jl:291-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(s::BitSet) = _check0(s.bits, 1, length(s.bits))
```
-/
def isempty (s : BitSet) : Bool := check0 s.bits 1 s.bits.length

-- Dispatch for the heterogeneous arguments accepted by `union(s, sets...)`.
def unionArgs (s : BitSet) : List UnionArg → Result BitSet
  | [] => .ok s
  | arg :: rest => do
      let out ← match arg with
        | .bitset other => .ok (unionBang s other)
        | .range first last => unionRange s (UnitRangeI64.mk first last)
        | .iterator values => unionIterator s values
      unionArgs out rest

/--
Julia source: base/bitset.jl:295-295 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
union(s::BitSet, sets...) = union!(copy(s), sets...)
```
-/
def union (s : BitSet) (sets : List UnionArg) : Result BitSet := do
  let copied := copy s
  unionArgs copied sets

/--
Julia source: base/bitset.jl:296-296 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
union!(s1::BitSet, s2::BitSet) = _matched_map!(|, s1, s2)
```
-/
def unionBang (s1 s2 : BitSet) : BitSet :=
  matchedMap (· || ·) JuliaLean.base.int.or_int s1 s2

/--
Julia source: base/bitset.jl:298-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect(s1::BitSet, s2::BitSet) =
    length(s1.bits) < length(s2.bits) ? intersect!(copy(s1), s2) : intersect!(copy(s2), s1)

```
-/
def intersect (s1 s2 : BitSet) : BitSet :=
  if s1.bits.length < s2.bits.length then intersectBang (copy s1) s2
  else intersectBang (copy s2) s1

/--
Julia source: base/bitset.jl:301-301 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
intersect!(s1::BitSet, s2::BitSet) = _matched_map!(&, s1, s2)
```
-/
def intersectBang (s1 s2 : BitSet) : BitSet :=
  matchedMap (· && ·) JuliaLean.base.int.and_int s1 s2

/--
Julia source: base/bitset.jl:303-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
setdiff!(s1::BitSet, s2::BitSet) = _matched_map!((p, q) -> p & ~q, s1, s2)
```
-/
def setdiffBang (s1 s2 : BitSet) : BitSet :=
  matchedMap (fun p q => p && !q)
    (fun p q => JuliaLean.base.int.and_int p (JuliaLean.base.int.not_int q)) s1 s2

-- The iterator loop is kept separate so it follows Julia's per-element toggling order.
def symdiffLoop (s : BitSet) : List Int → Result BitSet
  | [] => .ok s
  | x :: xs => do
      let next ← intSymdiff s x
      symdiffLoop next xs

/--
Julia source: base/bitset.jl:305-310 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function symdiff!(s::BitSet, ns)
    for x in ns
        int_symdiff!(s, x)
    end
    return s
end
```
-/
def symdiffIterator (s : BitSet) (ns : List Int) : Result BitSet := symdiffLoop s ns

/--
Julia source: base/bitset.jl:312-317 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function symdiff!(s::BitSet, ns::AbstractSet)
    for x in ns
        int_symdiff!(s, x)
    end
    return s
end
```
-/
def symdiffSet (s : BitSet) (ns : List Int) : Result BitSet := symdiffLoop s ns

/--
Julia source: base/bitset.jl:319-324 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function int_symdiff!(s::BitSet, n::Integer)
    n0 = Int(n)
    val = !(n0 in s)
    _setint!(s, n0, val)
    s
end
```
-/
def intSymdiff (s : BitSet) (n : Int) : Result BitSet := do
  let n0 ← toInt n
  let value := !(bitsGetindex s.bits n0 s.offset)
  pure (setint s n0 value)

/--
Julia source: base/bitset.jl:326-326 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
symdiff!(s1::BitSet, s2::BitSet) = _matched_map!(xor, s1, s2)
```
-/
def symdiffBitSet (s1 s2 : BitSet) : BitSet :=
  matchedMap (· ^^ ·) JuliaLean.base.int.xor_int s1 s2

-- `unsafe_filter!` walks an iteration state while applying `delete!` in place.
def filterLoop (f : I64 → Bool) : Nat → BitSet → U64 × Nat → BitSet
  | 0, s, _ => s
  | fuel + 1, s, state =>
      match iterate s state with
      | none => s
      | some (x, nextState) =>
          let out := if !(f x) then deleteInt s x else s
          filterLoop f fuel out nextState

/--
Julia source: base/bitset.jl:328-328 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
filter!(f, s::BitSet) = unsafe_filter!(f, s)
```
-/
def filter (f : I64 → Bool) (s : BitSet) : BitSet :=
  filterLoop f (s.bits.length * 64 + 1) s (zero64, 0)

/--
Julia source: base/bitset.jl:330-330 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline in(n::Int, s::BitSet) = _bits_getindex(s.bits, n, s.offset)
```
-/
def inInt (n : I64) (s : BitSet) : Bool := bitsGetindex s.bits n s.offset

/--
Julia source: base/bitset.jl:331-331 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@inline in(n::Integer, s::BitSet) = _is_convertible_Int(n) ? in(Int(n), s) : false
```
-/
def inInteger (n : Int) (s : BitSet) : Bool :=
  if isConvertibleInt n then inInt (int64 n) s else false

/--
Julia source: base/bitset.jl:333-340 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(s::BitSet, (word, idx) = (CHK0, 0))
    while word == 0
        idx == length(s.bits) && return nothing
        idx += 1
        word = @inbounds s.bits[idx]
    end
    trailing_zeros(word) + (idx - 1 + s.offset) << 6, (_blsr(word), idx)
end
```
-/
def iterate (s : BitSet) (state : U64 × Nat := (zero64, 0)) : Option (I64 × (U64 × Nat)) :=
  let rec scan (fuel : Nat) (word : U64) (idx : Nat) : Option (I64 × (U64 × Nat)) :=
    if word != zero64 then
      let trailing := JuliaLean.base.int.trailing_zeros word
      let chunkBase := JuliaLean.base.int.shl_int (int64 (idx - 1 + s.offset)) (int64 6)
      some (JuliaLean.base.int.add_int trailing chunkBase,
        (JuliaLean.base.bitarray.blsr word, idx))
    else match fuel with
      | 0 => none
      | fuel + 1 =>
          if idx == s.bits.length then none
          else scan fuel (bitsGet s.bits (idx + 1)) (idx + 1)
  scan (s.bits.length + 1) state.1 state.2

/--
Julia source: base/bitset.jl:342-343 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline _throw_bitset_notempty_error() =
    throw(ArgumentError("collection must be non-empty"))
```
-/
def throwNotempty {α : Type} : Result α :=
  .error (.julia (.argumentError "collection must be non-empty"))

/--
Julia source: base/bitset.jl:345-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function first(s::BitSet)
    idx = _bits_findnext(s.bits, 0)
    idx == -1 ? _throw_bitset_notempty_error() : idx + intoffset(s)
end
```
-/
def first (s : BitSet) : Result I64 :=
  let idx := bitsFindnext s.bits 0
  if idx == -1 then throwNotempty else .ok (JuliaLean.base.int.add_int (int64 idx) (int64 (s.offset * 64)))

/--
Julia source: base/bitset.jl:350-353 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function last(s::BitSet)
    idx = _bits_findprev(s.bits, (length(s.bits) << 6) - 1)
    idx == -1 ? _throw_bitset_notempty_error() : idx + intoffset(s)
end
```
-/
def last (s : BitSet) : Result I64 :=
  let idx := bitsFindprev s.bits ((s.bits.length : Int) * 64 - 1)
  if idx == -1 then throwNotempty else .ok (JuliaLean.base.int.add_int (int64 idx) (int64 (s.offset * 64)))

/--
Julia source: base/bitset.jl:355-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(s::BitSet) = bitcount(s.bits) # = mapreduce(count_ones, +, s.bits; init=0)
```
-/
def length (s : BitSet) : I64 :=
  s.bits.foldl (fun count word => count + JuliaLean.base.int.count_ones word) (int64 0)

/--
Julia source: base/bitset.jl:357-366 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, s::BitSet)
    print(io, "BitSet([")
    first = true
    for n in s
        !first && print(io, ", ")
        print(io, n)
        first = false
    end
    print(io, "])")
end
```
-/
def showStr (s : BitSet) : String :=
  let rec loop (fuel : Nat) (state : U64 × Nat) (out : String) (firstValue : Bool) : String :=
    match fuel with
    | 0 => out
    | fuel + 1 =>
        match iterate s state with
        | none => out
        | some (n, nextState) =>
            let separator := if firstValue then "" else ", "
            loop fuel nextState (out ++ separator ++ toString n.val) false
  "BitSet([" ++ loop (s.bits.length * 64 + 1) (zero64, 0) "" true ++ "])"

/--
Julia source: base/bitset.jl:368-373 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _check0(a::Vector{UInt64}, b::Int, e::Int)
    @inbounds for i in b:e
        a[i] == CHK0 || return false
    end
    true
end
```
-/
def check0 (a : List U64) (b e : Int) : Bool :=
  (intRange b e).all (fun i => bitsGet a i.toNat == zero64)

-- Chunk equality is Julia's `memcmp(..., n << 3) == 0` on aligned UInt64 data.
def memeq (a1 : List U64) (i : Int) (a2 : List U64) (n : Int) : Bool :=
  (List.range n.toNat).all (fun k => bitsGet a1 (i + k).toNat == bitsGet a2 (k + 1))

/--
Julia source: base/bitset.jl:375-407 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ==(s1::BitSet, s2::BitSet)
    # Swap so s1 has always the smallest offset
    if s1.offset > s2.offset
        s1, s2 = s2, s1
    end
    a1 = s1.bits
    a2 = s2.bits
    b1, b2 = s1.offset, s2.offset
    l1, l2 = length(a1), length(a2)
    e1 = l1+b1
    overlap0 = max(0, e1 - b2)
    included = overlap0 >= l2  # whether a2's indices are included in a1's
    overlap  = included ? l2 : overlap0

    # Ensure non-overlap chunks are zero (unlikely)
    _check0(a1, 1, l1-overlap0) || return false
    if included
        _check0(a1, b2-b1+l2+1, l1) || return false
    else
        _check0(a2, 1+overlap, l2) || return false
    end

    # compare overlap values
    if overlap > 0
        t1 = @_gc_preserve_begin a1
        t2 = @_gc_preserve_begin a2
        memcmp(pointer(a1, b2-b1+1), pointer(a2), overlap<<3) == 0 || return false
        @_gc_preserve_end t2
        @_gc_preserve_end t1
    end

    return true
end
```
-/
def eq (s1 s2 : BitSet) : Bool :=
  let (s1, s2) := if s1.offset > s2.offset then (s2, s1) else (s1, s2)
  let a1 := s1.bits
  let a2 := s2.bits
  let b1 := s1.offset
  let b2 := s2.offset
  let l1 : Int := a1.length
  let l2 : Int := a2.length
  let e1 := l1 + b1
  let overlap0 := max 0 (e1 - b2)
  let included := overlap0 ≥ l2
  let overlap := if included then l2 else overlap0
  if !check0 a1 1 (l1 - overlap0) then false
  else if (if included then !check0 a1 (b2 - b1 + l2 + 1) l1 else !check0 a2 (1 + overlap) l2) then false
  else if overlap > 0 then memeq a1 (b2 - b1 + 1) a2 overlap
  else true

/--
Julia source: base/bitset.jl:414-414 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    f(a, b) = a == a & b
```
-/
def subChunk (a b : U64) : Bool := a == JuliaLean.base.int.and_int a b

/--
Julia source: base/bitset.jl:409-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function issubset(a::BitSet, b::BitSet)
    n = length(a.bits)
    shift = b.offset - a.offset
    i, j = shift, shift + length(b.bits)

    f(a, b) = a == a & b
    return (
        all(@inbounds iszero(a.bits[i]) for i in 1:min(n, i)) &&
        all(@inbounds f(a.bits[i], b.bits[i - shift]) for i in max(1, i+1):min(n, j)) &&
        all(@inbounds iszero(a.bits[i]) for i in max(1, j+1):n))
end
```
-/
def issubset (a b : BitSet) : Bool :=
  let n : Int := a.bits.length
  let shift := b.offset - a.offset
  let i := shift
  let j := shift + b.bits.length
  let outsideLeft := (intRange 1 (min n i)).all (fun k => bitsGet a.bits k.toNat == zero64)
  let overlap := (intRange (max 1 (i + 1)) (min n j)).all
    (fun k => subChunk (bitsGet a.bits k.toNat) (bitsGet b.bits (k - shift).toNat))
  let outsideRight := (intRange (max 1 (j + 1)) n).all (fun k => bitsGet a.bits k.toNat == zero64)
  outsideLeft && overlap && outsideRight

/--
Julia source: base/bitset.jl:420-420 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
⊊(a::BitSet, b::BitSet) = a <= b && a != b
```
-/
def strictSubset (a b : BitSet) : Bool := issubset a b && !(eq a b)

/--
Julia source: base/bitset.jl:423-423 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
minimum(s::BitSet) = first(s)
```
-/
def minimum (s : BitSet) : Result I64 := first s

/--
Julia source: base/bitset.jl:424-424 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
maximum(s::BitSet) = last(s)
```
-/
def maximum (s : BitSet) : Result I64 := last s

/--
Julia source: base/bitset.jl:425-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
extrema(s::BitSet) = (first(s), last(s))
```
-/
def extrema (s : BitSet) : Result (I64 × I64) := do
  let lo ← first s
  let hi ← last s
  pure (lo, hi)

/--
Julia source: base/bitset.jl:426-426 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
issorted(s::BitSet) = true
```
-/
def issorted (_s : BitSet) : Bool := true
end

end JuliaLean.base.bitset

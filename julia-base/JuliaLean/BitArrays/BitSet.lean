import JuliaLean.BitArrays.Vector

/-!
# `BitSet` (`base/bitset.jl`, master `bbfa0ce4150`)

A `BitSet` stores chunks `bits::Vector{UInt64}` and an `offset`: chunk `c`
(1-based) holds the elements `64*(offset + c - 1) + j` for its set bits `j`.
`offset` is `NO_OFFSET = -2^60` while no element was ever stored.

Elements are `JInt64`. Chunk indices `_div64(n) = n >> 6` are floor divisions
by 64 and lie in `-2^57:2^57`, and offsets in `-2^60:2^57`, so the `Int`
arithmetic on them (`base/bitset.jl:63-111`) never wraps; the model uses `Int`.
-/

namespace JuliaLean.BitArrays

/-- Fields of `BitSet`, `base/bitset.jl:13-23`. -/
structure BitSetS where
  bits : List U64
  offset : Int
  deriving DecidableEq, Repr

/-- `NO_OFFSET`, `base/bitset.jl:5`. -/
def noOffset : Int := -(2 ^ 60)

namespace BitSetS

/-- `BitSet()`, `base/bitset.jl:18-22`. -/
def empty : BitSetS := ⟨[], noOffset⟩

/-- `_bits_getindex(b, n, offset)`, `base/bitset.jl:63-68`, i.e. `n in s`
(`base/bitset.jl:330`). -/
def contains (s : BitSetS) (n : JInt64) : Bool :=
  let ci := n.val / 64 - s.offset + 1
  if 1 ≤ ci ∧ ci ≤ s.bits.length then
    (cget s.bits ci.toNat).getLsbD (n.val % 64).toNat
  else false

/-- `_growend0!(b, k)`, `base/bitset.jl:116-122`. -/
def growend0 (b : List U64) (k : Nat) : List U64 := b ++ List.replicate k 0

/-- `_growbeg0!(b, k)`, `base/bitset.jl:124-129`. -/
def growbeg0 (b : List U64) (k : Nat) : List U64 := List.replicate k 0 ++ b

/-- `_setint!(s, idx, b)`, `base/bitset.jl:87-111`. -/
def setint (s : BitSetS) (idx : JInt64) (b : Bool) : BitSetS :=
  let cidx := idx.val / 64
  let len : Int := s.bits.length
  let diff := cidx - s.offset
  let r : Option (BitSetS × Int) :=
    if diff ≥ len then
      if ¬ b then none else
      let (off, diff) := if s.offset = noOffset then (cidx, (0 : Int)) else (s.offset, diff)
      some (⟨growend0 s.bits (diff - len + 1).toNat, off⟩, diff)
    else if diff < 0 then
      if ¬ b then none else
      some (⟨growbeg0 s.bits (-diff).toNat, s.offset + diff⟩, 0)
    else some (s, diff)
  match r with
  | none => s
  | some (s, diff) => { s with bits := unsafeBitsetAt s.bits b (diff + 1).toNat (idx.val % 64).toNat }

/-- `push!(s, n)`, `base/bitset.jl:255`. -/
def push (s : BitSetS) (n : JInt64) : BitSetS := setint s n true

/-- `delete!(s, n::Int)`, `base/bitset.jl:280`. -/
def delete (s : BitSetS) (n : JInt64) : BitSetS := setint s n false

/-- `BitSet(itr)` for a vector of `Int`s, `base/bitset.jl:33-41`. -/
def ofList (xs : List JInt64) : BitSetS := xs.foldl push empty

/-- `int_symdiff!(s, n)`, `base/bitset.jl:319-324`. -/
def intSymdiff (s : BitSetS) (n : JInt64) : BitSetS := setint s n (!(s.contains n))

/-- `symdiff!(s::BitSet, ns)` for a non-`AbstractSet` iterable `ns`,
`base/bitset.jl:305-310`. -/
def symdiff (s : BitSetS) (ns : List JInt64) : BitSetS := ns.foldl intSymdiff s

end BitSetS

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

import JuliaLean.AbstractArrays.Model
import JuliaLean.Dicts.ProofLookup
import JuliaLean.Dicts.ProofInsert
import JuliaLean.Show.Unicode

/-!
Bounds-obligation models for the unchecked accesses in `memsafety/sites-3.tsv`.

The models use zero-based offsets for pointer arithmetic and Julia's one-based
indices for arrays. External C storage is represented by its documented extent.
-/

namespace JuliaLean.MemSafety.G3

open JuliaLean

/-- Membership in an axis of `len` elements beginning at `first`. -/
def inAxis (first : Int) (len : Nat) (i : Int) : Prop :=
  first ≤ i ∧ i < first + len

/-- Membership in a one-based array of length `len`. -/
def inOneBased (len i : Nat) : Prop := 1 ≤ i ∧ i ≤ len

/-- The zero-based column-major offset used by `hvncat_calcindex`,
`base/abstractarray.jl:2865-2873`. -/
def linearOffset : List Nat → List Nat → Nat
  | [], [] => 0
  | d :: ds, c :: cs => c + d * linearOffset ds cs
  | _, _ => 0

/-- Every coordinate is below the corresponding dimension. -/
def coordsValid : List Nat → List Nat → Prop
  | [], [] => True
  | d :: ds, c :: cs => c < d ∧ coordsValid ds cs
  | _, _ => False

/-- Generic copy loops in `base/abstractarray.jl:953-1176`. The destination
block and the source block use their respective axes. -/
def AbstractArrayCopySafe : Prop :=
  ∀ (destFirst srcFirst : Int) (destLen srcLen start count k : Nat),
    start + count ≤ destLen → count ≤ srcLen → k < count →
      inAxis destFirst destLen (destFirst + start + k) ∧
      inAxis srcFirst srcLen (srcFirst + k)

/-- Concatenation fills in `base/abstractarray.jl:2253-2863`. The count checks
make the linear loops spans of the destination. The computed multidimensional
index is `linearOffset + 1`. -/
def AbstractArrayConcatSafe : Prop :=
  ∀ (dims coords : List Nat), coordsValid dims coords →
    inOneBased dims.prod (linearOffset dims coords + 1)

/-- `stack`, `map!`, `map_n!`, and `_keepat!` in
`base/abstractarray.jl:3075-3086,3482-3559,3699-3728`. Source positions come
from an axis and the compaction destination never passes the source position. -/
def AbstractArrayIterationSafe : Prop :=
  ∀ (first : Int) (len sourceOffset destOffset : Nat),
    sourceOffset < len → destOffset ≤ sourceOffset →
      inAxis first len (first + sourceOffset) ∧
      inAxis first len (first + destOffset)

/-- The `1:length(x)` memory-reference loop in
`base/deepcopy.jl:108-127`. -/
def DeepcopyMemorySafe : Prop :=
  ∀ (len i : Nat), 1 ≤ i → i ≤ len → inOneBased len i

/-- Probe arithmetic shared by Dict lookup, insertion, deletion, iteration,
and rehashing in `base/dict.jl:140-770`. -/
def DictProbeSafe : Prop :=
  ∀ (size index : Nat) (hash : JInt .u64), Dicts.IsPow size → size ≤ 2 ^ 62 →
    1 ≤ index → index ≤ size →
      inOneBased size (Dicts.hashindex hash size).1 ∧
      inOneBased size (Dicts.nextIdx size index) ∧
      inOneBased size (Dicts.prevIdx size index)

/-- Number of set bits below `n`, matching the mask and `count_ones` in
`HAMT.entry_index`, `base/hamt.jl:138-141`. -/
def bitCountPrefix (bitmap : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bitCountPrefix bitmap n + if bitmap.testBit n then 1 else 0

/-- `HAMT.path` reads the entry whose zero-based position is the count of set
bits below `bi`. The representation invariant says the data length is the
number of set bits in the 32-bit bitmap. -/
def PersistentDictPathSafe : Prop :=
  ∀ (bitmap dataLength bi : Nat), bi < 32 → bitmap.testBit bi = true →
    dataLength = bitCountPrefix bitmap 32 →
      inOneBased dataLength (bitCountPrefix bitmap bi + 1)

/-- A C string-vector or wide-character block is accessed only before its
terminator, `base/env.jl:193-245`. -/
def EnvironmentBufferSafe : Prop :=
  ∀ (storageLength position payloadLength : Nat),
    position < storageLength → payloadLength ≤ storageLength - position →
      position < storageLength ∧ position + payloadLength ≤ storageLength

/-- Four-byte and scalar digit stores used by `bin`, `oct`, `dec`, `hex`,
`_base`, and `bitstring`, `base/intfuncs.jl:878-1165`. -/
def FormattingStoresSafe : Prop :=
  ∀ (bufferLength i : Nat), i ≤ bufferLength →
    (4 ≤ i →
      inOneBased bufferLength (i - 3) ∧ inOneBased bufferLength (i - 2) ∧
      inOneBased bufferLength (i - 1) ∧ inOneBased bufferLength i) ∧
    (1 ≤ i → inOneBased bufferLength i)

/-- The store obligations plus the 100-entry decimal-pair table and the
62-entry largest base alphabet. -/
def IntegerFormattingSafe : Prop :=
  FormattingStoresSafe ∧
  (∀ c : Nat, c < 100 → inOneBased 100 (c + 1)) ∧
  (∀ d : Nat, d < 62 → inOneBased 62 (d + 1))

/-- The fixed 8192-byte buffer used by `countlines`, plus the four-byte
endianness probe, `base/io.jl:817-834,1700-1714`. -/
def IOSafe : Prop :=
  ∀ (bufferLength bytesRead i : Nat), bytesRead ≤ bufferLength →
    1 ≤ i → i ≤ bytesRead → inOneBased bufferLength i

/-- A Symbol points to at least its terminating byte,
`base/module.jl:67-75`. -/
def ModuleSymbolSafe : Prop :=
  ∀ storageLength : Nat, 1 ≤ storageLength → inOneBased storageLength 1

/-- Guarded byte accesses in the integer parser,
`base/parse.jl:68-147`. -/
def IntegerParseSafe : Prop :=
  ∀ (length i j : Nat), 1 ≤ i → i ≤ j → j ≤ length →
    inOneBased length i ∧ inOneBased length j ∧
      (i < j → inOneBased length (i + 1))

/-- Guarded scalar and eight-byte reads in the floating parser,
`base/parsers/floats.jl:171-419`. -/
def GuardedFloatParseSafe : Prop :=
  ∀ (length i j : Nat), 1 ≤ i → i ≤ j → j ≤ length →
    inOneBased length i ∧ inOneBased length j ∧
      (7 ≤ j - i → i + 7 ≤ length)

/-- The Clinger-table index selected after `abs(q) < length(p10)`,
`base/parsers/floats.jl:143-150`. -/
def exactPow10Index (q : Int) : Nat :=
  if q < 0 then q.natAbs + 1 else q.toNat + 1

/-- Parser span checks, the 651-entry `POW5[-342:308]` table, and exact-power
table selection. -/
def FloatParseSafe : Prop :=
  GuardedFloatParseSafe ∧
  (∀ q : Int, -342 ≤ q → q ≤ 308 → 1 ≤ q + 343 ∧ q + 343 ≤ 651) ∧
  (∀ (q : Int) (tableLength : Nat), q.natAbs < tableLength →
    inOneBased tableLength (exactPow10Index q))

/-- C-returned spans in `homedir` and `_win_profile_from_registry`,
`base/path.jl:708-754,781-807`. -/
def PathBufferSafe : Prop :=
  ∀ (storageLength offset width : Nat), offset + width ≤ storageLength →
    offset ≤ storageLength ∧ offset + width ≤ storageLength

/-- PCRE's name table stores two index bytes followed by the name in every
fixed-size entry. The context vector grows by at least `maxthreadid()` when
the current thread id does not fit, `base/pcre.jl:37-63,265-280`. -/
def PcreNameTableSafe : Prop :=
  ∀ (count entrySize entry currentLength threadId maxThreadId : Nat),
    2 ≤ entrySize → entry < count → 1 ≤ threadId → threadId ≤ maxThreadId →
    let offset := entry * entrySize
    offset < count * entrySize ∧ offset + 1 < count * entrySize ∧
      threadId ≤ (if currentLength < threadId then currentLength + maxThreadId else currentLength)

/-- Linear short-array reduction and the word-at-a-time Bool counter,
`base/reduce.jl:436-455,1097-1112`. -/
def ReduceSafe : Prop :=
  ∀ (length wordSize word index : Nat), 0 < wordSize → word < length / wordSize →
    1 ≤ index → index ≤ length →
      (word + 1) * wordSize ≤ length ∧ inOneBased length index

/-- Character and substring positions used by trimming, truncation, and
splitting in `base/strings/util.jl:268-806`. -/
def StringPositionSafe : Prop :=
  ∀ (codeunits position : Nat), position < codeunits →
    inOneBased codeunits (position + 1)

/-- `hex2bytes!`, `bytes2hex`, and `ascii` loops,
`base/strings/util.jl:1260-1341`. -/
def StringHexSafe : Prop :=
  ∀ (length i : Nat), 1 ≤ i → i ≤ length →
    inOneBased (2 * length) (2 * i - 1) ∧
    inOneBased (2 * length) (2 * i) ∧
    inOneBased length i

/-- The table access in `category_string(::Char)`,
`base/strings/unicode.jl:398-403`. -/
def UnicodeCategorySafe : Prop :=
  ∀ code : Nat, code ≤ 31 → inOneBased 32 (code + 1)

/-- C global arrays used by GC timing accessors,
`base/timing.jl:148-184`. -/
def TimingGlobalsSafe : Prop :=
  ∀ (globalLength exposedLength i : Nat), exposedLength ≤ globalLength →
    1 ≤ i → i ≤ exposedLength → inOneBased globalLength i

end JuliaLean.MemSafety.G3

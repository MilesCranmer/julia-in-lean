import JuliaLean.AbstractArrays
import JuliaLean.ArrayOps
import JuliaLean.BigNums
import JuliaLean.MathFuncs
import JuliaLean.Multidim
import JuliaLean.ReinterpretArrays

/-!
Bounds-obligation models for group 2 of `memsafety/sites-2.tsv`, against Julia
master `bbfa0ce4150`. Indices below are zero-based ordinals unless a definition
explicitly uses Julia's one-based indexing. Offset axes reduce to the same
ordinals because their wrapped additions and subtractions cancel modulo `Int`.
-/

namespace JuliaLean.MemSafety.G2

/-- The two ordinals accessed by `_reverse!` for loop ordinal `k`,
`base/arraymath.jl:107-130`. -/
def reverseOrdinals (n k : Nat) : Nat × Nat := (k, n - 1 - k)

def ReverseInBounds : Prop :=
  ∀ n k : Nat, k < n / 2 →
    (reverseOrdinals n k).1 < n ∧ (reverseOrdinals n k).2 < n

/-- `Const` multidimensional indexing uses the shared checked linear/Cartesian
conversion from `base/experimental.jl:32-40`. -/
def ConstGetindexInBounds : Prop := JuliaLean.AbstractArrays.LinearCartesianRoundTrip

/-- `1:n`, `eachindex`, an array's axes, and `CartesianIndices` enumerate only
positions in the collection they came from. This is the common obligation at
`base/expr.jl:45-79`, `base/missing.jl:252-256`,
`base/multidimensional.jl:631-640,1768-1800`. -/
def EnumeratedInBounds : Prop := ∀ n k : Nat, k ∈ List.range n → k < n

def ExprCopyInBounds : Prop := EnumeratedInBounds

/-- Readable limb capacity. GMP keeps one readable zero limb even when `_mp_size`
is zero; otherwise `abs(_mp_size) ≤ _mp_alloc` (`base/gmp.jl:68-72`). -/
def readableLimbs (allocated : Nat) : Nat := max 1 allocated

/-- The limb containing zero-based byte `start + offset`, as used by
`UnsafeLimbView.getindex`, `base/gmp.jl:873-915`. -/
def byteLimb (start offset : Nat) : Nat := (start + offset) / 8

/-- All direct BigInt limb reads, the constructor stores, hash's trailing-bit
window, and the byte view made by the two hash callers remain within the GMP
allocation (`base/gmp.jl:347-378,409-465,608-622,873-955`). -/
def GmpLimbAccessesInBounds : Prop :=
  (∀ allocated used i : Nat, used ≤ allocated → 1 ≤ i → i ≤ used → i ≤ readableLimbs allocated) ∧
  (∀ allocated : Nat, 1 ≤ readableLimbs allocated) ∧
  (∀ used pow : Nat, 0 < used → pow < 64 * used → pow / 64 + 1 ≤ used) ∧
  (∀ used start count offset : Nat, start + count ≤ 8 * used → offset < count →
    byteLimb start offset < used)

/-- `string(::BigInt)` allocates `nd + isnegative(n)` bytes before storing the
minus sign at byte one, `base/gmp.jl:765-781`. -/
def GmpStringSignInBounds : Prop :=
  ∀ nd : Nat, 0 < nd → 1 ≤ nd + 1

/-- All array overload calls to `load_le_array` in `hash_bytes` provide a
complete 4- or 8-byte window. The variables `pos` and `i` describe the state
after the 48-byte loop, where `n = pos + i`, `1 ≤ i ≤ 48`;
`base/hashing.jl:378-466`. -/
def HashArrayInBounds : Prop :=
  (∀ n : Nat, 8 ≤ n → n ≤ 16 → 8 ≤ n ∧ (n - 8) + 8 ≤ n) ∧
  (∀ n : Nat, 4 ≤ n → n < 8 → 4 ≤ n ∧ (n - 4) + 4 ≤ n) ∧
  (∀ n : Nat, 0 < n → n < 4 → 0 < n ∧ n - 1 < n ∧ n / 2 < n) ∧
  (∀ n pos : Nat, pos + 48 ≤ n →
    pos + 8 ≤ n ∧ pos + 16 ≤ n ∧ pos + 24 ≤ n ∧
    pos + 32 ≤ n ∧ pos + 40 ≤ n ∧ pos + 48 ≤ n) ∧
  (∀ n pos i : Nat, n = pos + i → 1 ≤ i → i ≤ 48 →
    (16 < i → pos + 16 ≤ n) ∧ (32 < i → pos + 32 ≤ n)) ∧
  (∀ n : Nat, 16 < n → (n - 16) + 8 ≤ n ∧ (n - 8) + 8 ≤ n)

/-- After `checkbounds(iter, i)`, the range index passed to the selected
underlying one-dimensional range has in-bounds endpoints,
`base/indices.jl:509-518`. -/
def LinearIndicesRangeInBounds : Prop := JuliaLean.AbstractArrays.CheckIndexForms

/-- The macOS `getattrlist` header load reads bytes 9 through 12 of a buffer
whose allocation is `basename length + 13`, `base/loading.jl:46-64`. -/
def LoadingHeaderInBounds : Prop := ∀ basenameLength : Nat, 12 ≤ basenameLength + 13

/-- The sequential and pairwise SkipMissing loops receive endpoints within the
same linear-index axis, `base/missing.jl:275-351`. -/
def MissingMapreduceInBounds : Prop :=
  ∀ n first last i : Nat, first ≤ i → i ≤ last → last < n → i < n

/-- Checked `CartesianIndices.getindex` delegates coordinate `I[d]` to range
`d`; the established Cartesian bounds model is reused for
`base/multidimensional.jl:400-419`. -/
def CartesianGetindexInBounds : Prop := JuliaLean.AbstractArrays.CheckboundsCartesian

/-- Cartesian collection enumerates the destination count, while partition
splitting uses the verified ReshapedArray subscript conversion,
`base/multidimensional.jl:631-704`. -/
def CartesianIterationInBounds : Prop :=
  EnumeratedInBounds ∧ JuliaLean.ReinterpretArrays.Ind2subCorrect

/-- For a well-formed BitArray, the number of true bits is at most 64 times
the number of chunks. The initial chunk and each increment in LogicalIndex
iteration are therefore in bounds, `base/multidimensional.jl:873-896`. -/
def LogicalIndexInBounds : Prop :=
  (∀ chunks sum : Nat, 0 < sum → sum ≤ 64 * chunks → 0 < chunks) ∧
  (∀ chunks current : Nat, current < chunks → current + 1 ≤ chunks)

/-- Generic indexed getindex/setindex allocate or shape-check a collection with
exactly the loop's number of values, `base/multidimensional.jl:995-1079`. -/
def MatchedIterationInBounds : Prop :=
  ∀ sourceCount destCount k : Nat, sourceCount = destCount → k < sourceCount → k < destCount

/-- `diff(r)` reads `i` and `i+1` while `i < length(r)`, and Cartesian block
copy maps equal-size source and destination ordinals,
`base/multidimensional.jl:1113-1126,1190-1215`. -/
def DiffAndBlockCopyInBounds : Prop :=
  (∀ n i : Nat, i + 1 < n → i < n ∧ i + 1 < n) ∧
  (∀ sourceCount destCount k : Nat, sourceCount = destCount → k < sourceCount → k < destCount)

/-- The BitArray copy helpers address the same `numbits` interval in source and
destination after public setindex has checked both ranges and their shapes,
`base/multidimensional.jl:1419-1615`. -/
def BitCopyInBounds : Prop :=
  ∀ destBits sourceCount destStart sourceStart count k : Nat,
    destStart + count ≤ destBits → sourceStart + count ≤ sourceCount → k < count →
    destStart + k < destBits ∧ sourceStart + k < sourceCount

def IsassignedInBounds : Prop := JuliaLean.AbstractArrays.IsassignedSpec

/-- ReshapedArray's checked indices are converted to verified in-bounds parent
subscripts by the shared `ind2sub_rs` model, `base/reshapedarray.jl:270-339`. -/
def ReshapedIndexingInBounds : Prop := JuliaLean.ReinterpretArrays.Ind2subCorrect

/-- Decimal exponents emitted for IEEE binary16/32/64 are at most 324 in
absolute value. The two `DIGIT_TABLE16` lookups use one of these indices;
`base/ryu/shortest.jl:425-447`. -/
def RyuExponentTableInBounds : Prop :=
  ∀ exp : Nat, exp ≤ 324 →
    (100 ≤ exp → exp / 10 + 1 ≤ 100) ∧
    (10 ≤ exp → exp < 100 → exp + 1 ≤ 100)

/-- One-based `INV_2PI` positions evaluated by `paynehanek` from the raw
binary64 exponent, mirroring `base/special/rem_pio2.jl:130-178`. The source
skips `idx+1` when `idx < 0` in the shifted branch. -/
def payneHanekTableIndices (rawExponent : Nat) : List Int :=
  let k : Int := rawExponent - 1023 - 52
  let idx := k / 64
  let shift := k - idx * 64
  if shift = 0 then [idx + 1, idx + 2, idx + 3]
  else (if idx < 0 then [] else [idx + 1]) ++ [idx + 2, idx + 3, idx + 4]

def PayneHanekTableInBounds : Prop :=
  ∀ rawExponent : Nat, rawExponent ≤ 2047 →
    ∀ i ∈ payneHanekTableIndices rawExponent, 1 ≤ i ∧ i ≤ 19

/-- After the range check and UTF-8 boundary checks, StringView slicing stays
inside its code units. `chomp` removes at most the available one or two final
bytes, `base/strings/stringview.jl:126-150`. -/
def StringViewInBounds : Prop :=
  (∀ n i j next : Nat, 1 ≤ i → i ≤ j → j < next → next ≤ n + 1 →
    i ≤ n ∧ next - 1 ≤ n) ∧
  (∀ n removed : Nat, removed ≤ n → n - removed ≤ n)

/-- In `summarysize`, `i` ranges over `length(x)*np` inline pointer fields, so
`(i-1)/np+1` is an element of `x`; the non-inline branch uses `i` directly,
`base/summarysize.jl:45-116`. Zero-based form. -/
def SummarySizeInBounds : Prop :=
  (∀ n np i : Nat, 0 < np → i < n * np → i / np < n) ∧
  (∀ n i : Nat, i < n → i < n)

end JuliaLean.MemSafety.G2

import JuliaLean.AbstractArrays
import JuliaLean.BigNums
import JuliaLean.Float
import JuliaLean.ParsePrint.Ryu
import JuliaLean.ReinterpretArrays

/-!
Source-level bounds models for the unchecked accesses in
`memsafety/sites-2.tsv`, against Julia master `bbfa0ce4150`.

Every trace below starts from the enclosing Julia function's arguments and
executes the checks, branches, loop bounds, and index arithmetic that lead to
the attributed access. An `Access` records the one-based index and the length
of the storage selected by that source path.
-/

namespace JuliaLean.MemSafety.G2

open JuliaLean
open JuliaLean.AbstractArrays

structure Access where
  len : Nat
  index : Int
  deriving DecidableEq, Repr

def Access.inBounds (a : Access) : Prop := 1 ≤ a.index ∧ a.index ≤ a.len

def AllInBounds (xs : List Access) : Prop := ∀ a ∈ xs, a.inBounds

def oneBased (n : Nat) : List Int :=
  (List.range n).map fun (k : Nat) => (k : Int) + 1

def axisValues (a : Axis) : List Int :=
  (List.range a.len).map fun (k : Nat) => a.first.val + k

def product (ns : List Nat) : Nat := ns.foldr (· * ·) 1

/-! ## `base/arraymath.jl:107-130`: `_reverse!` -/

def validReverseDims (rank : Nat) (dims : List Nat) : Bool :=
  !dims.isEmpty && dims.length ≤ rank &&
    (List.range rank).countP (fun k => dims.contains (k + 1)) == dims.length

def reverseAxisPass (a : Axis) (reverse leading : Bool) : List Access :=
  let count := if leading then a.len / 2 else a.len
  (List.range count).flatMap fun (k : Nat) =>
    let original : Int := (k : Int) + 1
    let reflected : Int := if reverse then (a.len : Int) - k else original
    [⟨a.len, original⟩, ⟨a.len, reflected⟩]

def middleViewAxes (axes : List Axis) (leadingDim : Nat) : List Axis :=
  axes.zipIdx.map fun (a, k) => Axis.oneTo (if k + 1 == leadingDim then 1 else a.len)

def reverseAccessesFuel : Nat → List Axis → List Nat → List Access
  | 0, _, _ => []
  | fuel + 1, axes, dims =>
      if h : validReverseDims axes.length dims then
        let leading := dims.headD 0
        let here := axes.zipIdx.flatMap fun (a, k) =>
          reverseAxisPass a (dims.contains (k + 1)) (k + 1 == leading)
        if dims.length > 1 &&
            ((axes.getD (leading - 1) (Axis.oneTo 0)).len % 2 == 1) then
          here ++ reverseAccessesFuel fuel (middleViewAxes axes leading) dims.tail
        else here
      else []

def reverseAccesses (axes : List Axis) (dims : List Nat) : List Access :=
  reverseAccessesFuel dims.length axes dims

def ReverseInBounds : Prop := ∀ axes dims, AllInBounds (reverseAccesses axes dims)

/-! ## `base/experimental.jl:32-40`: `Experimental.Const.getindex` -/

def arrayAxes (dims : List Nat) : List Axis := dims.map Axis.oneTo

def normalizeDims (dims : List Nat) (n : Nat) : List Nat :=
  dims ++ List.replicate (n - dims.length) 1

def normalizeCoords (coords : List Int) (n : Nat) : List Int :=
  coords ++ List.replicate (n - coords.length) 1

def coordsCheck (dims : List Nat) (coords : List Int) : Bool :=
  let n := max dims.length coords.length
  let ds := normalizeDims dims n
  let is := normalizeCoords coords n
  (ds.zip is).all fun (d, i) => decide (1 ≤ i ∧ i ≤ d)

def sub2ind : List Nat → List Int → Int
  | [], _ => 1
  | _, [] => 1
  | [_], [i] => i
  | n :: ns, i :: is => i + n * (sub2ind ns is - 1)

def constLinearAccess (dims : List Nat) (i : Int) : List Access :=
  let n := product dims
  if 1 ≤ i && i ≤ n then [⟨n, i⟩] else []

def constCartesianAccess (dims : List Nat) (coords : List Int) : List Access :=
  let n := max dims.length coords.length
  let ds := normalizeDims dims n
  let is := normalizeCoords coords n
  if coordsCheck dims coords then
    [⟨product ds, sub2ind ds is⟩]
  else []

def ConstGetindexInBounds : Prop :=
  (∀ dims i, AllInBounds (constLinearAccess dims i)) ∧
  (∀ dims coords, AllInBounds (constCartesianAccess dims coords))

/-! ## `base/expr.jl:45-79`: expression copies -/

def exprCopyAccesses (values : List Bool) : List Access :=
  let nvalues := values.length
  let newValuesLength := nvalues
  (oneBased nvalues).flatMap fun i =>
    ⟨nvalues, i⟩ :: if values.getD (i.toNat - 1) false then
      [⟨nvalues, i⟩, ⟨newValuesLength, i⟩]
    else []

def exprArgsAccesses (values : List Bool) : List Access :=
  (oneBased values.length).map fun i => ⟨values.length, i⟩

def ExprCopyInBounds : Prop := ∀ values,
  AllInBounds (exprCopyAccesses values) ∧ AllInBounds (exprArgsAccesses values)

/-! ## `base/gmp.jl`: BigInt limb and string accesses -/

inductive BigStorage where
  | owned (value : Int)
  | globalZero
  deriving DecidableEq, Repr

def BigStorage.used : BigStorage → Nat
  | .owned x => JuliaLean.BigNums.nlimbs x
  | .globalZero => 0

def BigStorage.capacity : BigStorage → Nat
  | .owned x => max 1 (JuliaLean.BigNums.nlimbs x)
  | .globalZero => 0

/-- Eager `&` evaluates the limb load even for zero. -/
def gmpBoolRemAccess (x : BigStorage) : List Access := [⟨x.capacity, 1⟩]

def GmpBoolRemInBounds : Prop := ∀ x, AllInBounds (gmpBoolRemAccess x)

structure IntegerInput where
  value : Int
  isBits : Bool
  deriving DecidableEq, Repr

def gmpConstructorAccesses (x : IntegerInput) : List Access :=
  if x.isBits && -(2^63 : Int) ≤ x.value && x.value ≤ (2^63 : Int) - 1 then []
  else (oneBased (JuliaLean.BigNums.nlimbs x.value)).map fun i =>
    ⟨JuliaLean.BigNums.nlimbs x.value, i⟩

def gmpRemainderAccesses (x : Int) (words : Nat) : List Access :=
  let used := JuliaLean.BigNums.nlimbs x
  let small := if x = 0 then [] else [⟨used, 1⟩]
  let wide := (oneBased (min used words)).map fun i => ⟨used, i⟩
  small ++ wide

def scanNonzeroLimbs (x : Int) : Nat → List Int
  | 0 => []
  | i + 1 =>
      (i + 1 : Int) ::
        if JuliaLean.BigNums.limb x i = 0 then scanNonzeroLimbs x i else []

def gmpFloatAccesses (x : Int) : List Access :=
  let used := JuliaLean.BigNums.nlimbs x
  if used = 0 then [] else
    let top := JuliaLean.BigNums.limb x (used - 1)
    let filled := top.log2 + 1
    let rest := if 1 < used && filled < 64 then scanNonzeroLimbs x (used - 1) else []
    ((used : Int) :: rest).map fun i => ⟨used, i⟩

def GmpLimbAccessesInBounds : Prop :=
  (∀ x, AllInBounds (gmpConstructorAccesses x)) ∧
  (∀ x words, AllInBounds (gmpRemainderAccesses x words)) ∧
  (∀ x, AllInBounds (gmpFloatAccesses x))

def gmpBitMagnitudeAccess (x : Int) : List Access :=
  if x = 0 then [] else
    let used := JuliaLean.BigNums.nlimbs x
    [⟨used, used⟩]

def GmpBitMagnitudeInBounds : Prop := ∀ x, AllInBounds (gmpBitMagnitudeAccess x)

def gmpStringSignAccess (n base pad : Int) : List Access :=
  if base < 0 || base < 2 || 62 < base || (n = 0 && pad < 1) then [] else
    let nd1 := (JuliaLean.BigNums.digitChars n base.toNat).length
    let nd := max nd1 pad.toNat
    if n < 0 then [⟨nd + 1, 1⟩] else []

def GmpStringSignInBounds : Prop := ∀ n base pad,
  AllInBounds (gmpStringSignAccess n base pad)

/-! ## `base/hashing.jl:378-466`: array hash windows -/

def window (start width : Nat) : List Nat :=
  (List.range width).map (start + ·)

def hashLoop : Nat → Nat → List Nat
  | i, pos =>
      if h : 48 < i then
        window pos 48 ++ hashLoop (i - 48) (pos + 48)
      else
        (if 16 < i then window pos 16 else []) ++
        (if 32 < i then window (pos + 16) 16 else [])
termination_by i pos => i
decreasing_by omega

def hashByteOffsets (n : Nat) : List Nat :=
  if n ≤ 16 then
    if 8 ≤ n then window 0 8 ++ window (n - 8) 8
    else if 4 ≤ n then window 0 4 ++ window (n - 4) 4
    else if 0 < n then [0, n - 1, n / 2]
    else []
  else hashLoop n 0 ++ window (n - 16) 8 ++ window (n - 8) 8

def hashArrayAccesses (a : Axis) : List Access :=
  (hashByteOffsets a.len).map fun (k : Nat) => ⟨a.len, (k : Int) + 1⟩

def HashArrayInBounds : Prop := ∀ a, AllInBounds (hashArrayAccesses a)

/-! `base/gmp.jl:873-955`: the two BigInt hash paths and their
`UnsafeLimbView`. `limbs` is the GMP little-endian limb storage; each value is
reduced to the 64-bit `Limb` width before bit and byte selection. -/

def limbBit (limbs : List Nat) (bit : Nat) : Bool :=
  let limb := (limbs.getD (bit / 64) 0) % 2^64
  decide (limb / 2^(bit % 64) % 2 = 1)

def firstNonzeroBit (limbs : List Nat) : Nat :=
  (List.range (64 * limbs.length)).findIdx? (limbBit limbs) |>.getD (64 * limbs.length)

def leadingZeroBytes (limbs : List Nat) : Nat :=
  if limbs.isEmpty then 0 else
    let top := (limbs.getLastD 0) % 2^64
    if top = 0 then 8 else (63 - top.log2) / 8

def viewLimbAccesses (limbs : List Nat) (startByte count : Nat) : List Access :=
  (hashByteOffsets count).map fun (byte : Nat) =>
    ⟨limbs.length, (((startByte + byte - 1) / 8 + 1 : Nat) : Int)⟩

def gmpHashIntegerAccesses (limbs : List Nat) : List Access :=
  if limbs.isEmpty then [] else
    let used := limbs.length
    let count := 8 * used - leadingZeroBytes limbs
    ⟨used, used⟩ :: viewLimbAccesses limbs 1 count

def gmpHashAccesses (limbs : List Nat) : List Access :=
  if limbs.isEmpty then [] else
    let used := limbs.length
    if used = 1 then [⟨used, 1⟩] else
      let pow := firstNonzeroBit limbs
      if pow = 64 * used then [] else
        let idx := pow / 64 + 1
        let shift := pow % 64
        let direct := if shift = 0 then [⟨used, idx⟩]
          else [⟨used, idx⟩] ++ if idx < used then [⟨used, idx + 1⟩] else []
        let trailingBytes := pow / 8
        let count := 8 * used - (leadingZeroBytes limbs + trailingBytes)
        direct ++ [⟨used, used⟩] ++ viewLimbAccesses limbs (trailingBytes + 1) count

def GmpHashInBounds : Prop :=
  (∀ limbs, AllInBounds (gmpHashIntegerAccesses limbs)) ∧
  (∀ limbs, AllInBounds (gmpHashAccesses limbs))

/-! ## `base/loading.jl:46-65`: macOS `getattrlist` header -/

def headerAccess (n : Nat) : List Access :=
  [⟨n, 9⟩, ⟨n, 10⟩, ⟨n, 11⟩, ⟨n, 12⟩]

def loadingHeaderAccess (basenameLength returnedLength : Nat) : List Access :=
  let initial := basenameLength + 12 + 1
  headerAccess initial ++
    if initial < returnedLength + 12 then headerAccess (returnedLength + 12) else []

def LoadingHeaderInBounds : Prop := ∀ basenameLength returnedLength,
  AllInBounds (loadingHeaderAccess basenameLength returnedLength)

/-! ## `base/missing.jl`: `SkipMissing` enumerators and mapreduce -/

def skipMissingEachindexAccesses (first : I64) (missing : List Bool) : List Access :=
  (axisValues ⟨first, missing.length⟩).map fun i =>
    ⟨missing.length, i - first.val + 1⟩

def SkipMissingEachindexInBounds : Prop := ∀ first missing,
  AllInBounds (skipMissingEachindexAccesses first missing)

def cartesianCoords : List Nat → List (List Int)
  | [] => [[]]
  | n :: ns =>
      (oneBased n).flatMap fun i => (cartesianCoords ns).map fun is => i :: is

def cartesianAxisCoords : List Axis → List (List Int)
  | [] => [[]]
  | a :: axes =>
      (axisValues a).flatMap fun i => (cartesianAxisCoords axes).map fun is => i :: is

def relativeCoords : List Axis → List Int → List Int
  | [], [] => []
  | axes, [] => List.replicate axes.length 1
  | [], i :: is => i :: relativeCoords [] is
  | a :: axes, i :: is => (i - a.first.val + 1) :: relativeCoords axes is

def constCartesianAccessAxes (axes : List Axis) (coords : List Int) : List Access :=
  constCartesianAccess (axes.map (·.len)) (relativeCoords axes coords)

def skipMissingKeysAccesses (axes : List Axis) : List Access :=
  (cartesianAxisCoords axes).flatMap (constCartesianAccessAxes axes)

def SkipMissingKeysInBounds : Prop := ∀ axes,
  AllInBounds (skipMissingKeysAccesses axes)

structure Scan where
  visited : List Nat
  found : Option Nat
  deriving DecidableEq, Repr

def scanMissing (missing : List Bool) (start count : Nat) : Scan :=
  let offsets := List.range (min count (missing.length - start))
  match offsets.findIdx? (fun off => !missing.getD (start + off) true) with
  | some off => ⟨(List.range (off + 1)).map (start + ·), some (start + off)⟩
  | none => ⟨offsets.map (start + ·), none⟩

def indexValue (first : I64) (ordinal : Nat) : I64 := first + i64 ordinal

def sequentialMapreduceTrace (first : I64) (missing : List Bool)
    (start count : Nat) : List Nat :=
  match (scanMissing missing start count).found with
  | none => (scanMissing missing start count).visited
  | some p =>
      if (indexValue first p).val = IntTy.max .i64 then
        (scanMissing missing start count).visited
      else match (scanMissing missing (p + 1) (start + count - (p + 1))).found with
      | none => (scanMissing missing start count).visited ++
          (scanMissing missing (p + 1) (start + count - (p + 1))).visited
      | some q =>
          if (indexValue first q).val = IntTy.max .i64 then
            (scanMissing missing start count).visited ++
              (scanMissing missing (p + 1) (start + count - (p + 1))).visited
          else
            (scanMissing missing start count).visited ++
              (scanMissing missing (p + 1) (start + count - (p + 1))).visited ++
              (List.range (start + count - (q + 1))).map (q + 1 + ·)

def mapreduceImplTrace : Nat → I64 → List Bool → Nat → Nat → Nat → List Nat
  | 0, _, _, _, _, _ => []
  | fuel + 1, first, missing, start, count, blockSize =>
      if count = 0 then []
      else if count = 1 then [start]
      else if count - 1 < blockSize then
        sequentialMapreduceTrace first missing start count
      else
        let leftCount := (count - 1) / 2 + 1
        mapreduceImplTrace fuel first missing start leftCount blockSize ++
          mapreduceImplTrace fuel first missing (start + leftCount) (count - leftCount) blockSize

def mapreduceOrdinals (first : I64) (missing : List Bool) (blockSize : Nat) : List Nat :=
  match (scanMissing missing 0 missing.length).found with
  | none => (scanMissing missing 0 missing.length).visited
  | some p =>
      if (indexValue first p).val = IntTy.max .i64 then
        (scanMissing missing 0 missing.length).visited
      else match (scanMissing missing (p + 1) (missing.length - (p + 1))).found with
      | none => (scanMissing missing 0 missing.length).visited ++
          (scanMissing missing (p + 1) (missing.length - (p + 1))).visited
      | some _ => (scanMissing missing 0 missing.length).visited ++
          (scanMissing missing (p + 1) (missing.length - (p + 1))).visited ++
          mapreduceImplTrace missing.length first missing 0 missing.length blockSize

def mapreduceBlockAccesses (first : I64) (missing : List Bool) (blockSize : Nat) : List Access :=
  (mapreduceOrdinals first missing blockSize).map fun (k : Nat) =>
    ⟨missing.length, (k : Int) + 1⟩

def MissingMapreduceInBounds : Prop := ∀ first missing blockSize,
  AllInBounds (mapreduceBlockAccesses first missing blockSize)

/-! ## `base/multidimensional.jl` -/

def cartesianCollectAccesses (axes : List Axis) : List Access :=
  let n := product (axes.map (·.len))
  (oneBased n).map fun i => ⟨n, i⟩

def CartesianCollectInBounds : Prop := ∀ axes,
  AllInBounds (cartesianCollectAccesses axes)

def bitChunkCount (bits : List Bool) : Nat := (bits.length + 63) / 64

def chunkHasTrue (bits : List Bool) (chunk : Nat) : Bool :=
  ((bits.drop (chunk * 64)).take 64).any id

def logicalChunkScan (bits : List Bool) : Nat → Nat → List Access
  | 0, _ => []
  | fuel + 1, chunk =>
      if h : chunk < bitChunkCount bits then
        let here := ⟨bitChunkCount bits, (chunk : Int) + 1⟩
        if chunkHasTrue bits chunk then [here]
        else here :: logicalChunkScan bits fuel (chunk + 1)
      else []

def logicalIndexAccesses (bits : List Bool) : List Access :=
  if bits.any id then logicalChunkScan bits (bitChunkCount bits) 0 else []

def LogicalIndexInBounds : Prop := ∀ bits, AllInBounds (logicalIndexAccesses bits)

def cartesianValues : List (List Int) → List (List Int)
  | [] => [[]]
  | values :: rest =>
      values.flatMap fun i => (cartesianValues rest).map fun is => i :: is

def genericGetindexAccesses (axes : List Axis) (indices : List (List Int)) : List Access :=
  let coords := cartesianValues indices
  if coords.all (fun is => !(constCartesianAccessAxes axes is).isEmpty) then
    coords.flatMap (constCartesianAccessAxes axes) ++
      (oneBased coords.length).map fun i => ⟨coords.length, i⟩
  else []

def genericSetindexAccesses (axes : List Axis) (indices : List (List Int))
    (sourceLength : Nat) : List Access :=
  let coords := cartesianValues indices
  if coords.all (fun is => !(constCartesianAccessAxes axes is).isEmpty) &&
      sourceLength = coords.length then
    coords.flatMap (constCartesianAccessAxes axes) ++
      (oneBased sourceLength).map fun i => ⟨sourceLength, i⟩
  else []

def GenericIndexingInBounds : Prop :=
  (∀ axes indices, AllInBounds (genericGetindexAccesses axes indices)) ∧
  (∀ axes indices sourceLength, AllInBounds (genericSetindexAccesses axes indices sourceLength))

structure Region where
  parentAxes : List Axis
  starts : List Int
  lengths : List Nat
  deriving DecidableEq, Repr

def Region.count (r : Region) : Nat := product r.lengths

def regionCoords (r : Region) : List (List Int) :=
  (cartesianCoords r.lengths).map fun offsets =>
    (r.starts.zip offsets).map fun (start, offset) => start + offset - 1

def regionValid (r : Region) : Bool :=
  r.parentAxes.length == r.starts.length && r.starts.length == r.lengths.length &&
    ((r.parentAxes.zip (r.starts.zip r.lengths)).all fun (axis, start, len) =>
      decide (axis.first.val ≤ start ∧
        (len = 0 ∨ start + len - 1 < axis.first.val + axis.len)))

def cartesianCopyAccesses (dest src : Region) : List Access :=
  if dest.lengths = src.lengths && regionValid dest && regionValid src then
    ((regionCoords src).flatMap (constCartesianAccessAxes src.parentAxes)) ++
      ((regionCoords dest).flatMap (constCartesianAccessAxes dest.parentAxes))
  else []

def CartesianCopyInBounds : Prop := ∀ dest src,
  AllInBounds (cartesianCopyAccesses dest src)

def bitSourceScanAccesses (sourceLength sourceStart count : Nat) : List Access :=
  if 1 ≤ sourceStart && sourceStart + count ≤ sourceLength + 1 then
    (List.range count).map fun k => ⟨sourceLength, (sourceStart + k : Nat)⟩
  else []

def BitSourceScanInBounds : Prop := ∀ sourceLength sourceStart count,
  AllInBounds (bitSourceScanAccesses sourceLength sourceStart count)

def isassignedAccess (axes : List Axis) (coords : List Int) (indexLinear : Bool) : List Access :=
  if !(constCartesianAccessAxes axes coords).isEmpty &&
      ((indexLinear && coords.length != 1) || (!indexLinear && coords.length != axes.length)) then
    constCartesianAccessAxes axes coords
  else []

def IsassignedInBounds : Prop := ∀ axes coords indexLinear,
  AllInBounds (isassignedAccess axes coords indexLinear)

/-! ## `base/reshapedarray.jl:270-339` -/

def reshapedLinearAccess (parent : Axis) (reshapeLength : Nat) (i : Int) : List Access :=
  if 1 ≤ i && i ≤ reshapeLength && reshapeLength = parent.len then
    let parentIndex := i - 1 + parent.first.val
    [⟨parent.len, parentIndex - parent.first.val + 1⟩]
  else []

def reshapedIndexAccess (parentLength : Nat) (parentIndex : Int) : List Access :=
  if 1 ≤ parentIndex && parentIndex ≤ parentLength then [⟨parentLength, parentIndex⟩] else []

def ReshapedIndexingInBounds : Prop :=
  (∀ parent reshapeLength i, AllInBounds (reshapedLinearAccess parent reshapeLength i)) ∧
  (∀ parentLength parentIndex, AllInBounds (reshapedIndexAccess parentLength parentIndex))

/-! ## `base/ryu/shortest.jl:319-447` -/

open JuliaLean.ParsePrint JuliaLean.ParsePrint.Ryu

abbrev RyuU64 := JuliaLean.ParsePrint.Ryu.U64

def ryuInitialE10 (e2 : Int) : Int :=
  if e2 ≥ 0 then log10pow2 e2 - (if e2 > 3 then 1 else 0)
  else log10pow5 (-e2) - (if -e2 > 1 then 1 else 0) + e2

def ryuInitialState (e2 : Int) (mfIsEven uShiftHalf : Bool)
    (u v w : RyuU64) : St :=
  let (a, b, c, e10, aAll, bAll) :=
    if e2 ≥ 0 then
      let q := log10pow2 e2 - (if e2 > 3 then 1 else 0)
      let k := 122 + pow5bits q - 1
      let i := -e2 + q + k
      let mul := pow5invsplit q
      let a := mulshift u mul i
      let b := mulshift v mul i
      let c := mulshift w mul i
      if q ≤ 21 then
        let vmod5 : RyuU64 := JInt.rem .u64 (JInt.rem .u32 v) - JInt.lit .u64 5 * udivLit v 5
        if vmod5.val == 0 then (a, b, c, q, false, pow5 v q)
        else if mfIsEven then (a, b, c, q, pow5 u q, false)
        else (a, b, c - ofBool .u64 (pow5 w q), q, false, false)
      else (a, b, c, q, false, false)
    else
      let q := log10pow5 (-e2) - (if -e2 > 1 then 1 else 0)
      let e10 := q + e2
      let i := -e2 - q
      let k := pow5bits i - 121
      let j := q - k
      let mul := pow5split i
      let a := mulshift u mul j
      let b := mulshift v mul j
      let c := mulshift w mul j
      if q ≤ 1 then
        if mfIsEven then (a, b, c, e10, !uShiftHalf, true)
        else (a, b, c - JInt.lit .u64 1, e10, false, true)
      else if q < 63 then (a, b, c, e10, false, pow2 v q)
      else (a, b, c, e10, false, false)
  let s : St := ⟨a, b, c, e10, aAll, bAll, JInt.lit .u8 0, false⟩
  { s with e10 := ryuInitialE10 e2 }

def ryuRoundState (mfIsEven : Bool) (m : Option Int) (s0 : St) : St :=
  if s0.aAll || s0.bAll then
    let s := slowLoop fuel s0
    let s := if s.aAll then aZeroLoop m fuel s else s
    let s := if s.bAll && s.bLast.val == 5 && s.b.val % 2 == 0 then
      { s with bLast := JInt.lit .u8 4 } else s
    { s with roundup := (s.b.val == s.a.val && (!mfIsEven || !s.aAll)) || decide (s.bLast.val ≥ 5) }
  else
    let s := { s0 with roundup := decide (s0.bLast.val ≥ 5) }
    let cd := udivLit s.c 100
    let ad := udivLit s.a 100
    let s := if cd.val > ad.val then
        let bd := udivLit s.b 100
        let bm := mod100 s.b bd
        { s with roundup := decide (bm.val ≥ 50), b := bd, c := cd, a := ad, e10 := s.e10 + 2 }
      else s
    let s := fastLoop fuel s
    { s with roundup := s.b.val == s.a.val || s.roundup }

def ryuFinish (mfIsEven : Bool) (m : Option Int) (s0 : St) : RyuU64 × Int :=
  let s := ryuRoundState mfIsEven m s0
  match m with
  | some M =>
    if s.b.val > M then
      let s := maxLoop M fuel s
      zeroLoop fuel (s.b + ofBool .u64 s.roundup, s.e10)
    else (s.b + ofBool .u64 s.roundup, s.e10)
  | none => (s.b + ofBool .u64 s.roundup, s.e10)

def ryuCore (rawM : RyuU64) (rawE ef : Int) (mf : RyuU64)
    (maxsignif : Option Int) : RyuU64 × Int :=
  let e2 := ef - 2
  let mfIsEven := mf.val % 2 == 0
  let v : RyuU64 := JInt.lit .u64 4 * mf
  let w : RyuU64 := v + JInt.lit .u64 2
  let uShiftHalf := rawM.val == 0 && decide (rawE > 1)
  let u : RyuU64 := v - JInt.lit .u64 2 + ofBool .u64 uShiftHalf
  ryuFinish mfIsEven maxsignif (ryuInitialState e2 mfIsEven uShiftHalf u v w)

def ryuLongPath (mf : RyuU64) (ef : Int) : Bool :=
  let fIsInteger := (band mf (shlI (JInt.lit .u64 1) (-ef) - JInt.lit .u64 1)).val == 0
  ef > 0 || ef < -52 || !fIsInteger

def ryuFixup (rawM : RyuU64) (rawE ef : Int) (mf : RyuU64) : Int × RyuU64 :=
  if rawE == 0 then ((1 : Int) - 1023 - 52, rawM) else (ef, mf)

def ryuFixupE (rawE ef : Int) : Int :=
  if rawE == 0 then (1 : Int) - 1023 - 52 else ef

def ryuFixupM (rawM : RyuU64) (rawE : Int) (mf : RyuU64) : RyuU64 :=
  if rawE == 0 then rawM else mf

def ryuReduceFromParts (rawM : RyuU64) (rawE ef : Int) (mf : RyuU64)
    (maxsignif : Option Int) : RyuU64 × Int :=
  if ryuLongPath mf ef then
    ryuCore rawM rawE (ryuFixupE rawE ef) (ryuFixupM rawM rawE mf) maxsignif
  else
    let b := shrI mf (-ef)
    let (b, e10) := match maxsignif with
      | some M =>
        if b.val > M then
          let s := maxLoop M fuel ⟨b, b, b, 0, false, true, JInt.lit .u8 0, false⟩
          (s.b + ofBool .u64 s.roundup, s.e10)
        else (b, 0)
      | none => (b, 0)
    zeroLoop fuel (b, e10)

def ryuReduceModel (x : JuliaLean.Float.F64) (maxsignif : Option Int) : RyuU64 × Int :=
  let uf : RyuU64 := JInt.wrap .u64 (JuliaLean.Float.F64.toBits x)
  let rawM := band uf (JInt.lit .u64 0x000fffffffffffff)
  let rawE : Int := JuliaLean.Float.F64.exponentField x
  let mf : RyuU64 := bor (shl (JInt.lit .u64 1) 52) rawM
  let ef : Int := rawE - 1023 - 52
  ryuReduceFromParts rawM rawE ef mf maxsignif

def ryuDecimalLength (x : RyuU64) : Fin 18 :=
  let v := x.val
  if v ≥ 10000000000000000 then ⟨17, by decide⟩
  else if v ≥ 1000000000000000 then ⟨16, by decide⟩
  else if v ≥ 100000000000000 then ⟨15, by decide⟩
  else if v ≥ 10000000000000 then ⟨14, by decide⟩
  else if v ≥ 1000000000000 then ⟨13, by decide⟩
  else if v ≥ 100000000000 then ⟨12, by decide⟩
  else if v ≥ 10000000000 then ⟨11, by decide⟩
  else if v ≥ 1000000000 then ⟨10, by decide⟩
  else if v ≥ 100000000 then ⟨9, by decide⟩
  else if v ≥ 10000000 then ⟨8, by decide⟩
  else if v ≥ 1000000 then ⟨7, by decide⟩
  else if v ≥ 100000 then ⟨6, by decide⟩
  else if v ≥ 10000 then ⟨5, by decide⟩
  else if v ≥ 1000 then ⟨4, by decide⟩
  else if v ≥ 100 then ⟨3, by decide⟩
  else if v ≥ 10 then ⟨2, by decide⟩
  else ⟨1, by decide⟩

def ryuExponentAccesses (x : JuliaLean.Float.F64) (compact : Bool) : List Access :=
  if JuliaLean.Float.F64.iszero x || JuliaLean.Float.F64.isnan x ||
      !JuliaLean.Float.F64.isfinite x then [] else
    let (output, nexp) := ryuReduceModel x
      (if compact then some (999999 : Int) else none)
    let olength := (ryuDecimalLength output).val
    let exp2 : Int := nexp + olength - 1
    let exp2 := if exp2 < 0 then -exp2 else exp2
    if 100 ≤ exp2 then [⟨100, exp2 / 10 + 1⟩]
    else if 10 ≤ exp2 then [⟨100, exp2 + 1⟩]
    else []

inductive RyuSmall where
  | f16 (bits : Fin (2^16))
  | f32 (bits : Fin (2^32))
  deriving DecidableEq, Repr

def RyuSmall.bits : RyuSmall → Nat
  | .f16 x | .f32 x => x.val

def RyuSmall.width : RyuSmall → Nat
  | .f16 _ => 16
  | .f32 _ => 32

def RyuSmall.significandBits : RyuSmall → Nat
  | .f16 _ => 10
  | .f32 _ => 23

def RyuSmall.exponentBits : RyuSmall → Nat
  | .f16 _ => 5
  | .f32 _ => 8

def RyuSmall.exponentBias : RyuSmall → Int
  | .f16 _ => 15
  | .f32 _ => 127

def RyuSmall.pow5InvBitcount : RyuSmall → Nat
  | .f16 _ => 30
  | .f32 _ => 59

def RyuSmall.pow5Bitcount : RyuSmall → Nat
  | .f16 _ => 30
  | .f32 _ => 61

def RyuSmall.qinvbound : RyuSmall → Int
  | .f16 _ => 4
  | .f32 _ => 9

def RyuSmall.qbound : RyuSmall → Int
  | .f16 _ => 15
  | .f32 _ => 31

def RyuSmall.modulus (x : RyuSmall) : Nat := 2^x.width

def RyuSmall.wrap (x : RyuSmall) (n : Nat) : Nat := n % x.modulus

def RyuSmall.sub (x : RyuSmall) (a b : Nat) : Nat :=
  (a + x.modulus - b % x.modulus) % x.modulus

def RyuSmall.rawM (x : RyuSmall) : Nat := x.bits % 2^x.significandBits

def RyuSmall.rawE (x : RyuSmall) : Int :=
  (x.bits / 2^x.significandBits % 2^x.exponentBits : Nat)

def RyuSmall.finite (x : RyuSmall) : Bool :=
  x.rawE != (2^x.exponentBits : Nat) - 1

def RyuSmall.zero (x : RyuSmall) : Bool :=
  x.bits % 2^(x.width - 1) == 0

def ryuSmallPow5InvSplit (x : RyuSmall) (q : Int) : Nat :=
  let pow := 5 ^ q.toNat
  2 ^ (nbits pow - 1 + x.pow5InvBitcount) / pow + 1

def ryuSmallPow5Split (x : RyuSmall) (i : Int) : Nat :=
  let pow := 5 ^ i.toNat
  let shift : Int := (nbits pow : Int) - x.pow5Bitcount
  if shift ≥ 0 then pow / 2^shift.toNat else pow * 2^(-shift).toNat

def ryuSmallMulshift (x : RyuSmall) (m mul : Nat) (j : Int) : RyuU64 :=
  let shifted := if j ≥ 0 then m * mul / 2^j.toNat else m * mul * 2^(-j).toNat
  JInt.lit .u64 (x.wrap shifted)

def ryuSmallPow5 (x : RyuSmall) (m : Nat) (q : Int) : Bool :=
  m % x.wrap (5^q.toNat) == 0

def ryuSmallPow2 (m : Nat) (q : Int) : Bool := m % 2^q.toNat == 0

def ryuSmallInitialE10 (e2 : Int) : Int :=
  if e2 ≥ 0 then log10pow2 e2 else log10pow5 (-e2) + e2

def ryuSmallInitialState (x : RyuSmall) (e2 : Int) (mfIsEven uShiftHalf : Bool)
    (u v w : Nat) : St :=
  let (a, b, c, e10, aAll, bAll, bLast) :=
    if e2 ≥ 0 then
      let q := log10pow2 e2
      let k := (x.pow5InvBitcount : Int) + pow5bits q - 1
      let i := -e2 + q + k
      let mul := ryuSmallPow5InvSplit x q
      let a := ryuSmallMulshift x u mul i
      let b := ryuSmallMulshift x v mul i
      let c := ryuSmallMulshift x w mul i
      let bLast := if q != 0 && x.sub c.val.toNat 1 / 10 ≤ a.val / 10 then
          JInt.lit .u8 ((ryuSmallMulshift x v (ryuSmallPow5InvSplit x (q - 1))
            (-e2 + q - 1 + ((x.pow5InvBitcount : Int) + pow5bits (q - 1) - 1))).val % 10)
        else JInt.lit .u8 0
      if q ≤ x.qinvbound then
        let vmod5 := v - 5 * (v / 5)
        if vmod5 == 0 then (a, b, c, q, false, ryuSmallPow5 x v q, bLast)
        else if mfIsEven then (a, b, c, q, ryuSmallPow5 x u q, false, bLast)
        else (a, b, JInt.lit .u64 (x.sub c.val.toNat (if ryuSmallPow5 x w q then 1 else 0)),
          q, false, false, bLast)
      else (a, b, c, q, false, false, bLast)
    else
      let q := log10pow5 (-e2)
      let e10 := q + e2
      let i := -e2 - q
      let k := pow5bits i - x.pow5Bitcount
      let j := q - k
      let mul := ryuSmallPow5Split x i
      let a := ryuSmallMulshift x u mul j
      let b := ryuSmallMulshift x v mul j
      let c := ryuSmallMulshift x w mul j
      let bLast := if q != 0 && x.sub c.val.toNat 1 / 10 ≤ a.val / 10 then
          let j' := q - 1 - (pow5bits (i + 1) - x.pow5Bitcount)
          JInt.lit .u8 ((ryuSmallMulshift x v (ryuSmallPow5Split x (i + 1)) j').val % 10)
        else JInt.lit .u8 0
      if q ≤ 1 then
        if mfIsEven then (a, b, c, e10, !uShiftHalf, true, bLast)
        else (a, b, JInt.lit .u64 (x.sub c.val.toNat 1), e10, false, true, bLast)
      else if q < x.qbound then
        (a, b, c, e10, false, ryuSmallPow2 v (q - 1), bLast)
      else (a, b, c, e10, false, false, bLast)
  { a := a, b := b, c := c, e10 := ryuSmallInitialE10 e2,
    aAll := aAll, bAll := bAll, bLast := bLast, roundup := false }

def ryuSmallLongPath (x : RyuSmall) (mf : Nat) (ef : Int) : Bool :=
  let mask := x.wrap (2^(-ef).toNat - 1)
  ef > 0 || ef < -(x.significandBits : Int) || ((x.wrap mf &&& mask) != 0)

def ryuSmallCore (x : RyuSmall) (rawM : Nat) (rawE ef : Int) (mf : Nat)
    (maxsignif : Option Int) : RyuU64 × Int :=
  let e2 := ef - 2
  let mfIsEven := mf % 2 == 0
  let v := x.wrap (4 * mf)
  let w := x.wrap (v + 2)
  let uShiftHalf := rawM == 0 && decide (rawE > 1)
  let u := x.wrap (x.sub v 2 + if uShiftHalf then 1 else 0)
  ryuFinish mfIsEven maxsignif (ryuSmallInitialState x e2 mfIsEven uShiftHalf u v w)

def ryuSmallEf (x : RyuSmall) : Int :=
  x.rawE - x.exponentBias - x.significandBits

def ryuSmallFixedEf (x : RyuSmall) : Int :=
  if x.rawE = 0 then 1 - x.exponentBias - x.significandBits else ryuSmallEf x

def ryuSmallReduce (x : RyuSmall) (maxsignif : Option Int) : RyuU64 × Int :=
  let rawM := x.rawM
  let rawE := x.rawE
  let mf := x.wrap (2^x.significandBits + rawM)
  let ef := ryuSmallEf x
  if ryuSmallLongPath x mf ef then
    let ef := ryuSmallFixedEf x
    let mf := if rawE = 0 then rawM else mf
    ryuSmallCore x rawM rawE ef mf maxsignif
  else
    let b := JInt.lit .u64 (x.wrap (mf / 2^(-ef).toNat))
    let (b, e10) := match maxsignif with
      | some M =>
        if b.val > M then
          let s := maxLoop M fuel ⟨b, b, b, 0, false, true, JInt.lit .u8 0, false⟩
          (s.b + ofBool .u64 s.roundup, s.e10)
        else (b, 0)
      | none => (b, 0)
    zeroLoop fuel (b, e10)

def ryuSmallExponentAccesses (x : RyuSmall) (compact : Bool) : List Access :=
  if x.zero || !x.finite then [] else
    let (output, nexp) := ryuSmallReduce x
      (if compact then some (999999 : Int) else none)
    let olength := (ryuDecimalLength output).val
    let exp2 : Int := nexp + olength - 1
    let exp2 := if exp2 < 0 then -exp2 else exp2
    if 100 ≤ exp2 then [⟨100, exp2 / 10 + 1⟩]
    else if 10 ≤ exp2 then [⟨100, exp2 + 1⟩]
    else []

def RyuExponentTableInBounds : Prop :=
  (∀ x compact, AllInBounds (ryuExponentAccesses x compact)) ∧
  (∀ x compact, AllInBounds (ryuSmallExponentAccesses x compact))

/-! ## `base/special/rem_pio2.jl:130-293` -/

def payneHanekIndices (rawExponent : Nat) : List Int :=
  let k : Int := rawExponent - 1023 - 52
  let idx := k / 64
  let shift := k - idx * 64
  if shift = 0 then [idx + 1, idx + 2, idx + 3]
  else (if idx < 0 then [] else [idx + 1]) ++ [idx + 2, idx + 3, idx + 4]

def f64PayneAccesses (x : JuliaLean.Float.F64) : List Access :=
  let bits := JuliaLean.Float.F64.toBits x
  let highword := (bits % 2^63) / 2^32
  let rawExponent := highword / 2^20
  if highword < 0x7ff00000 && 0x413921fb ≤ highword then
    (payneHanekIndices rawExponent).map fun i => ⟨19, i⟩
  else []

def f32PayneAccesses (bits : BitVec 32) : List Access :=
  let raw := bits.toNat / 2^23 % 256
  let magnitude := bits.toNat % 2^31
  if raw < 255 && 0x4dc90fdb ≤ magnitude then
    (payneHanekIndices (raw - 127 + 1023)).map fun i => ⟨19, i⟩
  else []

def PayneHanekCallerInBounds : Prop :=
  (∀ x, AllInBounds (f64PayneAccesses x)) ∧
  (∀ x, AllInBounds (f32PayneAccesses x))

/-! ## `base/strings/stringview.jl:126-150` -/

def stringRangeAccesses (bytes : List UInt8) (first last : Int) : List Access :=
  if first ≤ last && 1 ≤ first && last ≤ bytes.length then
    [⟨bytes.length, first⟩, ⟨bytes.length, last⟩]
  else []

def chompLength (bytes : List UInt8) : Nat :=
  let n := bytes.length
  if n = 0 then 0 else
    let hasLf := bytes.getD (n - 1) 0 == 0x0a
    let twoBytes := 1 < n
    let crIndex := if twoBytes then n - 2 else n - 1
    let hasCr := hasLf && bytes.getD crIndex 0 == 0x0d
    n - (if hasLf then 1 else 0) - (if hasCr then 1 else 0)

def chompAccesses (bytes : List UInt8) : List Access :=
  let len := chompLength bytes
  if len = 0 then [] else (oneBased len).map fun i => ⟨bytes.length, i⟩

def StringViewInBounds : Prop := ∀ bytes first last,
  AllInBounds (stringRangeAccesses bytes first last) ∧
  AllInBounds (chompAccesses bytes)

/-! ## `base/summarysize.jl:45-190` -/

def frontierIndices (nf : Nat) : List Nat := (List.range nf).map (· + 1)

def summaryInlineAccesses (length np : Nat) : List Access :=
  if length = 0 || np = 0 then [] else
    (frontierIndices (length * np)).map fun (i : Nat) =>
      ⟨length, (((i - 1) / np + 1 : Nat) : Int)⟩

def summaryOutlineAccesses (length : Nat) : List Access :=
  (frontierIndices length).map fun (i : Nat) => ⟨length, (i : Int)⟩

def SummarySizeInBounds : Prop :=
  (∀ length np, AllInBounds (summaryInlineAccesses length np)) ∧
  (∀ length, AllInBounds (summaryOutlineAccesses length))

end JuliaLean.MemSafety.G2

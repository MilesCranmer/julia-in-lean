import JuliaLean.base.operators
import JuliaLean.base.number
import JuliaLean.base.tuple
import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.array
import JuliaLean.base.int
import JuliaLean.base.bitarray
import JuliaLean.base.checked
import JuliaLean.base.abstractarray
import JuliaLean.base.range
import JuliaLean.Proofs.base.range
import JuliaLean.base.indices
import JuliaLean.Proofs.base.array

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

abbrev State := MutableMemory U64

def wordCount (n : Nat) : Nat := (n + 63) / 64

def encodeBits (xs : List Bool) : List U64 :=
  (List.range (wordCount xs.length)).map fun chunk =>
    (List.range 64).foldl (fun word bit =>
      if xs.getD (chunk * 64 + bit) false then or_int word (shl_int (u64 1) (int (Int.ofNat bit))) else word) (u64 0)

def initWords (words : List U64) : State := MutableMemory.initial (words.map some)

def vectorBits (xs : List Bool) : BitVector :=
  ⟨0, int xs.length, [int xs.length]⟩

def bitAt {N : Nat} (s : State) (B : BitArray N) (i : Nat) : Bool :=
  match (s.contents B.chunks)[i / 64]? with
  | none => false
  | some none => false
  | some (some word) => and_int word (shl_int (u64 1) (int (Int.ofNat (i % 64)))) != u64 0

def bitValues {N : Nat} (s : State) (B : BitArray N) : List Bool :=
  (List.range B.len.val.toNat).map (bitAt s B)

def validIndex (B : BitVector) (i : I64) : Prop := int 1 ≤ i ∧ i ≤ B.len

def BitArrayIndexAddress : Prop :=
  ∀ (i : I64), int 1 ≤ i →
    let (chunk, bit) := getChunksId i
    chunk.val = (i.val - 1) / 64 + 1 ∧ bit.val = (i.val - 1) % 64

def BitArrayChunkCount : Prop :=
  ∀ (n : I64), 0 ≤ n.val →
    (numBitChunks n).val = Int.ofNat ((n.val.toNat + 63) / 64)

def ScalarIndexAgrees : Prop :=
  ∀ (xs : List Bool) (i : I64) (x : Bool),
    let B := vectorBits xs
    let s := initWords (encodeBits xs)
    let check : BitVector → I64 → BitMutationM Unit := fun b j =>
      if int 1 ≤ j ∧ j ≤ b.len then pure () else throw .bounds
    let read := (bitArrayGetIndex check B i).run s
    let written := (bitArraySetIndex check (fun b => pure b) B x i).run s
    if int 1 ≤ i ∧ i ≤ B.len then
      read.1 = .ok (bitAt s B (i.val.toNat - 1)) ∧
      written.1 = .ok B ∧ bitValues written.2 B = (bitValues s B).set (i.val.toNat - 1) x
    else read.1 = .error .bounds ∧ written.1 = .error .bounds ∧ written.2 = s

def DequeAgrees : Prop :=
  ∀ (xs : List Bool) (x : Bool),
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    let check : BitVector → I64 → BitMutationM Unit := fun b i =>
      if int 1 ≤ i ∧ i ≤ b.len then pure () else throw .bounds
    let push := (bitVectorPush (fun b => pure b) check B x).run state
    let pushfront := (bitVectorPushfirst (fun b => pure b) B x).run state
    let pop := (bitVectorPop (bitArrayGetIndex check) (bitArraySetIndex check (fun b => pure b)) B).run state
    let popfront := (bitVectorPopfirst B).run state
    match push.1, pushfront.1, pop.1, popfront.1 with
    | .ok pushed, .ok front, .ok (popped, last), .ok (frontPopped, first) =>
        bitValues push.2 pushed = xs ++ [x] ∧ bitValues pushfront.2 front = x :: xs ∧
        last = xs.getD (xs.length - 1) false ∧ bitValues pop.2 popped = xs.take (xs.length - 1) ∧
        first = xs.headD false ∧ bitValues popfront.2 frontPopped = xs.drop 1
    | _, _, _, _ => xs.isEmpty

def InsertDeleteAgrees : Prop :=
  ∀ (xs : List Bool) (i : I64) (x : Bool),
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    let inserted := (bitVectorInsertInt (fun b => pure b) B i x).run state
    let deleted := (bitVectorDeleteAtInt B i).run state
    if int 1 ≤ i ∧ i ≤ int (Int.ofNat (xs.length + 1)) then
      match inserted.1 with
      | .ok B' => bitValues inserted.2 B' = xs.take (i.val.toNat - 1) ++ [x] ++ xs.drop (i.val.toNat - 1)
      | .error _ => False
    else inserted.1 = .error .bounds
    ∧ if int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length) then
      match deleted.1 with
      | .ok B' => bitValues deleted.2 B' = (xs.take (i.val.toNat - 1)) ++ xs.drop i.val.toNat
      | .error _ => False
    else True

def rangeLengthSpec (r : BitRange) : I64 :=
  if r.first > r.last then int 0 else r.last - r.first + int 1

def deleteRangeList (xs : List Bool) (r : BitRange) : List Bool :=
  if r.first > r.last then xs else xs.take (r.first.val - 1).toNat ++ xs.drop r.last.val.toNat

def resizeList (xs : List Bool) (n : Nat) (first : Bool) : List Bool :=
  if first then
    if n < xs.length then xs.drop (xs.length - n) else List.replicate (n - xs.length) false ++ xs
  else if n < xs.length then xs.take n else xs ++ List.replicate (n - xs.length) false

def DeleteatRangeAgrees : Prop :=
  ∀ (xs : List Bool) (first last : I64),
    let B := vectorBits xs
    let r := ⟨first, last⟩
    let result := (bitVectorDeleteRange rangeLengthSpec B r).run (initWords (encodeBits xs))
    if int 1 ≤ first ∧ first ≤ last ∧ last ≤ int (Int.ofNat xs.length) then
      match result.1 with
      | .ok B' => bitValues result.2 B' = deleteRangeList xs r
      | .error _ => False
    else True

def DeleteatRangeInsideAgrees : Prop :=
  ∀ (xs : List Bool) (first last : I64),
    first ≤ last → int 1 ≤ first → last ≤ int (Int.ofNat xs.length) →
    let B := vectorBits xs
    let r := ⟨first, last⟩
    match (bitVectorDeleteRange rangeLengthSpec B r).run (initWords (encodeBits xs)) with
    | (.ok B', state') => bitValues state' B' = deleteRangeList xs r
    | (.error _, _) => False

def AppendPrependAgrees : Prop :=
  ∀ (left right : List Bool),
    let a : BitVector := ⟨0, int left.length, [int left.length]⟩
    let b : BitVector := ⟨1, int right.length, [int right.length]⟩
    let state := MutableMemory.initialMany [(encodeBits left).map some, (encodeBits right).map some]
    let appended := (bitVectorAppend (fun x y => pure (x + y)) a b).run state
    let prepended := (bitVectorPrepend (fun x y => pure (x + y)) a b).run state
    match appended.1, prepended.1 with
    | .ok ap, .ok pr => bitValues appended.2 ap = left ++ right ∧ bitValues prepended.2 pr = right ++ left
    | _, _ => False

def ResizeAgrees : Prop :=
  ∀ (xs : List Bool) (n : I64),
    n.val < 0 →
    let B := vectorBits xs
    (bitVectorResize (fun i => i) B n false rangeLengthSpec).run (initWords (encodeBits xs)) |>.1 = .error .bounds

def ResizeNonnegAgrees : Prop :=
  ∀ (xs : List Bool) (n : I64) (first : Bool),
    0 ≤ n.val →
    let B := vectorBits xs
    match (bitVectorResize (fun i => i) B n first rangeLengthSpec).run (initWords (encodeBits xs)) with
    | (.ok B', state') => B'.len = n ∧ bitValues state' B' = resizeList xs n.val.toNat first
    | (.error _, _) => False

def fillVectorChunks (bc : Nat) (word : U64) : BitMutationM Unit := do
  let n ← mutableLength bc
  for i in intRange (int 1) n do mutableSet bc word i

def FillAgrees : Prop :=
  ∀ (xs : List Bool) (x : Bool),
    let B := vectorBits xs
    match (fillBitArray (fun b => pure b) fillVectorChunks B x).run (initWords (encodeBits xs)) with
    | (.ok B', state') => bitValues state' B' = List.replicate xs.length x
    | (.error _, _) => False

def reverseWord (word : U64) : U64 :=
  (List.range 64).foldl (fun out bit =>
    if word.val.toNat.testBit bit then or_int out (shl_int (u64 1) (int (Int.ofNat (63 - bit)))) else out) (u64 0)

def ReverseAgrees : Prop :=
  ∀ (xs : List Bool),
    let B := vectorBits xs
    match (bitVectorReverseInPlace reverseWord (fun n => n.val % 2 = 1) B).run (initWords (encodeBits xs)) with
    | (.ok _, state') => bitValues state' B = xs.reverse
    | (.error _, _) => False

def allocateZeroVector (n : I64) : BitMutationM BitVector := do
  let chunks ← mutableAllocate (some ⟨8, false, false⟩) 0 (numBitChunks n)
  let nc ← mutableLength chunks
  for i in intRange (int 1) nc do mutableSet chunks (u64 0) i
  return ⟨chunks, n, [n]⟩

def cloneVector (B : BitVector) : BitMutationM BitVector := do
  let n ← mutableLength B.chunks
  let chunks ← mutableAllocate (some ⟨8, false, false⟩) B.chunks n
  for i in intRange (int 1) n do mutableSet chunks (← mutableGet B.chunks i) i
  return { B with chunks := chunks }

def shiftLeftUnsigned (B : BitVector) (i : U64) : BitMutationM BitVector :=
  bitVectorShiftLeftUnsigned (fun n => u64 n.val) (fun x => int x.val) cloneVector allocateZeroVector B i

def shiftRightUnsigned (B : BitVector) (i : U64) : BitMutationM BitVector :=
  bitVectorShiftRightUnsigned (fun n => u64 n.val) (fun x => int x.val) cloneVector allocateZeroVector B i

def shiftRightSignedArg (B : BitVector) (i : I64) : BitMutationM BitVector :=
  shiftRightUnsigned B (u64 i.val)

def shiftLeftSignedArg (B : BitVector) (i : I64) : BitMutationM BitVector :=
  bitVectorShiftLeftUnsigned (fun n => u64 n.val) (fun x => int x.val) cloneVector allocateZeroVector B (u64 i.val)

def shiftLeftBits (xs : List Bool) (n : Nat) : List Bool :=
  if n ≥ xs.length then List.replicate xs.length false
  else xs.drop n ++ List.replicate n false

def shiftRightBits (xs : List Bool) (n : Nat) : List Bool :=
  if n ≥ xs.length then List.replicate xs.length false
  else List.replicate n false ++ xs.take (xs.length - n)

def ShiftAgrees : Prop :=
  ∀ (xs : List Bool) (i : I64), i.val > -(2 ^ 63 : Int) →
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    let left := (bitVectorShiftLeftSigned (fun x => x) (fun x => u64 x.val)
      shiftLeftUnsigned shiftRightSignedArg B i).run state
    let right := (bitVectorShiftRightSigned (fun x => x) (fun x => u64 x.val)
      shiftLeftSignedArg shiftRightUnsigned B i).run state
    let shift := i.val.natAbs
    match left.1, right.1 with
    | .ok l, .ok r =>
        bitValues left.2 l = (if i.val ≥ 0 then shiftLeftBits xs shift else shiftRightBits xs shift) ∧
        bitValues right.2 r = (if i.val ≥ 0 then shiftRightBits xs shift else shiftLeftBits xs shift)
    | _, _ => False

def normalizedShift (k : Int) (n : Nat) : Nat :=
  if n == 0 then 0 else ((k % Int.ofNat n + Int.ofNat n) % Int.ofNat n).toNat

def rotateRightBits (xs : List Bool) (k : Int) : List Bool :=
  if xs.isEmpty then xs else
    let r := normalizedShift k xs.length
    xs.drop (xs.length - r) ++ xs.take (xs.length - r)

def cloneChunkVector (bc : Nat) : BitMutationM Nat := do
  let n ← mutableLength bc
  let copy ← mutableAllocate (some ⟨8, false, false⟩) bc n
  for i in intRange (int 1) n do mutableSet copy (← mutableGet bc i) i
  return copy

def CircshiftAgrees : Prop :=
  ∀ (xs ys : List Bool) (i : I64), xs.length = ys.length →
    let dest : BitVector := ⟨0, int xs.length, [int xs.length]⟩
    let src : BitVector := ⟨1, int ys.length, [int ys.length]⟩
    let state := MutableMemory.initialMany [(encodeBits xs).map some, (encodeBits ys).map some]
    let result := (bitVectorCircshiftInt copyChunks cloneChunkVector dest src i).run state
    match result.1 with
    | .ok out => bitValues result.2 out = rotateRightBits ys i.val
    | .error _ => False

def CircshiftNonemptyAgrees : Prop :=
  ∀ (xs : List Bool) (i : I64), xs ≠ [] →
    let B := vectorBits xs
    match (bitVectorCircshiftInt copyChunks cloneChunkVector B B i).run (initWords (encodeBits xs)) with
    | (.ok out, state') => bitValues state' out = rotateRightBits xs i.val
    | (.error _, _) => False

def popcountWord (word : U64) : Nat :=
  (List.range 64).countP word.val.toNat.testBit

def countTrue (xs : List Bool) : Nat := xs.count true

def CountAgrees : Prop :=
  ∀ (t : IntTy) (xs : List Bool) (init : JInt t),
    let B := vectorBits xs
    let countOnes := fun word : U64 => int (Int.ofNat (popcountWord word))
    let addCount := fun n : JInt t => fun c : I64 => JInt.wrap t (n.val + c.val)
    match (bitcount addCount id countOnes init B.chunks).run (initWords (encodeBits xs)) with
    | (.ok result, _) => result = JInt.wrap t (init.val + Int.ofNat (countTrue xs))
    | (.error _, _) => False

/-- `count`, `any`, and `all` observe the logical bits for every BitArray rank. -/
def CountAnyAllAgrees : Prop :=
  ∀ {N : Nat} (dims : List I64) (xs : List Bool),
    dims.length = N →
    (∀ d ∈ dims, int 0 ≤ d) →
    dims.foldl (· * ·) (int 1) = int xs.length →
    xs.length ≤ (IntTy.max .i64).toNat →
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    let state := initWords (encodeBits xs)
    let count := (bitArrayCountIdentity (fun bc init => bitcount
      (fun n c => n + c) id JuliaLean.base.int.count_ones init bc) B (int 0)).run state
    let any := (bitArrayAny B).run state
    let all := (bitArrayAll B).run state
    count.1 = .ok (int (Int.ofNat (countTrue xs))) ∧
      any.1 = .ok (xs.any id) ∧ all.1 = .ok (xs.all id)

def listCopyRange (dest src : List Bool) (doffs soffs n : Nat) : List Bool :=
  dest.take doffs ++ (src.drop soffs).take n ++ dest.drop (doffs + n)

def BitArrayCopyChunksInBounds : Prop :=
  ∀ (dest src : List Bool) (doffs soffs n : Nat), doffs + n ≤ dest.length → soffs + n ≤ src.length →
    let d : BitVector := ⟨0, int dest.length, [int dest.length]⟩
    let s : BitVector := ⟨1, int src.length, [int src.length]⟩
    let state := MutableMemory.initialMany [(encodeBits dest).map some, (encodeBits src).map some]
    match (copyChunks d.chunks (int (Int.ofNat (doffs+1))) s.chunks (int (Int.ofNat (soffs+1))) (int (Int.ofNat n))).run state with
    | (.ok _, state') => bitValues state' d = listCopyRange dest src doffs soffs n
    | (.error _, _) => False

def BitArrayChunkInBounds : Prop :=
  ∀ (xs : List Bool) (i : I64), int 1 ≤ i → i ≤ int (Int.ofNat xs.length) →
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    ((unsafeBitGetIndex B.chunks i).run state).1 = .ok (bitAt state B (i.val.toNat - 1))

def trailingZerosWord (word : U64) : I64 :=
  int (Int.ofNat (((List.range 64).findIdx? word.val.toNat.testBit).getD 64))

def trailingOnesWord (word : U64) : I64 :=
  int (Int.ofNat (((List.range 64).findIdx? (fun bit => !word.val.toNat.testBit bit)).getD 64))

def topSetBitWord (word : U64) : I64 :=
  int (Int.ofNat (((((List.range 64).filter word.val.toNat.testBit).getLast?).map (· + 1)).getD 0))

def leadingOnesWord (word : U64) : I64 :=
  int (Int.ofNat ((List.range 64).reverse.takeWhile (fun bit => word.val.toNat.testBit bit)).length)

def findForwardSpec (xs : List Bool) (start : I64) (wanted : Bool) : Except Error (Option I64) :=
  if start ≤ int 0 then .error Error.bounds
  else if start > int (Int.ofNat xs.length) then .ok none
  else match (xs.drop (start.val.toNat - 1)).findIdx? (fun bit => bit == wanted) with
    | some offset => .ok (some (int (Int.ofNat (start.val.toNat + offset))))
    | none => .ok none

def findBackwardSpec (xs : List Bool) (start : I64) (wanted : Bool) : Except Error (Option I64) :=
  if start ≤ int 0 then .ok none
  else if start > int (Int.ofNat xs.length) then .error Error.bounds
  else match ((xs.take start.val.toNat).reverse.findIdx? (fun bit => bit == wanted)) with
    | some offset => .ok (some (int (Int.ofNat (start.val.toNat - offset))))
    | none => .ok none

def FindAgrees : Prop :=
  ∀ (xs : List Bool) (start : I64),
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    let next := (bitArrayFindNext id (unsafeBitFindNext trailingZerosWord) B start).run state
    let nextNot := (bitArrayFindNextNot trailingOnesWord B start).run state
    let prev := (bitArrayFindPrev id (unsafeBitFindPrev topSetBitWord) B start).run state
    let prevNot := (bitArrayFindPrevNot leadingOnesWord B start).run state
    next.1 = findForwardSpec xs start true ∧ nextNot.1 = findForwardSpec xs start false ∧
      prev.1 = findBackwardSpec xs start true ∧ prevNot.1 = findBackwardSpec xs start false

def FindExtremaAgrees : Prop :=
  ∀ (xs : List Bool),
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    let keyAt : BitArray 1 → I64 → BitMutationM I64 := fun _ i => pure i
    let largest := (bitArrayFindMax trailingZerosWord keyAt B).run state
    let smallest := (bitArrayFindMin trailingOnesWord keyAt B).run state
    if xs.isEmpty then largest.1 = .error (.argument "BitArray must be non-empty") ∧ smallest.1 = .error (.argument "BitArray must be non-empty")
    else match largest.1, smallest.1 with
      | .ok (maxValue, maxKey), .ok (minValue, minKey) =>
        maxValue = xs.any id ∧ minValue = xs.all id ∧
        maxKey = int (Int.ofNat (((xs.findIdx? id).map (· + 1)).getD 1)) ∧
        minKey = int (Int.ofNat (((xs.findIdx? (!·)).map (· + 1)).getD 1))
      | _, _ => False

def setMaskList (xs mask values : List Bool) : List Bool :=
  let rec loop : List Bool → List Bool → List Bool → List Bool
    | [], _, _ => []
    | x :: rest, flag :: flags, ys =>
        if flag then ys.headD false :: loop rest flags (ys.drop 1)
        else x :: loop rest flags ys
    | rest, [], _ => rest
  loop xs mask values

def MapAgrees : Prop :=
  ∀ (xs ys zs : List Bool),
    ys.length = zs.length → xs.length = ys.length →
    let dest : BitArray 1 := ⟨0, int xs.length, [int xs.length]⟩
    let a : BitArray 1 := ⟨1, int ys.length, [int ys.length]⟩
    let b : BitArray 1 := ⟨2, int zs.length, [int zs.length]⟩
    let state := MutableMemory.initialMany [(encodeBits xs).map some, (encodeBits ys).map some, (encodeBits zs).map some]
    let unary := (bitArrayMapBangUnary not_int dest a).run state
    let binary := (bitArrayMapBangBinary and_int dest a b).run state
    match unary.1, binary.1 with
    | .ok du, .ok db => bitValues unary.2 du = ys.map (!·) ∧ bitValues binary.2 db = List.zipWith (· && ·) ys zs
    | _, _ => False

def SetindexMaskAgrees : Prop :=
  ∀ (xs mask values : List Bool), values.length = countTrue mask → xs.length = mask.length →
    let B : BitArray 1 := ⟨0, int xs.length, [int xs.length]⟩
    let M : BitArray 1 := ⟨1, int mask.length, [int mask.length]⟩
    let state := MutableMemory.initialMany [(encodeBits xs).map some, (encodeBits mask).map some]
    let check : BitArray 1 → BitArray 1 → BitMutationM Unit := fun _ _ => pure ()
    let unsafeSet := bitArrayUnsafeSetIndexMask (N := 1) (A := List Bool) (I := Nat) check (fun vs => int vs.length) (fun _ => int 1)
      (fun _ i => i + int 1) (fun vs i => pure (vs.getD (i.val.toNat - 1) false))
      (fun vs i => pure (vs.getD (i.val.toNat - 1) false))
      (fun bm => pure (int (countTrue (bitValues state bm))))
      (fun _ _ => throw (.dimensionMismatch "mask length mismatch"))
    match (bitArraySetIndexMask (N := 1) (X := List Bool) (A := List Bool) check unsafeSet B values M).run state with
    | (.ok result, state') => bitValues state' result = setMaskList xs mask values
    | (.error _, _) => False

def VecAliasKeepsParentValid : Prop :=
  ∀ (xs : List Bool) (item : Bool),
    let parent : BitArray 2 := ⟨0, int xs.length, [int xs.length, int 1]⟩
    let vector : BitVector := ⟨0, int xs.length, [int xs.length]⟩
    let state := initWords (encodeBits xs)
    let check : BitVector → I64 → BitMutationM Unit := fun b i =>
      if int 1 ≤ i ∧ i ≤ b.len then pure () else throw .bounds
    let pushed := (bitVectorPush (fun b => pure b) check vector item).run state
    let popped := (bitVectorPop (bitArrayGetIndex check) (bitArraySetIndex check (fun b => pure b)) vector).run state
    let chunksAfterPush := (pushed.2.contents parent.chunks).length
    let chunksAfterPop := (popped.2.contents parent.chunks).length
    (match pushed.1 with | .ok _ => (numBitChunks parent.len).val.toNat = chunksAfterPush | .error _ => True) ∧
    (match popped.1 with | .ok _ => (numBitChunks parent.len).val.toNat = chunksAfterPop | .error _ => True)

def cloneBitArray {N : Nat} (B : BitArray N) : BitMutationM (BitArray N) := do
  let n ← mutableLength B.chunks
  let chunks ← mutableAllocate (some ⟨8, false, false⟩) B.chunks n
  for i in intRange (int 1) n do mutableSet chunks (← mutableGet B.chunks i) i
  return { B with chunks := chunks }

def similarBitArray {N : Nat} (B : BitArray N) : BitMutationM (BitArray N) := do
  let chunks ← mutableAllocate (some ⟨8, false, false⟩) B.chunks (numBitChunks B.len)
  let n ← mutableLength chunks
  for i in intRange (int 1) n do mutableSet chunks (u64 0) i
  return { B with chunks := chunks }

def rangeByStep (_ : BitArray N) (start stop step : I64) : List I64 :=
  if step ≤ int 0 || stop < start then []
  else (List.range ((stop.val - start.val).toNat / step.val.toNat + 1)).map fun k =>
    start + int (Int.ofNat k) * step

def reverseAxisBits (dims : List I64) (axis : I64) (xs : List Bool) : List Bool :=
  let sizes := dims.map fun d => d.val.toNat
  let d := axis.val.toNat - 1
  let size := sizes.getD d 1
  let stride := sizes.take d |>.foldl (· * ·) 1
  let block := stride * size
  (List.range xs.length).map fun i =>
    let coordinate := (i % block) / stride
    let source := (i / block) * block + (size - 1 - coordinate) * stride + i % stride
    xs.getD source false

def reverseDimTyped {N : Nat} (B : BitArray N) (d : I64) : BitMutationM (BitArray N) :=
  bitArrayReverseDim (A := Bool) (fun a => int a.dims.length)
    (fun a i => a.dims.getD (i.val.toNat - 1) (int 1))
    cloneBitArray similarBitArray
    (fun a i => unsafeBitGetIndex a.chunks i)
    (fun a x i => unsafeBitSetIndex a.chunks x i)
    (fun dims => dims.foldl (· * ·) (int 1)) copyChunks rangeByStep B d

def ReverseDimsAgrees : Prop :=
  ∀ (dims : List I64) (xs : List Bool) (axis : I64),
    dims.foldl (· * ·) (int 1) = int xs.length →
    int 1 ≤ axis → axis ≤ int (Int.ofNat dims.length) →
    let B : BitArray 2 := ⟨0, int xs.length, dims⟩
    let state := initWords (encodeBits xs)
    match (reverseDimTyped B axis).run state with
    | (.ok result, state') => result.dims = dims ∧ bitValues state' result = reverseAxisBits dims axis xs
    | (.error _, _) => False

def ReverseDimsNonemptyAgrees : Prop :=
  ∀ (dims : List I64) (xs : List Bool) (axis : I64),
    dims.foldl (· * ·) (int 1) = int xs.length →
    (∀ d ∈ dims, int 0 < d) → int 1 ≤ axis → axis ≤ int (Int.ofNat dims.length) →
    let B : BitArray 2 := ⟨0, int xs.length, dims⟩
    let state := initWords (encodeBits xs)
    match (reverseDimTyped B axis).run state with
    | (.ok result, state') => result.dims = dims ∧ bitValues state' result = reverseAxisBits dims axis xs
    | (.error _, _) => False

def SplitRestPartition : Prop :=
  ∀ (xs : List Bool) (n : I64),
    let check : I64 → I64 → BitMutationM Unit := fun len count =>
      if int 0 ≤ count ∧ count ≤ len then pure () else throw (.argument "requested count out of range")
    let suffix : List Bool → I64 → BitMutationM (List Bool) := fun values count =>
      pure (values.drop (values.length - count.val.toNat))
    let resize : List Bool → I64 → BitMutationM (List Bool) := fun values newLength =>
      pure (values.take newLength.val.toNat)
    let result := (bitArraySplitRest check suffix resize (fun values => int values.length) xs n).run (MutableMemory.initial [])
    if int 0 ≤ n ∧ n ≤ int (Int.ofNat xs.length) then
      result.1 = .ok (xs.take (xs.length - n.val.toNat), xs.drop (xs.length - n.val.toNat))
    else (match result.1 with | .error _ => True | .ok _ => False)

def BitArrayConstructorShape : Prop :=
  ∀ (dims : List I64), (∀ d ∈ dims, int 0 ≤ d) →
    let checked : List I64 → BitMutationM I64 := fun ds => pure (ds.foldl (· * ·) (int 1))
    let alloc : Nat → BitMutationM Nat := fun n => mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat n))
    let state := MutableMemory.initial []
    let created := (BitArrayUndef (N := 2) checked alloc dims).run state
    let empty := (bitVectorEmpty (fun ds => BitArrayUndef (N := 1) checked alloc ds)).run state
    match created.1, empty.1 with
    | .ok array, .ok vector =>
        array.dims = dims ∧ array.len = dims.foldl (· * ·) (int 1) ∧
        (created.2.contents array.chunks).length = (numBitChunks array.len).val.toNat ∧
        vector.dims = [int 0] ∧ vector.len = int 0
    | _, _ => False

def arrayBoolValues (state : State) (handle : Nat) (n : Nat) : List Bool :=
  (List.range n).map fun i =>
    match (state.contents handle)[i]? with
    | some (some value) => value == u64 1
    | _ => false

def ArrayConversionsKeepBits : Prop :=
  ∀ (xs : List Bool),
    let B : BitArray 1 := ⟨0, int xs.length, [int xs.length]⟩
    let state := initWords (encodeBits xs)
    let allocate : List I64 → BitMutationM Nat := fun dims =>
      mutableAllocate (some ⟨8, false, false⟩) 0 (dims.foldl (· * ·) (int 1))
    let set : Nat → Bool → I64 → BitMutationM Nat := fun handle bit i => do
      mutableSet handle (u64 (if bit then 1 else 0)) i
      pure handle
    let arrayResult := (arrayFromBitArray allocate (fun _ => int xs.length) set B).run state
    let checked : List I64 → BitMutationM I64 := fun dims => pure (dims.foldl (· * ·) (int 1))
    let allocChunks : Nat → BitMutationM Nat := fun n => mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat n))
    let undef : List I64 → BitMutationM (BitArray 1) := BitArrayUndef checked allocChunks
    let fromArray := (bitArrayFromAbstractTyped (fun _ => [int xs.length]) pure
      (fun dims _ => if dims == [int xs.length] then pure () else throw .bounds)
      undef (fun _ => int xs.length) (fun _ i => i + int 1) (fun _ => int 1)
      (fun values i => pure (values.getD (i.val.toNat - 1) false)) xs).run (initWords [])
    match arrayResult.1, fromArray.1 with
    | .ok handle, .ok result =>
      arrayBoolValues arrayResult.2 handle xs.length = xs ∧ bitValues fromArray.2 result = xs
    | _, _ => False

def BitArrayArithmetic : Prop :=
  ∀ (xs ys : List Bool), xs.length = ys.length →
    let a : BitArray 1 := ⟨0, int xs.length, [int xs.length]⟩
    let b : BitArray 1 := ⟨1, int ys.length, [int ys.length]⟩
    let state := MutableMemory.initialMany [(encodeBits xs).map some, (encodeBits ys).map some]
    let allocate : List I64 → BitMutationM Nat := fun dims => mutableAllocate (some ⟨8, false, false⟩) 0 (dims.foldl (· * ·) (int 1))
    let set : Nat → I64 → I64 → BitMutationM Unit := fun handle i value => mutableSet handle (u64 value.val) i
    let runOp (op : Bool → Bool → I64) := (bitArrayBinaryArithmetic (fun _ _ => [int xs.length]) set op allocate a b).run state
    let conjunction := runOp (fun x y => int (if x && y then 1 else 0))
    let disjunction := runOp (fun x y => int (if x || y then 1 else 0))
    let exclusive := runOp (fun x y => int (if x != y then 1 else 0))
    match conjunction.1, disjunction.1, exclusive.1 with
    | .ok andOut, .ok orOut, .ok xorOut =>
      arrayBoolValues conjunction.2 andOut xs.length = List.zipWith (· && ·) xs ys ∧
      arrayBoolValues disjunction.2 orOut xs.length = List.zipWith (· || ·) xs ys ∧
      arrayBoolValues exclusive.2 xorOut xs.length = List.zipWith (· != ·) xs ys
    | _, _, _ => False

def BitArrayEqualityAgrees : Prop :=
  ∀ (xs ys : List Bool),
    let a : BitArray 1 := ⟨0, int xs.length, [int xs.length]⟩
    let b : BitArray 1 := ⟨1, int ys.length, [int ys.length]⟩
    let state := MutableMemory.initialMany [(encodeBits xs).map some, (encodeBits ys).map some]
    let sameChunks : Nat → Nat → BitMutationM Bool := fun left right =>
      pure ((state.contents left) == (state.contents right))
    (bitArrayEqual sameChunks a b).run state |>.1 = .ok (xs.length = ys.length ∧ xs = ys)

def allocateMatrix (rows cols : I64) : BitMutationM BitMatrix := do
  let len := rows * cols
  let chunks ← mutableAllocate (some ⟨8, false, false⟩) 0 (numBitChunks len)
  let n ← mutableLength chunks
  for i in intRange (int 1) n do mutableSet chunks (u64 0) i
  return ⟨chunks, len, [rows, cols]⟩

def BitArrayConcatenation : Prop :=
  ∀ (xs ys : List Bool), xs.length = ys.length →
    let a : BitVector := ⟨0, int xs.length, [int xs.length]⟩
    let b : BitVector := ⟨1, int ys.length, [int ys.length]⟩
    let state := MutableMemory.initialMany [(encodeBits xs).map some, (encodeBits ys).map some]
    let hcat := (bitArrayHcatVectors [a, b] allocateMatrix).run state
    let vcat := (bitArrayVcatVectors [a, b] (fun n => do
      let chunks ← mutableAllocate (some ⟨8, false, false⟩) 0 (numBitChunks n)
      let count ← mutableLength chunks
      for i in intRange (int 1) count do mutableSet chunks (u64 0) i
      pure ⟨chunks, n, [n]⟩)).run state
    match hcat.1, vcat.1 with
    | .ok matrix, .ok vector =>
      matrix.dims = [int xs.length, int 2] ∧ bitValues hcat.2 matrix = xs ++ ys ∧
      vector.len = int (xs.length + ys.length) ∧ bitValues vcat.2 vector = xs ++ ys
    | _, _ => False

def BitFindAllSpec : Prop :=
  ∀ (xs : List Bool),
    let B : BitArray 1 := ⟨0, int xs.length, [int xs.length]⟩
    let state := initWords (encodeBits xs)
    let count : BitArray 1 → BitMutationM I64 := fun _ => pure (int (Int.ofNat (countTrue xs)))
    let allocate : I64 → BitMutationM Nat := fun n => mutableAllocate (some ⟨8, false, false⟩) 0 n
    let set : Nat → BitIndex → I64 → BitMutationM Unit := fun handle key index =>
      match key with
      | .scalar i => mutableSet handle (u64 i.val) index
      | .cartesian indices => mutableSet handle (u64 ((indices.headD (int 0)).val)) index
    let allindices : Nat → BitArray 1 → BitMutationM Nat := fun handle array => do
      for i in intRange (int 1) array.len do mutableSet handle (u64 i.val) i
      pure handle
    match (bitArrayFindAll count allocate set allindices trailingZerosWord B).run state with
    | (.ok output, state') => (state'.contents output).length = countTrue xs
    | (.error _, _) => False

def BitVectorLoopInBounds : Prop :=
  ∀ (xs : List Bool),
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    let anyResult := (bitArrayAny B).run state
    let allResult := (bitArrayAll B).run state
    anyResult.1 = .ok (xs.any id) ∧ allResult.1 = .ok (xs.all id)

def listIteratorStep (xs : List Bool) (_ : Unit) (state : Option Nat) : BitMutationM (Option (Bool × Nat)) := do
  match state with
  | none =>
    match xs.head? with | some value => pure (some (value, 0)) | none => pure none
  | some i =>
    match xs[i + 1]? with | some value => pure (some (value, i + 1)) | none => pure none

def allocateBoolCache (n : Nat) : BitMutationM Nat := mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat n))

def setBoolCache (cache : Nat) (value : Bool) (i : I64) : BitMutationM Unit :=
  mutableSet cache (u64 (if value then 1 else 0)) i

def fillBoolCacheFalse (cache : Nat) (start count : I64) : BitMutationM Unit := do
  for i in intRange start (start + count - int 1) do mutableSet cache (u64 0) i

def getBoolCache (cache : Nat) (i : I64) : BitMutationM Bool := do
  return (← mutableGet cache i) == u64 1

def loadEightBoolCache (cache : Nat) (start : I64) : BitMutationM U64 := do
  let mut word := u64 0
  for j in intRange (int 0) (int 7) do
    if ← getBoolCache cache (start + j) then
      word := or_int word (shl_int (u64 1) (int (j.val * 8)))
  return word

def IteratorConstructorsKeepElements : Prop :=
  ∀ (xs : List Bool),
    let iterate := listIteratorStep xs
    let hasLength := (genBitArrayHasLength (fun _ => int xs.length)
      (fun dims => pure (dims.foldl (· * ·) (int 1)))
      (fun n => mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat n))) allocateBoolCache iterate
      setBoolCache fillBoolCacheFalse getBoolCache (fun cache _ => cache) loadEightBoolCache
      (fun chunks => mutableLength chunks) id rangeLengthSpec ()).run (MutableMemory.initial [])
    let unknown := (genBitArrayFromIterator
      (fun dims => pure (dims.foldl (· * ·) (int 1)))
      (fun n => mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat n))) allocateBoolCache iterate
      setBoolCache fillBoolCacheFalse getBoolCache (fun cache _ => cache) loadEightBoolCache
      (fun chunks => mutableLength chunks) id rangeLengthSpec ()).run (MutableMemory.initial [])
    match hasLength.1, unknown.1 with
    | .ok known, .ok inferred =>
      known.len = int xs.length ∧ bitValues hasLength.2 known = xs ∧
      inferred.len = int xs.length ∧ bitValues unknown.2 inferred = xs
    | _, _ => False

def IteratorShapeBuilderKeepsElements : Prop :=
  ∀ (xs : List Bool),
    let state := MutableMemory.initial []
    let checked : List I64 → BitMutationM I64 := fun dims => pure (dims.foldl (· * ·) (int 1))
    let allocate : Nat → BitMutationM Nat := fun n => mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat n))
    let undef : List I64 → BitMutationM (BitArray 1) := BitArrayUndef checked allocate
    let pairs := (List.range xs.length).map fun i => (int (Int.ofNat (i + 1)), xs.getD i false)
    let shaped := (genBitArrayHasShape (N := 1) (I := Unit) (K := I64) (fun _ => [int xs.length]) undef (fun _ => pure pairs)
      (fun B i value => do
        unsafeBitSetIndex B.chunks value i
        pure B) ()).run state
    let generated := (genBitArrayGeneratorShape (N := 1) (I := Unit) (S := Nat) (C := Nat) (P := Nat)
      (fun _ => [int xs.length]) checked allocate
      allocateBoolCache (listIteratorStep xs) setBoolCache fillBoolCacheFalse getBoolCache
      (fun cache _ => cache) loadEightBoolCache (fun chunks => mutableLength chunks) id rangeLengthSpec ()).run state
    match shaped.1, generated.1 with
    | .ok a, .ok b =>
      a.len = int xs.length ∧ bitValues shaped.2 a = xs ∧
      b.len = int xs.length ∧ bitValues generated.2 b = xs
    | _, _ => False

/- Checked construction calls use the installed Julia integer multiplication model.
Source: `base/checked.jl:106-114`. -/
def checkedMultiplyMutation (x y : I64) : BitMutationM I64 :=
  match JuliaLean.base.checked.checkedMulBits x y with
  | .ok z => pure z
  | .error e => throw (match e with
      | .overflowError _ => JuliaLean.base.array.Error.overflow
      | .argumentError m => .argument m
      | .boundsError => .bounds
      | .inexactError _ => .inexact
      | .divideError => .divide
      | .domainError m => .argument m
      | .methodError f => .method f
      | .eofError => .method "EOFError")

def checkedDimensionsModel (dims : List I64) : BitMutationM I64 := do
  let mut product := int 1
  for dim in dims do product ← checkedMultiplyMutation product dim
  pure product

def allocateChunkVectorModel (count : Nat) : BitMutationM Nat :=
  mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat count))

def allocateBitArrayModel {N : Nat} (dims : List I64) : BitMutationM (BitArray N) :=
  BitArrayUndef checkedDimensionsModel allocateChunkVectorModel dims
def BitArrayReshapeKeepsBits : Prop :=
  ∀ {InputRank OutputRank : Nat} (xs : List Bool) (oldDims newDims : List I64)
    (_hOldRank : oldDims.length = InputRank)
    (hNewRank : newDims.length = OutputRank),
    InputRank ≠ OutputRank →
    (∀ d ∈ oldDims, int 0 ≤ d) → (∀ d ∈ newDims, int 0 ≤ d) →
    oldDims.foldl (· * ·) (int 1) = int xs.length →
    newDims.foldl (· * ·) (int 1) = int xs.length →
    let B : BitArray InputRank := ⟨0, int xs.length, oldDims⟩
    let result := (bitArrayReshapeAny checkedDimensionsModel
      allocateBitArrayModel B newDims hNewRank).run (initWords (encodeBits xs))
    match result.1 with
    | .ok reshaped =>
        bitArraySizeRanked reshaped = newDims ∧ reshaped.len = int xs.length ∧
        bitValues result.2 reshaped = xs
    | .error _ => False

def BitArrayFillConstructors : Prop :=
  ∀ (dims : List I64),
    let checked : List I64 → BitMutationM I64 := fun ds => pure (ds.foldl (· * ·) (int 1))
    let allocate : Nat → BitMutationM Nat := fun n => mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat n))
    let undef : List I64 → BitMutationM (BitArray 2) := BitArrayUndef checked allocate
    let fill : BitArray 2 → Bool → BitMutationM (BitArray 2) := fun B value => fillBitArray (fun x => pure x) fillVectorChunks B value
    let falseResult := (falsesIntegerDims undef fill dims).run (MutableMemory.initial [])
    let trueResult := (truesIntegerDims undef fill dims).run (MutableMemory.initial [])
    match falseResult.1, trueResult.1 with
    | .ok f, .ok t =>
      f.dims = dims ∧ t.dims = dims ∧
      bitValues falseResult.2 f = List.replicate f.len.val.toNat false ∧
      bitValues trueResult.2 t = List.replicate t.len.val.toNat true
    | _, _ => False

def BitArraySizeofAgrees : Prop :=
  ∀ {N : Nat} (xs : List Bool) (dims : List I64),
    dims.length = N →
    dims.foldl (· * ·) (int 1) = int xs.length →
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    match (bitArraySizeof (fun chunks => mutableLength chunks) B).run (initWords (encodeBits xs)) with
    | (.ok bytes, _) => bytes = int (Int.ofNat (wordCount xs.length * 8))
    | (.error _, _) => False

def BitMatrixOneAgrees : Prop :=
  ∀ (n : Nat),
    let matrix : BitMatrix := ⟨0, int (n * n), [int n, int n]⟩
    let state := initWords (encodeBits (List.replicate (n * n) false))
    let checked : List I64 → BitMutationM I64 := fun dims => pure (dims.foldl (· * ·) (int 1))
    let allocate : Nat → BitMutationM Nat := fun count => mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat count))
    let undef : List I64 → BitMutationM BitMatrix := BitArrayUndef checked allocate
    let falses : List I64 → BitMutationM BitMatrix := fun dims => do fillBitArray (fun b => pure b) fillVectorChunks (← undef dims) false
    let setDiagonal : BitMatrix → Bool → List I64 → BitMutationM BitMatrix := fun B value indices => do
      let i := indices.headD (int 1)
      unsafeBitSetIndex B.chunks value ((i - int 1) * int n + i)
      pure B
    let result := (bitMatrixOne (fun _ => pure (int n, int n)) falses setDiagonal matrix).run state
    match result.1 with
    | .ok identity => identity.dims = [int n, int n] ∧
      bitValues result.2 identity = (List.range (n*n)).map fun k => k % n == k / n
    | .error _ => False

def BitArrayFilterAgrees : Prop :=
  ∀ (xs : List Bool),
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    let makeMask : (Bool → BitMutationM Bool) → BitArray 1 → BitMutationM BoolArray := fun f source => do
      let mask ← mutableAllocate (some ⟨8, false, false⟩) 0 source.len
      for i in intRange (int 1) source.len do
        let bit ← unsafeBitGetIndex source.chunks i
        let keep ← f bit
        mutableSet mask (u64 (if keep then 1 else 0)) i
      pure mask
    let gather : BitArray 1 → BoolArray → BitMutationM (List Bool) := fun source mask => do
      let mut kept : List Bool := []
      for i in intRange (int 1) source.len do
        if (← mutableGet mask i) == u64 1 then
          let bit ← unsafeBitGetIndex source.chunks i
          kept := kept ++ [bit]
      pure kept
    match (bitArrayFilter makeMask gather (fun bit => pure bit) B).run state with
    | (.ok kept, _) => kept = xs.filter id
    | (.error _, _) => False


def compareBoolLists (xs ys : List Bool) : I64 :=
  match (List.range (min xs.length ys.length)).find? fun i => xs.getD i false != ys.getD i false with
  | some i => if xs.getD i false then int 1 else int (-1)
  | none => if xs.length < ys.length then int (-1) else if xs.length > ys.length then int 1 else int 0

def BitVectorComparisonAgrees : Prop :=
  ∀ (xs ys : List Bool),
    let a : BitVector := ⟨0, int xs.length, [int xs.length]⟩
    let b : BitVector := ⟨1, int ys.length, [int ys.length]⟩
    let state := MutableMemory.initialMany [(encodeBits xs).map some, (encodeBits ys).map some]
    let cmpLength := fun m n => if m < n then int (-1) else if m > n then int 1 else int 0
    (bitVectorCmp (A := Unit) trailingZerosWord topSetBitWord cmpLength a b).run state |>.1 = .ok (compareBoolLists xs ys)

def BitArrayIteratorYields : Prop :=
  ∀ (xs : List Bool) (i : Nat),
    let B := vectorBits xs
    let result := (bitArrayIterate B (int (Int.ofNat i))).run (initWords (encodeBits xs))
    if i < xs.length then result.1 = .ok (some (xs.getD i false, int (Int.ofNat (i+1)))) else result.1 = .ok none

def BitArrayMetadataAgrees : Prop :=
  ∀ (xs : List Bool) (i : I64),
    let B : BitArray 2 := ⟨7, int xs.length, [int xs.length, int 1]⟩
    let V : BitVector := ⟨7, int xs.length, [int xs.length]⟩
    bitArrayLength B = int xs.length ∧ bitArraySize B = B.dims ∧ bitVectorSize V = [V.len] ∧
    bitArrayDataIds (fun handle => handle) B = B.chunks ∧
    bitArrayIsAssigned B i = (int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length)) ∧
    bitArrayIndexStyle = JuliaLean.base.indices.IndexStyle.linear

def BitArrayCopytoAgrees : Prop :=
  ∀ (dest src : List Bool),
    let d : BitArray 1 := ⟨0, int dest.length, [int dest.length]⟩
    let s : BitArray 1 := ⟨1, int src.length, [int src.length]⟩
    let state := MutableMemory.initialMany [(encodeBits dest).map some, (encodeBits src).map some]
    let result := (bitArrayCopyto d s).run state
    if src.length ≤ dest.length then
      match result.1 with
      | .ok output => bitValues result.2 output = src ++ dest.drop src.length
      | .error _ => False
    else (match result.1 with | .error .bounds => True | _ => False)

def AbstractArrayCopyAgrees : Prop :=
  ∀ (xs destValues : List Bool), xs.length ≤ destValues.length →
    let B : BitArray 1 := ⟨0, int destValues.length, [int destValues.length]⟩
    let state := initWords (encodeBits destValues)
    let result := (copytoBitArrayFromAbstract (fun values => int values.length) (fun _ i => i + int 1)
      (fun _ => int 1) (fun values i => pure (values.getD (i.val.toNat - 1) false)) B xs).run state
    match result.1 with
    | .ok output => bitValues result.2 output = xs ++ destValues.drop xs.length
    | .error _ => False

def DeleteAtIndicesAgrees : Prop :=
  ∀ (xs : List Bool) (indices : List I64),
    (∀ i ∈ indices, int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length)) →
    indices.Pairwise (· < ·) →
    let B := vectorBits xs
    let iterate : List I64 → Option (I64 × Nat) := fun values => values.head?.map fun value => (value, 0)
    let next : List I64 → Nat → Option (I64 × Nat) := fun values index => values[index + 1]?.map fun value => (value, index + 1)
    let check : BitVector → I64 → BitMutationM Unit := fun _ i =>
      if int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length) then pure () else throw .bounds
    let result := (bitVectorDeleteAtIndices iterate next check (fun _ => false) id B indices).run (initWords (encodeBits xs))
    let expected := (List.range xs.length).filterMap fun i =>
      if indices.contains (int (Int.ofNat (i+1))) then none else some (xs.getD i false)
    match result.1 with | .ok output => bitValues result.2 output = expected | .error _ => False

def DeleteAtMaskAgrees : Prop :=
  ∀ (xs mask : List Bool), xs.length = mask.length →
    let B := vectorBits xs
    let indices := (List.range mask.length).filter fun i => mask.getD i false
    let first : List Bool → BitMutationM (Option I64) := fun _ => pure (indices.head?.map fun i => int (Int.ofNat (i+1)))
    let next : List Bool → I64 → BitMutationM (Option I64) := fun _ start =>
      pure (((indices.filter fun i => int (Int.ofNat (i+1)) ≥ start).head?).map fun i => int (Int.ofNat (i+1)))
    let check : BitVector → I64 → BitMutationM Unit := fun _ i =>
      if int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length) then pure () else throw .bounds
    let result := (bitVectorDeleteAtBoolMask (fun _ => int mask.length) first next check B mask).run (initWords (encodeBits xs))
    match result.1 with
    | .ok output => bitValues result.2 output = (List.range xs.length).filterMap fun i =>
        if mask.getD i false then none else some (xs.getD i false)
    | .error _ => False

def InfiniteIteratorRejected : Prop :=
  ∀ {N : Nat},
    let result : Except Error (BitArray N) := ((genBitArrayInfinite (N := N) ()).run (MutableMemory.initial [])).1
    result = .error (.argument "infinite-size iterable used in BitArray constructor")

def IteratorWrongShapeRejected : Prop :=
  ∀ {I : Type} (rank : Nat) (itr : I),
    let result : Except Error BitVector := ((genBitArrayNVectorWrongShape rank itr).run (MutableMemory.initial [])).1
    result = .error (.dimensionMismatch "cannot create a BitVector from a multidimensional iterator")

def MatrixHcatAgrees : Prop :=
  ∀ (rows : Nat) (left right : List Bool), left.length = right.length →
    let a : BitMatrix := ⟨0, int left.length, [int rows, int (left.length / rows)]⟩
    let b : BitMatrix := ⟨1, int right.length, [int rows, int (right.length / rows)]⟩
    let state := MutableMemory.initialMany [(encodeBits left).map some, (encodeBits right).map some]
    let sizeDim : BitMatrix → I64 → I64 := fun B dim => B.dims.getD (dim.val.toNat - 1) (int 0)
    match (bitArrayHcatArrays [a,b] sizeDim (fun _ => int 2) allocateMatrix).run state with
    | (.ok output, state') => output.dims = [int rows, int ((left.length + right.length) / rows)] ∧ bitValues state' output = left ++ right
    | (.error _, _) => False

def spreadEight (bits : List Bool) : U64 :=
  (List.range bits.length).foldl (fun word i => if bits.getD i false then or_int word (shl_int (u64 1) (int (Int.ofNat (8*i)))) else word) (u64 0)

def packedByte (bits : List Bool) : U64 :=
  (List.range bits.length).foldl (fun word i => if bits.getD i false then or_int word (shl_int (u64 1) (int (Int.ofNat i))) else word) (u64 0)

def BitArrayPackHelpers : Prop :=
  ∀ bits : List Bool, bits.length = 8 → pack8bools (spreadEight bits) = packedByte bits

def listFillRange (xs : List Bool) (start count : Nat) (value : Bool) : List Bool :=
  (List.range xs.length).map fun i => if start ≤ i ∧ i < start + count then value else xs.getD i false

def BitArrayChunkFill : Prop :=
  ∀ (xs : List Bool) (start count : Nat) (value : Bool), start + count ≤ xs.length →
    let B := vectorBits xs
    let result := (fillChunks B.chunks value (int (Int.ofNat (start+1))) (int (Int.ofNat count))).run (initWords (encodeBits xs))
    result.1 = .ok () ∧ bitValues result.2 B = listFillRange xs start count value

def TupleConstructorAgrees : Prop :=
  ∀ (xs : List Bool),
    let undef : Nat → BitMutationM BitVector := fun n => do
      let chunks ← mutableAllocate (some ⟨8, false, false⟩) 0 (numBitChunks (int (Int.ofNat n)))
      let count ← mutableLength chunks
      for i in intRange (int 1) count do mutableSet chunks (u64 0) i
      pure ⟨chunks, int (Int.ofNat n), [int (Int.ofNat n)]⟩
    let assign : BitVector → List Bool → BitMutationM BitVector := fun B values => do
      for i in intRange (int 1) (int (Int.ofNat values.length)) do
        unsafeBitSetIndex B.chunks (values.getD (i.val.toNat - 1) false) i
      pure B
    match (bitVectorFromTuple List.length undef assign xs).run (MutableMemory.initial []) with
    | (.ok B, state) => B.len = int (Int.ofNat xs.length) ∧ bitValues state B = xs
    | (.error _, _) => False

def BitVectorEmptyAgrees : Prop :=
  ∀ (xs : List Bool),
    let B := vectorBits xs
    match (bitVectorEmptyBang deleteChunkEnd B).run (initWords (encodeBits xs)) with
    | (.ok empty, state) => empty.len = int 0 ∧ (state.contents B.chunks).isEmpty
    | (.error _, _) => False

def BitVectorUnaryMinusAgrees : Prop :=
  ∀ (xs : List Bool),
    let B := vectorBits xs
    let allocate : List I64 → BitMutationM Nat := fun dims => mutableAllocate (some ⟨8, false, false⟩) 0 (dims.foldl (· * ·) (int 1))
    let set : Nat → I64 → I64 → BitMutationM Unit := fun handle i value => mutableSet handle (u64 value.val) i
    let result := (bitArrayUnaryMinus allocate (fun _ => int (Int.ofNat xs.length)) set B).run (initWords (encodeBits xs))
    match result.1 with
    | .ok output => (List.range xs.length).all fun i => (result.2.contents output)[i]? =
        some (some (if xs.getD i false then u64Max else u64 0))
    | .error _ => False

def matrixVcatBits (left right : List Bool) (leftRows rightRows columns : Nat) : List Bool :=
  (List.range columns).flatMap fun column =>
    (left.drop (column * leftRows)).take leftRows ++ (right.drop (column * rightRows)).take rightRows

def MatrixVcatAgrees : Prop :=
  ∀ (leftRows rightRows columns : Nat) (left right : List Bool),
    left.length = leftRows * columns → right.length = rightRows * columns →
    let a : BitMatrix := ⟨0, int left.length, [int leftRows, int columns]⟩
    let b : BitMatrix := ⟨1, int right.length, [int rightRows, int columns]⟩
    let state := MutableMemory.initialMany [(encodeBits left).map some, (encodeBits right).map some]
    let sizeDim : BitMatrix → I64 → I64 := fun B dim => B.dims.getD (dim.val.toNat - 1) (int 0)
    match (bitArrayVcatMatrices [a,b] sizeDim allocateMatrix).run state with
    | (.ok output, state') => output.dims = [int (leftRows+rightRows), int columns] ∧
        bitValues state' output = matrixVcatBits left right leftRows rightRows columns
    | (.error _, _) => False

def makeBitVector (xs : List Bool) : BitMutationM BitVector := do
  let chunks ← mutableAllocate (some ⟨8, false, false⟩) 0 (int (Int.ofNat (wordCount xs.length)))
  for (word, i) in (encodeBits xs).zipIdx do mutableSet chunks word (int (Int.ofNat (i+1)))
  pure ⟨chunks, int (Int.ofNat xs.length), [int (Int.ofNat xs.length)]⟩

def spliceSliceList (xs : List Bool) (r : BitRange) : List Bool :=
  if r.first.val ≤ 0 || r.first.val > xs.length || r.last.val < r.first.val then []
  else xs.drop (r.first.val.toNat - 1) |>.take (r.last.val - r.first.val + 1).toNat

def SpliceRemovedAgrees : Prop :=
  ∀ (xs ins : List Bool) (first last : I64),
    int 1 ≤ first → first ≤ int (Int.ofNat (xs.length+1)) → last ≤ int (Int.ofNat xs.length) →
    let B := vectorBits xs
    let convert : List Bool → BitMutationM (BitArray 1) := fun values => makeBitVector values
    let slice : BitVector → BitRange → BitMutationM BitVector := fun source r => do
      let values := spliceSliceList (bitValues (initWords (encodeBits xs)) source) r
      makeBitVector values
    let empty : BitMutationM BitVector := makeBitVector []
    let result := (bitVectorSpliceInt convert (fun x y => pure (x+y)) slice empty rangeLengthSpec
      (fun _ _ => pure ()) B ⟨first,last⟩ ins).run (initWords (encodeBits xs))
    match result.1 with
    | .ok removed => bitValues result.2 removed = spliceSliceList xs ⟨first,last⟩
    | .error _ => False
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace Round2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

abbrev State := JuliaLean.Proofs.base.bitarray.State

/-- Copy a chunk vector through the installed public array-copy model. -/
def copyChunkVectorPublic (chunks : Nat) : BitMutationM Nat :=
  JuliaLean.base.abstractarray.copyMutableArray
    (fun src => do
      let len ← mutableLength src
      mutableAllocate (some ⟨8, false, false⟩) 0 len)
    (fun dest src => do
      let len ← mutableLength src
      let _ ← JuliaLean.base.array.mutableCopyto dest (int 1) src (int 1) len
      pure dest)
    chunks

def mutationErrorOfRange : JuliaLean.base.range.Exc → JuliaLean.base.array.Error
  | .jl (.overflowError _) => .overflow
  | .jl (.argumentError message) => .argument message
  | .jl .boundsError => .bounds
  | .jl (.inexactError _) => .inexact
  | .jl .divideError => .divide
  | .jl (.domainError message) => .argument message
  | .jl (.methodError name) => .method name
  -- This BitArray range path has no EOF-producing call.
  | .jl .eofError => .method "EOFError"
  | .errorException message => .argument message
  | .dimensionMismatch message => .dimensionMismatch message
  | .showError error => .showError error
  | .inboundsViolation => .bounds

def liftRangeResult {α : Type} (result : JuliaLean.base.range.JlX α) : BitMutationM α :=
  match result with
  | .ok value => pure value
  | .error error => throw (mutationErrorOfRange error)

/-- Apply the public BitVector circular-shift wrapper after Integer conversion.
Source: `base/bitarray.jl:1425-1444`; generic destination method:
`base/multidimensional.jl:1257-1266`. -/
def bitVectorCircshiftPublic {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (dest src : BitVector) (i : X) : BitMutationM BitVector := do
  let shift ← liftRangeResult (JuliaLean.base.range.JConvert.convert (T := I64) i)
  JuliaLean.base.bitarray.bitVectorCircshiftTo (fun _ => shift)
    (fun d s n => JuliaLean.base.bitarray.bitVectorCircshiftInt
      JuliaLean.base.bitarray.copyChunks copyChunkVectorPublic d s n)
    dest src i

def countOnesInstalled (word : U64) : I64 :=
  JuliaLean.base.int.count_ones word

/-- Empty `circshift!` calls return the original vector after Integer conversion.
Source: `base/bitarray.jl:1425-1444`; generic destination method:
`base/multidimensional.jl:1257-1266`. -/
def CircshiftEmptyAgrees : Prop :=
  ∀ {X : Type} [JuliaLean.base.range.JConvert I64 X] (i : X),
    match JuliaLean.base.range.JConvert.convert (T := I64) i with
    | .error _ => True
    | .ok shift =>
      let dest := vectorBits []
      let src : BitVector := ⟨1, int 0, [int 0]⟩
      let state := initWords []
      let out := (bitVectorCircshiftPublic dest src i).run state
      let alias := vectorBits []
      let inplace := (bitVectorCircshiftInPlace
        (fun d s n => bitVectorCircshiftPublic d s n) alias shift).run state
      out.1 = .ok dest ∧ inplace.1 = .ok alias

/-- `count`, `any`, and `all` agree with logical bits for every valid rank.
Source: `base/bitarray.jl:1439-1447,1715-1745`. -/
def CountAnyAllAgrees : Prop :=
  ∀ {N : Nat} (dims : List I64) (xs : List Bool),
    dims.length = N →
    (∀ d ∈ dims, int 0 ≤ d) →
    dims.foldl (· * ·) (int 1) = int xs.length →
    xs.length < (IntTy.max .i64).toNat / 2 →
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    let state := initWords (encodeBits xs)
    let count := (bitArrayCountIdentity (fun bc init =>
      bitcount (fun n c => n + c) id countOnesInstalled init bc) B (int 0)).run state
    let any := (bitArrayAny B).run state
    let all := (bitArrayAll B).run state
    count.1 = .ok (int (Int.ofNat (countTrue xs))) ∧
      any.1 = .ok (xs.any id) ∧ all.1 = .ok (xs.all id)

/-- Deleting a BitVector clears its logical length and chunk vector.
Source: `base/bitarray.jl:1137-1141`. -/
def BitVectorEmptyAgrees : Prop :=
  ∀ (xs : List Bool), xs.length < (IntTy.max .i64).toNat / 2 →
    let B := vectorBits xs
    match (bitVectorEmptyBang deleteChunkEnd B).run (initWords (encodeBits xs)) with
    | (.ok empty, state) => empty.len = int 0 ∧ (state.contents B.chunks).isEmpty
    | (.error _, _) => False

/-- Valid reshapes preserve all logical bits and expose their requested dimensions.
The same-rank and rank-changing public methods dispatch separately.
Source: `base/bitarray.jl:472-485`; checked dimensions: `base/checked.jl:106-114`. -/
def BitArrayReshapeKeepsBits : Prop :=
  (∀ {N : Nat} (xs : List Bool) (oldDims targetDims : List I64),
    oldDims.length = N → targetDims.length = N →
    (∀ d ∈ oldDims, int 0 ≤ d) → (∀ d ∈ targetDims, int 0 ≤ d) →
    let state := initWords (encodeBits xs)
    let oldChecked := (checkedDimensionsModel oldDims).run state
    let targetChecked := (checkedDimensionsModel targetDims).run state
    if xs.length < (IntTy.max .i64).toNat / 2 ∧
        oldChecked.1 = .ok (int (Int.ofNat xs.length)) ∧
        targetChecked.1 = .ok (int (Int.ofNat xs.length)) then
      let B : BitArray N := ⟨0, int (Int.ofNat xs.length), oldDims⟩
      match (bitArrayReshapeSameRank checkedDimensionsModel
        allocateBitArrayModel B targetDims).run state with
      | (.ok reshaped, state') =>
          bitArrayLength reshaped = int (Int.ofNat xs.length) ∧
          bitArraySize reshaped = targetDims ∧
          bitValues state' reshaped = xs
      | (.error _, _) => False
    else True) ∧
  (∀ {N M : Nat} (xs : List Bool) (oldDims targetDims : List I64),
    N ≠ M → oldDims.length = N → (hDims : targetDims.length = M) →
    (∀ d ∈ oldDims, int 0 ≤ d) → (∀ d ∈ targetDims, int 0 ≤ d) →
    let state := initWords (encodeBits xs)
    let oldChecked := (checkedDimensionsModel oldDims).run state
    let targetChecked := (checkedDimensionsModel targetDims).run state
    if xs.length < (IntTy.max .i64).toNat / 2 ∧
        oldChecked.1 = .ok (int (Int.ofNat xs.length)) ∧
        targetChecked.1 = .ok (int (Int.ofNat xs.length)) then
      let B : BitArray N := ⟨0, int (Int.ofNat xs.length), oldDims⟩
      match (bitArrayReshapeAny checkedDimensionsModel
        (allocateBitArrayModel (N := M)) B targetDims hDims).run state with
      | (.ok reshaped, state') =>
          bitArrayLength reshaped = int (Int.ofNat xs.length) ∧
          bitArraySize reshaped = targetDims ∧
          bitValues state' reshaped = xs
      | (.error _, _) => False
    else True)

/-- Packed storage size is eight bytes per UInt64 chunk.
Source: `base/bitarray.jl:1939-1940`. -/
def BitArraySizeofAgrees : Prop :=
  ∀ {N : Nat} (xs : List Bool) (dims : List I64),
    xs.length < (IntTy.max .i64).toNat / 2 →
    dims.length = N →
    (∀ d ∈ dims, int 0 ≤ d) →
    dims.foldl (· * ·) (int 1) = int xs.length →
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    match (bitArraySizeof (fun chunks => mutableLength chunks) B).run (initWords (encodeBits xs)) with
    | (.ok bytes, _) => bytes = int (Int.ofNat (wordCount xs.length * 8))
    | (.error _, _) => False
end Round2
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
/-! No methods in this file are excluded from the method-to-property table. -/
def nothingToPromise : List (String × String) := [
  ("sizehint!@798", "This call is only a capacity hint and promises no change to the logical bit sequence."),
  ("keepat!@1063", "The overload forwards to the separate Base keep-at implementation; it adds no behavior in this file."),
  ("keepat!@1064", "The overload forwards to the separate Base keep-at implementation; it adds no behavior in this file."),
]

/-- Julia methods and the source-backed properties that cover them. -/
def methodPropertyTable : List (String × List String) := [
  ("length@102", ["BitArrayMetadataAgrees"]),
  ("_div64@115", ["BitArrayIndexAddress", "BitArrayChunkCount"]),
  ("_mod64@116", ["BitArrayIndexAddress", "BitArrayChunkCount"]),
  ("_blsr@117", ["BitArrayIndexAddress", "BitArrayChunkCount"]),
  ("_msk_end@118", ["BitArrayIndexAddress", "BitArrayChunkCount"]),
  ("_msk_end@119", ["BitArrayMetadataAgrees"]),
  ("num_bit_chunks@120", ["BitArrayIndexAddress", "BitArrayChunkCount"]),
  ("BitArray@28", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("get_chunks_id@122", ["BitArrayIndexAddress", "BitArrayChunkCount"]),
  ("glue_src_bitchunks@124", ["BitArrayCopyChunksInBounds"]),
  ("copy_chunks!@135", ["BitArrayCopytoAgrees", "ArrayConversionsKeepBits"]),
  ("copy_chunks_rtol!@189", ["BitArrayCopytoAgrees", "ArrayConversionsKeepBits"]),
  ("fill_chunks!@235", ["BitArrayChunkFill"]),
  ("copy_to_bitarray_chunks!@261", ["BitArrayCopytoAgrees", "ArrayConversionsKeepBits"]),
  ("pack8bools@266", ["BitArrayPackHelpers"]),
  ("copy_to_bitarray_chunks!@274", ["BitArrayPackHelpers"]),
  ("dumpbitcache@347", ["BitArrayMetadataAgrees"]),
  ("iterate@352", ["BitArrayMetadataAgrees"]),
  ("similar@359", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("similar@363", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("similar@366", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("fill!@368", ["ArrayConversionsKeepBits"]),
  ("unsafe_bitgetindex@661", ["ScalarIndexAgrees"]),
  ("_unsafe_bitsetindex!@680", ["ScalarIndexAgrees", "BitArrayChunkInBounds"]),
  ("unsafe_bitsetindex!@675", ["BitArrayIndexAddress", "BitArrayChunkCount"]),
  ("getindex@668", ["ScalarIndexAgrees"]),
  ("setindex!@688", ["ScalarIndexAgrees", "SetindexMaskAgrees"]),
  ("_unsafe_setindex!@707", ["ScalarIndexAgrees", "SetindexMaskAgrees"]),
  ("push!@739", ["DequeAgrees"]),
  ("append!@757", ["AppendPrependAgrees"]),
  ("append!@774", ["AppendPrependAgrees"]),
  ("append!@775", ["AppendPrependAgrees"]),
  ("prepend!@777", ["AppendPrependAgrees"]),
  ("prepend!@795", ["AppendPrependAgrees"]),
  ("prepend!@796", ["AppendPrependAgrees"]),
  ("sizehint!@798", ["NothingToPromise"]),
  ("deleteat!@955", ["DeleteatRangeAgrees", "DeleteatRangeInsideAgrees"]),
  ("_resize_int!@804", ["InsertDeleteAgrees"]),
  ("resize!@803", ["ResizeAgrees", "ResizeNonnegAgrees"]),
  ("pop!@827", ["DequeAgrees"]),
  ("pushfirst!@839", ["DequeAgrees"]),
  ("popfirst!@861", ["DequeAgrees"]),
  ("_insert_int!@885", ["ArrayConversionsKeepBits"]),
  ("insert!@884", ["DequeAgrees", "InsertDeleteAgrees"]),
  ("_deleteat!@913", ["InsertDeleteAgrees"]),
  ("deleteat!@946", ["InsertDeleteAgrees"]),
  ("deleteat!@979", ["DeleteAtIndicesAgrees"]),
  ("deleteat!@1022", ["DeleteAtMaskAgrees"]),
  ("keepat!@1063", ["NothingToPromise"]),
  ("keepat!@1064", ["NothingToPromise"]),
  ("splice!@1126", ["SpliceRemovedAgrees"]),
  ("_splice_int!@1087", ["SpliceRemovedAgrees"]),
  ("splice!@1082", ["SpliceRemovedAgrees"]),
  ("empty!@1137", ["SpliceRemovedAgrees", "Round2.BitVectorEmptyAgrees"]),
  ("unsafe_copyto!@449", ["BitArrayCopytoAgrees", "AbstractArrayCopyAgrees", "BitArrayCopyChunksInBounds", "ArrayConversionsKeepBits"]),
  ("_copyto_int!@456", ["BitArrayCopytoAgrees", "AbstractArrayCopyAgrees", "BitArrayCopyChunksInBounds", "ArrayConversionsKeepBits"]),
  ("_bitreshape@476", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("_copyto_bitarray!@507", ["BitArrayCopytoAgrees", "AbstractArrayCopyAgrees", "BitArrayCopyChunksInBounds", "ArrayConversionsKeepBits"]),
  ("BitArray@500", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("BitArray@498", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("Array@489", ["ScalarIndexAgrees"]),
  ("falses@396", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("falses@397", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("falses@398", ["BitArrayFillConstructors"]),
  ("trues@415", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("trues@416", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("trues@417", ["BitArrayFillConstructors"]),
  ("falses@394", ["BitArrayFillConstructors"]),
  ("falses@395", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("trues@413", ["BitArrayFillConstructors"]),
  ("trues@414", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("one@419", ["BitArrayFillConstructors"]),
  ("fill_bitarray_from_itr!@634", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("gen_bitarray_from_itr@607", ["ResizeAgrees", "ResizeNonnegAgrees"]),
  ("gen_bitarray@573", ["ArrayConversionsKeepBits"]),
  ("gen_bitarray@576", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("gen_bitarray@585", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("gen_bitarray@589", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("gen_bitarray@594", ["ArrayConversionsKeepBits"]),
  ("gen_bitarrayN@596", ["ArrayConversionsKeepBits"]),
  ("gen_bitarrayN@597", ["ArrayConversionsKeepBits"]),
  ("gen_bitarrayN@598", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("gen_bitarrayN@600", ["IteratorConstructorsKeepElements", "IteratorShapeBuilderKeepsElements", "InfiniteIteratorRejected", "IteratorWrongShapeRejected"]),
  ("gen_bitarrayN@601", ["IteratorConstructorsKeepElements", "IteratorShapeBuilderKeepsElements", "InfiniteIteratorRejected", "IteratorWrongShapeRejected"]),
  ("gen_bitarrayN@602", ["IteratorConstructorsKeepElements", "IteratorShapeBuilderKeepsElements", "InfiniteIteratorRejected", "IteratorWrongShapeRejected"]),
  ("BitArray@68", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("BitArray{N}@69", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("BitArray@70", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("BitArray{N}@71", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("BitVector@76", ["BitArrayConstructorShape"]),
  ("BitVector@95", ["TupleConstructorAgrees"]),
  ("size@103", ["BitArrayMetadataAgrees"]),
  ("size@104", ["BitArrayMetadataAgrees"]),
  ("isassigned@106", ["BitArrayMetadataAgrees"]),
  ("IndexStyle@108", ["BitArrayMetadataAgrees"]),
  ("dataids@110", ["BitArrayMetadataAgrees"]),
  ("similar@360", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("similar@361", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("copyto!@429", ["BitArrayCopytoAgrees", "AbstractArrayCopyAgrees", "BitArrayCopyChunksInBounds", "ArrayConversionsKeepBits"]),
  ("copyto!@454", ["BitArrayCopytoAgrees", "AbstractArrayCopyAgrees", "BitArrayCopyChunksInBounds", "ArrayConversionsKeepBits"]),
  ("copyto!@466", ["BitArrayCopytoAgrees", "AbstractArrayCopyAgrees", "BitArrayCopyChunksInBounds", "ArrayConversionsKeepBits"]),
  ("reshape@472", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("reshape@475", ["Round2.BitArrayReshapeKeepsBits"]),
  ("::Type{T}@535", ["BitArrayCopytoAgrees", "ArrayConversionsKeepBits"]),
  ("BitArray@536", ["ArrayConversionsKeepBits"]),
  ("BitArray@566", ["ArrayConversionsKeepBits"]),
  ("BitArray{N}@567", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("convert@569", ["ArrayConversionsKeepBits"]),
  ("indexoffset@694", ["ScalarIndexAgrees"]),
  ("indexoffset@695", ["ScalarIndexAgrees"]),
  ("setindex!@697", ["ScalarIndexAgrees", "SetindexMaskAgrees"]),
  ("setindex!@703", ["ScalarIndexAgrees", "SetindexMaskAgrees"]),
  ("splice!@1066", ["SpliceRemovedAgrees"]),
  ("-@1145", ["BitVectorUnaryMinusAgrees"]),
  ("generated@1177", ["BitArrayConstructorShape", "BitArrayChunkCount"]),
  ("$f@1194", ["ArrayConversionsKeepBits"]),
  ("/@1197", ["ArrayConversionsKeepBits"]),
  ("/@1198", ["ArrayConversionsKeepBits"]),
  ("==@1206", ["BitArrayEqualityAgrees"]),
  ("cmp@1211", ["BitVectorComparisonAgrees"]),
  ("_reverse@1225", ["ReverseDimsAgrees", "ReverseDimsNonemptyAgrees"]),
  ("_reverse@1226", ["ReverseDimsAgrees", "ReverseDimsNonemptyAgrees"]),
  ("_reverse!@1272", ["ReverseAgrees"]),
  ("<<@1326", ["ShiftAgrees"]),
  (">>>@1334", ["ShiftAgrees"]),
  (">>@1377", ["ShiftAgrees"]),
  ("<<@1415", ["ShiftAgrees"]),
  (">>>@1423", ["ShiftAgrees"]),
  ("circshift!@1425", ["Round2.CircshiftEmptyAgrees", "CircshiftNonemptyAgrees"]),
  ("_circshift_int!@1426", ["Round2.CircshiftEmptyAgrees", "CircshiftNonemptyAgrees"]),
  ("circshift!@1444", ["Round2.CircshiftEmptyAgrees", "CircshiftNonemptyAgrees"]),
  ("bitcount@1448", ["CountAgrees", "Round2.CountAnyAllAgrees"]),
  ("_count@1456", ["CountAgrees", "Round2.CountAnyAllAgrees"]),
  ("unsafe_bitfindnext@1458", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("findnext@1478", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("findnextnot@1488", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("findfirstnot@1517", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("findnext@1520", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("findnext@1530", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("_findnext_int@1531", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("unsafe_bitfindprev@1544", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("findprev@1563", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("findprevnot@1570", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("findlastnot@1593", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("findprev@1596", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("findprev@1606", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("_findprev_int@1607", ["FindAgrees", "BitArrayChunkInBounds"]),
  ("findmax@1620", ["FindExtremaAgrees", "Round2.CountAnyAllAgrees"]),
  ("findmin@1633", ["FindExtremaAgrees", "Round2.CountAnyAllAgrees"]),
  ("allindices!@1652", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("allindices!@1661", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("allindices!@1666", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("_overflowind@1674", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("_overflowind@1675", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("_toind@1685", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("_toind@1686", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("findall@1688", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("findall@1717", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("_sum@1721", ["Round2.CountAnyAllAgrees"]),
  ("_sum@1722", ["Round2.CountAnyAllAgrees"]),
  ("all@1724", ["BitArrayMetadataAgrees"]),
  ("any@1736", ["BitArrayMetadataAgrees"]),
  ("minimum@1747", ["FindExtremaAgrees", "Round2.CountAnyAllAgrees"]),
  ("maximum@1748", ["FindExtremaAgrees", "Round2.CountAnyAllAgrees"]),
  ("map@1756", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("map@1757", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("map@1758", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("map@1759", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("map!@1761", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("map!@1762", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("map!@1763", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("map!@1764", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("generated@1776", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("generated@1777", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("bit_map@1783", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("bit_map_constant!@1789", ["BitArrayChunkFill"]),
  ("bit_map!@1795", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("bit_map!@1814", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("filter@1839", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("hcat@1847", ["BitArrayConcatenation", "MatrixHcatAgrees"]),
  ("vcat@1860", ["BitArrayConcatenation", "MatrixHcatAgrees"]),
  ("hcat@1874", ["BitArrayConcatenation", "MatrixHcatAgrees"]),
  ("vcat@1898", ["MatrixVcatAgrees"]),
  ("_cat@1924", ["BitArrayConcatenation", "MatrixHcatAgrees"]),
  ("_cat@1925", ["MapAgrees", "BitArrayFilterAgrees"]),
  ("sizeof@1939", ["Round2.BitArraySizeofAgrees"]),
  ("_split_rest@1941", ["ResizeAgrees", "ResizeNonnegAgrees"]),
]
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch2.Group4

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

theorem shape_wrap64_congr {a b : Int}
    (h : a % 18446744073709551616 = b % 18446744073709551616) :
    wrapInt .i64 a = wrapInt .i64 b := by
  simp only [wrapInt, IntTy.signed, IntTy.bits, ite_true] at *
  omega

theorem shape_wrap64_mod (a : Int) :
    wrapInt .i64 a % 18446744073709551616 = a % 18446744073709551616 := by
  simp only [wrapInt, IntTy.signed, IntTy.bits, ite_true]
  omega

theorem shape_wrap64_mul_left (a b : Int) :
    wrapInt .i64 (wrapInt .i64 a * b) = wrapInt .i64 (a * b) := by
  apply shape_wrap64_congr
  rw [Int.mul_emod, shape_wrap64_mod, ← Int.mul_emod]

theorem shape_int_sub_self (a : I64) : a - a = int 0 := by
  apply Subtype.ext
  change wrapInt .i64 (a.val - a.val) = wrapInt .i64 0
  rw [Int.sub_self]

theorem shape_int_add_zero (a : I64) : a + int 0 = a := by
  apply Subtype.ext
  change wrapInt .i64 (a.val + (int 0).val) = a.val
  have hz : (int 0).val = 0 := rfl
  rw [hz, Int.add_zero]
  exact wrapInt_of_inRange .i64 a.val a.property

theorem shape_int_zero_add (a : I64) : int 0 + a = a := by
  apply Subtype.ext
  change wrapInt .i64 ((int 0).val + a.val) = a.val
  have hz : (int 0).val = 0 := rfl
  rw [hz, Int.zero_add]
  exact wrapInt_of_inRange .i64 a.val a.property

theorem shape_initial_length (words : List (Option U64)) :
    (mutableLength 0).run (MutableMemory.initial words) =
      (.ok (JInt.wrap .i64 words.length), MutableMemory.initial words) := by
  rfl

theorem shape_one_add_sub_one (a : I64) : one + a - one = a := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 (one.val + a.val) - one.val) = a.val
  have hb : -9223372036854775808 ≤ a.val ∧ a.val ≤ 9223372036854775807 := a.property
  have hone : one.val = 1 := rfl
  simp only [hone, wrapInt, IntTy.signed, IntTy.bits, ite_true]
  omega

theorem shape_nat_wrap_le (n : Nat) : (JInt.wrap .i64 (n : Int)).val ≤ n := by
  by_cases h : (n : Int) ≤ IntTy.max .i64
  · change wrapInt .i64 (n : Int) ≤ n
    rw [wrapInt_of_inRange .i64 (n : Int) ⟨by
      simp only [IntTy.min, IntTy.signed, IntTy.bits]
      omega, h⟩]
    omega
  · have hb := (JInt.wrap .i64 (n : Int)).property
    omega

theorem shape_run_pure {α β : Type} (x : β) (s : MutableMemory α) :
    (pure x : JuliaLean.base.array.MutationM α β).run s = (.ok x, s) := rfl

theorem shape_run_bind {α β γ : Type}
    (action : JuliaLean.base.array.MutationM α β)
    (next : β → JuliaLean.base.array.MutationM α γ) (s : MutableMemory α) :
    (action >>= next).run s =
      match action.run s with
      | (.error e, state) => (.error e, state)
      | (.ok x, state) => (next x).run state := by
  simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.bind, Bind.bind]
  cases h : action s with
  | mk r state => cases r <;> rfl

theorem shape_run_get {α : Type} (s : MutableMemory α) :
    (get : JuliaLean.base.array.MutationM α (MutableMemory α)).run s =
      (.ok s, s) := rfl

theorem shape_run_modify {α : Type} (f : MutableMemory α → MutableMemory α)
    (s : MutableMemory α) :
    (modify f : JuliaLean.base.array.MutationM α Unit).run s = (.ok (), f s) := rfl

theorem shape_vector_run {α : Type} (s : MutableMemory α) (handle : Nat) :
    (mutableVector handle).run s =
      match s.arrays[handle]? with
      | none => (.error .bounds, s)
      | some a => (.ok a, s) := by
  simp only [mutableVector, shape_run_bind, shape_run_get]
  cases s.arrays[handle]? <;> rfl

theorem shape_length_run {α : Type} (s : MutableMemory α) (n : I64)
    (h : s.arrays[0]? = some ⟨(0, one), n⟩) :
    (mutableLength 0).run s = (.ok n, s) := by
  simp only [mutableLength, shape_run_bind, shape_vector_run, h, shape_run_pure]


theorem shape_unset_run {α : Type} (s : MutableMemory α) (slots : List (Option α))
    (n : I64) (ha : s.arrays[0]? = some ⟨(0, one), n⟩)
    (hm : s.memories[0]? = some slots) (hn : n.val ≤ (slots.length : Int))
    (j : I64) (hj : 1 ≤ j.val ∧ j.val ≤ n.val) :
    (mutableUnset uint64Layout 0 j).run s = (.ok (), s) := by
  have hin : one ≤ j ∧ j ≤ n := hj
  have hk : (j.val - 1).toNat < slots.length := by omega
  have hmem : 0 < s.memories.length := (List.getElem?_eq_some_iff.mp hm).choose
  have hslot := (List.getElem?_eq_some_iff.mp hm).choose_spec
  have hu : JuliaLean.Proofs.base.array.unsetClears uint64Layout = false := by decide
  have hw := JuliaLean.Proofs.base.array.mutableMemoryUnset_run uint64Layout s 0 slots hm j (by omega)
  simp only [JuliaLean.Proofs.base.array.expectedUnset, hu, Bool.false_eq_true, ite_false,
    List.getElem?_eq_getElem hk, Option.join_some, List.set_getElem_self hk] at hw
  have hself : s.memories.set 0 slots = s.memories := by
    rw [← hslot]
    exact List.set_getElem_self hmem
  simp only [hself] at hw
  simp only [mutableUnset, unsetindexInt, mutableBounds, mutableInBounds,
    mutableLength, mutableMemoryref, mutableRef, shape_run_bind, shape_vector_run,
    ha, shape_run_pure, hin, and_self, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, shape_one_add_sub_one, hw]


theorem shape_unset_loop {α : Type} (n : I64) (js : List I64) :
    ∀ (s : MutableMemory α) (slots : List (Option α)),
      s.arrays[0]? = some ⟨(0, one), n⟩ → s.memories[0]? = some slots →
      n.val ≤ (slots.length : Int) →
      (∀ j ∈ js, 1 ≤ j.val ∧ j.val ≤ n.val) →
      (forIn js PUnit.unit (fun j _ => do
        mutableUnset uint64Layout 0 j
        pure (ForInStep.yield PUnit.unit))).run s =
          (.ok PUnit.unit, s) := by
  induction js with
  | nil =>
    intro s slots _ _ _ _
    exact shape_run_pure _ s
  | cons j js ih =>
    intro s slots ha hm hn hj
    have hstep := shape_unset_run s slots n ha hm hn j (hj j List.mem_cons_self)
    have hrest := ih s slots ha hm hn
      (fun j' hj' => hj j' (List.mem_cons_of_mem _ hj'))
    simp only [List.forIn_cons, shape_run_bind, hstep, shape_run_pure]
    exact hrest

theorem shape_range_mem (n j : I64) (hj : j ∈ intRange one n) :
    1 ≤ j.val ∧ j.val ≤ n.val := by
  simp only [intRange, List.mem_map, List.mem_range] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  have hn : -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 := n.property
  have hone : one.val = 1 := rfl
  have hk' : (k : Int) < n.val := by
    simp only [hone] at hk
    omega
  change 1 ≤ wrapInt .i64 (one.val + (k : Int)) ∧
    wrapInt .i64 (one.val + (k : Int)) ≤ n.val
  rw [wrapInt_of_inRange .i64 _ (by
    change -9223372036854775808 ≤ one.val + (k : Int) ∧
      one.val + (k : Int) ≤ 9223372036854775807
    simp only [hone]
    omega)]
  simp only [hone]
  omega

theorem shape_delete_all {α : Type} (s : MutableMemory α) (slots : List (Option α))
    (n : I64) (ha : s.arrays[0]? = some ⟨(0, one), n⟩)
    (hm : s.memories[0]? = some slots) (hn : n.val ≤ (slots.length : Int)) :
    (deleteend (mutableStorage (MemoryLayoutMetadata.ofRuntime uint64Layout)) pure 0 n).run s =
      (.ok (), {s with arrays := s.arrays.set 0 ⟨(0, one), int 0⟩}) := by
  have hcmp : ¬ JInt.rem .u64 n > JInt.rem .u64 n := Int.lt_irrefl _
  have hloop := shape_unset_loop n (intRange one n) s slots ha hm hn
    (fun j hj => shape_range_mem n j hj)
  simp only [deleteend, mutableStorage, MemoryLayoutMetadata.ofRuntime, shape_run_bind, shape_run_pure,
    shape_length_run s n ha, hcmp, ite_false, shape_int_sub_self,
    shape_int_zero_add, hloop, shape_vector_run, ha, shape_run_modify]

set_option maxRecDepth 10000 in
theorem shape_empty_run (B : BitVector) (s : State) (slots : List (Option U64))
    (n : I64) (hc : B.chunks = 0)
    (ha : s.arrays[0]? = some ⟨(0, one), n⟩)
    (hm : s.memories[0]? = some slots) (hn : n.val ≤ (slots.length : Int)) :
    (bitVectorEmptyBang deleteChunkEnd B).run s =
      (.ok {B with len := int 0}, {s with arrays := s.arrays.set 0 ⟨(0, one), int 0⟩}) := by
  have hd := shape_delete_all s slots n ha hm hn
  unfold BitVector
  simp only [bitVectorEmptyBang, hc, shape_run_bind, shape_length_run s n ha,
    deleteChunkEnd, hd, shape_run_pure]

theorem shape_empty_initial (B : BitVector) (words : List (Option U64)) (hc : B.chunks = 0) :
    (bitVectorEmptyBang deleteChunkEnd B).run (MutableMemory.initial words) =
      (.ok {B with len := int 0},
        {memories := [words ++ List.replicate 32 none],
          arrays := [⟨(0, one), int 0⟩]}) := by
  have hn : (JInt.wrap .i64 (words.length : Int)).val ≤
      ((words ++ List.replicate 32 none).length : Int) := by
    have hle := shape_nat_wrap_le words.length
    simp only [List.length_append, List.length_replicate]
    omega
  exact shape_empty_run B (MutableMemory.initial words)
    (words ++ List.replicate 32 none) (JInt.wrap .i64 words.length) hc rfl rfl hn

theorem shape_empty_observations (B : BitVector) (words : List (Option U64))
    (hc : B.chunks = 0) :
    match (bitVectorEmptyBang deleteChunkEnd B).run (MutableMemory.initial words) with
    | (.ok out, state) => out.len = int 0 ∧ (state.contents B.chunks).isEmpty
    | (.error _, _) => False := by
  rw [shape_empty_initial B words hc]
  rw [hc]
  exact ⟨rfl, rfl⟩


theorem BitarrayBitArraySizeofAgrees_proven :
    JuliaLean.Proofs.base.bitarray.BitArraySizeofAgrees := by
  intro N xs dims _ _
  change (match (bitArraySizeof (fun chunks => mutableLength chunks)
      (BitArray.mk 0 (int xs.length) dims : BitArray N)).run
      (initWords (encodeBits xs)) with
    | (.ok bytes, _) => bytes = int (Int.ofNat (wordCount xs.length * 8))
    | (.error _, _) => False)
  change JInt.wrap .i64 (((encodeBits xs).map some).length : Int) * int 8 =
    int (Int.ofNat (wordCount xs.length * 8))
  simp only [List.length_map, encodeBits, List.length_range]
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 (wordCount xs.length : Int) * (int 8).val) =
    wrapInt .i64 ((wordCount xs.length * 8 : Nat) : Int)
  rw [shape_wrap64_mul_left]
  rfl

theorem shape_zero_volume_hypotheses :
    let oldDims := [int 0, int 1, int 1]
    let newDims := [int 4294967296, int 4294967296, int 0]
    oldDims.length = 3 ∧ newDims.length = 3 ∧
      (∀ d ∈ oldDims, int 0 ≤ d) ∧ (∀ d ∈ newDims, int 0 ≤ d) ∧
      oldDims.foldl (· * ·) (int 1) = int 0 ∧
      newDims.foldl (· * ·) (int 1) = int 0 := by
  decide

/-- A discrepancy in the installed model; the matching Julia call succeeds. -/
theorem shape_zero_volume_model_overflow :
    ((bitArrayReshapeSameRank checkedDimensionsModel allocateBitArrayModel
      (⟨0, int 0, [int 0, int 1, int 1]⟩ : BitArray 3)
      [int 4294967296, int 4294967296, int 0]).run
      (initWords (encodeBits []))).1 = .error .overflow := by
  rfl
end JuliaLean.ChatGPT.Batch2.Group4
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch2.Group4

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

set_option maxRecDepth 2000

theorem bcLoop_nat_value (n : Nat) (h : n ≤ (IntTy.max .i64).toNat) :
    (int (n : Int)).val = n := by
  exact wrapInt_of_inRange .i64 (n : Int) (by
    change -9223372036854775808 ≤ (n : Int) ∧ (n : Int) ≤ 9223372036854775807
    change n ≤ 9223372036854775807 at h
    omega)

theorem bcLoop_get_initial (words : List U64)
    (hbound : words.length ≤ (IntTy.max .i64).toNat) (j : I64)
    (hj : 1 ≤ j.val ∧ j.val ≤ (words.length : Int)) :
    (mutableGet 0 j).run (initWords words) =
      (.ok (words.getD (j.val - 1).toNat (u64 0)), initWords words) := by
  let s := initWords words
  have hlen := bcLoop_nat_value words.length hbound
  have ha : s.arrays[0]? = some ⟨(0, one), int words.length⟩ := by
    simp only [s, initWords, MutableMemory.initial, List.length_map]
    rfl
  have hm : s.memories[0]? = some (words.map some ++ List.replicate 32 none) := rfl
  have hin : 1 ≤ j.val ∧ j ≤ int words.length := by
    change 1 ≤ j.val ∧ j.val ≤ (int words.length).val
    rw [hlen]
    exact hj
  have hk : (j.val - 1).toNat < words.length := by omega
  have haddr : (one.val + j.val - 2).toNat = (j.val - 1).toNat := by
    have hone : one.val = 1 := rfl
    rw [hone]
    exact congrArg Int.toNat (by omega)
  have hget : (words.map some ++ List.replicate 32 none)[(j.val - 1).toNat]? =
      some (some (words.getD (j.val - 1).toNat (u64 0))) := by
    rw [List.getElem?_append_left (by simpa only [List.length_map] using hk)]
    rw [List.getElem?_map, List.getElem?_eq_getElem hk]
    simp only [Option.map_some, List.getElem_eq_getD (u64 0)]
  change (mutableGet 0 j).run s = _
  simp only [mutableGet, shape_run_bind, shape_vector_run, ha, hin, and_self,
    decide_true, Bool.not_true, Bool.false_eq_true, ite_false, memoryRead,
    shape_run_get, hm, shape_run_pure, haddr, hget]
  rfl

theorem bcLoop_forIn {T : Type} (addCount : T → I64 → T) (remCount : T → T)
    (countOnes : U64 → I64) (s : State) (getWord : I64 → U64)
    (indices : List I64) :
    ∀ (init : T),
      (∀ i ∈ indices, (mutableGet 0 i).run s = (.ok (getWord i), s)) →
      (forIn indices init (fun i n => do
        let w ← mutableGet 0 i
        pure (ForInStep.yield (remCount (addCount n (countOnes w)))))).run s =
      (.ok (indices.foldl (fun n i => remCount (addCount n (countOnes (getWord i)))) init), s) := by
  induction indices with
  | nil =>
    intro init _
    rfl
  | cons i indices ih =>
    intro init hget
    simp only [List.forIn_cons, shape_run_bind, hget i List.mem_cons_self,
      shape_run_pure, List.foldl_cons]
    exact ih _ (fun j hj => hget j (List.mem_cons_of_mem _ hj))

theorem bcLoop_range_words (words : List U64)
    (hbound : words.length ≤ (IntTy.max .i64).toNat) :
    (intRange (int 1) (int words.length)).map
      (fun j => words.getD (j.val - 1).toNat (u64 0)) = words := by
  have hlen := bcLoop_nat_value words.length hbound
  have hone : (int 1).val = 1 := rfl
  simp only [intRange, hlen, hone, Int.sub_add_cancel, Int.toNat_natCast, List.map_map]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    have hval : (JInt.wrap .i64 (1 + (i : Int))).val = 1 + (i : Int) := by
      exact wrapInt_of_inRange .i64 (1 + (i : Int)) (by
        change -9223372036854775808 ≤ 1 + (i : Int) ∧
          1 + (i : Int) ≤ 9223372036854775807
        change words.length ≤ 9223372036854775807 at hbound
        omega)
    rw [hval]
    have heq : (1 + (i : Int) - 1).toNat = i := by omega
    rw [heq]
    exact (List.getElem_eq_getD (u64 0)).symm

theorem bcLoop_bitcount_of_loop {T : Type} (addCount : T → I64 → T)
    (remCount : T → T) (countOnes : U64 → I64) (init final : T)
    (s : State) (n : I64)
    (hlen : (mutableLength 0).run s = (.ok n, s))
    (hloop : (forIn (intRange (int 1) n) init (fun i acc => do
      let w ← mutableGet 0 i
      pure (ForInStep.yield (remCount (addCount acc (countOnes w)))))).run s =
      (.ok final, s)) :
    (bitcount addCount remCount countOnes init 0).run s = (.ok final, s) := by
  simp only [bitcount, bitcountLoop, pure_bind, shape_run_bind, hlen, hloop, shape_run_pure]

theorem bcLoop_bitcount_run {T : Type} (addCount : T → I64 → T) (remCount : T → T)
    (countOnes : U64 → I64) (init : T) (words : List U64)
    (hbound : words.length ≤ (IntTy.max .i64).toNat) :
    (bitcount addCount remCount countOnes init 0).run (initWords words) =
      (.ok (words.foldl (fun n w => remCount (addCount n (countOnes w))) init), initWords words) := by
  have hlen := bcLoop_nat_value words.length hbound
  have hrange := bcLoop_range_words words hbound
  have hloop := bcLoop_forIn addCount remCount countOnes (initWords words)
    (fun j => words.getD (j.val - 1).toNat (u64 0))
    (intRange (int 1) (int words.length)) init (by
      intro j hj
      have hb := shape_range_mem (int words.length) j hj
      rw [hlen] at hb
      exact bcLoop_get_initial words hbound j hb)
  have hfold : (intRange (int 1) (int words.length)).foldl
      (fun n j => remCount (addCount n (countOnes (words.getD (j.val - 1).toNat (u64 0))))) init =
      words.foldl (fun n w => remCount (addCount n (countOnes w))) init := by
    have heq := List.foldl_map
      (f := fun j : I64 => words.getD (j.val - 1).toNat (u64 0))
      (g := fun n w => remCount (addCount n (countOnes w))) (init := init)
      (l := intRange (int 1) (int words.length))
    rw [hrange] at heq
    exact heq.symm
  rw [hfold] at hloop
  have hheader : (initWords words).arrays[0]? = some ⟨(0, one), int words.length⟩ := by
    simp only [initWords, MutableMemory.initial, List.length_map]
    rfl
  exact bcLoop_bitcount_of_loop addCount remCount countOnes init _ (initWords words)
    (int words.length) (shape_length_run _ _ hheader) hloop
end JuliaLean.ChatGPT.Batch2.Group4
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch2.Group4

theorem packedGrouping_flatMapRange {α : Type} (width chunks : Nat) (f : Nat → α) :
    (List.range chunks).flatMap
        (fun c => (List.range width).map (fun k => f (c * width + k))) =
      (List.range (chunks * width)).map f := by
  induction chunks with
  | zero =>
    simp only [Nat.zero_mul, List.range_zero, List.flatMap_nil, List.map_nil]
  | succ chunks ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ih,
      Nat.succ_mul, List.range_add, List.map_append, List.map_map]
    rfl

theorem packedGrouping_getDPadded {α : Type} (xs : List α) (d : α) (n : Nat)
    (hn : xs.length ≤ n) :
    (List.range n).map (fun i => xs.getD i d) =
      xs ++ List.replicate (n - xs.length) d := by
  induction xs generalizing n with
  | nil =>
    simp only [List.getD, List.getElem?_nil, Option.getD_none, List.map_const',
      List.length_range, List.length_nil, Nat.sub_zero, List.nil_append]
  | cons x xs ih =>
    cases n with
    | zero => simp only [List.length_cons] at hn; omega
    | succ n =>
      have htail : xs.length ≤ n := by simp only [List.length_cons] at hn; omega
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.getD_cons_zero, List.map_map, Function.comp_def,
        List.getD_cons_succ, List.length_cons, Nat.succ_sub_succ_eq_sub, List.cons_append]
      rw [ih n htail]

theorem packedGrouping_paddingBound (n : Nat) : n ≤ ((n + 63) / 64) * 64 := by
  omega

theorem packedGrouping_bits (xs : List Bool) :
    (List.range ((xs.length + 63) / 64)).flatMap
        (fun c => (List.range 64).map (fun k => xs.getD (c * 64 + k) false)) =
      xs ++ List.replicate (((xs.length + 63) / 64) * 64 - xs.length) false := by
  rw [packedGrouping_flatMapRange 64 ((xs.length + 63) / 64)
    (fun i => xs.getD i false)]
  exact packedGrouping_getDPadded xs false _ (packedGrouping_paddingBound xs.length)

theorem packedGrouping_countIdentity (xs : List Bool) : xs.countP id = xs.count true := by
  rw [List.count_eq_countP]
  congr 1
  funext b
  cases b <;> rfl

theorem packedGrouping_count (xs : List Bool) :
    ((List.range ((xs.length + 63) / 64)).map
      (fun c => (List.range 64).countP (fun k => xs.getD (c * 64 + k) false))).sum =
      xs.count true := by
  have h := congrArg (List.countP id) (packedGrouping_bits xs)
  simpa only [List.countP_flatMap, Function.comp_def, List.countP_map, id_eq,
    List.countP_append, List.countP_replicate, Bool.false_eq_true, ite_false,
    Nat.add_zero, packedGrouping_countIdentity] using h

theorem packedGrouping_any (xs : List Bool) :
    (List.range ((xs.length + 63) / 64)).any
      (fun c => (List.range 64).any (fun k => xs.getD (c * 64 + k) false)) =
      xs.any id := by
  have h := congrArg (fun ys => ys.any id) (packedGrouping_bits xs)
  simpa only [List.any_flatMap, List.any_map, Function.comp_def, id_eq, List.any_append,
    List.any_replicate, ite_self, Bool.or_false] using h

theorem packedGrouping_lastStartBound (n : Nat) :
    (((n + 63) / 64) - 1) * 64 ≤ n := by
  omega

theorem packedGrouping_logicalBits (xs : List Bool) :
    (List.range (((xs.length + 63) / 64) - 1)).flatMap
        (fun c => (List.range 64).map (fun k => xs.getD (c * 64 + k) false)) ++
      (List.range (xs.length - (((xs.length + 63) / 64) - 1) * 64)).map
        (fun k => xs.getD ((((xs.length + 63) / 64) - 1) * 64 + k) false) = xs := by
  rw [packedGrouping_flatMapRange 64 (((xs.length + 63) / 64) - 1)
    (fun i => xs.getD i false)]
  have hlen : (((xs.length + 63) / 64) - 1) * 64 +
      (xs.length - (((xs.length + 63) / 64) - 1) * 64) = xs.length := by
    have := packedGrouping_lastStartBound xs.length
    omega
  have hmap := packedGrouping_getDPadded xs false xs.length (Nat.le_refl xs.length)
  rw [← hlen, List.range_add, List.map_append, List.map_map] at hmap
  simpa only [Function.comp_def, hlen, Nat.sub_self, List.replicate_zero,
    List.append_nil] using hmap

theorem packedGrouping_all (xs : List Bool) :
    ((List.range (((xs.length + 63) / 64) - 1)).all
        (fun c => (List.range 64).all (fun k => xs.getD (c * 64 + k) false)) &&
      (List.range (xs.length - (((xs.length + 63) / 64) - 1) * 64)).all
        (fun k => xs.getD ((((xs.length + 63) / 64) - 1) * 64 + k) false)) =
      xs.all id := by
  have h := congrArg (fun ys => ys.all id) (packedGrouping_logicalBits xs)
  simpa only [List.all_append, List.all_flatMap, List.all_map, Function.comp_def,
    id_eq] using h

theorem packedGrouping_tailBound (n : Nat) :
    n - (((n + 63) / 64) - 1) * 64 ≤ 64 := by
  omega

theorem packedGrouping_all_iff (xs : List Bool) :
    xs.all id = true ↔
      (∀ c, c < ((xs.length + 63) / 64) - 1 →
        ∀ k, k < 64 → xs.getD (c * 64 + k) false = true) ∧
      (∀ k, k < 64 → (((xs.length + 63) / 64) - 1) * 64 + k < xs.length →
        xs.getD ((((xs.length + 63) / 64) - 1) * 64 + k) false = true) := by
  rw [← packedGrouping_all xs]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  have hstart := packedGrouping_lastStartBound xs.length
  have htail := packedGrouping_tailBound xs.length
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro k _ hk
    exact h.2 k (by omega)
  · intro h
    refine ⟨h.1, ?_⟩
    intro k hk
    exact h.2 k (by omega) (by omega)

theorem packedGrouping_mask_iff (xs : List Bool) (start : Nat) :
    (∀ k, k < 64 → xs.getD (start + k) false = decide (start + k < xs.length)) ↔
      (∀ k, k < 64 → start + k < xs.length → xs.getD (start + k) false = true) := by
  constructor
  · intro h k hk hbound
    simpa only [hbound, decide_true] using h k hk
  · intro h k hk
    by_cases hbound : start + k < xs.length
    · simpa only [hbound, decide_true] using h k hk hbound
    · simp only [hbound, decide_false, List.getD,
        List.getElem?_eq_none (by omega : xs.length ≤ start + k), Option.getD_none]

theorem packedGrouping_all_mask_iff (xs : List Bool) :
    xs.all id = true ↔
      (∀ c, c < ((xs.length + 63) / 64) - 1 →
        ∀ k, k < 64 → xs.getD (c * 64 + k) false = true) ∧
      (∀ k, k < 64 →
        xs.getD ((((xs.length + 63) / 64) - 1) * 64 + k) false =
          decide ((((xs.length + 63) / 64) - 1) * 64 + k < xs.length)) := by
  rw [packedGrouping_mask_iff]
  exact packedGrouping_all_iff xs
end JuliaLean.ChatGPT.Batch2.Group4
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray

def packedBit (word : U64) (bit : Nat) : Bool := word.val.toNat.testBit bit

theorem packedInt_val (n : Nat) (hn : n ≤ 9223372036854775807) :
    (int (n : Int)).val = n := by
  change wrapInt .i64 (n : Int) = (n : Int)
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ (n : Int) ∧ (n : Int) ≤ 9223372036854775807
  omega

theorem packedToJInt_val (word : BitVec IntTy.u64.bits) :
    (toJInt .u64 word).val = (word.toNat : Int) := by
  change wrapInt .u64 (word.toNat : Int) = (word.toNat : Int)
  apply wrapInt_of_inRange
  have h := word.isLt
  change word.toNat < 18446744073709551616 at h
  change 0 ≤ (word.toNat : Int) ∧ (word.toNat : Int) ≤ 18446744073709551615
  omega

theorem packedFromJInt_nat (word : U64) :
    (fromJInt word).toNat = word.val.toNat := by
  rw [fromJInt, BitVec.toNat_ofInt]
  change (word.val % 18446744073709551616).toNat = word.val.toNat
  have h := word.property
  have hv : 0 ≤ word.val ∧ word.val < 18446744073709551616 := by
    change 0 ≤ word.val ∧ word.val ≤ 18446744073709551615 at h
    omega
  rw [Int.emod_eq_of_lt hv.1 hv.2]

theorem packedBit_toJInt (word : BitVec IntTy.u64.bits) (bit : Nat) :
    packedBit (toJInt .u64 word) bit = word.getLsbD bit := by
  rw [packedBit, packedToJInt_val, Int.toNat_natCast, BitVec.testBit_toNat]

theorem packedBit_fromJInt (word : U64) (bit : Nat) :
    (fromJInt word).getLsbD bit = packedBit word bit := by
  rw [← BitVec.testBit_toNat, packedFromJInt_nat]
  rfl

theorem packedBit_or (a b : U64) (bit : Nat) :
    packedBit (or_int a b) bit = (packedBit a bit || packedBit b bit) := by
  simp only [or_int, jlOrInt, packedBit_toJInt, BitVec.getLsbD_or,
    packedBit_fromJInt]

theorem packedBit_zero (bit : Nat) : packedBit (u64 0) bit = false := by
  change Nat.testBit 0 bit = false
  exact Nat.zero_testBit bit

theorem packedBit_shift_one (bit k : Nat) (hb : bit < 64) :
    packedBit (shl_int (u64 1) (int (bit : Int))) k = decide (k = bit) := by
  have hi : (fromJInt (int (bit : Int))).toNat = bit := by
    rw [fromJInt, BitVec.toNat_ofInt, packedInt_val bit (by omega)]
    change ((bit : Int) % 18446744073709551616).toNat = bit
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  unfold shl_int
  rw [packedBit_toJInt]
  unfold jlShlInt
  rw [hi, if_neg (show ¬ bit ≥ IntTy.u64.bits by exact Nat.not_le.mpr hb)]
  rw [BitVec.getLsbD_ofNat]
  change (decide (k < 64) && (1 * 2 ^ bit).testBit k) = decide (k = bit)
  rw [Nat.one_mul]
  simp only [Nat.testBit_two_pow, eq_comm (a := bit) (b := k)]
  by_cases hkb : k = bit
  · subst k
    simp only [hb, decide_true, Bool.true_and]
  · simp only [hkb, decide_false, Bool.and_false]

def packedPrefix (xs : List Bool) (chunk n : Nat) : U64 :=
  (List.range n).foldl (fun word bit =>
    if xs.getD (chunk * 64 + bit) false then
      or_int word (shl_int (u64 1) (int (bit : Int)))
    else word) (u64 0)

theorem packedPrefix_bit (xs : List Bool) (chunk n k : Nat) (hn : n ≤ 64) :
    packedBit (packedPrefix xs chunk n) k =
      (decide (k < n) && xs.getD (chunk * 64 + k) false) := by
  induction n with
  | zero =>
    simp only [packedPrefix, List.range_zero, List.foldl_nil, packedBit_zero,
      Nat.not_lt_zero, decide_false, Bool.false_and]
  | succ n ih =>
    have hn64 : n < 64 := by omega
    have hrec := ih (by omega)
    simp only [packedPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    change packedBit (if xs.getD (chunk * 64 + n) false then
      or_int (packedPrefix xs chunk n) (shl_int (u64 1) (int (n : Int)))
      else packedPrefix xs chunk n) k = _
    cases hb : xs.getD (chunk * 64 + n) false
    · simp only [hb, Bool.false_eq_true, ite_false, hrec]
      by_cases hk : k = n
      · subst k
        simp only [hb, Bool.and_false]
      · have : (k < n + 1) = (k < n) := propext (by omega)
        simp only [this]
    · simp only [hb, ite_true, packedBit_or, hrec, packedBit_shift_one n k hn64]
      by_cases hk : k = n
      · subst k
        simp only [Nat.lt_succ_self, decide_true, Bool.or_true, hb, Bool.true_and]
      · have : (k < n + 1) = (k < n) := propext (by omega)
        simp only [hk, decide_false, Bool.or_false, this]

theorem packedPrefix_eq_encode (xs : List Bool) :
    encodeBits xs = (List.range (wordCount xs.length)).map (fun c => packedPrefix xs c 64) := rfl

theorem packedWord_bit (xs : List Bool) (chunk k : Nat) (hk : k < 64) :
    packedBit (packedPrefix xs chunk 64) k = xs.getD (chunk * 64 + k) false := by
  rw [packedPrefix_bit xs chunk 64 k (by omega)]
  simp only [hk, decide_true, Bool.true_and]

theorem packedFold_count (p : Nat) (indices : List Nat) (acc : Nat) :
    indices.foldl (fun r i => r + p / 2 ^ i % 2) acc =
      acc + indices.countP (fun i => p.testBit i) := by
  induction indices generalizing acc with
  | nil => simp only [List.foldl_nil, List.countP_nil, Nat.add_zero]
  | cons i indices ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    have hd : p / 2 ^ i % 2 = if p.testBit i then 1 else 0 := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ i) with h | h
      · simp only [h, Nat.zero_ne_one, decide_false, Bool.false_eq_true, ite_false]
      · simp only [h, decide_true, ite_true]
    rw [hd]
    cases p.testBit i <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem packedCast_val (word : U64) (hw : word.val ≤ 9223372036854775807) :
    (remT .i64 word).val = word.val := by
  change wrapInt .i64 ((BitVec.ofInt 64 word.val).toInt) = word.val
  rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le (by have := word.property.1; change 0 ≤ word.val at this; omega)
    (by omega)]
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ word.val ∧ word.val ≤ 9223372036854775807
  have := word.property.1
  change 0 ≤ word.val at this
  omega

theorem packedCountOnes_val (word : U64) :
    (JuliaLean.base.int.count_ones word).val =
      ((List.range 64).countP (packedBit word) : Int) := by
  have hc : (List.range 64).countP (packedBit word) ≤ 64 :=
    Nat.le_trans List.countP_le_length (by simp only [List.length_range, Nat.le_refl])
  have hct : (ctpop_int word).val =
      ((List.range 64).countP (packedBit word) : Int) := by
    unfold ctpop_int jlCtpopInt
    rw [packedFromJInt_nat, packedFold_count, Nat.zero_add, packedToJInt_val, BitVec.toNat_ofNat]
    change (((List.range 64).countP (packedBit word) % 18446744073709551616 : Nat) : Int) = _
    rw [Nat.mod_eq_of_lt (by change (List.range 64).countP (packedBit word) < 18446744073709551616; omega)]
  rw [JuliaLean.base.int.count_ones, packedCast_val (ctpop_int word) (by rw [hct]; omega), hct]

theorem packedWord_count (xs : List Bool) (chunk : Nat) :
    (JuliaLean.base.int.count_ones (packedPrefix xs chunk 64)).val =
      ((List.range 64).countP (fun k => xs.getD (chunk * 64 + k) false) : Int) := by
  rw [packedCountOnes_val]
  congr 1
  apply List.countP_congr
  intro k hk
  rw [packedWord_bit xs chunk k (List.mem_range.mp hk)]

theorem packedBit_ext {a b : U64}
    (h : ∀ k, k < 64 → packedBit a k = packedBit b k) : a = b := by
  apply Subtype.ext
  have ha := a.property
  have hb := b.property
  change 0 ≤ a.val ∧ a.val ≤ 18446744073709551615 at ha
  change 0 ≤ b.val ∧ b.val ≤ 18446744073709551615 at hb
  have he : a.val.toNat = b.val.toNat := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 64
    · exact h k hk
    · have hk64 : 2 ^ 64 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (by omega : a.val.toNat < 2 ^ k),
        Nat.testBit_lt_two_pow (by omega : b.val.toNat < 2 ^ k)]
  omega

theorem packedBit_max (k : Nat) : packedBit u64Max k = decide (k < 64) := by
  change (2 ^ 64 - 1 : Nat).testBit k = decide (k < 64)
  exact Nat.testBit_two_pow_sub_one 64 k

theorem packedWord_zero_iff (xs : List Bool) (chunk : Nat) :
    packedPrefix xs chunk 64 = u64 0 ↔
      ∀ k, k < 64 → xs.getD (chunk * 64 + k) false = false := by
  constructor
  · intro h k hk
    rw [← packedWord_bit xs chunk k hk, h, packedBit_zero]
  · intro h
    apply packedBit_ext
    intro k hk
    rw [packedWord_bit xs chunk k hk, packedBit_zero, h k hk]

theorem packedWord_max_iff (xs : List Bool) (chunk : Nat) :
    packedPrefix xs chunk 64 = u64Max ↔
      ∀ k, k < 64 → xs.getD (chunk * 64 + k) false = true := by
  constructor
  · intro h k hk
    rw [← packedWord_bit xs chunk k hk, h, packedBit_max]
    exact decide_eq_true hk
  · intro h
    apply packedBit_ext
    intro k hk
    rw [packedWord_bit xs chunk k hk, h k hk, packedBit_max]
    exact (decide_eq_true hk).symm

theorem packedI64_roundtrip_nat (word : BitVec IntTy.i64.bits) :
    (fromJInt (toJInt .i64 word)).toNat = word.toNat := by
  rw [fromJInt, BitVec.toNat_ofInt]
  change (wrapInt .i64 word.toInt % 18446744073709551616).toNat = word.toNat
  have hw (x : Int) : wrapInt .i64 x % 18446744073709551616 = x % 18446744073709551616 := by
    simp only [wrapInt, IntTy.signed, IntTy.bits, ite_true]
    omega
  rw [hw, BitVec.toInt_eq_toNat_bmod]
  change ((word.toNat : Int).bmod 18446744073709551616 % 18446744073709551616).toNat = word.toNat
  have he := Int.bmod_emod (x := (word.toNat : Int)) (m := 18446744073709551616)
  change (word.toNat : Int).bmod 18446744073709551616 % 18446744073709551616 =
    (word.toNat : Int) % 18446744073709551616 at he
  rw [he]
  have hb := word.isLt
  change word.toNat < 18446744073709551616 at hb
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

theorem packedMod64_nat (value : I64) :
    (fromJInt (mod64 value)).toNat = (value.val % 64).toNat := by
  rw [mod64, and_int, packedI64_roundtrip_nat]
  change ((fromJInt value) &&& (BitVec.ofNat IntTy.i64.bits 63)).toNat = _
  rw [BitVec.toNat_and]
  change (fromJInt value).toNat &&& (2 ^ 6 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, fromJInt, BitVec.toNat_ofInt]
  change (value.val % 18446744073709551616).toNat % 64 = (value.val % 64).toNat
  have hm : 0 ≤ value.val % 18446744073709551616 := Int.emod_nonneg _ (by decide)
  have h64 : 0 ≤ value.val % 64 := Int.emod_nonneg _ (by decide)
  have he : value.val % 18446744073709551616 % 64 = value.val % 64 :=
    Int.emod_emod_of_dvd _ (by decide)
  omega

theorem packedMask_bit (n k : Nat) (hn : n ≤ 9223372036854775807) :
    packedBit (maskEnd (int (n : Int))) k =
      decide (k + ((-(n : Int)) % 64).toNat < 64) := by
  have hneg : (-(int (n : Int))).val = -(n : Int) := by
    change wrapInt .i64 (-(int (n : Int)).val) = -(n : Int)
    rw [packedInt_val n hn]
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ -(n : Int) ∧ -(n : Int) ≤ 9223372036854775807
    omega
  have hs : ((-(n : Int)) % 64).toNat < 64 := by
    have := Int.emod_nonneg (-(n : Int)) (by decide : (64 : Int) ≠ 0)
    have := Int.emod_lt_of_pos (-(n : Int)) (by decide : (0 : Int) < 64)
    omega
  unfold maskEnd lshr_int
  rw [packedBit_toJInt]
  unfold jlLshrInt
  rw [packedMod64_nat, hneg, if_neg (show ¬ ((-(n : Int)) % 64).toNat ≥ IntTy.u64.bits
    by exact Nat.not_le.mpr hs)]
  rw [BitVec.getLsbD_ofNat, packedFromJInt_nat,
    Nat.testBit_div_two_pow]
  change (decide (k < 64) && packedBit u64Max (k + ((-(n : Int)) % 64).toNat)) = _
  rw [packedBit_max]
  by_cases hk : k + ((-(n : Int)) % 64).toNat < 64
  · simp only [hk, show k < 64 by omega, decide_true, Bool.true_and]
  · simp only [hk, decide_false, Bool.and_false]

theorem packedMask_last_bit (n k : Nat) (hpos : 0 < n)
    (hn : n ≤ 9223372036854775807) :
    packedBit (maskEnd (int (n : Int))) k =
      decide ((wordCount n - 1) * 64 + k < n) := by
  rw [packedMask_bit n k hn]
  have hs : ((-(n : Int)) % 64).toNat = wordCount n * 64 - n := by
    unfold wordCount
    omega
  rw [hs]
  have he : (k + (wordCount n * 64 - n) < 64) ↔ ((wordCount n - 1) * 64 + k < n) := by
    unfold wordCount
    omega
  simp only [he]

theorem packedWord_last_iff (xs : List Bool) (hpos : 0 < xs.length)
    (hn : xs.length ≤ 9223372036854775807) :
    packedPrefix xs (wordCount xs.length - 1) 64 = maskEnd (int (xs.length : Int)) ↔
      ∀ k, k < 64 → (wordCount xs.length - 1) * 64 + k < xs.length →
        xs.getD ((wordCount xs.length - 1) * 64 + k) false = true := by
  constructor
  · intro he k hk hi
    rw [← packedWord_bit xs (wordCount xs.length - 1) k hk, he,
      packedMask_last_bit xs.length k hpos hn]
    exact decide_eq_true hi
  · intro h
    apply packedBit_ext
    intro k hk
    rw [packedWord_bit xs (wordCount xs.length - 1) k hk,
      packedMask_last_bit xs.length k hpos hn]
    by_cases hi : (wordCount xs.length - 1) * 64 + k < xs.length
    · rw [h k hk hi]
      exact (decide_eq_true hi).symm
    · rw [List.getD_eq_getElem?_getD,
        show xs[(wordCount xs.length - 1) * 64 + k]? = none from List.getElem?_eq_none (by omega),
        Option.getD_none, decide_eq_false hi]

theorem packedInt_add (a b : Int) : int a + int b = int (a + b) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a + wrapInt .i64 b) = wrapInt .i64 (a + b)
  simp only [wrapInt, IntTy.signed, IntTy.bits, ite_true]
  omega

theorem packedWord_count_eq (xs : List Bool) (chunk : Nat) :
    JuliaLean.base.int.count_ones (packedPrefix xs chunk 64) =
      int (((List.range 64).countP (fun k => xs.getD (chunk * 64 + k) false)) : Int) := by
  apply Subtype.ext
  rw [packedWord_count, packedInt_val _ (by
    have hc : (List.range 64).countP (fun k => xs.getD (chunk * 64 + k) false) ≤ 64 :=
      Nat.le_trans List.countP_le_length (by simp only [List.length_range, Nat.le_refl])
    omega)]

theorem packedCount_fold (xs : List Bool) (indices : List Nat) (acc : Int) :
    indices.foldl (fun a c => a + JuliaLean.base.int.count_ones (packedPrefix xs c 64)) (int acc) =
      int (acc + (((indices.map (fun c =>
        (List.range 64).countP (fun k => xs.getD (c * 64 + k) false))).sum) : Int)) := by
  induction indices generalizing acc with
  | nil => simp only [List.foldl_nil, List.map_nil, List.sum_nil, Int.ofNat_zero, Int.add_zero]
  | cons c indices ih =>
    rw [List.foldl_cons, packedWord_count_eq, packedInt_add, ih, List.map_cons, List.sum_cons]
    congr 1
    omega
end JuliaLean.ChatGPT.Batch2.Group4
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch2.Group4

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

theorem packedObserve_intVal (n : Nat) (hn : n ≤ 9223372036854775807) :
    (int (n : Int)).val = n := by
  change wrapInt .i64 (n : Int) = (n : Int)
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ (n : Int) ∧ (n : Int) ≤ 9223372036854775807
  omega

theorem packedObserve_runPure {α : Type} (x : α) (s : MutableMemory U64) :
    (pure x : BitMutationM α).run s = (.ok x, s) := rfl

theorem packedObserve_runBind {α β : Type} (action : BitMutationM α)
    (next : α → BitMutationM β) (s : MutableMemory U64) :
    (action >>= next).run s =
      match action.run s with
      | (.error e, state) => (.error e, state)
      | (.ok x, state) => (next x).run state := by
  simp only [ExceptT.run, ExceptT.bind, ExceptT.mk, StateT.bind, Bind.bind]
  cases h : action s with
  | mk result state => cases result <;> rfl

theorem packedObserve_initialVector (words : List U64) :
    (mutableVector 0).run (initWords words) =
      (.ok ⟨(0, one), int words.length⟩, initWords words) := by
  change ((Except.ok (⟨(0, one), int (words.map some).length⟩ : MutableVector) :
    Except Error MutableVector), initWords words) = _
  rw [List.length_map]

theorem packedObserve_initialMemory (words : List U64) :
    (memoryRead 0).run (initWords words) =
      (.ok (words.map some ++ List.replicate 32 none), initWords words) := rfl

theorem packedObserve_initialLength (words : List U64) :
    (mutableLength 0).run (initWords words) =
      (.ok (int words.length), initWords words) := by
  simp only [mutableLength, packedObserve_runBind, packedObserve_initialVector,
    packedObserve_runPure]

theorem packedObserve_read (words : List U64) (hn : words.length ≤ 9223372036854775807)
    (j : Nat) (hj : j < words.length) :
    (mutableGet 0 (int ((j + 1 : Nat) : Int))).run (initWords words) =
      (.ok words[j], initWords words) := by
  have hi := packedObserve_intVal (j + 1) (by omega)
  have hsize := packedObserve_intVal words.length hn
  have hb : 1 ≤ (int ((j + 1 : Nat) : Int)).val ∧
      int ((j + 1 : Nat) : Int) ≤ int (words.length : Int) := by
    change 1 ≤ (int ((j + 1 : Nat) : Int)).val ∧
      (int ((j + 1 : Nat) : Int)).val ≤ (int (words.length : Int)).val
    rw [hi, hsize]
    omega
  have hidx : (one.val + (int ((j + 1 : Nat) : Int)).val - 2).toNat = j := by
    rw [hi]
    change (1 + ((j + 1 : Nat) : Int) - 2).toNat = j
    omega
  have hget : (words.map some ++ List.replicate 32 none)[j]? = some (some words[j]) := by
    rw [List.getElem?_append_left (by simpa only [List.length_map] using hj)]
    rw [List.getElem?_map, List.getElem?_eq_getElem hj]
    rfl
  simp only [mutableGet, packedObserve_runBind, packedObserve_initialVector,
    hb.1, hb.2, and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    packedObserve_initialMemory, hidx, hget, packedObserve_runPure]

theorem packedObserve_intRange (n : Nat) (hn : n ≤ 9223372036854775807) :
    intRange (int 1) (int (n : Int)) =
      (List.range n).map (fun j => int ((j + 1 : Nat) : Int)) := by
  unfold intRange
  rw [packedObserve_intVal n hn]
  have hlen : (((n : Int) - (int 1).val + 1).toNat) = n := by
    change (((n : Int) - 1 + 1).toNat) = n
    omega
  rw [hlen]
  apply List.map_congr_left
  intro j _
  apply Subtype.ext
  change wrapInt .i64 (1 + (j : Int)) = wrapInt .i64 ((j + 1 : Nat) : Int)
  congr 1
  omega

theorem packedObserve_loop {I : Type} (predicate : U64 → Bool) (answer : Bool)
    (read : I → BitMutationM U64) (s : MutableMemory U64) (f : I → U64) :
    ∀ (indices : List I),
      (∀ i ∈ indices, (read i).run s = (.ok (f i), s)) →
      (forIn indices (none, ()) (fun i (_ : Option Bool × Unit) => do
        let value ← read i
        if predicate value then pure (ForInStep.done (some answer, ()))
        else pure (ForInStep.yield (none, ())))).run s =
        (.ok (if indices.any (fun i => predicate (f i)) then (some answer, ())
          else (none, ())), s) := by
  intro indices
  induction indices with
  | nil => intro _; rfl
  | cons i indices ih =>
    intro hread
    have hfirst := hread i List.mem_cons_self
    have hrest := ih (fun j hj => hread j (List.mem_cons_of_mem _ hj))
    rw [List.forIn_cons, packedObserve_runBind, packedObserve_runBind, hfirst]
    cases hp : predicate (f i) <;>
      simp only [hp, Bool.false_eq_true, ite_false, ite_true,
        packedObserve_runPure, hrest, List.any_cons, Bool.false_or, Bool.true_or]

theorem packedObserve_getDPrefix (words : List U64) (n : Nat) (hn : n ≤ words.length) :
    (List.range n).map (fun j => words.getD j (u64 0)) = words.take n := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, Nat.min_eq_left hn]
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    exact (List.getElem_eq_getD _).symm

theorem packedObserve_initialLoop (predicate : U64 → Bool) (answer : Bool)
    (words : List U64) (hwords : words.length ≤ 9223372036854775807)
    (n : Nat) (hn : n ≤ words.length) :
    (forIn (intRange (int 1) (int (n : Int))) (none, ())
      (fun i (_ : Option Bool × Unit) => do
        let value ← mutableGet 0 i
        if predicate value then pure (ForInStep.done (some answer, ()))
        else pure (ForInStep.yield (none, ())))).run (initWords words) =
      (.ok (if (words.take n).any predicate then (some answer, ())
        else (none, ())), initWords words) := by
  rw [packedObserve_intRange n (by omega), List.forIn_map]
  have hreads : ∀ j ∈ List.range n,
      (mutableGet 0 (int ((j + 1 : Nat) : Int))).run (initWords words) =
        (.ok (words.getD j (u64 0)), initWords words) := by
    intro j hj
    have hjn := List.mem_range.mp hj
    have hjw : j < words.length := by omega
    rw [packedObserve_read words hwords j hjw, ← List.getElem_eq_getD]
  rw [packedObserve_loop predicate answer
    (fun j => mutableGet 0 (int ((j + 1 : Nat) : Int))) (initWords words)
    (fun j => words.getD j (u64 0)) (List.range n) hreads]
  have hany : (List.range n).any (fun j => predicate (words.getD j (u64 0))) =
      (words.take n).any predicate := by
    rw [← packedObserve_getDPrefix words n hn, List.any_map]
    rfl
  rw [hany]

theorem packedObserve_anyResult {N : Nat} (B : BitArray N) (s : State)
    (nc : I64) (result : Bool) (hne : (B.len == int 0) = false)
    (hsize : (mutableLength B.chunks).run s = (.ok nc, s))
    (hloop : (forIn (intRange (int 1) nc) (none, ())
      (fun i (_ : Option Bool × Unit) => do
        let value ← mutableGet B.chunks i
        if value != u64 0 then pure (ForInStep.done (some true, ()))
        else pure (ForInStep.yield (none, ())))).run s =
      (.ok (if result then (some true, ()) else (none, ())), s)) :
    (bitArrayAny B).run s = (.ok result, s) := by
  simp only [bitArrayAny, hne, Bool.false_eq_true, ite_false, packedObserve_runBind,
    hsize, hloop]
  cases result <;> rfl

theorem packedObserve_any {N : Nat} (len : I64) (dims : List I64)
    (words : List U64) (hlen : len ≠ int 0)
    (hwords : words.length ≤ 9223372036854775807) :
    (bitArrayAny (⟨0, len, dims⟩ : BitArray N)).run (initWords words) =
      (.ok (words.any (fun word => word != u64 0)), initWords words) := by
  have hne : (len == int 0) = false := beq_eq_false_iff_ne.mpr hlen
  have hloop := packedObserve_initialLoop (fun word => word != u64 0) true
    words hwords words.length (Nat.le_refl _)
  simp only [List.take_length] at hloop
  exact packedObserve_anyResult (⟨0, len, dims⟩ : BitArray N) (initWords words)
    (int words.length) (words.any (fun word => word != u64 0)) hne
    (packedObserve_initialLength words) hloop

theorem packedObserve_subOne (n : Nat) (hn : n ≤ 9223372036854775807) (hpos : 0 < n) :
    int (n : Int) - int 1 = int ((n - 1 : Nat) : Int) := by
  apply Subtype.ext
  change wrapInt .i64 ((int (n : Int)).val - (int 1).val) =
    (int ((n - 1 : Nat) : Int)).val
  rw [packedObserve_intVal n hn, packedObserve_intVal (n - 1) (by omega)]
  have hbound : IntTy.min .i64 ≤ (n : Int) - (int 1).val ∧
      (n : Int) - (int 1).val ≤ IntTy.max .i64 := by
    change -9223372036854775808 ≤ (n : Int) - 1 ∧
      (n : Int) - 1 ≤ 9223372036854775807
    omega
  rw [wrapInt_of_inRange .i64 _ hbound]
  change (n : Int) - 1 = ((n - 1 : Nat) : Int)
  omega

theorem packedObserve_allResult {N : Nat} (B : BitArray N) (s : State)
    (nc : I64) (prefixOK : Bool) (last : U64) (hne : (B.len == int 0) = false)
    (hsize : (mutableLength B.chunks).run s = (.ok nc, s))
    (hloop : (forIn (intRange (int 1) (nc - int 1)) (none, ())
      (fun i (_ : Option Bool × Unit) => do
        let value ← mutableGet B.chunks i
        if value != u64Max then pure (ForInStep.done (some false, ()))
        else pure (ForInStep.yield (none, ())))).run s =
      (.ok (if !prefixOK then (some false, ()) else (none, ())), s))
    (hlast : (mutableGet B.chunks nc).run s = (.ok last, s)) :
    (bitArrayAll B).run s = (.ok (prefixOK && (last == maskEndArray B)), s) := by
  simp only [bitArrayAll, hne, Bool.false_eq_true, ite_false, packedObserve_runBind,
    hsize, hloop]
  cases prefixOK
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, packedObserve_runBind,
      hlast, Bool.true_and]
    change (if (!(last == maskEndArray B)) = true then
      (pure false : BitMutationM Bool) else pure true).run s =
        (.ok (last == maskEndArray B), s)
    cases heq : last == maskEndArray B <;>
      simp only [heq, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ite_true, ite_false, packedObserve_runPure]

theorem packedObserve_all {N : Nat} (len : I64) (dims : List I64)
    (words : List U64) (hlen : len ≠ int 0)
    (hwords : words.length ≤ 9223372036854775807) (hpos : 0 < words.length) :
    (bitArrayAll (⟨0, len, dims⟩ : BitArray N)).run (initWords words) =
      (.ok ((words.take (words.length - 1)).all (fun word => word == u64Max) &&
        (words.getD (words.length - 1) (u64 0) == maskEndArray
          (⟨0, len, dims⟩ : BitArray N))), initWords words) := by
  have hne : (len == int 0) = false := beq_eq_false_iff_ne.mpr hlen
  have hloop := packedObserve_initialLoop (fun word => word != u64Max) false
    words hwords (words.length - 1) (by omega)
  have hcomp : (words.take (words.length - 1)).any (fun word => word != u64Max) =
      !(words.take (words.length - 1)).all (fun word => word == u64Max) :=
    List.not_all_eq_any_not.symm
  rw [hcomp, ← packedObserve_subOne words.length hwords hpos] at hloop
  have hlast : (mutableGet 0 (int (words.length : Int))).run (initWords words) =
      (.ok (words.getD (words.length - 1) (u64 0)), initWords words) := by
    have h := packedObserve_read words hwords (words.length - 1) (by omega)
    rw [show words.length - 1 + 1 = words.length by omega] at h
    rw [← List.getElem_eq_getD]
    exact h
  exact packedObserve_allResult (⟨0, len, dims⟩ : BitArray N) (initWords words)
    (int words.length) ((words.take (words.length - 1)).all (fun word => word == u64Max))
    (words.getD (words.length - 1) (u64 0)) hne (packedObserve_initialLength words)
    hloop hlast

theorem packedObserve_anyZero {N : Nat} (dims : List I64) (s : State) :
    (bitArrayAny (⟨0, int 0, dims⟩ : BitArray N)).run s = (.ok false, s) := rfl

theorem packedObserve_allZero {N : Nat} (dims : List I64) (s : State) :
    (bitArrayAll (⟨0, int 0, dims⟩ : BitArray N)).run s = (.ok true, s) := rfl
end JuliaLean.ChatGPT.Batch2.Group4
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch2.Group4

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray

set_option maxRecDepth 4096

theorem packedEncoded_length (xs : List Bool) :
    (encodeBits xs).length = wordCount xs.length := by
  rw [packedPrefix_eq_encode, List.length_map, List.length_range]

theorem packedEncoded_lengthBound (xs : List Bool)
    (hn : xs.length ≤ (IntTy.max .i64).toNat) :
    (encodeBits xs).length ≤ (IntTy.max .i64).toNat := by
  rw [packedEncoded_length]
  change xs.length ≤ 9223372036854775807 at hn
  change (xs.length + 63) / 64 ≤ 9223372036854775807
  omega

theorem packedEncoded_countFold (xs : List Bool) :
    (encodeBits xs).foldl (fun n word => n + JuliaLean.base.int.count_ones word) (int 0) =
      int (countTrue xs : Int) := by
  rw [packedPrefix_eq_encode, List.foldl_map]
  rw [packedCount_fold]
  change int (0 + (((List.range ((xs.length + 63) / 64)).map (fun c =>
    (List.range 64).countP (fun k => xs.getD (c * 64 + k) false))).sum : Int)) = _
  rw [packedGrouping_count, Int.zero_add]
  rfl

theorem packedWord_nonzero (xs : List Bool) (chunk : Nat) :
    (packedPrefix xs chunk 64 != u64 0) =
      (List.range 64).any (fun k => xs.getD (chunk * 64 + k) false) := by
  apply Bool.eq_iff_iff.mpr
  rw [bne_iff_ne, List.any_eq_true]
  simp only [ne_eq, packedWord_zero_iff, List.mem_range, Classical.not_forall,
    Bool.not_eq_false, exists_prop]

theorem packedEncoded_any (xs : List Bool) :
    (encodeBits xs).any (fun word => word != u64 0) = xs.any id := by
  rw [packedPrefix_eq_encode, List.any_map]
  have he : (fun c => packedPrefix xs c 64 != u64 0) =
      (fun c => (List.range 64).any (fun k => xs.getD (c * 64 + k) false)) := by
    funext c
    exact packedWord_nonzero xs c
  change (List.range (wordCount xs.length)).any (fun c => packedPrefix xs c 64 != u64 0) = _
  rw [he]
  exact packedGrouping_any xs

theorem packedEncoded_take (xs : List Bool) (n : Nat) (hn : n ≤ wordCount xs.length) :
    (encodeBits xs).take n = (List.range n).map (fun c => packedPrefix xs c 64) := by
  rw [packedPrefix_eq_encode, ← List.map_take, List.take_range, Nat.min_eq_left hn]

theorem packedEncoded_last (xs : List Bool) (hpos : 0 < xs.length) :
    (encodeBits xs).getD ((encodeBits xs).length - 1) (u64 0) =
      packedPrefix xs (wordCount xs.length - 1) 64 := by
  rw [packedEncoded_length]
  have hc : wordCount xs.length - 1 < wordCount xs.length := by
    unfold wordCount
    omega
  rw [← List.getElem_eq_getD (h := by rw [packedEncoded_length]; exact hc)]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]

theorem packedEncoded_all {N : Nat} (xs : List Bool) (dims : List I64)
    (hpos : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    (((encodeBits xs).take ((encodeBits xs).length - 1)).all (fun word => word == u64Max) &&
      ((encodeBits xs).getD ((encodeBits xs).length - 1) (u64 0) == maskEndArray
        (⟨0, int xs.length, dims⟩ : BitArray N))) = xs.all id := by
  rw [packedEncoded_last xs hpos]
  rw [packedEncoded_length, packedEncoded_take xs (wordCount xs.length - 1) (by omega)]
  simp only [List.all_map]
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
  simp only [Function.comp_def, List.mem_range, beq_iff_eq, maskEndArray, bitArrayLength,
    packedWord_max_iff, packedWord_last_iff xs hpos hn]
  exact (packedGrouping_all_iff xs).symm

theorem packedResult_projection {T : Type} (action : BitMutationM T)
    (state : State) (answer : T)
    (hr : action.run state = (.ok answer, state)) :
    (action.run state).1 = .ok answer := congrArg Prod.fst hr

theorem packedCount_result {N : Nat} (B : BitArray N) (state : State) (answer : I64)
    (hr : (bitcount (fun n c : I64 => n + c) id JuliaLean.base.int.count_ones
      (int 0) B.chunks).run state = (.ok answer, state)) :
    ((bitArrayCountIdentity (fun bc init => bitcount
      (fun n c => n + c) id JuliaLean.base.int.count_ones init bc) B (int 0)).run state).1 =
      .ok answer := by
  exact packedResult_projection _ state answer hr

theorem BitarraysCountAnyAll_proven : JuliaLean.Proofs.base.bitarray.CountAnyAllAgrees := by
  intro N dims xs _ _ _ hbound
  have hwordBound := packedEncoded_lengthBound xs hbound
  have hn : xs.length ≤ 9223372036854775807 := hbound
  have hw : (encodeBits xs).length ≤ 9223372036854775807 := hwordBound
  have hc := bcLoop_bitcount_run (fun n c : I64 => n + c) id
    JuliaLean.base.int.count_ones (int 0) (encodeBits xs) hwordBound
  simp only [id_eq, packedEncoded_countFold] at hc
  refine ⟨packedCount_result (⟨0, int xs.length, dims⟩ : BitArray N)
    (initWords (encodeBits xs)) (int (countTrue xs : Int)) hc, ?_⟩
  by_cases hempty : xs = []
  · subst xs
    exact ⟨rfl, rfl⟩
  · have hpos : 0 < xs.length := List.length_pos_iff.mpr hempty
    have hlen : int xs.length ≠ int 0 := by
      intro he
      have hv := congrArg Subtype.val he
      rw [packedInt_val xs.length hn] at hv
      change (xs.length : Int) = 0 at hv
      omega
    have hwordsPos : 0 < (encodeBits xs).length := by
      rw [packedEncoded_length]
      unfold wordCount
      omega
    have ha := packedObserve_any (N := N) (int xs.length) dims (encodeBits xs) hlen hw
    rw [packedEncoded_any] at ha
    have hall := packedObserve_all (N := N) (int xs.length) dims (encodeBits xs) hlen hw hwordsPos
    rw [packedEncoded_all xs dims hpos hn] at hall
    exact ⟨packedResult_projection _ _ _ ha, packedResult_projection _ _ _ hall⟩
end JuliaLean.ChatGPT.Batch2.Group4
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch2.Group4

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

theorem emptyFrozenMatch (B : (BitArray 1)) (slots : List (Option U64))
    (result : Except Error (BitArray 1) × State)
    (hr : result = (.ok { B with len := int 0 },
      { memories := [slots], arrays := [⟨(0, one), int 0⟩] }))
    (hc : B.chunks = 0) :
    JuliaLean.Proofs.base.bitarray.DeleteatRangeInsideAgrees.match_1
      (fun _ => Prop) result
      (fun empty state => empty.len = int 0 ∧ (state.contents B.chunks).isEmpty)
      (fun _ _ => False) := by
  rw [hr, hc]
  exact ⟨rfl, rfl⟩

theorem emptyInitialFrozen (B : (BitArray 1)) (words : List (Option U64))
    (hc : B.chunks = 0) :
    JuliaLean.Proofs.base.bitarray.DeleteatRangeInsideAgrees.match_1
      (fun _ => Prop)
      ((bitVectorEmptyBang deleteChunkEnd B).run (MutableMemory.initial words))
      (fun empty state => empty.len = int 0 ∧ (state.contents B.chunks).isEmpty)
      (fun _ _ => False) :=
  emptyFrozenMatch B
    (words ++ List.replicate 32 none)
    ((bitVectorEmptyBang deleteChunkEnd B).run (MutableMemory.initial words))
    (shape_empty_initial B words hc) hc

set_option maxRecDepth 4096 in
theorem emptyWordsFrozen (B : (BitArray 1)) (words : List U64) (hc : B.chunks = 0) :
    JuliaLean.Proofs.base.bitarray.DeleteatRangeInsideAgrees.match_1
      (fun _ => Prop)
      ((bitVectorEmptyBang deleteChunkEnd B).run (initWords words))
      (fun empty state => empty.len = int 0 ∧ (state.contents B.chunks).isEmpty)
      (fun _ _ => False) :=
  emptyInitialFrozen B (words.map some) hc

theorem BitarrayBitVectorEmptyAgrees_proven :
    JuliaLean.Proofs.base.bitarray.BitVectorEmptyAgrees := by
  intro xs
  dsimp only
  generalize hb : vectorBits xs = B
  generalize hw : encodeBits xs = words
  have hc : B.chunks = 0 := by
    rw [← hb]
    rfl
  exact emptyWordsFrozen B words hc
end JuliaLean.ChatGPT.Batch2.Group4
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray

theorem Round2.CountAnyAllAgrees_proven : Round2.CountAnyAllAgrees := by
  intro N dims xs hdims hnonnegative hshape hbound
  apply JuliaLean.ChatGPT.Batch2.Group4.BitarraysCountAnyAll_proven dims xs hdims hnonnegative hshape
  exact Nat.le_trans (Nat.le_of_lt hbound) (Nat.div_le_self _ _)

theorem Round2.BitArraySizeofAgrees_proven : Round2.BitArraySizeofAgrees := by
  intro N xs dims _ hdims _ hshape
  exact JuliaLean.ChatGPT.Batch2.Group4.BitarrayBitArraySizeofAgrees_proven xs dims hdims hshape
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace Round5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

def maxVectorLength : Nat := (IntTy.max .i64).toNat / 2
end Round5
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace Round5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
namespace Round2

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

abbrev State := JuliaLean.Proofs.base.bitarray.State

def PackedInvariant {N : Nat} (s : State) (B : BitArray N) : Prop :=
  (s.contents B.chunks).length = (numBitChunks B.len).val.toNat ∧
  (if B.len == int 0 then True else
    match (s.contents B.chunks).getLast? with
    | some (some word) => and_int word (not_int (maskEndArray B)) = u64 0
    | _ => False)

def fillChunkVectorModel (chunks : Nat) (word : U64) : BitMutationM Unit := do
  let _ ← JuliaLean.base.array.fillTyped
    (fun (handle : Nat) => do
      let n ← mutableLength handle
      pure (intRange (int 1) n))
    (fun handle value i => mutableSet handle value i)
    chunks word
  pure ()

def checkBitArrayBounds {N : Nat} (B : BitArray N) (i : I64) : BitMutationM Unit := do
  let indices := fun (a : BitArray N) =>
    JuliaLean.base.abstractarray.eachindexLinear
      (fun value => Except.ok value.len)
      (fun n => Except.ok (⟨n⟩ : JuliaLean.base.range.OneTo I64)) a
  let checked := JuliaLean.base.abstractarray.checkboundsOne indices
    (fun range j => Except.ok (JuliaLean.base.abstractarray.checkindexOneTo range.stop j)) B i
  match checked with
  | .ok true => pure ()
  | .ok false => throw .bounds
  | .error _ => throw .bounds

def checkBitVectorBounds (B : BitVector) (i : I64) : BitMutationM Unit :=
  checkBitArrayBounds B i

def mutationErrorOfRange : JuliaLean.base.range.Exc → JuliaLean.base.array.Error
  | .jl (.overflowError _) => .overflow
  | .jl (.argumentError message) => .argument message
  | .jl .boundsError => .bounds
  | .jl (.inexactError _) => .inexact
  | .jl .divideError => .divide
  | .jl (.domainError message) => .argument message
  | .jl (.methodError name) => .method name
  -- This BitArray range path has no EOF-producing call.
  | .jl .eofError => .method "EOFError"
  | .errorException message => .argument message
  | .dimensionMismatch message => .dimensionMismatch message
  | .showError error => .showError error
  | .inboundsViolation => .bounds

def liftRangeResult {α : Type} (result : JuliaLean.base.range.JlX α) : BitMutationM α :=
  match result with
  | .ok value => pure value
  | .error error => throw (mutationErrorOfRange error)

def convertBoolMutation {X : Type} [JuliaLean.base.range.JConvert Bool X]
    (x : X) : BitMutationM Bool :=
  liftRangeResult (JuliaLean.base.range.JConvert.convert (T := Bool) x)

def installedBitRangeLength (r : BitRange) : BitMutationM I64 :=
  liftRangeResult (JuliaLean.Proofs.base.range.lengthUnit
    (⟨r.first, r.last⟩ : JuliaLean.base.range.UnitRange I64))

def deleteBitRangePublic (B : BitVector) (r : BitRange) : BitMutationM BitVector := do
  let rangeLength ← installedBitRangeLength r
  bitVectorDeleteRange (fun _ => rangeLength) B r

def resizeBitVectorPublic {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (B : BitVector) (n : X) (first : Bool) : BitMutationM BitVector := do
  let n64 ← liftRangeResult (JuliaLean.base.range.JConvert.convert (T := I64) n)
  if n64 < int 0 ∨ B.len ≤ n64 then
    bitVectorResize (fun _ => n64) B n64 first (fun _ => int 0)
  else
    let r := if first then ⟨int 1, B.len - n64⟩ else ⟨n64 + int 1, B.len⟩
    let rangeLength ← installedBitRangeLength r
    bitVectorResize (fun _ => n64) B n64 first (fun _ => rangeLength)

def allocateBitArrayModel {N : Nat} (dims : List I64) : BitMutationM (BitArray N) :=
  JuliaLean.Proofs.base.bitarray.allocateBitArrayModel dims

def allocateMatrixModel (rows cols : I64) : BitMutationM BitMatrix :=
  allocateBitArrayModel [rows, cols]

def copyBitVectorPublic (B : BitVector) : BitMutationM BitVector :=
  JuliaLean.base.abstractarray.copyMutableArray
    (JuliaLean.base.bitarray.similarBitArray allocateBitArrayModel)
    (fun dest src => bitArrayCopyto dest src)
    B

def zeroBitVectorModel (n : I64) : BitMutationM BitVector :=
  JuliaLean.base.bitarray.falsesIntegerDims allocateBitArrayModel
    (fun B value => fillBitArray convertBoolMutation fillChunkVectorModel B value)
    [n]

def shiftLeftUnsignedModel (B : BitVector) (i : U64) : BitMutationM BitVector :=
  bitVectorShiftLeftUnsigned JuliaLean.base.int.unsigned (fun x => int x.val)
    copyBitVectorPublic zeroBitVectorModel B i

def shiftRightUnsignedModel (B : BitVector) (i : U64) : BitMutationM BitVector :=
  bitVectorShiftRightUnsigned JuliaLean.base.int.unsigned (fun x => int x.val)
    copyBitVectorPublic zeroBitVectorModel B i

def shiftRightSignedArgModel (B : BitVector) (i : I64) : BitMutationM BitVector :=
  shiftRightUnsignedModel B (JuliaLean.base.int.unsigned i)

def shiftLeftSignedArgModel (B : BitVector) (i : I64) : BitMutationM BitVector :=
  shiftLeftUnsignedModel B (JuliaLean.base.int.unsigned i)

def isOddIntegerModel (n : I64) : Bool :=
  JuliaLean.base.int.isodd_Real JuliaLean.base.number.isintegerInteger id
    (fun value _ => JuliaLean.base.int.rem_Integer_Bool value) (fun remainder => !remainder) n

def ScalarIndexAgrees {N : Nat} (xs : List Bool) (dims : List I64) (i : I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (_hRank : dims.length = N)
    (_hSize : dims.foldl (· * ·) (int 1) = int xs.length) : Prop :=
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    let s := initWords (encodeBits xs)
    let read := (bitArrayGetIndex checkBitArrayBounds B i).run s
    let written := (bitArraySetIndex checkBitArrayBounds convertBoolMutation B x i).run s
    if int 1 ≤ i ∧ i ≤ B.len then
      read.1 = .ok (bitAt s B (i.val.toNat - 1)) ∧
      match JuliaLean.base.range.JConvert.convert (T := Bool) x, written.1 with
      | .ok value, .ok _ =>
          bitValues written.2 B = (bitValues s B).set (i.val.toNat - 1) value ∧
          PackedInvariant written.2 B
      | .error _, .error _ => written.2 = s
      | _, _ => False
    else read.1 = .error .bounds ∧ written.1 = .error .bounds ∧ written.2 = s

def DequeAgrees (xs : List Bool) {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X) : Prop :=
    match JuliaLean.base.range.JConvert.convert (T := Bool) x with
    | .error _ =>
        let B := vectorBits xs
        let s := initWords (encodeBits xs)
        let push := (bitVectorPush convertBoolMutation checkBitVectorBounds B x).run s
        let pushfront := (bitVectorPushfirst convertBoolMutation B x).run s
        (match push.1 with | .error _ => push.2 = s | .ok _ => False) ∧
        (match pushfront.1 with | .error _ => pushfront.2 = s | .ok _ => False)
    | .ok value =>
      let B := vectorBits xs
      let s := initWords (encodeBits xs)
      let push := (bitVectorPush convertBoolMutation checkBitVectorBounds B x).run s
      let pushfront := (bitVectorPushfirst convertBoolMutation B x).run s
      let pop := (bitVectorPop (bitArrayGetIndex checkBitVectorBounds)
        (bitArraySetIndex checkBitVectorBounds convertBoolMutation) B).run s
      let popfront := (bitVectorPopfirst B).run s
      if xs.isEmpty then
        (match push.1, pushfront.1 with
         | .ok pushed, .ok front =>
             bitValues push.2 pushed = [value] ∧ bitValues pushfront.2 front = [value] ∧
             PackedInvariant push.2 pushed ∧ PackedInvariant pushfront.2 front
         | _, _ => False) ∧
        (match pop.1 with | .error _ => pop.2 = s | .ok _ => False) ∧
        (match popfront.1 with | .error _ => popfront.2 = s | .ok _ => False)
      else
        match push.1, pushfront.1, pop.1, popfront.1 with
        | .ok pushed, .ok front, .ok (popped, last), .ok (frontPopped, first) =>
            bitValues push.2 pushed = xs ++ [value] ∧
            bitValues pushfront.2 front = value :: xs ∧
            last = xs.getD (xs.length - 1) false ∧
            bitValues pop.2 popped = xs.take (xs.length - 1) ∧
            first = xs.headD false ∧
            bitValues popfront.2 frontPopped = xs.drop 1 ∧
            PackedInvariant push.2 pushed ∧ PackedInvariant pushfront.2 front ∧
            PackedInvariant pop.2 popped ∧ PackedInvariant popfront.2 frontPopped
        | _, _, _, _ => False

def InsertDeleteAgrees (xs : List Bool) (i : I64) {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X) : Prop :=
    let B := vectorBits xs
    let s := initWords (encodeBits xs)
    let inserted := (bitVectorInsert id (bitVectorInsertInt convertBoolMutation) B i x).run s
    let deleted := (bitVectorDeleteAt (fun _ : I64 => false) (fun _ => pure ()) id B i).run s
    (int 1 ≤ i ∧ i ≤ int (Int.ofNat (xs.length + 1))) →
      (match JuliaLean.base.range.JConvert.convert (T := Bool) x with
       | .error _ => match inserted.1 with | .error _ => inserted.2 = s | .ok _ => False
       | .ok value =>
         match inserted.1 with
         | .ok B' => bitValues inserted.2 B' =
             xs.take (i.val.toNat - 1) ++ [value] ++ xs.drop (i.val.toNat - 1) ∧
             PackedInvariant inserted.2 B'
         | .error _ => False) ∧
      (if int 1 ≤ i ∧ i ≤ int (Int.ofNat xs.length) then
        match deleted.1 with
        | .ok B' => bitValues deleted.2 B' =
            xs.take (i.val.toNat - 1) ++ xs.drop i.val.toNat ∧
            PackedInvariant deleted.2 B'
        | .error _ => False
       else True)

def DeleteatRangeAgrees (xs : List Bool) (first last : I64) : Prop :=
    let B := vectorBits xs
    let s := initWords (encodeBits xs)
    let r := ⟨first, last⟩
    let result := (deleteBitRangePublic B r).run s
    if first > last then
      result.1 = .ok B ∧ result.2 = s
    else if int 1 ≤ first ∧ last ≤ int (Int.ofNat xs.length) then
      match result.1 with
      | .ok B' => bitValues result.2 B' = deleteRangeList xs r ∧ PackedInvariant result.2 B'
      | .error _ => False
    else True

def DeleteatRangeInsideAgrees (xs : List Bool) (first last : I64) : Prop :=
    first ≤ last → int 1 ≤ first → last ≤ int (Int.ofNat xs.length) →
    let B := vectorBits xs
    let r := ⟨first, last⟩
    match (deleteBitRangePublic B r).run (initWords (encodeBits xs)) with
    | (.ok B', state') =>
        bitValues state' B' = deleteRangeList xs r ∧ PackedInvariant state' B'
    | (.error _, _) => False

def FillAgrees {N : Nat} (dims : List I64) (xs : List Bool)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X)
    (_hRank : dims.length = N)
    (_hDims : ∀ d ∈ dims, int 0 ≤ d)
    (_hSize : dims.foldl (· * ·) (int 1) = int xs.length) : Prop :=
    let B : BitArray N := ⟨0, int xs.length, dims⟩
    let state := initWords (encodeBits xs)
    let result := (fillBitArray convertBoolMutation fillChunkVectorModel B x).run state
    match JuliaLean.base.range.JConvert.convert (T := Bool) x with
    | .error _ => (match result.1 with | .error _ => result.2 = state | .ok _ => False)
    | .ok value =>
        match result.1 with
        | .ok B' => bitValues result.2 B' = List.replicate xs.length value ∧
            PackedInvariant result.2 B'
        | .error _ => False

def ShiftAgrees (xs : List Bool) (i : I64) : Prop :=
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    let left := (bitVectorShiftLeftSigned id JuliaLean.base.int.unsigned
      shiftLeftUnsignedModel shiftRightSignedArgModel B i).run state
    let right := (bitVectorShiftRightSigned id JuliaLean.base.int.unsigned
      shiftLeftSignedArgModel shiftRightUnsignedModel B i).run state
    let shift := i.val.natAbs
    match left.1, right.1 with
    | .ok l, .ok r =>
        bitValues left.2 l = (if i.val ≥ 0 then shiftLeftBits xs shift else shiftRightBits xs shift) ∧
        bitValues right.2 r = (if i.val ≥ 0 then shiftRightBits xs shift else shiftLeftBits xs shift)
    | _, _ => False

def ReverseAgrees (xs : List Bool) : Prop :=
    let B := vectorBits xs
    match (bitVectorReverseInPlace JuliaLean.base.int.bitreverse isOddIntegerModel B).run
        (initWords (encodeBits xs)) with
    | (.ok _, state') => bitValues state' B = xs.reverse ∧ PackedInvariant state' B
    | (.error _, _) => False

def bitArrayChunkEqualPublic (state : State) (left right : Nat) : BitMutationM Bool := do
  let result ← JuliaLean.base.abstractarray.arrayEqual
    (fun chunks => pure chunks.length)
    (fun chunks => pure chunks.length)
    (fun a b => pure (List.zip a b))
    (fun a b => pure (a == b))
    (fun _ => false)
    (fun equal => pure (!equal))
    (state.contents left) (state.contents right)
  pure (result.getD false)

def BitArrayEqualityAgrees {N M : Nat} (xs ys : List Bool)
    (dimsA dimsB : List I64)
    (_hRankA : dimsA.length = N) (_hRankB : dimsB.length = M)
    (_hSizeA : dimsA.foldl (· * ·) (int 1) = int (Int.ofNat xs.length))
    (_hSizeB : dimsB.foldl (· * ·) (int 1) = int (Int.ofNat ys.length)) : Prop :=
    let a : BitArray N := ⟨0, int xs.length, dimsA⟩
    let b : BitArray M := ⟨1, int ys.length, dimsB⟩
    let state := MutableMemory.initialMany [(encodeBits xs).map some, (encodeBits ys).map some]
    (bitArrayEqual (bitArrayChunkEqualPublic state) a b).run state |>.1 =
      .ok (dimsA = dimsB ∧ xs = ys)

def compareBoolLists : List Bool → List Bool → I64
  | [], [] => int 0
  | [], _ :: _ => int (-1)
  | _ :: _, [] => int 1
  | false :: _, true :: _ => int (-1)
  | true :: _, false :: _ => int 1
  | _ :: xs, _ :: ys => compareBoolLists xs ys

def BitVectorComparisonAgrees (xs ys : List Bool) : Prop :=
    let a : BitVector := ⟨0, int xs.length, [int xs.length]⟩
    let b : BitVector := ⟨1, int ys.length, [int ys.length]⟩
    let state := MutableMemory.initialMany [(encodeBits xs).map some, (encodeBits ys).map some]
    let cmpLength := fun m n => int (JuliaLean.base.operators.cmpInteger
      (fun x y => JuliaLean.base.int.lt x y)
      (fun x y => JuliaLean.base.int.lt x y) m n)
    (bitVectorCmp (A := Unit) JuliaLean.base.int.trailing_zeros
      JuliaLean.base.int.top_set_bit cmpLength a b).run state |>.1 =
        .ok (compareBoolLists xs ys)
end Round2
end Round5
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace Round5

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

/- Public scalar reads and writes agree with logical bits for every valid
BitArray rank and every installed Bool conversion. -/
def ScalarIndexAgrees : Prop :=
  ∀ {N : Nat} (xs : List Bool) (dims : List I64) (i : I64)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X),
    (hRank : dims.length = N) →
    (∀ d ∈ dims, int 0 ≤ d) →
    (hSize : dims.foldl (· * ·) (int 1) = int xs.length) →
    dims.foldl (fun total d => total * d.val.toNat) 1 = xs.length →
    xs.length < maxVectorLength →
    _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.ScalarIndexAgrees
      (N := N) xs dims i x hRank hSize

/-- End pushes and nonempty pops preserve vector order and packed storage;
empty pops fail without changing the vector. -/
def DequeAgrees : Prop :=
  ∀ (xs : List Bool) {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X),
    xs.length < maxVectorLength →
    _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.DequeAgrees xs x

/- Valid insertions and deletions preserve logical bit order and packed padding; failed conversions leave state unchanged. -/
def InsertDeleteAgrees : Prop :=
  ∀ (xs : List Bool) (i : I64) {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X),
    xs.length + 1 < maxVectorLength →
    _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.InsertDeleteAgrees xs i x

/-- Every empty unit range is a no-op; valid nonempty ranges delete their elements.
The empty-range clause intentionally includes `0:-1`. -/
def DeleteatRangeAgrees : Prop :=
  ∀ (xs : List Bool) (first last : I64),
    xs.length < maxVectorLength →
    _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.DeleteatRangeAgrees xs first last

/-- Valid nonempty range deletion preserves every element outside the range and
keeps the final packed word zero-padded. -/
def DeleteatRangeInsideAgrees : Prop :=
  ∀ (xs : List Bool) (first last : I64),
    xs.length < maxVectorLength →
    _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.DeleteatRangeInsideAgrees xs first last


/-- Negative `resize!` requests and failed `Integer` conversions return an
error without changing the vector. No particular error class is promised. -/
def ResizeNegativeAgrees : Prop :=
  ∀ (xs : List Bool) {X : Type} [JuliaLean.base.range.JConvert I64 X] (n : X),
    xs.length < maxVectorLength →
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    let result := (_root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.resizeBitVectorPublic B n false).run state
    match JuliaLean.base.range.JConvert.convert (T := I64) n with
    | .error _ => (match result.1 with | .error _ => result.2 = state | .ok _ => False)
    | .ok newLength =>
        if newLength.val < 0 then
          match result.1 with
          | .error _ => result.2 = state
          | .ok _ => False
        else True

/-- Nonnegative `resize!` preserves the documented prefix or `first=true` suffix;
new values remain unspecified. -/
def ResizeNonnegAgrees : Prop :=
  ∀ (xs : List Bool) {X : Type} [JuliaLean.base.range.JConvert I64 X]
    (n : X) (first : Bool),
    xs.length < maxVectorLength →
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    let result := (_root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.resizeBitVectorPublic B n first).run state
    match JuliaLean.base.range.JConvert.convert (T := I64) n with
    | .error _ => (match result.1 with | .error _ => result.2 = state | .ok _ => False)
    | .ok newLength =>
      if 0 ≤ newLength.val ∧ newLength.val.toNat < maxVectorLength then
        match result.1 with
        | .ok B' =>
            let state' := result.2
            B'.len = newLength ∧
            (if first then
              if newLength.val.toNat < xs.length then
                bitValues state' B' = xs.drop (xs.length - newLength.val.toNat)
              else xs = (bitValues state' B').drop (newLength.val.toNat - xs.length)
             else
              if newLength.val.toNat < xs.length then
                bitValues state' B' = xs.take newLength.val.toNat
              else xs = (bitValues state' B').take xs.length) ∧
            _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.PackedInvariant state' B'
        | .error _ => False
      else True

/-- `fill!` converts through Base and sets every logical bit while preserving
packed padding for every valid rank. -/
def FillAgrees : Prop :=
  ∀ {N : Nat} (dims : List I64) (xs : List Bool)
    {X : Type} [JuliaLean.base.range.JConvert Bool X] (x : X),
    (hRank : dims.length = N) →
    (hDims : ∀ d ∈ dims, int 0 ≤ d) →
    (hSize : dims.foldl (· * ·) (int 1) = int xs.length) →
    dims.foldl (fun total d => total * d.val.toNat) 1 = xs.length →
    xs.length < maxVectorLength →
    _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.FillAgrees
      (N := N) dims xs x hRank hDims hSize

/-- Signed shifts move bits in the documented direction, false-fill the vacated
positions, and cover every `Int` shift including `typemin` and `typemax`. -/
def ShiftAgrees : Prop :=
  ∀ (xs : List Bool) (i : I64),
    xs.length < maxVectorLength →
    _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.ShiftAgrees xs i


/-- In-place BitVector reversal reverses logical bits and preserves the packed
chunk and zero-padding invariant. -/
def ReverseAgrees : Prop :=
  ∀ (xs : List Bool),
    xs.length < maxVectorLength → _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.ReverseAgrees xs





/-- Variadic BitVector concatenation preserves hcat shape and column-major bits;
vcat accepts unequal input lengths and preserves input order. -/
def BitArrayConcatenation : Prop :=
  ∀ (vectors : List (List Bool)),
    vectors.length > 0 →
    (∀ xs ∈ vectors, xs.length < maxVectorLength) →
    vectors.length < maxVectorLength →
    (vectors.flatten.length < maxVectorLength) →
    let handles : List BitVector :=
      (vectors.zip (List.range vectors.length)).map fun (xs, handle) =>
        ⟨handle, int xs.length, [int xs.length]⟩
    let state := MutableMemory.initialMany
      (vectors.map fun xs => (encodeBits xs).map some)
    let vertical := (bitArrayVcatVectors handles
      (fun n => _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.allocateBitArrayModel [n])).run state
    match vertical.1 with
    | .ok v =>
        v.dims = [int (Int.ofNat vectors.flatten.length)] ∧
        bitValues vertical.2 v = vectors.flatten ∧
        _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.PackedInvariant vertical.2 v ∧
        ((∀ xs ∈ vectors, xs.length = (vectors.headD []).length) →
          let horizontal := (bitArrayHcatVectors handles
            (fun rows cols => _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.allocateBitArrayModel [rows, cols])).run state
          match horizontal.1 with
          | .ok h =>
              h.dims = [int (Int.ofNat (vectors.headD []).length), int (Int.ofNat vectors.length)] ∧
              bitValues horizontal.2 h = vectors.flatten ∧
              _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.PackedInvariant horizontal.2 h
          | .error _ => False)
    | .error _ => False


/- Equality compares dimensions and then the logical bit sequences across all
BitArray ranks. -/
def BitArrayEqualityAgrees : Prop :=
  ∀ {N M : Nat} (xs ys : List Bool) (dimsA dimsB : List I64),
    (hRankA : dimsA.length = N) → (hRankB : dimsB.length = M) →
    (∀ d ∈ dimsA, int 0 ≤ d) → (∀ d ∈ dimsB, int 0 ≤ d) →
    (hSizeA : dimsA.foldl (· * ·) (int 1) = int (Int.ofNat xs.length)) →
    (hSizeB : dimsB.foldl (· * ·) (int 1) = int (Int.ofNat ys.length)) →
    dimsA.foldl (fun total d => total * d.val.toNat) 1 = xs.length →
    dimsB.foldl (fun total d => total * d.val.toNat) 1 = ys.length →
    xs.length < maxVectorLength → ys.length < maxVectorLength →
    _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.BitArrayEqualityAgrees
      (N := N) (M := M) xs ys dimsA dimsB hRankA hRankB hSizeA hSizeB
def dataIdsPublic {N : Nat} (B : BitArray N) : List (JInt .u64) :=
  bitArrayDataIds
    (fun handle => JuliaLean.base.abstractarray.dataidsArray
      (fun storage => JInt.wrap .u64 (Int.ofNat storage)) handle) B

/- Public metadata describes reshape shapes, and rank-changing reshapes preserve
the logical storage alias across writes. -/
def BitArrayMetadataAgrees : Prop :=
  ∀ {N M : Nat} (xs : List Bool) (oldDims targetDims : List I64) (i : I64),
    oldDims.length = N → (hTargetDims : targetDims.length = M) →
    (∀ d ∈ oldDims, int 0 ≤ d) → (∀ d ∈ targetDims, int 0 ≤ d) →
    xs.length < maxVectorLength →
    let state := initWords (encodeBits xs)
    let oldChecked := (checkedDimensionsModel oldDims).run state
    let targetChecked := (checkedDimensionsModel targetDims).run state
    if oldChecked.1 = .ok (int (Int.ofNat xs.length)) ∧
        targetChecked.1 = .ok (int (Int.ofNat xs.length)) then
      let B : BitArray N := ⟨0, int xs.length, oldDims⟩
      let reshaped := (bitArrayReshapeAny checkedDimensionsModel
        (_root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.allocateBitArrayModel (N := M))
        B targetDims hTargetDims).run state
      match reshaped with
      | (.ok output, state') =>
          let read := (bitArrayGetIndex _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.checkBitArrayBounds output i).run state'
          let metadata :=
            bitArrayLength output = int (Int.ofNat xs.length) ∧
            bitArraySizeRanked output = (if M = 1 then [int (Int.ofNat xs.length)] else targetDims) ∧
            bitArrayIsAssigned output i =
              (match read.1 with | .ok _ => true | .error _ => false) ∧
            bitArrayIndexStyle = JuliaLean.base.indices.IndexStyle.linear ∧
            dataIdsPublic output = dataIdsPublic B
          metadata ∧
            if xs.isEmpty then True
            else
              let changed := !(xs.headD false)
              let update := (bitArraySetIndex
                _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.checkBitArrayBounds
                _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.convertBoolMutation
                output changed (int 1)).run state'
              match update.1 with
              | .ok _ =>
                  let oldRead := (bitArrayGetIndex
                    _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.checkBitArrayBounds
                    B (int 1)).run update.2
                  let newRead := (bitArrayGetIndex
                    _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.checkBitArrayBounds
                    output (int 1)).run update.2
                  oldRead.1 = .ok changed ∧ newRead.1 = .ok changed
              | .error _ => False
      | (.error _, _) => False
    else True

def BitVectorComparisonAgrees : Prop :=
  ∀ (xs ys : List Bool),
    xs.length < maxVectorLength → ys.length < maxVectorLength →
    _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.BitVectorComparisonAgrees xs ys

/-- Variadic matrix `vcat` joins each input's rows in every column and preserves
column-major order. -/
def MatrixVcatAgrees : Prop :=
  ∀ (columns : Nat) (inputs : List (Nat × List Bool)),
    inputs.length > 0 →
    inputs.length < maxVectorLength →
    (∀ input ∈ inputs, input.2.length = input.1 * columns) →
    (∀ input ∈ inputs, input.1 < maxVectorLength) →
    (∀ input ∈ inputs, input.2.length < maxVectorLength) →
    columns < maxVectorLength →
    inputs.foldl (fun rows input => rows + input.1) 0 < maxVectorLength →
    (inputs.foldl (fun rows input => rows + input.1) 0) * columns < maxVectorLength →
    let arrays : List BitMatrix :=
      (inputs.zip (List.range inputs.length)).map fun (input, handle) =>
        ⟨handle, int (Int.ofNat input.2.length),
          [int (Int.ofNat input.1), int (Int.ofNat columns)]⟩
    let state := MutableMemory.initialMany
      (inputs.map fun input => (encodeBits input.2).map some)
    let result := (bitArrayVcatMatrices arrays
      (fun A d => (bitArraySizeRanked A).getD (d.val.toNat - 1) (int 0))
      _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.allocateMatrixModel).run state
    match result.1 with
    | .ok output =>
        let rows := inputs.foldl (fun total input => total + input.1) 0
        let expected := (List.range columns).flatMap fun column =>
          inputs.flatMap fun input =>
            (List.range input.1).map fun row =>
              input.2.getD (row + column * input.1) false
        output.dims = [int (Int.ofNat rows), int (Int.ofNat columns)] ∧
          bitValues result.2 output = expected ∧
          _root_.JuliaLean.Proofs.base.bitarray.Round5.Round2.PackedInvariant result.2 output
    | .error _ => False

/-- Public same-rank and rank-changing `reshape` preserves all logical bits and
reports the requested shape for checked dimensions. -/
def BitArrayReshapeKeepsBits : Prop :=
  (∀ {N : Nat} (xs : List Bool) (oldDims targetDims : List I64),
    oldDims.length = N → targetDims.length = N →
    (∀ d ∈ oldDims, int 0 ≤ d) → (∀ d ∈ targetDims, int 0 ≤ d) →
    let state := initWords (encodeBits xs)
    let oldChecked := (checkedDimensionsModel oldDims).run state
    let targetChecked := (checkedDimensionsModel targetDims).run state
    if xs.length < maxVectorLength ∧
        oldChecked.1 = .ok (int (Int.ofNat xs.length)) ∧
        targetChecked.1 = .ok (int (Int.ofNat xs.length)) then
      let B : BitArray N := ⟨0, int (Int.ofNat xs.length), oldDims⟩
      match (bitArrayReshapeSameRank checkedDimensionsModel
        allocateBitArrayModel B targetDims).run state with
      | (.ok reshaped, state') =>
          bitArrayLength reshaped = int (Int.ofNat xs.length) ∧
          bitArraySize reshaped = targetDims ∧
          bitValues state' reshaped = xs
      | (.error _, _) => False
    else True) ∧
  (∀ {N M : Nat} (xs : List Bool) (oldDims targetDims : List I64),
    N ≠ M → oldDims.length = N → (hTargetDims : targetDims.length = M) →
    (∀ d ∈ oldDims, int 0 ≤ d) → (∀ d ∈ targetDims, int 0 ≤ d) →
    let state := initWords (encodeBits xs)
    let oldChecked := (checkedDimensionsModel oldDims).run state
    let targetChecked := (checkedDimensionsModel targetDims).run state
    if xs.length < maxVectorLength ∧
        oldChecked.1 = .ok (int (Int.ofNat xs.length)) ∧
        targetChecked.1 = .ok (int (Int.ofNat xs.length)) then
      let B : BitArray N := ⟨0, int (Int.ofNat xs.length), oldDims⟩
      match (bitArrayReshapeAny checkedDimensionsModel
        (allocateBitArrayModel (N := M)) B targetDims hTargetDims).run state with
      | (.ok reshaped, state') =>
          bitArrayLength reshaped = int (Int.ofNat xs.length) ∧
          bitArraySize reshaped = targetDims ∧
          bitValues state' reshaped = xs
      | (.error _, _) => False
    else True)
end Round5
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace Archive20261102Round6

open JuliaLean JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.base.bitarray

/-- BitArray's public assignment query recognizes exactly the separately
enumerated one-based logical positions, for every native index and nonnegative
native logical length; it makes no claim about the physical chunk allocation.
Julia source: base/bitarray.jl:102-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/essentials.jl:1124-1149; doc/src/base/arrays.md:108
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BitArrayAssignedLogicalExtentFull : Prop :=
  ∀ {N : Nat} (B : BitArray N) (i : I64), 0 ≤ B.len.val →
    (bitArrayIsAssigned B i = true ↔
      i.val ∈ (List.range B.len.val.toNat).map (fun (n : Nat) => (n : Int) + 1))
end Archive20261102Round6
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace Archive20261102Round6

open JuliaLean JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.base.bitarray

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

abbrev Heap := MutableMemory U64

/-- Physical little-endian bit interpretation, independent of the source mask/shift code. -/
def storedBit (s : Heap) {N : Nat} (b : BitArray N) (i : Nat) : Bool :=
  let word := ((s.contents b.chunks)[i / 64]?.getD none).getD (u64 0)
  decide ((word.val.toNat / 2 ^ (i % 64)) % 2 = 1)

/-- Input representation invariants of a live packed BitArray. Chunk contents are
arbitrary UInt64 values. A Some word represents one concrete realization of
physical isbits bytes, including unspecified bytes from undef; this is not an
initialized-logical-value restriction or a claim that the model allocator None
is already a concrete Julia UInt64. Every such UInt64 realization is quantified.
The size relation is metadata validity, not a hypothesis about iterate's result.
Rank-one size is read from len, as in the actual specialized Julia method.
Storage need only cover the logical words: extra chunks and arbitrary tail bits
from public alias growth are included, since iteration does not inspect them.
Julia source: base/bitarray.jl:5-6,24-41,102-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ValidIterationStorage (s : Heap) {N : Nat} (b : BitArray N) : Prop :=
  s.validVector b.chunks ∧
  0 ≤ b.len.val ∧
  (bitArraySizeRanked b).length = N ∧
  (∀ d ∈ bitArraySizeRanked b, 0 ≤ d.val) ∧
  ((bitArraySizeRanked b).map (fun d => d.val.toNat)).prod = b.len.val.toNat ∧
  (b.len.val.toNat + 63) / 64 ≤ (s.contents b.chunks).length ∧
  (∀ cell ∈ s.contents b.chunks, cell.isSome = true) ∧
  (∀ slots ∈ s.memories, slots.length < 2 ^ 60)

/-- Iteration returns each logical bit in column-major order, advances exactly one
position, stops at the logical length, and never mutates the array or its aliases.
All native states are included: negative states reject with BoundsError and states
at or beyond length terminate. The default call is the included state zero.
Julia source: base/bitarray.jl:352-355 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/manual/interfaces.md:8-15,30-54;
base/bitarray.jl:5-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BitArrayIterationFull : Prop :=
  ∀ {N : Nat} (s : Heap) (b : BitArray N) (i : I64),
    ValidIterationStorage s b →
    let result := (bitArrayIterate b i).run s
    result.2 = s ∧
    if i.val < 0 then result.1 = .error .bounds
    else if i.val < b.len.val then
      result.1 = .ok (some (storedBit s b i.val.toNat, int (i.val + 1)))
    else result.1 = .ok none

/-- Independent lexicographic comparison of Boolean sequences, with false before
true and a proper prefix before its extension. -/
def compareBooleanSequences : List Bool → List Bool → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | false :: _, true :: _ => -1
  | true :: _, false :: _ => 1
  | _ :: xs, _ :: ys => compareBooleanSequences xs ys

/-- Actual native Integer cmp dispatch: cmpInteger calls islessReal, which calls
the installed native Int less-than model. The returned -1/0/1 is a Julia Int.
Julia source: base/operators.jl:505,537;
base/int.jl:84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def compareNativeLengths (m n : I64) : I64 :=
  int (JuliaLean.base.operators.cmpInteger
    (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt_BitSigned)
    (JuliaLean.base.operators.islessReal JuliaLean.base.int.lt_BitSigned) m n)

/-- BitVector comparison is lexicographic on logical Boolean values and preserves
both inputs and all aliases, including readable states reached through alias growth.
Julia source: base/bitarray.jl:1211-1218 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/operators.jl:507-526;
base/abstractarray.jl:3140-3145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BitVectorComparisonFull : Prop :=
  ∀ (s : Heap) (a b : BitVector),
    ValidIterationStorage s a → ValidIterationStorage s b →
    let result := (bitVectorCmp (A := Unit) JuliaLean.base.int.trailing_zeros
      JuliaLean.base.int.top_set_bit compareNativeLengths a b).run s
    result.2 = s ∧
    result.1 = .ok (int (compareBooleanSequences
      ((List.range a.len.val.toNat).map (storedBit s a))
      ((List.range b.len.val.toNat).map (storedBit s b))))
end Archive20261102Round6
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace Archive20261102Round6

open JuliaLean JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.base.bitarray

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

open JuliaLean JuliaLean.base.bitarray JuliaLean.base.array JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray


/-- Error translation for the native tuple/axis calls below. Only BoundsError is
reachable there; the remaining constructors retain their existing Array error classes. -/
def liftArray {α : Type} (x : JuliaLean.base.abstractarray.Result α) : BitMutationM α :=
  match x with
  | .ok a => pure a
  | .error (.julia .boundsError) => throw .bounds
  | .error (.julia (.argumentError s)) => throw (.argument s)
  | .error (.julia (.overflowError _)) => throw .overflow
  | .error (.julia (.inexactError _)) => throw .inexact
  | .error (.julia .divideError) => throw .divide
  | .error (.julia (.domainError s)) => throw (.argument s)
  | .error (.julia (.methodError s)) => throw (.method s)
  | .error (.julia .eofError) => throw (.method "EOFError")
  | .error (.dimensionMismatch s) => throw (.dimensionMismatch s)
  | .error (.canonicalIndex f t) => throw (.method (f ++ ":" ++ t))
  | .error (.errorException s) => throw (.argument s)
  | .error (.assertionError s) => throw (.assertion s)
  | .error (.showError e) => throw (.showError e)

abbrev Axis := JuliaLean.base.range.OneTo I64

def rangeArray {α : Type} (x : JuliaLean.base.range.JlX α) : JuliaLean.base.abstractarray.Result α :=
  x.mapError fun e =>
    match e with
    | .jl e => .julia e
    | .errorException s => .errorException s
    | .dimensionMismatch s => .dimensionMismatch s
    | .showError e => .showError e
    | .inboundsViolation => .julia .boundsError

def axisLength (r : Axis) : JuliaLean.base.abstractarray.Result I64 :=
  rangeArray (JuliaLean.base.range.length_OneTo_smallints r)

def matrixAxes (B : BitMatrix) : JuliaLean.base.abstractarray.Result (List Axis) :=
  JuliaLean.base.abstractarray.axesDefault (fun B => pure (bitArraySize B)) JuliaLean.base.range.unchecked_oneto B

/-- Public native BitArray scalar bounds dispatch through the installed oneto constructor. -/
def scalarBounds {N : Nat} (B : BitArray N) (i : I64) : BitMutationM Unit := do
  let each : BitArray N → JuliaLean.base.abstractarray.Result Axis := JuliaLean.base.abstractarray.eachindexLinear
    (fun (a : BitArray N) => pure (bitArrayLength a))
    (fun n => rangeArray (JuliaLean.base.range.oneto n))
  if !(← liftArray (JuliaLean.base.abstractarray.checkboundsOne each
      (fun ax j => pure (JuliaLean.base.abstractarray.checkindexOneTo ax.stop j)) B i)) then
    throw .bounds

/-- The dense Array eachindex method constructs an unchecked OneTo. Its installed
native iteration is pure and total on valid lengths, so collecting this range before
fillTyped changes no mutation/error order. The extra unit of fuel admits termination. -/
def chunkIndices (handle : Nat) : BitMutationM (List I64) := do
  let range ← JuliaLean.base.abstractarray.eachindexDense mutableLength
    JuliaLean.base.range.unchecked_oneto handle
  liftArray (rangeArray (JuliaLean.base.range.collectIter range pure (range.stop.val.toNat + 1)))

/-- bitarray.fillBitArray normalizes its two source fill arguments to U64.
Recover the actual source-selected argument type: the zero branch is Int zero and
must enter public fill! with its real Int→UInt64 conversion; the all-ones branch
is already UInt64. The unused failed-type cast is never evaluated. -/
def fillChunksNative (handle : Nat) (word : U64) : BitMutationM Unit := do
  if word == u64 0 then
    let _ ← JuliaLean.base.array.fillBang
      (fun (_ : I64) => false) (fun (_ : I64) => u64 0)
      (fun x => liftArray (JuliaLean.base.abstractarray.liftJulia (JuliaLean.base.int.convert .u64 x)))
      (JuliaLean.base.array.fillTyped chunkIndices mutableSet) handle (int 0)
    pure ()
  else
    let _ ← JuliaLean.base.array.fillBang
      (fun (_ : U64) => true) (fun x => x)
      (fun x => pure (JuliaLean.base.number.convertSame x))
      (JuliaLean.base.array.fillTyped chunkIndices mutableSet) handle word
    pure ()

/-- Dispatch of checkbounds_indices on native OneTo axes and native integer
coordinates. Each recursive step is the installed source method. -/
def checkCoordinates (axes : List Axis) : List I64 → JuliaLean.base.abstractarray.Result Bool
  | [] => JuliaLean.base.abstractarray.checkboundsIndicesNil axisLength axes
  | i :: is => JuliaLean.base.abstractarray.checkboundsIndicesCons (JuliaLean.base.range.unchecked_oneto (int 1))
      (fun ax j => pure (JuliaLean.base.abstractarray.checkindexOneTo ax.stop j))
      (fun axs _ => checkCoordinates axs is) axes i is

def matrixCheck (B : BitMatrix) (is : List I64) : BitMutationM Unit := do
  if !(← liftArray (JuliaLean.base.abstractarray.checkboundsMany matrixAxes checkCoordinates B is)) then throw .bounds

/-- Native OneTo subscript dispatch through _sub2ind_recurse, retaining
native signed arithmetic and the installed nextL/offsetin methods. -/
def linearCoordinates (axes : List Axis) (stride index : I64) : List I64 → JuliaLean.base.abstractarray.Result I64
  | [] => pure (JuliaLean.base.abstractarray.sub2indRecurseDone axes stride index)
  | i :: is =>
    match axes with
    | [] => JuliaLean.base.abstractarray.sub2indRecurseEmpty
        (fun a b => pure (sub_int a b)) (fun a b => pure (mul_int a b))
        (fun a b => pure (add_int a b))
        (fun _ st ind _ => linearCoordinates [] st ind is) stride index i is
    | _ :: _ => JuliaLean.base.abstractarray.sub2indRecurse
        (fun axs => JuliaLean.base.abstractarray.tupleGet axs (int 1)) (fun axs => pure axs.tail)
        (JuliaLean.base.abstractarray.nextLRange axisLength (fun a b => pure (mul_int a b)))
        (JuliaLean.base.abstractarray.offsetinRange (fun r => pure (JuliaLean.base.range.first_OneTo r)) (fun a b => pure (sub_int a b)))
        (fun a b => pure (mul_int a b)) (fun a b => pure (add_int a b))
        (fun axs st ind _ => linearCoordinates axs st ind is) axes stride index i is

def matrixLinear (B : BitMatrix) (is : List I64) : BitMutationM I64 :=
  liftArray (JuliaLean.base.abstractarray.toLinearMany
    (JuliaLean.base.abstractarray.sub2indArray matrixAxes (JuliaLean.base.abstractarray.sub2indAxes linearCoordinates)) B is)

def matrixSet (B : BitMatrix) (x : Bool) (is : List I64) : BitMutationM BitMatrix :=
  JuliaLean.base.abstractarray.setindexArray (fun _ => pure bitArrayIndexStyle)
    (fun sty a inds => liftArray (JuliaLean.base.abstractarray.errorCanonicalSetindexOther sty a inds))
    (fun a inds => pure (JuliaLean.base.indices.to_indices_A_Ints a inds))
    (fun _ => JuliaLean.base.abstractarray.setindexLinear matrixCheck matrixLinear
      (bitArraySetIndex scalarBounds
        (fun b => pure (JuliaLean.base.number.convertSame b)))) B x is

/-- Constructor dispatch for a native two-element dimension tuple. The same-type
Int conversion cannot throw; the fallback of getD is therefore unreachable. -/
def nativeDimension (x : I64) : I64 :=
  (JuliaLean.base.int.convert .i64 x).toOption.getD (int 0)

def matrixUndef (ds : List I64) : BitMutationM BitMatrix :=
  bitArrayUndefTuple (JuliaLean.base.tuple.mapOneTwo nativeDimension)
    (BitArrayUndef JuliaLean.base.array.checkedDims
      (fun n => mutableAllocate (some ⟨8, false, false⟩) 0 (int n))) ds

def matrixFalses (ds : List I64) : BitMutationM BitMatrix :=
  falsesVarargs (falsesIntegerDims matrixUndef
    (fun B x => fillBitArray (fun b => pure (JuliaLean.base.number.convertSame b))
      fillChunksNative B x)) ds

def oneMatrix (B : BitMatrix) : BitMutationM BitMatrix :=
  bitMatrixOne
    (fun B => do
      let ds := bitArraySize B
      pure (← liftArray (JuliaLean.base.abstractarray.tupleGet ds (int 1)), ← liftArray (JuliaLean.base.abstractarray.tupleGet ds (int 2))))
    matrixFalses matrixSet B

/-- Native BitMatrix dimensions and stored length. The subject reads no input chunk
storage: even a parent invalidated by resizing an aliased vec remains in scope. -/
def MatrixInput (B : BitMatrix) (rows columns : Nat) : Prop :=
  (rows : Int) ≤ IntTy.max .i64 ∧ (columns : Int) ≤ IntTy.max .i64 ∧
  B.dims = [int rows, int columns] ∧ B.len.val = (rows * columns : Nat)

/-- The multiplicative identity of every square BitMatrix is a fresh packed
matrix with exactly its diagonal true; nonsquare matrices throw DimensionMismatch.
Julia source: base/bitarray.jl:419-427 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/number.jl:367-390; doc/src/base/numbers.md:102
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def BitMatrixOneFull : Prop :=
  ∀ (s : State) (B : BitMatrix) (rows columns : Nat), MatrixInput B rows columns →
    let result := (oneMatrix B).run s
    if rows = columns then
      ∃ identity, result.1 = .ok identity ∧
        identity.dims = [int rows, int columns] ∧
        identity.len.val = (rows * columns : Nat) ∧
        bitValues result.2 identity =
          (List.range (rows * columns)).map (fun k => k % rows == k / rows) ∧
        Round5.Round2.PackedInvariant result.2 identity ∧
        result.2.validVector identity.chunks ∧
        identity.chunks ≥ s.arrays.length ∧
        result.2.arrays.take s.arrays.length = s.arrays ∧
        result.2.memories.take s.memories.length = s.memories
    else result.1 = .error (.dimensionMismatch "multiplicative identity defined only for square matrices") ∧
      result.2 = s
end Archive20261102Round6
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace Archive20261102Round6

open JuliaLean JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.base.bitarray

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

open JuliaLean JuliaLean.base.bitarray JuliaLean.base.array JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

/-- Mathematical value of a packed bit, using division and parity rather than
the implementation's masks, shifts, and chunkwise equality tests. -/
def extremaStoredBit (s : State) {N : Nat} (B : BitArray N) (i : Nat) : Bool :=
  let word := ((s.contents B.chunks)[i / 64]?.getD none).getD (u64 0)
  decide ((word.val.toNat / 2 ^ (i % 64)) % 2 = 1)

/-- Representation validity for readable packed UInt64 storage, including arbitrary
chunk-array offsets, sharing, and tail bits exposed by public alias resizing.
Julia source: base/bitarray.jl:24-41,103-104,472-485,739-755
@ f755f49a9e41380d7da126b3c1db9fe7f83dd027
These are input/storage invariants only; zero tail padding is deliberately not assumed. -/
def ValidExtremaStorage (s : State) {N : Nat} (B : BitArray N) : Prop :=
  s.validVector B.chunks ∧
  0 ≤ B.len.val ∧
  (bitArraySizeRanked B).length = N ∧
  (∀ d ∈ bitArraySizeRanked B, 0 ≤ d.val) ∧
  ((bitArraySizeRanked B).map (fun d => d.val.toNat)).prod = B.len.val.toNat ∧
  (B.len.val.toNat + 63) / 64 ≤ (s.contents B.chunks).length ∧
  (∀ cell ∈ s.contents B.chunks, cell.isSome = true) ∧
  (∀ slots ∈ s.memories, slots.length < 2^60)

/-- Minimum and maximum return the Boolean extrema of all logical elements, reject
empty arrays with ArgumentError, and leave packed source storage unchanged.
Julia source: base/bitarray.jl:1724-1748 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/reduce.jl:689-752;
doc/src/base/collections.md:124-130 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ScalarExtremaValues : Prop :=
  ∀ {N : Nat} (state : State) (B : BitArray N),
    ValidExtremaStorage state B →
    let lo := (bitArrayMinimum bitArrayAll B).run state
    let hi := (bitArrayMaximum bitArrayAny B).run state
    lo.2 = state ∧ hi.2 = state ∧
    if B.len.val = 0 then
      lo.1 = .error (.argument "argument must be non-empty") ∧
      hi.1 = .error (.argument "argument must be non-empty")
    else
      lo.1 = .ok ((List.range B.len.val.toNat).all (extremaStoredBit state B)) ∧
      hi.1 = .ok ((List.range B.len.val.toNat).any (extremaStoredBit state B))
end Archive20261102Round6
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

private theorem scalar_oneTo_check (n i : I64) (hn : 0 ≤ n.val) :
    JuliaLean.base.abstractarray.checkindexOneTo n i =
      decide (int 1 ≤ i ∧ i ≤ n) := by
  apply Bool.eq_iff_iff.mpr
  simp only [JuliaLean.base.abstractarray.checkindexOneTo, decide_eq_true_eq]
  change (wrapInt .u64 (wrapInt .i64 (i.val - wrapInt .i64 1)) <
    wrapInt .u64 n.val ↔ 1 ≤ i.val ∧ i.val ≤ n.val)
  have hi := i.property
  have hb := n.property
  simp [wrapInt, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hi hb ⊢
  omega

/-- The installed linear bounds check agrees with the inclusive scalar interval. -/
theorem scalar_bounds_run {N : Nat} (B : BitArray N) (i : I64)
    (s : State) (hn : 0 ≤ B.len.val) :
    (Round5.Round2.checkBitArrayBounds B i).run s =
      (if int 1 ≤ i ∧ i ≤ B.len then (.ok (), s) else (.error .bounds, s)) := by
  have hc := scalar_oneTo_check B.len i hn
  unfold Round5.Round2.checkBitArrayBounds
  simp only [JuliaLean.base.abstractarray.eachindexLinear,
    JuliaLean.base.abstractarray.checkboundsOne, bind, pure, Except.bind, Except.pure]
  rw [hc]
  by_cases h : int 1 ≤ i ∧ i ≤ B.len
  · simp only [h, and_self, decide_true, ite_true]
    rfl
  · simp only [h, decide_false, ite_false]
    rfl

/-- Failure of a Bool conversion does not alter the state. -/
theorem scalar_conversion_error {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X)
    (e : JuliaLean.base.range.Exc) (s : State)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .error e) :
    (Round5.Round2.convertBoolMutation x).run s =
      (.error (Round5.Round2.mutationErrorOfRange e), s) := by
  simp only [Round5.Round2.convertBoolMutation, he,
    Round5.Round2.liftRangeResult]
  rfl

/-- Successful conversion returns the converted bit without changing the state. -/
theorem scalar_conversion_ok {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (x : X) (b : Bool) (s : State)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok b) :
    (Round5.Round2.convertBoolMutation x).run s = (.ok b, s) := by
  simp only [Round5.Round2.convertBoolMutation, he,
    Round5.Round2.liftRangeResult]
  rfl

/-- A valid public read performs its internal bit read. -/
theorem scalar_public_read_valid {N : Nat} (B : BitArray N) (i : I64)
    (s : State) (hn : 0 ≤ B.len.val) (hi : int 1 ≤ i ∧ i ≤ B.len) :
    (bitArrayGetIndex Round5.Round2.checkBitArrayBounds B i).run s =
      (unsafeBitGetIndex B.chunks i).run s := by
  simp only [bitArrayGetIndex, shape_run_bind, scalar_bounds_run B i s hn,
    hi, and_self, ite_true]

/-- A valid converted write returns the same header after the internal store. -/
theorem scalar_public_write_valid {N : Nat} {X : Type}
    [JuliaLean.base.range.JConvert Bool X] (B : BitArray N) (x : X) (i : I64)
    (value : Bool) (s s' : State) (hn : 0 ≤ B.len.val)
    (hi : int 1 ≤ i ∧ i ≤ B.len)
    (he : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok value)
    (hs : (unsafeBitSetIndex B.chunks value i).run s = (.ok (), s')) :
    (bitArraySetIndex Round5.Round2.checkBitArrayBounds
      Round5.Round2.convertBoolMutation B x i).run s = (.ok B, s') := by
  simp only [bitArraySetIndex, shape_run_bind, scalar_bounds_run B i s hn,
    hi, and_self, ite_true, scalar_conversion_ok x value s he, hs, shape_run_pure]

/-- Arithmetic shift by six computes the chunk quotient. -/
theorem scalar_div64_val (i : I64) : (div64 i).val = i.val / 64 := by
  rw [div64, JuliaLean.Proofs.base.int.ashr_int_val (by rfl)]
  rfl

/-- The low six bits represent the nonnegative remainder modulo 64. -/
theorem scalar_mod64_val (i : I64) : (mod64 i).val = i.val % 64 := by
  have he := packedMod64_nat i
  have hr := JuliaLean.Proofs.base.int.fromJInt_toNat (mod64 i)
  have hb := (mod64 i).property
  change -9223372036854775808 ≤ (mod64 i).val ∧
    (mod64 i).val ≤ 9223372036854775807 at hb
  change ((fromJInt (mod64 i)).toNat : Int) =
    (mod64 i).val % 18446744073709551616 at hr
  have hmod : 0 ≤ i.val % 64 ∧ i.val % 64 < 64 :=
    ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  rw [he] at hr
  omega

/-- Positive scalar indices decompose into the expected one-based chunk and bit. -/
theorem scalar_chunks_id (i : I64) (hi : int 1 ≤ i) :
    (getChunksId i).1.val = (i.val - 1) / 64 + 1 ∧
    (getChunksId i).2.val = (i.val - 1) % 64 := by
  have hb := i.property
  change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 at hb
  have hip : 1 ≤ i.val := hi
  have hs : (i - int 1).val = i.val - 1 := by
    change wrapInt .i64 (i.val - 1) = i.val - 1
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ i.val - 1 ∧ i.val - 1 ≤ 9223372036854775807
    omega
  constructor
  · change wrapInt .i64 ((div64 (i - int 1)).val + 1) = _
    rw [scalar_div64_val, hs]
    apply wrapInt_of_inRange
    change -9223372036854775808 ≤ (i.val - 1) / 64 + 1 ∧
      (i.val - 1) / 64 + 1 ≤ 9223372036854775807
    omega
  · exact (scalar_mod64_val (i - int 1)).trans (congrArg (fun z : Int => z % 64) hs)

/-- The chunk count equals ceiling division for every nonnegative native length. -/
theorem scalar_num_chunks (n : I64) (hn : 0 ≤ n.val) :
    (numBitChunks n).val = (n.val + 63) / 64 := by
  have hb := n.property
  change -9223372036854775808 ≤ n.val ∧ n.val ≤ 9223372036854775807 at hb
  have hm : (mod64 n == int 0) = decide (n.val % 64 = 0) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      rw [scalar_mod64_val] at hv
      exact hv
    · intro h
      apply Subtype.ext
      rw [scalar_mod64_val, h]
      rfl
  unfold numBitChunks
  rw [hm]
  by_cases hz : n.val % 64 = 0
  · simp only [hz, decide_true, ite_true]
    change wrapInt .i64 ((div64 n).val + 0) = _
    rw [scalar_div64_val]
    rw [wrapInt_of_inRange .i64 _ (by
      change -9223372036854775808 ≤ n.val / 64 + 0 ∧
        n.val / 64 + 0 ≤ 9223372036854775807
      omega)]
    omega
  · simp only [hz, decide_false, Bool.false_eq_true, ite_false]
    change wrapInt .i64 ((div64 n).val + 1) = _
    rw [scalar_div64_val]
    rw [wrapInt_of_inRange .i64 _ (by
      change -9223372036854775808 ≤ n.val / 64 + 1 ∧
        n.val / 64 + 1 ≤ 9223372036854775807
      omega)]
    omega


/-- The visible contents of the initial chunk vector omit its spare capacity. -/
theorem scalar_initial_contents (words : List U64)
    (hn : words.length ≤ 9223372036854775807) :
    (initWords words).contents 0 = words.map some := by
  change ((words.map some ++ List.replicate 32 none).drop 0).take
    (int (words.map some).length).val.toNat = words.map some
  rw [List.length_map, packedInt_val words.length hn, Int.toNat_natCast,
    List.drop_zero]
  exact List.take_left' (List.length_map ..)

/-- Reading one bit of an AND reads the AND of the corresponding bits. -/
theorem scalar_packedBit_and (a b : U64) (k : Nat) :
    packedBit (and_int a b) k = (packedBit a k && packedBit b k) := by
  simp only [and_int, jlAndInt, packedBit_toJInt, BitVec.getLsbD_and,
    packedBit_fromJInt]

/-- Bitwise complement flips every in-range bit. -/
theorem scalar_packedBit_not (a : U64) (k : Nat) (hk : k < 64) :
    packedBit (not_int a) k = !packedBit a k := by
  unfold not_int
  rw [packedBit_toJInt]
  simp only [jlNotInt, BitVec.getLsbD_not, packedBit_fromJInt]
  change (decide (k < 64) && !packedBit a k) = !packedBit a k
  simp only [hk, decide_true, Bool.true_and]

/-- Testing a one-bit mask returns exactly that logical bit. -/
theorem scalar_mask_test (word : U64) (bit : Nat) (hb : bit < 64) :
    (and_int word (shl_int (u64 1) (int bit)) != u64 0) = packedBit word bit := by
  cases hv : packedBit word bit
  · have hz : and_int word (shl_int (u64 1) (int bit)) = u64 0 := by
      apply packedBit_ext
      intro k hk
      rw [scalar_packedBit_and, packedBit_shift_one bit k hb, packedBit_zero]
      by_cases he : k = bit
      · subst k
        rw [hv]
        rfl
      · simp only [he, decide_false, Bool.and_false]
    rw [hz]
    rfl
  · have hz : and_int word (shl_int (u64 1) (int bit)) ≠ u64 0 := by
      intro he
      have hbit := congrArg (fun w => packedBit w bit) he
      rw [scalar_packedBit_and, packedBit_shift_one bit bit hb, packedBit_zero,
        hv] at hbit
      simp only [decide_true, Bool.true_and] at hbit
      contradiction
    exact bne_iff_ne.mpr hz

/-- The source spelling of the natural-to-integer mask count. -/
theorem scalar_mask_test_ofNat (word : U64) (bit : Nat) (hb : bit < 64) :
    (and_int word (shl_int (u64 1) (int (Int.ofNat bit))) != u64 0) =
      packedBit word bit := scalar_mask_test word bit hb

/-- The ordinary bit setter changes exactly its addressed bit. -/
theorem scalar_set_word_bits (word : U64) (bit k : Nat) (value : Bool)
    (hb : bit < 64) (hk : k < 64) :
    packedBit (if value then or_int word (shl_int (u64 1) (int bit))
      else and_int word (not_int (shl_int (u64 1) (int bit)))) k =
      (if k = bit then value else packedBit word k) := by
  cases value <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, packedBit_or,
      scalar_packedBit_and, scalar_packedBit_not _ k hk,
      packedBit_shift_one bit k hb]
  all_goals by_cases he : k = bit <;>
    simp only [he, decide_true, decide_false, ite_true, ite_false,
      Bool.or_true, Bool.or_false, Bool.not_true, Bool.not_false,
      Bool.and_false, Bool.and_true]


/-- A checked store updates one heap slot and retains every other field. -/
theorem scalar_memory_write (s : State) (slots : List (Option U64))
    (hm : s.memories[0]? = some slots) (j : I64) (word : U64)
    (hj : 1 ≤ j.val ∧ j.val ≤ (slots.length : Int)) :
    (memoryWrite 0 j (some word)).run s =
      (.ok (), {s with memories := s.memories.set 0 (slots.set (j.val - 1).toNat (some word))}) := by
  simp only [memoryWrite, memoryRead, shape_run_bind, shape_run_get, hm,
    shape_run_pure, hj, and_self, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, shape_run_modify]

/-- A checked vector store preserves the header and updates the selected slot. -/
theorem scalar_set_run (s : State) (slots : List (Option U64)) (n : I64)
    (ha : s.arrays[0]? = some ⟨(0, one), n⟩)
    (hm : s.memories[0]? = some slots) (hn : n.val ≤ (slots.length : Int))
    (j : I64) (word : U64) (hj : 1 ≤ j.val ∧ j.val ≤ n.val) :
    (mutableSet 0 word j).run s =
      (.ok (), {s with memories := s.memories.set 0 (slots.set (j.val - 1).toNat (some word))}) := by
  have hin : one ≤ j ∧ j ≤ n := hj
  have hw := scalar_memory_write s slots hm j word (by omega)
  simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds,
    mutableLength, mutableMemoryref, mutableRef, shape_run_bind, shape_vector_run,
    ha, shape_run_pure, hin, and_self, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, shape_one_add_sub_one, hw]

/-- Writing in the initial packed vector is a list update of its chunk words. -/
theorem scalar_initial_set (words : List U64) (j : Nat) (word : U64)
    (hn : words.length ≤ 9223372036854775807) (hj : j < words.length) :
    (mutableSet 0 word (int ((j + 1 : Nat) : Int))).run (initWords words) =
      (.ok (), initWords (words.set j word)) := by
  have hi := packedInt_val (j + 1) (by omega)
  have hsize := packedInt_val words.length hn
  have hin : one ≤ int ((j + 1 : Nat) : Int) ∧
      int ((j + 1 : Nat) : Int) ≤ int words.length := by
    change 1 ≤ (int ((j + 1 : Nat) : Int)).val ∧
      (int ((j + 1 : Nat) : Int)).val ≤ (int words.length).val
    rw [hi, hsize]
    omega
  have hidx : ((int ((j + 1 : Nat) : Int)).val - 1).toNat = j := by
    rw [hi]
    omega
  have hslots : (words.map some ++ List.replicate 32 none).length = words.length + 32 := by
    simp only [List.length_append, List.length_map, List.length_replicate]
  have ha : (initWords words).arrays[0]? = some ⟨(0, one), int words.length⟩ := by
    change some (⟨(0, one), int (words.map some).length⟩ : MutableVector) = _
    rw [List.length_map]
  have hraw := scalar_set_run (initWords words)
    (words.map some ++ List.replicate 32 none) (int words.length) ha rfl
    (by rw [hsize, hslots]; omega)
    (int ((j + 1 : Nat) : Int)) word (by rw [hi, hsize]; omega)
  rw [hraw, hidx]
  change ((Except.ok (), MutableMemory.mk
      [(words.map some ++ List.replicate 32 none).set j (some word)]
      [⟨(0, one), int (words.map some).length⟩]) : Except Error Unit × State) = _
  rw [List.set_append_left _ _ (by simpa only [List.length_map] using hj)]
  rw [← List.map_set]
  simp only [initWords, MutableMemory.initial, List.length_map, List.length_set]
  rfl


/-- Reading a list update, including padded positions beyond the list. -/
theorem scalar_getD_set (xs : List Bool) (i j : Nat) (value : Bool)
    (hi : i < xs.length) :
    (xs.set i value).getD j false =
      (if i = j then value else xs.getD j false) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set, hi, and_self, ite_true]
  by_cases he : i = j <;> simp only [he, ite_true, ite_false, Option.getD_some]

def scalar_set_word (word : U64) (bit : Nat) (value : Bool) : U64 :=
  if value then or_int word (shl_int (u64 1) (int bit))
  else and_int word (not_int (shl_int (u64 1) (int bit)))

/-- Updating a logical bit changes only its packed chunk. -/
theorem scalar_encode_set (xs : List Bool) (i : Nat) (value : Bool)
    (hi : i < xs.length) :
    encodeBits (xs.set i value) =
      (encodeBits xs).set (i / 64)
        (scalar_set_word (packedPrefix xs (i / 64) 64) (i % 64) value) := by
  apply List.ext_getElem
  · simp only [packedEncoded_length, List.length_set]
  · intro c hc hc'
    have hci : c < wordCount xs.length := by
      simpa only [packedEncoded_length, List.length_set] using hc
    rw [List.getElem_set]
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
    by_cases he : i / 64 = c
    · subst c
      simp only [ite_true]
      apply packedBit_ext
      intro k hk
      rw [packedWord_bit _ _ k hk]
      rw [scalar_getD_set xs i _ value hi]
      rw [scalar_set_word, scalar_set_word_bits _ _ k value (Nat.mod_lt _ (by decide)) hk,
        packedWord_bit xs _ k hk]
      by_cases hkbit : k = i % 64
      · rw [if_pos (show i = i / 64 * 64 + k by omega), if_pos hkbit]
      · rw [if_neg (show i ≠ i / 64 * 64 + k by omega), if_neg hkbit]
    · simp only [he, ite_false]
      apply packedBit_ext
      intro k hk
      rw [packedWord_bit _ _ k hk, packedWord_bit xs _ k hk]
      rw [scalar_getD_set xs i _ value hi]
      have hp : i ≠ c * 64 + k := by omega
      rw [if_neg hp]


/-- Logical bit inspection depends only on the visible word list. -/
theorem scalar_bitAt_contents {N : Nat} (s : State) (B : BitArray N)
    (words : List U64) (i : Nat)
    (hc : s.contents B.chunks = words.map some) (hi : i / 64 < words.length) :
    bitAt s B i = packedBit words[i / 64] (i % 64) := by
  unfold bitAt
  rw [hc, List.getElem?_map, List.getElem?_eq_getElem hi]
  simp only [Option.map_some]
  exact scalar_mask_test_ofNat _ _ (Nat.mod_lt _ (by decide))

/-- Decoding an encoded chunk returns the corresponding source bit. -/
theorem scalar_bitAt_initial {N : Nat} (xs : List Bool) (dims : List I64)
    (i : Nat) (hn : xs.length ≤ 9223372036854775807) (hi : i < xs.length) :
    bitAt (initWords (encodeBits xs)) (⟨0, int xs.length, dims⟩ : BitArray N) i =
      xs.getD i false := by
  have hc : i / 64 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have hw : (encodeBits xs).length ≤ 9223372036854775807 :=
    packedEncoded_lengthBound xs hn
  have he := scalar_bitAt_contents (initWords (encodeBits xs))
    (⟨0, int xs.length, dims⟩ : BitArray N) (encodeBits xs) i
    (scalar_initial_contents (encodeBits xs) hw) hc
  rw [he]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  rw [packedWord_bit xs _ _ (Nat.mod_lt _ (by decide))]
  have hindex : i / 64 * 64 + i % 64 = i := by omega
  rw [hindex]

/-- Any store with an encoding decodes to the original logical sequence. -/
theorem scalar_bitValues_contents {N : Nat} (s : State) (B : BitArray N)
    (xs : List Bool) (hn : xs.length ≤ 9223372036854775807)
    (hl : B.len = int xs.length)
    (hc : s.contents B.chunks = (encodeBits xs).map some) : bitValues s B = xs := by
  unfold bitValues
  rw [hl, packedInt_val xs.length hn, Int.toNat_natCast]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range]
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_range]
    have hchunk : i / 64 < (encodeBits xs).length := by
      rw [packedEncoded_length]
      unfold wordCount
      omega
    rw [scalar_bitAt_contents s B (encodeBits xs) i hc hchunk]
    simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
    rw [packedWord_bit xs _ _ (Nat.mod_lt _ (by decide))]
    have hindex : i / 64 * 64 + i % 64 = i := by omega
    rw [hindex]
    exact (List.getElem_eq_getD false).symm

/-- Initial packed storage decodes to the entire original logical sequence. -/
theorem scalar_bits_initial {N : Nat} (xs : List Bool) (dims : List I64)
    (hn : xs.length ≤ 9223372036854775807) :
    bitValues (initWords (encodeBits xs)) (⟨0, int xs.length, dims⟩ : BitArray N) = xs := by
  exact scalar_bitValues_contents _ _ xs hn rfl
    (scalar_initial_contents (encodeBits xs) (packedEncoded_lengthBound xs hn))

/-- Padding bits above the logical end are zero in every encoded vector. -/
theorem scalar_encoded_padding (xs : List Bool)
    (hpos : 0 < xs.length) (hn : xs.length ≤ 9223372036854775807) :
    and_int (packedPrefix xs (wordCount xs.length - 1) 64)
      (not_int (maskEnd (int xs.length))) = u64 0 := by
  apply packedBit_ext
  intro k hk
  rw [scalar_packedBit_and, scalar_packedBit_not _ k hk,
    packedWord_bit xs _ k hk, packedMask_last_bit xs.length k hpos hn, packedBit_zero]
  by_cases hi : (wordCount xs.length - 1) * 64 + k < xs.length
  · simp only [hi, decide_true, Bool.not_true, Bool.and_false]
  · rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), Option.getD_none]
    rfl

/-- Native chunk-count arithmetic expressed using natural lengths. -/
theorem scalar_count_nat (n : Nat) (hn : n ≤ 9223372036854775807) :
    (numBitChunks (int n)).val.toNat = wordCount n := by
  have hi := packedInt_val n hn
  rw [scalar_num_chunks _ (by rw [hi]; omega), hi]
  unfold wordCount
  omega

/-- The final visible encoded chunk is the final packed prefix. -/
theorem scalar_encoded_last_some (xs : List Bool) (hp : 0 < xs.length) :
    ((encodeBits xs).map some).getLast? =
      some (some (packedPrefix xs (wordCount xs.length - 1) 64)) := by
  have hc : 0 < wordCount xs.length := by unfold wordCount; omega
  rw [List.getLast?_eq_getElem?, List.length_map, packedEncoded_length,
    List.getElem?_map,
    List.getElem?_eq_getElem (by rw [packedEncoded_length]; omega)]
  simp only [Option.map_some, packedPrefix_eq_encode,
    List.getElem_map, List.getElem_range]

/-- Any store with the encoded contents satisfies the packed representation invariant. -/
theorem scalar_invariant_of_contents {N : Nat} (s : State) (B : BitArray N)
    (xs : List Bool) (hn : xs.length ≤ 9223372036854775807)
    (hl : B.len = int xs.length)
    (hc : s.contents B.chunks = (encodeBits xs).map some) :
    Round5.Round2.PackedInvariant s B := by
  have hcount : (s.contents B.chunks).length = (numBitChunks B.len).val.toNat := by
    rw [hc, hl, List.length_map, packedEncoded_length, scalar_count_nat xs.length hn]
  by_cases hz : xs.length = 0
  · have hzero : (int (xs.length : Int) == int 0) = true := by rw [hz]; rfl
    refine ⟨hcount, ?_⟩
    simp only [hl, hzero, ite_true]
  · have hp : 0 < xs.length := by omega
    have hne : (int (xs.length : Int) == int 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro he
      have hv := congrArg Subtype.val he
      rw [packedInt_val xs.length hn] at hv
      change (xs.length : Int) = 0 at hv
      omega
    refine ⟨hcount, ?_⟩
    simp only [hl, hne, Bool.false_eq_true, ite_false, hc, scalar_encoded_last_some xs hp]
    change and_int (packedPrefix xs (wordCount xs.length - 1) 64)
      (not_int (maskEnd B.len)) = u64 0
    rw [hl]
    exact scalar_encoded_padding xs hp hn

/-- Encoding produces the required chunk count and zero padding. -/
theorem scalar_initial_invariant {N : Nat} (xs : List Bool) (dims : List I64)
    (hn : xs.length ≤ 9223372036854775807) :
    Round5.Round2.PackedInvariant (initWords (encodeBits xs))
      (⟨0, int xs.length, dims⟩ : BitArray N) := by
  exact scalar_invariant_of_contents _ _ xs hn rfl
    (scalar_initial_contents (encodeBits xs) (packedEncoded_lengthBound xs hn))


/-- Natural-number form of the machine chunk-address calculation. -/
theorem scalar_chunks_nat (i : Nat) (hi : i + 1 ≤ 9223372036854775807) :
    getChunksId (int ((i + 1 : Nat) : Int)) =
      (int ((i / 64 + 1 : Nat) : Int), int ((i % 64 : Nat) : Int)) := by
  have hv := packedInt_val (i + 1) hi
  have h := scalar_chunks_id (int ((i + 1 : Nat) : Int)) (by
    change 1 ≤ (int ((i + 1 : Nat) : Int)).val
    rw [hv]
    omega)
  rw [hv] at h
  apply Prod.ext
  · apply Subtype.ext
    rw [h.1, packedInt_val (i / 64 + 1) (by omega)]
    omega
  · apply Subtype.ext
    rw [h.2, packedInt_val (i % 64) (by omega)]
    omega

/-- Read execution from a known chunk address and successful word read. -/
theorem scalar_internal_read_run (s : State) (chunks : Nat) (i chunk bit : I64)
    (word : U64) (ha : getChunksId i = (chunk, bit))
    (hg : (mutableGet chunks chunk).run s = (.ok word, s)) :
    (unsafeBitGetIndex chunks i).run s =
      (.ok (and_int word (shl_int (u64 1) bit) != u64 0), s) := by
  simp only [unsafeBitGetIndex, ha, shape_run_bind, hg, shape_run_pure]

/-- Store execution from known address, read, and word-write results. -/
theorem scalar_internal_write_run (s s' : State) (chunks : Nat) (i chunk bit : I64)
    (word : U64) (value : Bool) (ha : getChunksId i = (chunk, bit))
    (hg : (mutableGet chunks chunk).run s = (.ok word, s))
    (hs : (mutableSet chunks
      (if value then or_int word (shl_int (u64 1) bit)
       else and_int word (not_int (shl_int (u64 1) bit))) chunk).run s = (.ok (), s')) :
    (unsafeBitSetIndex chunks value i).run s = (.ok (), s') := by
  simp only [unsafeBitSetIndex, unsafeBitSetIndexAt, ha, shape_run_bind, hg, hs]

/-- The internal read obtains the intended bit from encoded storage. -/
theorem scalar_read_initial (xs : List Bool) (i : Nat)
    (hn : xs.length ≤ 9223372036854775807) (hi : i < xs.length) :
    (unsafeBitGetIndex 0 (int ((i + 1 : Nat) : Int))).run
      (initWords (encodeBits xs)) =
        (.ok (xs.getD i false), initWords (encodeBits xs)) := by
  have hw : (encodeBits xs).length ≤ 9223372036854775807 :=
    packedEncoded_lengthBound xs hn
  have hc : i / 64 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  have he := scalar_internal_read_run (initWords (encodeBits xs)) 0
    (int ((i + 1 : Nat) : Int)) (int ((i / 64 + 1 : Nat) : Int)) (int ((i % 64 : Nat) : Int))
    (encodeBits xs)[i / 64] (scalar_chunks_nat i (by omega))
    (packedObserve_read (encodeBits xs) hw (i / 64) hc)
  rw [he, scalar_mask_test _ (i % 64) (Nat.mod_lt i (by decide))]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
  rw [packedWord_bit xs _ _ (Nat.mod_lt _ (by decide))]
  have heq : i / 64 * 64 + i % 64 = i := by omega
  rw [heq]

/-- The internal setter installs precisely the encoding of a list update. -/
theorem scalar_write_initial (xs : List Bool) (i : Nat) (value : Bool)
    (hn : xs.length ≤ 9223372036854775807) (hi : i < xs.length) :
    (unsafeBitSetIndex 0 value (int ((i + 1 : Nat) : Int))).run
      (initWords (encodeBits xs)) =
        (.ok (), initWords (encodeBits (xs.set i value))) := by
  have hw : (encodeBits xs).length ≤ 9223372036854775807 :=
    packedEncoded_lengthBound xs hn
  have hc : i / 64 < (encodeBits xs).length := by
    rw [packedEncoded_length]
    unfold wordCount
    omega
  apply scalar_internal_write_run (initWords (encodeBits xs))
    (initWords (encodeBits (xs.set i value))) 0
    (int ((i + 1 : Nat) : Int)) (int ((i / 64 + 1 : Nat) : Int)) (int ((i % 64 : Nat) : Int))
    (encodeBits xs)[i / 64] value (scalar_chunks_nat i (by omega))
    (packedObserve_read (encodeBits xs) hw (i / 64) hc)
  rw [scalar_initial_set (encodeBits xs) (i / 64) _ hw hc]
  rw [scalar_encode_set xs i value hi]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range,
    scalar_set_word]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem scalar_valid_index_coordinates (xs : List Bool) (i : I64)
    (hn : xs.length ≤ 9223372036854775807)
    (hi : int 1 ≤ i ∧ i ≤ int xs.length) :
    i.val.toNat - 1 < xs.length ∧
      i = int ((i.val.toNat - 1 + 1 : Nat) : Int) := by
  have hlen := packedInt_val xs.length hn
  have hiv : 1 ≤ i.val ∧ i.val ≤ xs.length := by
    change 1 ≤ i.val ∧ i.val ≤ (int xs.length).val at hi
    rw [hlen] at hi
    exact hi
  have hj : i.val.toNat - 1 < xs.length := by omega
  have hjmax : i.val.toNat - 1 + 1 ≤ 9223372036854775807 := by omega
  refine ⟨hj, ?_⟩
  apply Subtype.ext
  rw [packedInt_val _ hjmax]
  omega
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

/-- Successful conversions are also read-only. -/
theorem dequeConvertOk {X : Type} [JuliaLean.base.range.JConvert Bool X]
    (x : X) (value : Bool) (s : State)
    (h : JuliaLean.base.range.JConvert.convert (T := Bool) x = .ok value) :
    (Round5.Round2.convertBoolMutation x).run s = (.ok value, s) := by
  simp only [Round5.Round2.convertBoolMutation, h, Round5.Round2.liftRangeResult]
  rfl

/-- With spare storage, chunk growth only changes the array header. -/
theorem dequeGrowWithRoom (s : State) (slots : List (Option U64))
    (n delta : I64)
    (ha : s.arrays[0]? = some ⟨(0, one), n⟩)
    (hm : s.memories[0]? = some slots)
    (hd : JuliaLean.base.array.zero ≤ delta)
    (hr : ¬ (JInt.wrap .i64 slots.length - (one - one) - n < delta)) :
    (growChunkVector 0 delta).run s =
      (.ok (), { s with arrays := s.arrays.set 0 ⟨(0, one), n + delta⟩ }) := by
  simp only [growChunkVector, growend, mutableStorage, mutableRef,
    memoryRead, shape_run_bind, shape_run_pure, hd, decide_true,
    Bool.not_true, Bool.false_eq_true, ite_false, shape_vector_run,
    ha, shape_length_run s n ha, shape_run_get, hm, hr, shape_run_modify]

/-- Removing a suffix updates the header; UInt64 unset leaves the backing slots assigned. -/
theorem dequeDeleteChunks (s : State) (slots : List (Option U64))
    (n delta : I64)
    (ha : s.arrays[0]? = some ⟨(0, one), n⟩)
    (hm : s.memories[0]? = some slots)
    (hn : n.val ≤ (slots.length : Int))
    (hd : ¬ (JInt.rem .u64 delta > JInt.rem .u64 n))
    (hi : ∀ j ∈ intRange (n - delta + one) n, 1 ≤ j.val ∧ j.val ≤ n.val) :
    (deleteChunkEnd 0 delta).run s =
      (.ok (), { s with arrays := s.arrays.set 0 ⟨(0, one), n - delta⟩ }) := by
  have hl := shape_unset_loop n (intRange (n - delta + one) n) s slots ha hm hn hi
  simp only [deleteChunkEnd, deleteend, mutableStorage, MemoryLayoutMetadata.ofRuntime,
    shape_run_bind, shape_run_pure, shape_length_run s n ha, hd, ite_false, hl,
    shape_vector_run, ha, shape_run_modify]

/-- Small nonnegative shift counts retain their unsigned bit-pattern value. -/
theorem dequeShiftCountNat (n : Nat) (hn : n < 64) :
    (fromJInt (int n)).toNat = n := by
  rw [fromJInt, BitVec.toNat_ofInt, packedInt_val n (by omega)]
  change ((n : Int) % 18446744073709551616).toNat = n
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]

/-- Packed words have no bits above their 64-bit width. -/
theorem dequePackedBitHigh (word : U64) (k : Nat) (hk : 64 ≤ k) :
    packedBit word k = false := by
  rw [← packedBit_fromJInt]
  exact BitVec.getLsbD_of_ge (fromJInt word) k hk

/-- The concrete left-shift intrinsic moves low bits and zero-fills. -/
theorem dequePackedShiftLeft (word : U64) (n k : Nat) (hn : n < 64) :
    packedBit (shl_int word (int n)) k =
      (decide (k < 64) && (decide (n ≤ k) && packedBit word (k - n))) := by
  unfold shl_int
  rw [packedBit_toJInt]
  unfold jlShlInt
  rw [dequeShiftCountNat n hn,
    if_neg (show ¬ n ≥ IntTy.u64.bits by exact Nat.not_le.mpr hn)]
  rw [BitVec.getLsbD_ofNat, packedFromJInt_nat, Nat.testBit_mul_two_pow]
  rfl

/-- The concrete logical right-shift intrinsic selects higher input bits. -/
theorem dequePackedShiftRight (word : U64) (n k : Nat) (hn : n < 64) :
    packedBit (lshr_int word (int n)) k =
      (decide (k < 64) && packedBit word (k + n)) := by
  unfold lshr_int
  rw [packedBit_toJInt]
  unfold jlLshrInt
  rw [dequeShiftCountNat n hn,
    if_neg (show ¬ n ≥ IntTy.u64.bits by exact Nat.not_le.mpr hn)]
  rw [BitVec.getLsbD_ofNat, packedFromJInt_nat, Nat.testBit_div_two_pow]
  rfl

/-- Bitwise conjunction acts pointwise on packed words. -/
theorem dequePackedAnd (a b : U64) (k : Nat) :
    packedBit (and_int a b) k = (packedBit a k && packedBit b k) := by
  simp only [and_int, jlAndInt, packedBit_toJInt, BitVec.getLsbD_and,
    packedBit_fromJInt]

/-- Canonical packed storage with an explicit amount of unused capacity. -/
def dequeWordStore (words : List U64) (spare : Nat) : State :=
  ⟨[words.map some ++ List.replicate spare none],
    [⟨(0, one), int words.length⟩]⟩

theorem dequeWordStoreInitial (words : List U64) :
    dequeWordStore words 32 = initWords words := by
  simp only [dequeWordStore, initWords, MutableMemory.initial, List.length_map]
  rfl

theorem dequeWordVector (words : List U64) (spare : Nat) :
    (mutableVector 0).run (dequeWordStore words spare) =
      (.ok ⟨(0, one), int words.length⟩, dequeWordStore words spare) := rfl

theorem dequeWordMemory (words : List U64) (spare : Nat) :
    (memoryRead 0).run (dequeWordStore words spare) =
      (.ok (words.map some ++ List.replicate spare none), dequeWordStore words spare) := rfl

theorem dequeWordLength (words : List U64) (spare : Nat) :
    (mutableLength 0).run (dequeWordStore words spare) =
      (.ok (int words.length), dequeWordStore words spare) := by
  simp only [mutableLength, shape_run_bind, dequeWordVector, shape_run_pure]

/-- Reading a chunk is independent of the unused capacity after it. -/
theorem dequeWordRead (words : List U64) (spare j : Nat)
    (hn : words.length ≤ 9223372036854775807) (hj : j < words.length) :
    (mutableGet 0 (int ((j + 1 : Nat) : Int))).run (dequeWordStore words spare) =
      (.ok (words.getD j (u64 0)), dequeWordStore words spare) := by
  have hi := packedInt_val (j + 1) (by omega)
  have hsize := packedInt_val words.length hn
  have hb : 1 ≤ (int ((j + 1 : Nat) : Int)).val ∧
      int ((j + 1 : Nat) : Int) ≤ int (words.length : Int) := by
    change 1 ≤ (int ((j + 1 : Nat) : Int)).val ∧
      (int ((j + 1 : Nat) : Int)).val ≤ (int (words.length : Int)).val
    rw [hi, hsize]
    omega
  have hidx : (one.val + (int ((j + 1 : Nat) : Int)).val - 2).toNat = j := by
    rw [hi]
    change (1 + ((j + 1 : Nat) : Int) - 2).toNat = j
    omega
  have hget : (words.map some ++ List.replicate spare none)[j]? =
      some (some (words.getD j (u64 0))) := by
    rw [List.getElem?_append_left (by simpa only [List.length_map] using hj)]
    rw [List.getElem?_map, List.getElem?_eq_getElem hj]
    rw [List.getElem_eq_getD]
    rfl
  simp only [mutableGet, shape_run_bind, dequeWordVector, hb.1, hb.2,
    and_self, decide_true, Bool.not_true, Bool.false_eq_true, ite_false,
    dequeWordMemory, hidx, hget, shape_run_pure]

/-- A concrete word write keeps the rest of the backing store intact. -/
theorem dequeMemoryWrite (s : State) (slots : List (Option U64))
    (hm : s.memories[0]? = some slots) (j : I64) (word : U64)
    (hj : 1 ≤ j.val ∧ j.val ≤ (slots.length : Int)) :
    (memoryWrite 0 j (some word)).run s =
      (.ok (), {s with memories := s.memories.set 0 (slots.set (j.val - 1).toNat (some word))}) := by
  simp only [memoryWrite, memoryRead, shape_run_bind, shape_run_get, hm,
    shape_run_pure, hj, and_self, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_false, shape_run_modify]

/-- A word write in a raw store requires only the header and backing-slot bounds. -/
theorem dequeSetRaw (s : State) (slots : List (Option U64)) (n j : I64) (word : U64)
    (ha : s.arrays[0]? = some ⟨(0, one), n⟩)
    (hm : s.memories[0]? = some slots)
    (hn : n.val ≤ (slots.length : Int))
    (hj : 1 ≤ j.val ∧ j.val ≤ n.val) :
    (mutableSet 0 word j).run s =
      (.ok (), { s with memories := s.memories.set 0 (slots.set (j.val - 1).toNat (some word)) }) := by
  have hin : one ≤ j ∧ j ≤ n := hj
  have hw := dequeMemoryWrite s slots hm j word (by omega)
  simp only [mutableSet, setindexTyped, mutableBounds, mutableInBounds,
    mutableLength, mutableMemoryref, mutableRef, shape_run_bind, shape_vector_run,
    ha, shape_run_pure, hin, and_self, decide_true, Bool.not_true,
    Bool.false_eq_true, ite_false, shape_one_add_sub_one, hw]

/-- A chunk write changes one word regardless of the amount of spare capacity. -/
theorem dequeWordSet (words : List U64) (spare j : Nat) (word : U64)
    (hn : words.length ≤ 9223372036854775807) (hj : j < words.length) :
    (mutableSet 0 word (int ((j + 1 : Nat) : Int))).run (dequeWordStore words spare) =
      (.ok (), dequeWordStore (words.set j word) spare) := by
  have hi := packedInt_val (j + 1) (by omega)
  have hsize := packedInt_val words.length hn
  have hin : one ≤ int ((j + 1 : Nat) : Int) ∧
      int ((j + 1 : Nat) : Int) ≤ int words.length := by
    change 1 ≤ (int ((j + 1 : Nat) : Int)).val ∧
      (int ((j + 1 : Nat) : Int)).val ≤ (int words.length).val
    rw [hi, hsize]
    omega
  have hidx : ((int ((j + 1 : Nat) : Int)).val - 1).toNat = j := by
    rw [hi]
    omega
  have hslots : (words.map some ++ List.replicate spare none).length = words.length + spare := by
    simp only [List.length_append, List.length_map, List.length_replicate]
  have hraw := dequeSetRaw (dequeWordStore words spare)
    (words.map some ++ List.replicate spare none) (int words.length)
    (int ((j + 1 : Nat) : Int)) word rfl rfl
    (by rw [hsize, hslots]; omega) (by rw [hi, hsize]; omega)
  rw [hraw, hidx]
  change ((.ok (), { memories := [(words.map some ++ List.replicate spare none).set j (some word)], arrays := [⟨(0, one), int words.length⟩] }) : Except Error Unit × State) = _
  rw [List.set_append_left _ _ (by simpa only [List.length_map] using hj)]
  rw [← List.map_set]
  simp only [dequeWordStore, List.length_set]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4
/-- Pointwise observation of a list update, including out-of-range reads. -/
theorem dequeWordGetSet (words : List U64) (i j : Nat) (word : U64)
    (hi : i < words.length) :
    (words.set i word).getD j (u64 0) =
      (if i = j then word else words.getD j (u64 0)) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set, hi, and_self, ite_true]
  by_cases he : i = j <;> simp only [he, ite_true, ite_false, Option.getD_some]

/-- Integer literals commute with the modeled wrapping subtraction. -/
theorem dequeIntSub (a b : Int) : int a - int b = int (a - b) := by
  apply Subtype.ext
  change wrapInt .i64 (wrapInt .i64 a - wrapInt .i64 b) = wrapInt .i64 (a - b)
  apply shape_wrap64_congr
  rw [Int.sub_emod, shape_wrap64_mod, shape_wrap64_mod, ← Int.sub_emod]

/-- Logical contents do not depend on the reserve after the visible chunks. -/
theorem dequeWordContents (words : List U64) (spare : Nat)
    (hn : words.length ≤ 9223372036854775807) :
    (dequeWordStore words spare).contents 0 = words.map some := by
  change ((words.map some ++ List.replicate spare none).drop 0).take
    (int words.length).val.toNat = words.map some
  rw [packedInt_val words.length hn, Int.toNat_natCast, List.drop_zero]
  exact List.take_left' (List.length_map ..)

/-- A visible word prefix followed by arbitrary backing slots beyond the header. -/
def dequeTailStore (words : List U64) (tail : List (Option U64)) : State :=
  ⟨[words.map some ++ tail], [⟨(0, one), int words.length⟩]⟩

/-- The chunk-extension action shared by pushes and insertions. -/
def dequeGrowZero : BitMutationM Unit := do
  growChunkVector 0 (int 1)
  mutableSet 0 (u64 0) (← mutableLength 0)

/-- Chunks entirely above the logical sequence are identically zero. -/
theorem dequePackedBeyond (xs : List Bool) (chunk : Nat)
    (hc : xs.length ≤ chunk * 64) : packedPrefix xs chunk 64 = u64 0 := by
  apply packedBit_ext
  intro k hk
  rw [packedWord_bit xs chunk k hk, packedBit_zero]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- Read-only loop control transports an abstract state invariant through a fold. -/
theorem dequeForInFold {ι σ : Type} (action : ι → BitMutationM Unit)
    (step : σ → ι → σ) (store : σ → State) (P : σ → Prop) (indices : List ι)
    (hrun : ∀ w, P w → ∀ i ∈ indices,
      (action i).run (store w) = (.ok (), store (step w i)))
    (hpres : ∀ w, P w → ∀ i ∈ indices, P (step w i)) :
    ∀ w, P w →
      (forIn indices PUnit.unit (fun i _ => do
        action i
        pure (ForInStep.yield PUnit.unit))).run (store w) =
          (.ok PUnit.unit, store (indices.foldl step w)) := by
  induction indices with
  | nil =>
    intro w _
    rfl
  | cons i indices ih =>
    intro w hw
    have hs := hrun w hw i List.mem_cons_self
    have hp := hpres w hw i List.mem_cons_self
    have ht := ih
      (fun w hw j hj => hrun w hw j (List.mem_cons_of_mem i hj))
      (fun w hw j hj => hpres w hw j (List.mem_cons_of_mem i hj))
      (step w i) hp
    simp only [List.forIn_cons, shape_run_bind, hs, shape_run_pure]
    exact ht

/-- The growth action can be verified using its three primitive outcomes. -/
theorem dequeGrowZeroFrom (s mid out : State) (n : I64)
    (hg : (growChunkVector 0 (int 1)).run s = (.ok (), mid))
    (hl : (mutableLength 0).run mid = (.ok n, mid))
    (hw : (mutableSet 0 (u64 0) n).run mid = (.ok (), out)) :
    dequeGrowZero.run s = (.ok (), out) := by
  simp only [dequeGrowZero, shape_run_bind, hg, hl, hw]

theorem dequeNatAddOne (j : Nat) : int j + int 1 = int ((j + 1 : Nat) : Int) := by
  rw [packedInt_add]
  rfl

/-- Combining a word with zero leaves it unchanged. -/
theorem dequePackedOrZero (word : U64) : or_int word (u64 0) = word := by
  apply packedBit_ext
  intro k _
  rw [packedBit_or, packedBit_zero, Bool.or_false]

/-- Indexed access to an encoded word. -/
theorem dequeEncodedGet (xs : List Bool) (chunk : Nat)
    (hc : chunk < wordCount xs.length) :
    (encodeBits xs).getD chunk (u64 0) = packedPrefix xs chunk 64 := by
  rw [← List.getElem_eq_getD (h := by rw [packedEncoded_length]; exact hc)]
  simp only [packedPrefix_eq_encode, List.getElem_map, List.getElem_range]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1
open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.bitarray JuliaLean.base.int
open JuliaLean.Proofs.base.bitarray JuliaLean.ChatGPT.Batch2.Group4

/-- Extending into spare capacity appends exactly one zero word. -/
theorem dequeGrowZeroRun (words : List U64) (spare : Nat)
    (hn : words.length + spare + 1 ≤ 9223372036854775807) :
    dequeGrowZero.run (dequeWordStore words (spare + 1)) =
      (.ok (), dequeWordStore (words ++ [u64 0]) spare) := by
  let slots := words.map some ++ List.replicate (spare + 1) none
  let s := dequeWordStore words (spare + 1)
  let n := int words.length
  let sn : State := { s with arrays := s.arrays.set 0 ⟨(0, one), n + int 1⟩ }
  have hslots : slots.length = words.length + spare + 1 := by
    simp only [slots, List.length_append, List.length_map, List.length_replicate]
    omega
  have hsucc : n + int 1 = int ((words.length + 1 : Nat) : Int) := by
    rw [packedInt_add]
    rfl
  have hroomEq : JInt.wrap .i64 slots.length - (one - one) - n =
      int ((spare + 1 : Nat) : Int) := by
    change int slots.length - (int 1 - int 1) - int words.length = _
    rw [shape_int_sub_self, dequeIntSub, dequeIntSub]
    congr 1
    rw [hslots]
    omega
  have hroom : ¬ (JInt.wrap .i64 slots.length - (one - one) - n < int 1) := by
    rw [hroomEq]
    change ¬ (int ((spare + 1 : Nat) : Int)).val < 1
    rw [packedInt_val (spare + 1) (by omega)]
    omega
  have hg : (growChunkVector 0 (int 1)).run s = (.ok (), sn) :=
    dequeGrowWithRoom s slots n (int 1) rfl rfl (by decide) hroom
  have ha : sn.arrays[0]? = some ⟨(0, one), n + int 1⟩ := rfl
  have hm : sn.memories[0]? = some slots := rfl
  have hv : (n + int 1).val = (words.length + 1 : Nat) := by
    rw [hsucc, packedInt_val (words.length + 1) (by omega)]
  have hl : (mutableLength 0).run sn = (.ok (n + int 1), sn) :=
    shape_length_run sn (n + int 1) ha
  have hw := dequeSetRaw sn slots (n + int 1) (n + int 1) (u64 0) ha hm
    (by rw [hv, hslots]; omega) (by rw [hv]; omega)
  have hi : ((n + int 1).val - 1).toNat = words.length := by rw [hv]; omega
  have hs : slots.set words.length (some (u64 0)) =
      (words ++ [u64 0]).map some ++ List.replicate spare none := by
    unfold slots
    rw [List.set_append_right _ _ (by rw [List.length_map]; omega)]
    simp only [List.length_map, Nat.sub_self, List.replicate_succ, List.set_cons_zero,
      List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
      List.nil_append]
  change dequeGrowZero.run s = (.ok (), dequeWordStore (words ++ [u64 0]) spare)
  rw [dequeGrowZeroFrom s sn _ (n + int 1) hg hl hw, hi, hs]
  simp only [sn, s, dequeWordStore, List.set_cons_zero, hsucc,
    List.length_append, List.length_cons, List.length_nil, Nat.add_zero]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

/-- The installed native UnitRange length is the same wrapped arithmetic used by Base. -/
theorem rangeDelete_length_formula (r : BitRange) :
    Round5.Round2.installedBitRangeLength r =
      (pure (int 1 + (r.last - r.first)) : BitMutationM I64) := by
  simp only [Round5.Round2.installedBitRangeLength,
    JuliaLean.Proofs.base.range.lengthUnit, JuliaLean.base.range.length_AbstractUnitRange, JuliaLean.base.range.JFirst.first, JuliaLean.base.range.JLast.last,
    JuliaLean.base.range.first_OrdinalRange, JuliaLean.base.range.last_OrdinalRange, JuliaLean.base.range.JFieldStart.start, JuliaLean.base.range.JFieldStop.stop,
    JuliaLean.Proofs.base.range.convert_self, bind, Except.bind, pure, Except.pure, JuliaLean.base.range.JType.isSigned,
    IntTy.signed, Bool.true_or, ite_true, JuliaLean.base.range.JInteger.integer,
    JuliaLean.Proofs.base.range.liftIntegerConvertI64]
  change (pure (JuliaLean.base.int.add
    (JuliaLean.base.range.JOneunit.oneunit : I64)
    (JuliaLean.base.int.sub r.last r.first)) : BitMutationM I64) =
      pure (int 1 + (r.last - r.first))
  apply congrArg (fun n : I64 => (pure n : BitMutationM I64))
  apply Subtype.ext
  simp only [JuliaLean.base.int.add, JuliaLean.base.int.sub,
    JuliaLean.Proofs.base.int.add_int_val, JuliaLean.Proofs.base.int.sub_int_val,
    JuliaLean.Proofs.base.range.oneunit_iv]
  rfl

/-- Expose the installed length binding without changing the range-deletion model. -/
theorem rangeDelete_public_eq (B : BitVector) (r : BitRange) :
    Round5.Round2.deleteBitRangePublic B r =
      bitVectorDeleteRange (fun _ => int 1 + (r.last - r.first)) B r := by
  unfold Round5.Round2.deleteBitRangePublic
  rw [rangeDelete_length_formula]
  rfl
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- A 130-bit input containing a single true bit at public index 65. -/
def rangeDeleteWitnessBits : List Bool :=
  List.replicate 64 false ++ [true] ++ List.replicate 65 false

/-- This small input has three fully initialized packed words. -/
theorem rangeDeleteWitness_encode :
    encodeBits rangeDeleteWitnessBits = [u64 0, u64 1, u64 0] := by
  decide
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
open JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

/-- The first vector of a two-vector store exposes exactly its initialized words. -/
theorem equalityInitialLeft (xs ys : List U64)
    (hx : xs.length ≤ 9223372036854775807) :
    (MutableMemory.initialMany [xs.map some, ys.map some]).contents 0 = xs.map some := by
  have hv : (JInt.wrap .i64 (xs.map some).length).val.toNat = xs.length := by
    rw [List.length_map]
    change (int (xs.length : Int)).val.toNat = xs.length
    rw [packedInt_val xs.length hx, Int.toNat_natCast]
  change ((xs.map some ++ List.replicate 32 none).drop 0).take
    (JInt.wrap .i64 (xs.map some).length).val.toNat = xs.map some
  rw [List.drop_zero, hv]
  have hn : xs.length = (xs.map some).length := (List.length_map _).symm
  rw [hn, List.take_left]
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray

namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.Registry JuliaLean.base.array JuliaLean.base.int JuliaLean.base.bitarray
namespace JuliaLean.ChatGPT.Batch3.Group1

open JuliaLean JuliaLean.C JuliaLean.base.array JuliaLean.base.int
open JuliaLean.base.bitarray JuliaLean.Proofs.base.bitarray
open JuliaLean.ChatGPT.Batch2.Group4

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- A native interval whose endpoints coincide contains just that endpoint. -/
theorem endPop_range_singleton (n : I64) : intRange n n = [n] := by
  unfold intRange
  rw [Int.sub_self, Int.zero_add]
  change [JInt.wrap .i64 (n.val + 0)] = [n]
  congr 1
  apply Subtype.ext
  rw [Int.add_zero]
  exact wrapInt_of_inRange .i64 n.val n.property
end JuliaLean.ChatGPT.Batch3.Group1
end JuliaLean.Proofs.base.bitarray


namespace JuliaLean.Proofs.base.bitarray

open JuliaLean JuliaLean.base.array JuliaLean.base.bitarray

def BitcountInitialTypeError : Prop :=
  ∀ (N : Nat) (T A R C : Type) (init : T) (B : BitArray N)
    (convertInit : T → BitMutationM C) (add : T → I64 → BitMutationM A)
    (remainder : A → BitMutationM R) (convertResult : R → BitMutationM C)
    (asT : C → Option T) (initial : C) (s final : MutableMemory U64),
    (convertInit init).run s = (.ok initial, final) → asT initial = none →
    (bitcountDispatch convertInit add remainder convertResult asT init B.chunks).run s =
      (.error (.typeError "bitcount: n"), final) ∧
    (bitArrayCountDispatch convertInit add remainder convertResult asT B init).run s =
      (.error (.typeError "bitcount: n"), final)

end JuliaLean.Proofs.base.bitarray

import JuliaLean.Core
import JuliaLean.Registry.Types
import JuliaLean.base.array
import JuliaLean.base.int
import JuliaLean.base.bitarray

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
  let chunks ← mutableAllocate 0 (numBitChunks n)
  let nc ← mutableLength chunks
  for i in intRange (int 1) nc do mutableSet chunks (u64 0) i
  return ⟨chunks, n, [n]⟩

def cloneVector (B : BitVector) : BitMutationM BitVector := do
  let n ← mutableLength B.chunks
  let chunks ← mutableAllocate B.chunks n
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
  let copy ← mutableAllocate bc n
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

def CountAnyAllAgrees : Prop :=
  ∀ (xs : List Bool),
    let B := vectorBits xs
    let state := initWords (encodeBits xs)
    let count := (bitArrayCountIdentity (fun bc init => bitcount
      (fun n c => n + c) id (fun word => int (Int.ofNat (popcountWord word))) init bc) B (int 0)).run state
    let any := (bitArrayAny B).run state
    let all := (bitArrayAll B).run state
    count.1 = .ok (int (Int.ofNat (countTrue xs))) ∧ any.1 = .ok (xs.any id) ∧ all.1 = .ok (xs.all id)

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
  let chunks ← mutableAllocate B.chunks n
  for i in intRange (int 1) n do mutableSet chunks (← mutableGet B.chunks i) i
  return { B with chunks := chunks }

def similarBitArray {N : Nat} (B : BitArray N) : BitMutationM (BitArray N) := do
  let chunks ← mutableAllocate B.chunks (numBitChunks B.len)
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
    let alloc : Nat → BitMutationM Nat := fun n => mutableAllocate 0 (int (Int.ofNat n))
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
      mutableAllocate 0 (dims.foldl (· * ·) (int 1))
    let set : Nat → Bool → I64 → BitMutationM Nat := fun handle bit i => do
      mutableSet handle (u64 (if bit then 1 else 0)) i
      pure handle
    let arrayResult := (arrayFromBitArray allocate (fun _ => int xs.length) set B).run state
    let checked : List I64 → BitMutationM I64 := fun dims => pure (dims.foldl (· * ·) (int 1))
    let allocChunks : Nat → BitMutationM Nat := fun n => mutableAllocate 0 (int (Int.ofNat n))
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
    let allocate : List I64 → BitMutationM Nat := fun dims => mutableAllocate 0 (dims.foldl (· * ·) (int 1))
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
  let chunks ← mutableAllocate 0 (numBitChunks len)
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
      let chunks ← mutableAllocate 0 (numBitChunks n)
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
    let allocate : I64 → BitMutationM Nat := fun n => mutableAllocate 0 n
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

def allocateBoolCache (n : Nat) : BitMutationM Nat := mutableAllocate 0 (int (Int.ofNat n))

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
      (fun n => mutableAllocate 0 (int (Int.ofNat n))) allocateBoolCache iterate
      setBoolCache fillBoolCacheFalse getBoolCache (fun cache _ => cache) loadEightBoolCache
      (fun chunks => mutableLength chunks) id rangeLengthSpec ()).run (MutableMemory.initial [])
    let unknown := (genBitArrayFromIterator
      (fun dims => pure (dims.foldl (· * ·) (int 1)))
      (fun n => mutableAllocate 0 (int (Int.ofNat n))) allocateBoolCache iterate
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
    let allocate : Nat → BitMutationM Nat := fun n => mutableAllocate 0 (int (Int.ofNat n))
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

def BitArrayReshapeKeepsBits : Prop :=
  ∀ (xs : List Bool) (rows cols : I64), rows * cols = int xs.length →
    let B : BitArray 2 := ⟨0, int xs.length, [int xs.length, int 1]⟩
    let checked : List I64 → BitMutationM I64 := fun dims => pure (dims.foldl (· * ·) (int 1))
    let allocate : List I64 → BitMutationM (BitArray 2) := fun dims => do
      let len := dims.foldl (· * ·) (int 1)
      let chunks ← mutableAllocate 0 (numBitChunks len)
      let count ← mutableLength chunks
      for i in intRange (int 1) count do mutableSet chunks (u64 0) i
      pure ⟨chunks, len, dims⟩
    match (bitArrayReshapeSameRank checked allocate B [rows, cols]).run (initWords (encodeBits xs)) with
    | (.ok reshaped, state') => reshaped.dims = [rows, cols] ∧ reshaped.len = int xs.length ∧ bitValues state' reshaped = xs
    | (.error _, _) => False

def BitArrayFillConstructors : Prop :=
  ∀ (dims : List I64),
    let checked : List I64 → BitMutationM I64 := fun ds => pure (ds.foldl (· * ·) (int 1))
    let allocate : Nat → BitMutationM Nat := fun n => mutableAllocate 0 (int (Int.ofNat n))
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
  ∀ (xs : List Bool),
    let B := vectorBits xs
    match (bitArraySizeof (fun chunks => mutableLength chunks) B).run (initWords (encodeBits xs)) with
    | (.ok bytes, _) => bytes = int (Int.ofNat (wordCount xs.length * 8))
    | (.error _, _) => False

def BitMatrixOneAgrees : Prop :=
  ∀ (n : Nat),
    let matrix : BitMatrix := ⟨0, int (n * n), [int n, int n]⟩
    let state := initWords (encodeBits (List.replicate (n * n) false))
    let checked : List I64 → BitMutationM I64 := fun dims => pure (dims.foldl (· * ·) (int 1))
    let allocate : Nat → BitMutationM Nat := fun count => mutableAllocate 0 (int (Int.ofNat count))
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
      let mask ← mutableAllocate 0 source.len
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
      let chunks ← mutableAllocate 0 (numBitChunks (int (Int.ofNat n)))
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
    let allocate : List I64 → BitMutationM Nat := fun dims => mutableAllocate 0 (dims.foldl (· * ·) (int 1))
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
  let chunks ← mutableAllocate 0 (int (Int.ofNat (wordCount xs.length)))
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
  ("empty!@1137", ["SpliceRemovedAgrees", "BitVectorEmptyAgrees"]),
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
  ("reshape@475", ["BitArrayReshapeKeepsBits"]),
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
  ("circshift!@1425", ["CircshiftAgrees", "CircshiftNonemptyAgrees"]),
  ("_circshift_int!@1426", ["CircshiftAgrees", "CircshiftNonemptyAgrees"]),
  ("circshift!@1444", ["CircshiftAgrees", "CircshiftNonemptyAgrees"]),
  ("bitcount@1448", ["CountAgrees", "CountAnyAllAgrees"]),
  ("_count@1456", ["CountAgrees", "CountAnyAllAgrees"]),
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
  ("findmax@1620", ["FindExtremaAgrees", "CountAnyAllAgrees"]),
  ("findmin@1633", ["FindExtremaAgrees", "CountAnyAllAgrees"]),
  ("allindices!@1652", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("allindices!@1661", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("allindices!@1666", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("_overflowind@1674", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("_overflowind@1675", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("_toind@1685", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("_toind@1686", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("findall@1688", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("findall@1717", ["BitFindAllSpec", "BitArrayChunkInBounds", "BitVectorLoopInBounds"]),
  ("_sum@1721", ["CountAnyAllAgrees"]),
  ("_sum@1722", ["CountAnyAllAgrees"]),
  ("all@1724", ["BitArrayMetadataAgrees"]),
  ("any@1736", ["BitArrayMetadataAgrees"]),
  ("minimum@1747", ["FindExtremaAgrees", "CountAnyAllAgrees"]),
  ("maximum@1748", ["FindExtremaAgrees", "CountAnyAllAgrees"]),
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
  ("sizeof@1939", ["BitArraySizeofAgrees"]),
  ("_split_rest@1941", ["ResizeAgrees", "ResizeNonnegAgrees"]),
]

/-- Open behavioral properties for `base/bitarray.jl`. -/
def entries : List JuliaLean.Registry.Entry := [
  { id := "tuples-split-rest-negative", juliaFile := "base/bitarray.jl", juliaFns := ["split_rest(v::Vector, n)", "_split_rest(a::Union{Vector,BitVector}, n)"],
    statement := "Base.split_rest(v, n) for a Vector either throws or returns (rest_but_n, last_n) whose concatenation is v.", source := "base/tuple.jl:215-226 (split_rest docstring: the first collection contains all elements but the n last ones, which make up the second)",
    status := .todo, prop := ``SplitRestPartition, thm := none },
  { id := "bitarrays-scalar-index", juliaFile := "base/bitarray.jl", juliaFns := ["getindex(::BitArray, ::Int)", "setindex!(::BitArray, x, ::Int)"],
    statement := "B[i] and B[i] = x agree with Vector{Bool} for every Int i (BoundsError outside 1:length(B)) and keep the zero padding of the last chunk.", source := "invariant: BitVector behaves as Vector{Bool} (BitArray docstring, base/bitarray.jl:7-23); unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``ScalarIndexAgrees, thm := none },
  { id := "bitarrays-deque", juliaFile := "base/bitarray.jl", juliaFns := ["push!(::BitVector, x)", "pop!(::BitVector)", "pushfirst!(::BitVector, x)", "popfirst!(::BitVector)"],
    statement := "push!, pop!, pushfirst! and popfirst! agree with Vector{Bool} (ArgumentError when popping an empty vector) and keep the chunk invariant, whatever the contents of newly allocated chunks.", source := "invariant: BitVector behaves as Vector{Bool}; unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``DequeAgrees, thm := none },
  { id := "bitarrays-insert-deleteat", juliaFile := "base/bitarray.jl", juliaFns := ["insert!(::BitVector, i, x)", "deleteat!(::BitVector, i::Integer)"],
    statement := "insert!(B, i, x) and deleteat!(B, i) agree with Vector{Bool} for every Int i and keep the chunk invariant.", source := "invariant: BitVector behaves as Vector{Bool}; insert!/deleteat! docstrings (base/array.jl)",
    status := .todo, prop := ``InsertDeleteAgrees, thm := none },
  { id := "bitarrays-deleteat-empty-range", juliaFile := "base/bitarray.jl", juliaFns := ["deleteat!(::BitVector, ::AbstractUnitRange{Int})", "splice!(::BitVector, ::AbstractUnitRange{Int}, ins)"],
    statement := "deleteat!(B, r) agrees with deleteat!(v, r) on Vector{Bool} for every UnitRange{Int} r, including empty ranges.", source := "deleteat! docstring (base/array.jl:1916-1944: remove the items at the indices given by inds); invariant: BitVector behaves as Vector{Bool}",
    status := .todo, prop := ``DeleteatRangeAgrees, thm := none },
  { id := "bitarrays-deleteat-range-inside", juliaFile := "base/bitarray.jl", juliaFns := ["deleteat!(::BitVector, ::AbstractUnitRange{Int})", "copy_chunks!"],
    statement := "deleteat!(B, r) agrees with Vector{Bool} and keeps the chunk invariant for every UnitRange{Int} r that is nonempty or starts in 1:length(B)+1.", source := "invariant: BitVector behaves as Vector{Bool}; unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``DeleteatRangeInsideAgrees, thm := none },
  { id := "bitarrays-append-prepend", juliaFile := "base/bitarray.jl", juliaFns := ["append!(::BitVector, ::BitVector)", "prepend!(::BitVector, ::BitVector)", "copy_chunks!", "copy_chunks_rtol!"],
    statement := "append!(B, C) and prepend!(B, C) compute [B; C] and [C; B] and keep the chunk invariant, also when C === B.", source := "append!/prepend! docstrings (base/array.jl); unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``AppendPrependAgrees, thm := none },
  { id := "bitarrays-resize-negative", juliaFile := "base/bitarray.jl", juliaFns := ["resize!(::BitVector, n)"],
    statement := "resize!(B, n; first) throws the same exception type as resize!(v, n) on Vector{Bool} (ArgumentError for n < 0) and otherwise keeps the old elements and the invariant.", source := "invariant: BitVector behaves as Vector{Bool}; resize!(::Vector) throws ArgumentError(\"new length must be ≥ 0\") (base/array.jl:1575-1576)",
    status := .todo, prop := ``ResizeAgrees, thm := none },
  { id := "bitarrays-resize-nonneg", juliaFile := "base/bitarray.jl", juliaFns := ["resize!(::BitVector, n; first)"],
    statement := "For every n >= 0, resize!(B, n; first) returns a valid BitVector of length n keeping the old elements (at the end when first=true).", source := "resize! docstring (base/array.jl); unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``ResizeNonnegAgrees, thm := none },
  { id := "bitarrays-fill", juliaFile := "base/bitarray.jl", juliaFns := ["fill!(::BitArray, x)"],
    statement := "fill!(B, x) sets every element to x and keeps the chunk invariant.", source := "fill! docstring; unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``FillAgrees, thm := none },
  { id := "bitarrays-shift", juliaFile := "base/bitarray.jl", juliaFns := ["<<(::BitVector, ::Int)", ">>(::BitVector, ::Int)", ">>>(::BitVector, ::Int)", "<<(::BitVector, ::UInt)", ">>>(::BitVector, ::UInt)"],
    statement := "B << k and B >> k (= B >>> k) shift the elements k positions backwards resp. forwards for every k::Int, filling with false, and return valid BitVectors.", source := "<< and >> docstrings (base/bitarray.jl:1333-1414)",
    status := .todo, prop := ``ShiftAgrees, thm := none },
  { id := "bitarrays-circshift-empty", juliaFile := "base/bitarray.jl", juliaFns := ["circshift!(::BitVector, ::Integer)", "circshift!(::BitVector, ::BitVector, ::Integer)"],
    statement := "circshift!(B, k) and circshift!(dest, B, k) agree with circshift! on Vector{Bool} for every k::Int, including empty vectors.", source := "invariant: BitVector behaves as Vector{Bool}; circshift!(::AbstractVector) returns empty vectors unchanged (base/abstractarray.jl:3756-3758)",
    status := .todo, prop := ``CircshiftAgrees, thm := none },
  { id := "bitarrays-circshift-nonempty", juliaFile := "base/bitarray.jl", juliaFns := ["circshift!(::BitVector, ::Integer)", "circshift!(::BitVector, ::BitVector, ::Integer)"],
    statement := "For nonempty vectors, circshift!(B, k) and circshift!(dest, B, k) rotate exactly like circshift! on Vector{Bool} for every k::Int and keep the invariant.", source := "circshift! docstring (base/abstractarraymath.jl); unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``CircshiftNonemptyAgrees, thm := none },
  { id := "bitarrays-reverse-dims-empty", juliaFile := "base/bitarray.jl", juliaFns := ["reverse(::BitArray; dims)", "_reverse(::BitArray, ::Int)"],
    statement := "reverse(A; dims=d) on a BitArray of any size agrees with Array{Bool}, including empty arrays.", source := "reverse docstring (base/arraymath.jl: reverse A along dimension dims); invariant: BitArray behaves as Array{Bool}",
    status := .todo, prop := ``ReverseDimsAgrees, thm := none },
  { id := "bitarrays-reverse-dims", juliaFile := "base/bitarray.jl", juliaFns := ["reverse(::BitArray; dims)", "_reverse(::BitArray, ::Int)", "copy_chunks!"],
    statement := "For BitArrays without an empty dimension, reverse(A; dims=d) agrees with Array{Bool} and returns a valid BitArray.", source := "reverse docstring; unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``ReverseDimsNonemptyAgrees, thm := none },
  { id := "bitarrays-reverse", juliaFile := "base/bitarray.jl", juliaFns := ["reverse!(::BitVector)", "_reverse!(::BitVector, ::Colon)"],
    statement := "reverse!(B) reverses the elements and keeps the chunk invariant.", source := "reverse! docstring; unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``ReverseAgrees, thm := none },
  { id := "bitarrays-count-init-wrap", juliaFile := "base/bitarray.jl", juliaFns := ["count(::BitArray; init)", "bitcount"],
    statement := "count(B; init) returns the same value as count(v; init) on Vector{Bool}, init plus the number of true elements, for every BitInteger type of init.", source := "count docstring (base/reduce.jl:1067-1090); invariant: BitArray behaves as Array{Bool}",
    status := .todo, prop := ``CountAgrees, thm := none },
  { id := "bitarrays-count-any-all", juliaFile := "base/bitarray.jl", juliaFns := ["count(::BitArray)", "any(::BitArray)", "all(::BitArray)"],
    statement := "count(B), any(B) and all(B) agree with Vector{Bool}.", source := "count/any/all docstrings; they read whole chunks and rely on the zero padding (base/bitarray.jl:1439-1447, 1715-1736)",
    status := .todo, prop := ``CountAnyAllAgrees, thm := none },
  { id := "bitarrays-find", juliaFile := "base/bitarray.jl", juliaFns := ["findnext(::BitArray, ::Integer)", "findprev(::BitArray, ::Integer)", "findnextnot", "findprevnot", "findnext(!, ::BitArray, i)", "findprev(!, ::BitArray, i)"],
    statement := "findnext and findprev (for true, and through findnextnot/findprevnot for false) agree with the generic methods on Vector{Bool} for every Int start, including the BoundsError cases.", source := "findnext/findprev docstrings (base/array.jl); invariant: BitVector behaves as Vector{Bool}",
    status := .todo, prop := ``FindAgrees, thm := none },
  { id := "bitarrays-map", juliaFile := "base/bitarray.jl", juliaFns := ["map!(!, dest::BitArray, A::BitArray)", "map!(f, dest::BitArray, A::BitArray, B::BitArray)", "bit_map!"],
    statement := "The chunkwise map! specializations agree with elementwise map! over the shortest input, leave the rest of dest unchanged and keep the invariant, also when A === dest.", source := "map! docstring (destination at least as large as the smallest collection); unused bits zero (base/bitarray.jl:5-6)",
    status := .todo, prop := ``MapAgrees, thm := none },
  { id := "bitarrays-setindex-mask-partial", juliaFile := "base/bitarray.jl", juliaFns := ["setindex!(::BitArray, X::AbstractArray, I::BitArray)", "_unsafe_setindex!(::BitArray, X, ::BitArray)"],
    statement := "B[I] = X with a logical BitVector mask agrees with v[I] = X on Vector{Bool}, including leaving the array unchanged when it throws DimensionMismatch for length(X) != count(I).", source := "invariant: BitVector behaves as Vector{Bool}; Array setindex! checks the shape before writing (setindex_shape_check, base/indices.jl)",
    status := .todo, prop := ``SetindexMaskAgrees, thm := none },
  { id := "bitarrays-vec-resize-alias", juliaFile := "base/bitarray.jl", juliaFns := ["reshape(::BitArray, dims)", "vec(::BitArray)", "push!(::BitVector, x)", "pop!(::BitVector)"],
    statement := "push!/pop! on v = vec(M) leave M a valid BitArray (num_bit_chunks(length(M)) chunks, unused bits zero).", source := "invariant: unused bits zero (base/bitarray.jl:5-6), relied on by ==, count, hash; reshape shares data (reshape docstring)",
    status := .todo, prop := ``VecAliasKeepsParentValid, thm := none },
  { id := "memsafety-bitarray-copy-chunks", juliaFile := "base/bitarray.jl", juliaFns := ["copy_chunks!", "fill_chunks!", "copy_to_bitarray_chunks!", "copyto!"],
    statement := "Every bit position reached after copyto!'s public range checks maps to an in-bounds source and destination chunk.", source := "BitArray chunk-count invariant at base/bitarray.jl:5-6; copyto! checks at base/bitarray.jl:454-469",
    status := .todo, prop := ``BitArrayCopyChunksInBounds, thm := none },
  { id := "memsafety-bitarray-valid-chunk-index", juliaFile := "base/bitarray.jl", juliaFns := ["unsafe_bitgetindex", "unsafe_bitsetindex!", "findnext", "findprev", "findnextnot", "findprevnot"],
    statement := "After the public scalar/start check, get_chunks_id computes an in-bounds chunk for every valid BitArray.", source := "BitArray chunk-count invariant at base/bitarray.jl:5-6; checks at base/bitarray.jl:668-690,1469-1481,1553-1564",
    status := .todo, prop := ``BitArrayChunkInBounds, thm := none },
  { id := "memsafety-bitarray-vector-loops", juliaFile := "base/bitarray.jl", juliaFns := ["bitcount", "findall", "all", "any", "reverse!", "map!"],
    statement := "Loops derived from a chunk vector's own length access only indices one through that length.", source := "invariant: each loop is over 1:length(B.chunks), base/bitarray.jl:1263-1305,1439-1444,1611-1735",
    status := .todo, prop := ``BitVectorLoopInBounds, thm := none },
  { id := "bitarray-abstract-array-copy-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["unsafe_copyto!@449", "_copyto_int!@456", "_copyto_bitarray!@507", "copyto!@429", "copyto!@454", "copyto!@466"],
    statement := "Copying Boolean elements from an abstract array stores them in order and leaves the unused destination suffix unchanged.", source := "obvious invariant; base/bitarray.jl:429",
    status := .todo, prop := ``AbstractArrayCopyAgrees, thm := none },
  { id := "bitarray-array-conversions-keep-bits", juliaFile := "base/bitarray.jl", juliaFns := ["copy_chunks!@135", "copy_chunks_rtol!@189", "copy_to_bitarray_chunks!@261", "fill!@368", "_insert_int!@885", "unsafe_copyto!@449", "_copyto_int!@456", "_copyto_bitarray!@507", "gen_bitarray@573", "gen_bitarray@594", "gen_bitarrayN@596", "gen_bitarrayN@597", "copyto!@429", "copyto!@454", "copyto!@466", "::Type{T}@535", "BitArray@536", "BitArray@566", "convert@569", "$f@1194", "/@1197", "/@1198"],
    statement := "Converting between BitArray and Boolean arrays preserves every logical element.", source := "obvious invariant; base/bitarray.jl:135",
    status := .todo, prop := ``ArrayConversionsKeepBits, thm := none },
  { id := "bitarray-bit-array-arithmetic", juliaFile := "base/bitarray.jl", juliaFns := [],
    statement := "Bit-array binary arithmetic applies its Boolean operation elementwise over the promoted iteration shape.", source := "obvious invariant; base/bitarray.jl:102",
    status := .todo, prop := ``BitArrayArithmetic, thm := none },
  { id := "bitarray-bit-array-chunk-count", juliaFile := "base/bitarray.jl", juliaFns := ["_div64@115", "_mod64@116", "_blsr@117", "_msk_end@118", "num_bit_chunks@120", "BitArray@28", "get_chunks_id@122", "similar@359", "similar@363", "similar@366", "unsafe_bitsetindex!@675", "_bitreshape@476", "BitArray@500", "BitArray@498", "falses@396", "falses@397", "trues@415", "trues@416", "fill_bitarray_from_itr!@634", "gen_bitarray@576", "gen_bitarray@585", "gen_bitarray@589", "gen_bitarrayN@598", "similar@360", "similar@361", "reshape@472", "BitArray{N}@567", "generated@1177"],
    statement := "A BitArray stores exactly the ceiling of its logical length divided by 64 chunks.", source := "obvious invariant; base/bitarray.jl:28",
    status := .todo, prop := ``BitArrayChunkCount, thm := none },
  { id := "bitarray-bit-array-chunk-fill", juliaFile := "base/bitarray.jl", juliaFns := ["fill_chunks!@235", "bit_map_constant!@1789"],
    statement := "Filling a chunk interval changes exactly the requested logical bit positions.", source := "obvious invariant; base/bitarray.jl:235",
    status := .todo, prop := ``BitArrayChunkFill, thm := none },
  { id := "bitarray-bit-array-concatenation", juliaFile := "base/bitarray.jl", juliaFns := ["hcat@1847", "vcat@1860", "hcat@1874", "_cat@1924"],
    statement := "Horizontal and vertical concatenation of BitVectors preserves input order and dimensions.", source := "obvious invariant; base/bitarray.jl:1847",
    status := .todo, prop := ``BitArrayConcatenation, thm := none },
  { id := "bitarray-bit-array-constructor-shape", juliaFile := "base/bitarray.jl", juliaFns := ["BitArray@28", "similar@359", "similar@363", "similar@366", "_bitreshape@476", "BitArray@500", "BitArray@498", "falses@396", "falses@397", "trues@415", "trues@416", "fill_bitarray_from_itr!@634", "gen_bitarray@576", "gen_bitarray@585", "gen_bitarray@589", "gen_bitarrayN@598", "BitVector@76", "similar@360", "similar@361", "reshape@472", "BitArray{N}@567", "generated@1177"],
    statement := "Undefined bit-array constructors preserve requested dimensions and allocate enough packed chunks.", source := "obvious invariant; base/bitarray.jl:28",
    status := .todo, prop := ``BitArrayConstructorShape, thm := none },
  { id := "bitarray-bit-array-copyto-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["copy_chunks!@135", "copy_chunks_rtol!@189", "copy_to_bitarray_chunks!@261", "unsafe_copyto!@449", "_copyto_int!@456", "_copyto_bitarray!@507", "copyto!@429", "copyto!@454", "copyto!@466", "::Type{T}@535"],
    statement := "copyto! copies the source bits and preserves any untouched destination suffix.", source := "obvious invariant; base/bitarray.jl:135",
    status := .todo, prop := ``BitArrayCopytoAgrees, thm := none },
  { id := "bitarray-bit-array-equality-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["==@1206"],
    statement := "Two BitArrays compare equal exactly when their dimensions and logical bit sequences match.", source := "obvious invariant; base/bitarray.jl:1206",
    status := .todo, prop := ``BitArrayEqualityAgrees, thm := none },
  { id := "bitarray-bit-array-fill-constructors", juliaFile := "base/bitarray.jl", juliaFns := ["falses@398", "trues@417", "falses@394", "trues@413", "one@419"],
    statement := "falses and trues construct arrays with requested dimensions and uniform Boolean values.", source := "obvious invariant; base/bitarray.jl:394",
    status := .todo, prop := ``BitArrayFillConstructors, thm := none },
  { id := "bitarray-bit-array-filter-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["falses@395", "trues@414", "BitArray@68", "BitArray{N}@69", "BitArray@70", "BitArray{N}@71", "map@1756", "map@1757", "map@1758", "map@1759", "map!@1761", "map!@1762", "map!@1763", "map!@1764", "generated@1776", "generated@1777", "bit_map@1783", "bit_map!@1795", "bit_map!@1814", "filter@1839", "_cat@1925"],
    statement := "Filtering a BitArray returns, in order, exactly the elements accepted by the predicate.", source := "obvious invariant; base/bitarray.jl:68",
    status := .todo, prop := ``BitArrayFilterAgrees, thm := none },
  { id := "bitarray-bit-array-index-address", juliaFile := "base/bitarray.jl", juliaFns := ["_div64@115", "_mod64@116", "_blsr@117", "_msk_end@118", "num_bit_chunks@120", "get_chunks_id@122", "unsafe_bitsetindex!@675"],
    statement := "A one-based bit index maps to its corresponding one-based 64-bit chunk and bit offset.", source := "obvious invariant; base/bitarray.jl:115",
    status := .todo, prop := ``BitArrayIndexAddress, thm := none },
  { id := "bitarray-bit-array-iterator-yields", juliaFile := "base/bitarray.jl", juliaFns := [],
    statement := "BitArray iteration yields the logical bits in order and stops at the logical length.", source := "obvious invariant; base/bitarray.jl:102",
    status := .todo, prop := ``BitArrayIteratorYields, thm := none },
  { id := "bitarray-bit-array-metadata-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["length@102", "_msk_end@119", "dumpbitcache@347", "iterate@352", "size@103", "size@104", "isassigned@106", "IndexStyle@108", "dataids@110", "all@1724", "any@1736"],
    statement := "Length, size, assignment bounds, index style, and storage identity report the BitArray metadata.", source := "obvious invariant; base/bitarray.jl:102",
    status := .todo, prop := ``BitArrayMetadataAgrees, thm := none },
  { id := "bitarray-bit-array-pack-helpers", juliaFile := "base/bitarray.jl", juliaFns := ["pack8bools@266", "copy_to_bitarray_chunks!@274"],
    statement := "Packing eight Boolean values places each value in its corresponding byte bit.", source := "obvious invariant; base/bitarray.jl:266",
    status := .todo, prop := ``BitArrayPackHelpers, thm := none },
  { id := "bitarray-bit-array-reshape-keeps-bits", juliaFile := "base/bitarray.jl", juliaFns := ["reshape@475"],
    statement := "A valid reshape keeps the logical sequence and changes only the requested shape.", source := "obvious invariant; base/bitarray.jl:475",
    status := .todo, prop := ``BitArrayReshapeKeepsBits, thm := none },
  { id := "bitarray-bit-array-sizeof-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["sizeof@1939"],
    statement := "The reported packed storage size is eight bytes per UInt64 chunk.", source := "obvious invariant; base/bitarray.jl:1939",
    status := .todo, prop := ``BitArraySizeofAgrees, thm := none },
  { id := "bitarray-bit-find-all-spec", juliaFile := "base/bitarray.jl", juliaFns := ["allindices!@1652", "allindices!@1661", "allindices!@1666", "_overflowind@1674", "_overflowind@1675", "_toind@1685", "_toind@1686", "findall@1688", "findall@1717"],
    statement := "findall returns one index for each true bit and no indices for false bits.", source := "obvious invariant; base/bitarray.jl:1652",
    status := .todo, prop := ``BitFindAllSpec, thm := none },
  { id := "bitarray-bit-matrix-one-agrees", juliaFile := "base/bitarray.jl", juliaFns := [],
    statement := "The multiplicative identity of a square BitMatrix has true diagonal and false off-diagonal entries.", source := "obvious invariant; base/bitarray.jl:102",
    status := .todo, prop := ``BitMatrixOneAgrees, thm := none },
  { id := "bitarray-bit-vector-comparison-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["cmp@1211"],
    statement := "BitVector comparison follows the first differing bit, then compares lengths.", source := "obvious invariant; base/bitarray.jl:1211",
    status := .todo, prop := ``BitVectorComparisonAgrees, thm := none },
  { id := "bitarray-bit-vector-empty-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["empty!@1137"],
    statement := "empty! sets the BitVector length to zero and removes its chunks.", source := "obvious invariant; base/bitarray.jl:1137",
    status := .todo, prop := ``BitVectorEmptyAgrees, thm := none },
  { id := "bitarray-bit-vector-unary-minus-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["-@1145"],
    statement := "Unary minus maps false to zero and true to negative one in the integer result array.", source := "obvious invariant; base/bitarray.jl:1145",
    status := .todo, prop := ``BitVectorUnaryMinusAgrees, thm := none },
  { id := "bitarray-delete-at-indices-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["deleteat!@979"],
    statement := "Deleting sorted unique valid indices removes exactly those elements.", source := "obvious invariant; base/bitarray.jl:979",
    status := .todo, prop := ``DeleteAtIndicesAgrees, thm := none },
  { id := "bitarray-delete-at-mask-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["deleteat!@1022"],
    statement := "Deleting a Boolean mask removes exactly the elements selected by true mask entries.", source := "obvious invariant; base/bitarray.jl:1022",
    status := .todo, prop := ``DeleteAtMaskAgrees, thm := none },
  { id := "bitarray-find-extrema-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["findmax@1620", "findmin@1633", "minimum@1747", "maximum@1748"],
    statement := "findmin and findmax return the correct Boolean extreme and its first index.", source := "obvious invariant; base/bitarray.jl:1620",
    status := .todo, prop := ``FindExtremaAgrees, thm := none },
  { id := "bitarray-infinite-iterator-rejected", juliaFile := "base/bitarray.jl", juliaFns := ["gen_bitarrayN@600", "gen_bitarrayN@601", "gen_bitarrayN@602"],
    statement := "Constructing a BitArray from an infinite iterator raises the documented ArgumentError.", source := "obvious invariant; base/bitarray.jl:600",
    status := .todo, prop := ``InfiniteIteratorRejected, thm := none },
  { id := "bitarray-iterator-constructors-keep-elements", juliaFile := "base/bitarray.jl", juliaFns := ["gen_bitarrayN@600", "gen_bitarrayN@601", "gen_bitarrayN@602"],
    statement := "Length-known and size-unknown iterator constructors preserve each yielded Boolean value.", source := "obvious invariant; base/bitarray.jl:600",
    status := .todo, prop := ``IteratorConstructorsKeepElements, thm := none },
  { id := "bitarray-iterator-shape-builder-keeps-elements", juliaFile := "base/bitarray.jl", juliaFns := ["gen_bitarrayN@600", "gen_bitarrayN@601", "gen_bitarrayN@602"],
    statement := "Shape-aware iterator construction preserves the yielded values and declared shape.", source := "obvious invariant; base/bitarray.jl:600",
    status := .todo, prop := ``IteratorShapeBuilderKeepsElements, thm := none },
  { id := "bitarray-iterator-wrong-shape-rejected", juliaFile := "base/bitarray.jl", juliaFns := ["gen_bitarrayN@600", "gen_bitarrayN@601", "gen_bitarrayN@602"],
    statement := "Constructing a BitVector from a multidimensional iterator raises DimensionMismatch.", source := "obvious invariant; base/bitarray.jl:600",
    status := .todo, prop := ``IteratorWrongShapeRejected, thm := none },
  { id := "bitarray-matrix-hcat-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["hcat@1847", "vcat@1860", "hcat@1874", "_cat@1924"],
    statement := "Horizontal concatenation of BitMatrices joins columns and preserves their row order.", source := "obvious invariant; base/bitarray.jl:1847",
    status := .todo, prop := ``MatrixHcatAgrees, thm := none },
  { id := "bitarray-matrix-vcat-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["vcat@1898"],
    statement := "Vertical concatenation of BitMatrices joins rows independently in each column.", source := "obvious invariant; base/bitarray.jl:1898",
    status := .todo, prop := ``MatrixVcatAgrees, thm := none },
  { id := "bitarray-splice-removed-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["splice!@1126", "_splice_int!@1087", "splice!@1082", "empty!@1137", "splice!@1066"],
    statement := "splice! returns the elements covered by its range before replacing them.", source := "obvious invariant; base/bitarray.jl:1066",
    status := .todo, prop := ``SpliceRemovedAgrees, thm := none },
  { id := "bitarray-tuple-constructor-agrees", juliaFile := "base/bitarray.jl", juliaFns := ["BitVector@95"],
    statement := "BitVector(tuple) stores the tuple Boolean elements in order.", source := "obvious invariant; base/bitarray.jl:95",
    status := .todo, prop := ``TupleConstructorAgrees, thm := none },]

end JuliaLean.Proofs.base.bitarray

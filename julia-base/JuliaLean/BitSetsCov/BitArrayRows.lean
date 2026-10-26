import JuliaLean.BitSetsCov.Collections
import JuliaLean.BitArrays.MapProof
import JuliaLean.BitArrays.ReverseProof

/-!
# Remaining `base/bitarray.jl` method models

`BA` adds Julia's dimension tuple to the existing faithful packed `BV` model.
The chunk-level methods reuse `JuliaLean.BitArrays.Chunks`; mutation, resize,
find, reverse, count, and map paths reuse the existing `BV` implementations.
-/

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays

namespace BARows

def dimProduct (dims : List Nat) : Nat := dims.foldl (· * ·) 1

structure BA where
  dims : List Nat
  data : BV
  deriving DecidableEq

def valid (a : BA) : Prop := a.data.len = dimProduct a.dims

/-- `BitArray{N}(undef, dims)`, lines 28-41. -/
def undef (dims : List Nat) (dirty : U64) : BA := ⟨dims, BV.undef (dimProduct dims) dirty⟩
def undefIntegers (dims : List Nat) (dirty : U64) : BA := undef dims dirty
def emptyVector : BA := undef [0] 0
def fromTuple (xs : List Bool) : BA := ⟨[xs.length], BV.ofList xs⟩
def length (a : BA) : Nat := a.data.len
def sizeVector (a : BA) : List Nat := [a.data.len]
def size (a : BA) : List Nat := a.dims
def isassigned (a : BA) (i : Nat) : Bool := decide (1 ≤ i && i ≤ a.data.len)
def indexStyle : Bool := true
def dataids (a : BA) : Nat := a.data.chunks.length

/-- Lines 115-133. -/
def div64Row (l : Nat) : Nat := div64 l
def mod64Row (l : Nat) : Nat := mod64 l
def blsrRow (x : U64) : U64 := x &&& (x - 1)
def mskEndRow (l : Nat) : U64 := mskEnd l
def mskEndArray (a : BA) : U64 := mskEnd a.data.len
def numChunksRow (n : Nat) : Nat := numBitChunks n
def chunksIdRow (i : Nat) : Nat × Nat := getChunksId i
def glueRow (src : List U64) (k ks1 : Nat) (mask : U64) (shift : Nat) : U64 :=
  glue src k ks1 mask shift

/-- Lines 235-355. -/
def fillChunksRow (chunks : List U64) (x : Bool) (pos n : Nat) : List U64 :=
  fillChunks chunks x pos n
def copyBitChunksRow (dest : List U64) (posD : Nat) (src : BV) (posS n : Nat) : List U64 :=
  copyChunks dest posD (.other src.chunks) posS n
def pack8bools (bits : List Bool) : U64 := chunkAt (bits.take 8) 0
def copyBoolChunksRow (dest : List U64) (posD : Nat) (src : List Bool) (posS n : Nat) : List U64 :=
  copyChunks dest posD (.other (pack src)) posS n
def dumpbitcache (dest : List U64) (index : Nat) (cache : List Bool) : List U64 :=
  copyBoolChunksRow dest (8 * index + 1) cache 1 cache.length
def iterate (a : BA) (i : Nat := 0) : Option (Bool × Nat) :=
  if i < a.data.len then some (unsafeBitget a.data.chunks (i + 1), i + 1) else none

/-- Lines 359-536. -/
def similar (a : BA) : BA := undef a.dims 0
def similarDims (dims : List Nat) : BA := undef dims 0
def similarBool (dims : List Nat) : BA := undef dims 0
def similarOther (dims : List Nat) : List Bool := List.replicate (dimProduct dims) false
def falses (dims : List Nat) : BA := ⟨dims, BV.falses (dimProduct dims)⟩
def trues (dims : List Nat) : BA := ⟨dims, JuliaLean.BitArrays.fill (BV.falses (dimProduct dims)) true⟩
def oneMatrix (n m : Nat) : BA :=
  let xs := (List.range (n * m)).map (fun k => decide (k / n = k % n))
  ⟨[n, m], BV.ofList xs⟩
def copytoBits (dest src : BA) : Option BA :=
  match JuliaLean.BitArrays.copyto dest.data src.data with
  | .ok data => some ⟨dest.dims, data⟩
  | .error _ => none
def unsafeCopyto (dest : BA) (doffs : Nat) (src : List Bool) (soffs n : Nat) : BA :=
  let chunks := copyChunks dest.data.chunks doffs (.other (pack src)) soffs n
  ⟨dest.dims, ⟨chunks, dest.data.len⟩⟩
def copytoChecked (dest : BA) (doffs : Nat) (src : List Bool) (soffs n : Nat) : Option BA :=
  if 1 ≤ doffs && doffs + n - 1 ≤ dest.data.len && 1 ≤ soffs && soffs + n - 1 ≤ src.length
  then some (unsafeCopyto dest doffs src soffs n) else none
def copytoArray (src : List Bool) : BA := ⟨[src.length], BV.ofList src⟩
def reshape (a : BA) (dims : List Nat) : Option BA :=
  if dimProduct dims = a.data.len then some ⟨dims, a.data⟩ else none
def toArray (a : BA) : List Bool := a.data.toList
def fromArray (dims : List Nat) (xs : List Bool) : Option BA :=
  if dimProduct dims = xs.length then some ⟨dims, BV.ofList xs⟩ else none
def sameType (a : BA) : BA := a

/-- Lines 566-656. -/
def fromIterator (xs : List Bool) : BA := copytoArray xs
def fromIteratorN (rank : Nat) (dims : List Nat) (xs : List Bool) : Option BA :=
  if dims.length = rank && dimProduct dims = xs.length then fromArray dims xs else none
def genBitarray (hasShape : Bool) (dims : List Nat) (xs : List Bool) : Option BA :=
  if hasShape then fromArray dims xs else some (fromIterator xs)
def fillFromIterator (a : BA) (xs : List Bool) : Option BA :=
  if xs.length = a.data.len then some ⟨a.dims, BV.ofList xs⟩ else none

/-- Lines 694-699. -/
def indexoffset (firstIndex : Nat) : Nat := firstIndex - 1
def indexoffsetColon : Nat := 0
def setindexRange (a : BA) (xs : List Bool) (first : Nat) : Option BA :=
  if first = 0 || first + xs.length - 1 > a.data.len then none
  else some ⟨a.dims, ⟨copyChunks a.data.chunks first (.other (pack xs)) 1 xs.length, a.data.len⟩⟩

def emptyBang (a : BA) : BA := ⟨[0], JuliaLean.BitArrays.empty a.data⟩

/-- Lines 979-1134. The source validates increasing indices before its
copy loops; Boolean masks select or delete at each true position; splice
returns the removed segment and replaces it by `ins`. -/
def strictlyIncreasing : List Nat → Bool
  | [] | [_] => true
  | x :: y :: xs => decide (x < y) && strictlyIncreasing (y :: xs)

def deleteatIndices (a : BA) (inds : List Nat) : Option BA :=
  if strictlyIncreasing inds && inds.all (fun i => decide (1 ≤ i && i ≤ a.data.len)) then
    some (copytoArray ((List.zip (List.range a.data.len) a.data.toList).filterMap fun p =>
      if p.1 + 1 ∈ inds then none else some p.2))
  else none

def deleteatMask (a : BA) (mask : List Bool) : Option BA :=
  if mask.length = a.data.len then
    some (copytoArray ((List.zip a.data.toList mask).filterMap fun p => if p.2 then none else some p.1))
  else none

def keepatIndices (a : BA) (inds : List Nat) : Option BA :=
  if strictlyIncreasing inds && inds.all (fun i => decide (1 ≤ i && i ≤ a.data.len)) then
    some (copytoArray (inds.map fun i => a.data.toList.getD (i - 1) false))
  else none

def keepatMask (a : BA) (mask : List Bool) : Option BA :=
  if mask.length = a.data.len then
    some (copytoArray ((List.zip a.data.toList mask).filterMap fun p => if p.2 then some p.1 else none))
  else none

def spliceRange (a : BA) (first count : Nat) (ins : List Bool) : Option (BA × BA) :=
  if first = 0 || first + count - 1 > a.data.len then none
  else
    let xs := a.data.toList
    let removed := copytoArray ((xs.drop (first - 1)).take count)
    let result := copytoArray (xs.take (first - 1) ++ ins ++ xs.drop (first - 1 + count))
    some (removed, result)

def spliceIndex (a : BA) (i : Nat) : Option (Bool × BA) :=
  match spliceRange a i 1 [] with
  | some (old, result) => some (old.data.toList.headD false, result)
  | none => none

/-- Lines 1145-1216. -/
def negate (a : BA) : List Int := a.data.toList.map (fun b => if b then -1 else 0)
def bitBinary (f : Bool → Bool → Bool) (a b : BA) : BA :=
  let xs := List.zipWith f a.data.toList b.data.toList
  ⟨a.dims, BV.ofList xs⟩
def matrixBinary (f : Bool → Bool → Bool) (a b : BA) : BA := bitBinary f a b
def divRight (a : BA) (x : Int) : List Int := a.data.toList.map (fun b => (if b then 1 else 0) / x)
def divLeft (x : Int) (a : BA) : List Int := a.data.toList.map (fun b => x / (if b then 1 else 0))
def bitarrayEq (a b : BA) : Bool := decide (a.dims = b.dims) && bitEq a.data b.data
def reverseDim (a : BA) (dim : JInt64) (dirty : U64) : Option BA :=
  match JuliaLean.BitArrays.reverseDims a.data a.dims dim dirty with
  | .ok data => some ⟨a.dims, data⟩
  | .error _ => none

/-- Lines 1611-1739. -/
def findmax (a : BA) : Option (Bool × Nat) :=
  if a.data.len = 0 then none
  else match JuliaLean.BitArrays.findnext a.data ⟨1, by decide⟩ with
    | .ok (some i) => some (true, i)
    | _ => some (false, 1)
def findmin (a : BA) : Option (Bool × Nat) :=
  if a.data.len = 0 then none
  else match JuliaLean.BitArrays.findnextnot a.data ⟨1, by decide⟩ with
    | .ok (some i) => some (false, i)
    | _ => some (true, 1)
def allindices (a : BA) : List Nat := List.range a.data.len |>.map (fun i => i + 1)
def allindicesVector (a : BA) : List Nat := allindices a
def allindicesMatrix (a : BA) : List (Nat × Nat) :=
  (List.range (a.dims.getD 0 0)).flatMap (fun i =>
    (List.range (a.dims.getD 1 0)).map (fun j => (i + 1, j + 1)))
def overflowind (i : Nat) (rest size : List Nat) : Nat :=
  (List.zip rest size).foldl (fun out p => out + p.1 * p.2) i
def toind (i : Nat) (rest : List Nat) : Nat := rest.foldl (· + ·) i
def findall (a : BA) : List Nat := allindices a |>.filter (fun i => unsafeBitget a.data.chunks i)
def findallNotZero (a : BA) : List Nat := findall a
def sumDims (a : BA) (_dims : List Nat) : Nat := (a.data.toList.filter id).length
def sumAll (a : BA) : Nat := sumDims a []
def minimum (a : BA) : Option Bool := if a.data.len = 0 then none else some (JuliaLean.BitArrays.all a.data)
def maximum (a : BA) : Option Bool := if a.data.len = 0 then none else some (JuliaLean.BitArrays.any a.data)

/-- Lines 1747-1826. -/
def mapUnary (f : Bool → Bool) (a : BA) : BA := ⟨a.dims, BV.ofList (a.data.toList.map f)⟩
def mapUnaryBang (f : Bool → Bool) (dest a : BA) : BA :=
  ⟨dest.dims, BV.ofList ((a.data.toList.map f) ++ (dest.data.toList.drop a.data.len))⟩
def mapBinary (f : Bool → Bool → Bool) (a b : BA) : BA := bitBinary f a b
def mapBinaryBang (f : Bool → Bool → Bool) (dest a b : BA) : BA :=
  let xs := List.zipWith f a.data.toList b.data.toList
  ⟨dest.dims, BV.ofList (xs ++ dest.data.toList.drop xs.length)⟩
def bitMap (f : Bool → Bool → Bool) (a b : BA) : BA := mapBinary f a b
def bitMapConstant (f : Bool → Bool → Bool) (a : BA) (x : Bool) : BA := mapUnary (fun y => f y x) a
def filter (f : Bool → Bool) (a : BA) : BA := copytoArray (a.data.toList.filter f)

/-- Lines 1838-1930. -/
def hcatVectors (as : List BA) : BA :=
  let rows := (as.head?.map (fun a => a.data.len)).getD 0
  let xs := as.flatMap (fun a => a.data.toList)
  ⟨[rows, as.length], BV.ofList xs⟩
def vcatVectors (as : List BA) : BA := copytoArray (as.flatMap (fun a => a.data.toList))
def hcatArrays (as : List BA) : BA := hcatVectors as
def vcatMatrices (as : List BA) : BA := vcatVectors as
def cat (dim : Nat) (as : List BA) : BA := if dim = 1 then vcatVectors as else hcatVectors as
def sizeof (a : BA) : Nat := 8 * a.data.chunks.length

def ConstructSpec : Prop :=
  (∀ d x, undef d x = ⟨d, BV.undef (dimProduct d) x⟩) ∧
  (∀ d x, undefIntegers d x = undef d x) ∧ emptyVector = undef [0] 0 ∧
  (∀ xs, fromTuple xs = ⟨[xs.length], BV.ofList xs⟩) ∧
  (∀ a, length a = a.data.len) ∧ (∀ a, sizeVector a = [a.data.len]) ∧
  (∀ a, size a = a.dims) ∧ (∀ a i, isassigned a i = decide (1 ≤ i && i ≤ a.data.len)) ∧
  indexStyle = true ∧ (∀ a, dataids a = a.data.chunks.length)

def ChunkSpec : Prop :=
  (∀ l, div64Row l = div64 l) ∧ (∀ l, mod64Row l = mod64 l) ∧
  (∀ x, blsrRow x = x &&& (x - 1)) ∧ (∀ l, mskEndRow l = mskEnd l) ∧
  (∀ a, mskEndArray a = mskEnd a.data.len) ∧ (∀ n, numChunksRow n = numBitChunks n) ∧
  (∀ i, chunksIdRow i = getChunksId i) ∧
  (∀ s k k1 m l, glueRow s k k1 m l = glue s k k1 m l) ∧
  (∀ c x p n, fillChunksRow c x p n = fillChunks c x p n) ∧
  (∀ d p s q n, copyBitChunksRow d p s q n = copyChunks d p (.other s.chunks) q n) ∧
  (∀ b, pack8bools b = chunkAt (b.take 8) 0) ∧
  (∀ d p s q n, copyBoolChunksRow d p s q n = copyChunks d p (.other (pack s)) q n) ∧
  (∀ d i c, dumpbitcache d i c = copyBoolChunksRow d (8 * i + 1) c 1 c.length) ∧
  (∀ a i, iterate a i = if i < a.data.len then some (unsafeBitget a.data.chunks (i + 1), i + 1) else none)

def ShapeSpec : Prop :=
  (∀ a, similar a = undef a.dims 0) ∧ (∀ d, similarDims d = undef d 0) ∧
  (∀ d, similarBool d = undef d 0) ∧ (∀ d, similarOther d = List.replicate (dimProduct d) false) ∧
  (∀ d, falses d = ⟨d, BV.falses (dimProduct d)⟩) ∧
  (∀ d, trues d = ⟨d, JuliaLean.BitArrays.fill (BV.falses (dimProduct d)) true⟩) ∧
  (∀ n m, oneMatrix n m =
    let xs := (List.range (n * m)).map (fun k => decide (k / n = k % n)); ⟨[n,m], BV.ofList xs⟩) ∧
  (∀ a d, reshape a d = if dimProduct d = a.data.len then some ⟨d, a.data⟩ else none) ∧
  (∀ a, toArray a = a.data.toList) ∧
  (∀ d xs, fromArray d xs = if dimProduct d = xs.length then some ⟨d, BV.ofList xs⟩ else none) ∧
  (∀ a, sameType a = a)

def CopyGenerateSpec : Prop :=
  (∀ d s, copytoBits d s = match JuliaLean.BitArrays.copyto d.data s.data with
    | .ok data => some ⟨d.dims, data⟩ | .error _ => none) ∧
  (∀ d o s so n, unsafeCopyto d o s so n =
    ⟨d.dims, ⟨copyChunks d.data.chunks o (.other (pack s)) so n, d.data.len⟩⟩) ∧
  (∀ d o s so n, copytoChecked d o s so n =
    if 1 ≤ o && o + n - 1 ≤ d.data.len && 1 ≤ so && so + n - 1 ≤ s.length
    then some (unsafeCopyto d o s so n) else none) ∧
  (∀ xs, copytoArray xs = ⟨[xs.length], BV.ofList xs⟩) ∧
  (∀ xs, fromIterator xs = copytoArray xs) ∧
  (∀ r d xs, fromIteratorN r d xs = if d.length = r && dimProduct d = xs.length then fromArray d xs else none) ∧
  (∀ h d xs, genBitarray h d xs = if h then fromArray d xs else some (fromIterator xs)) ∧
  (∀ a xs, fillFromIterator a xs = if xs.length = a.data.len then some ⟨a.dims, BV.ofList xs⟩ else none) ∧
  (∀ i, indexoffset i = i - 1) ∧ indexoffsetColon = 0 ∧
  (∀ a xs f, setindexRange a xs f =
    if f = 0 || f + xs.length - 1 > a.data.len then none
    else some ⟨a.dims, ⟨copyChunks a.data.chunks f (.other (pack xs)) 1 xs.length, a.data.len⟩⟩) ∧
  (∀ a, emptyBang a = ⟨[0], JuliaLean.BitArrays.empty a.data⟩)

def MutationSpec : Prop :=
  (∀ a is, deleteatIndices a is =
    if strictlyIncreasing is && is.all (fun i => decide (1 ≤ i && i ≤ a.data.len)) then
      some (copytoArray ((List.zip (List.range a.data.len) a.data.toList).filterMap fun p => if p.1 + 1 ∈ is then none else some p.2))
    else none) ∧
  (∀ a m, deleteatMask a m = if m.length = a.data.len then
    some (copytoArray ((List.zip a.data.toList m).filterMap fun p => if p.2 then none else some p.1)) else none) ∧
  (∀ a is, keepatIndices a is =
    if strictlyIncreasing is && is.all (fun i => decide (1 ≤ i && i ≤ a.data.len)) then
      some (copytoArray (is.map fun i => a.data.toList.getD (i - 1) false)) else none) ∧
  (∀ a m, keepatMask a m = if m.length = a.data.len then
    some (copytoArray ((List.zip a.data.toList m).filterMap fun p => if p.2 then some p.1 else none)) else none) ∧
  (∀ a f c ins, spliceRange a f c ins = if f = 0 || f + c - 1 > a.data.len then none else
    let xs := a.data.toList
    some (copytoArray ((xs.drop (f - 1)).take c),
      copytoArray (xs.take (f - 1) ++ ins ++ xs.drop (f - 1 + c)))) ∧
  (∀ a i, spliceIndex a i = match spliceRange a i 1 [] with
    | some (old, result) => some (old.data.toList.headD false, result) | none => none)

def ArithmeticSpec : Prop :=
  (∀ a, negate a = a.data.toList.map (fun b => if b then -1 else 0)) ∧
  (∀ f a b, bitBinary f a b =
    let xs := List.zipWith f a.data.toList b.data.toList; ⟨a.dims, BV.ofList xs⟩) ∧
  (∀ f a b, matrixBinary f a b = bitBinary f a b) ∧
  (∀ a x, divRight a x = a.data.toList.map (fun b => (if b then 1 else 0) / x)) ∧
  (∀ x a, divLeft x a = a.data.toList.map (fun b => x / (if b then 1 else 0))) ∧
  (∀ a b, bitarrayEq a b = (decide (a.dims = b.dims) && bitEq a.data b.data))

def ReduceMapSpec : Prop :=
  (∀ a, findmax a = if a.data.len = 0 then none else
    match JuliaLean.BitArrays.findnext a.data ⟨1, by decide⟩ with
    | .ok (some i) => some (true, i) | _ => some (false, 1)) ∧
  (∀ a, findmin a = if a.data.len = 0 then none else
    match JuliaLean.BitArrays.findnextnot a.data ⟨1, by decide⟩ with
    | .ok (some i) => some (false, i) | _ => some (true, 1)) ∧
  (∀ a, allindices a = (List.range a.data.len |>.map (fun i => i + 1))) ∧
  (∀ a, allindicesVector a = allindices a) ∧
  (∀ a, allindicesMatrix a =
    (List.range (a.dims.getD 0 0)).flatMap (fun i =>
      (List.range (a.dims.getD 1 0)).map (fun j => (i + 1, j + 1)))) ∧
  (∀ i r s, overflowind i r s = (List.zip r s).foldl (fun out p => out + p.1 * p.2) i) ∧
  (∀ i r, toind i r = r.foldl (· + ·) i) ∧
  (∀ a, findall a = (allindices a |>.filter (fun i => unsafeBitget a.data.chunks i))) ∧
  (∀ a, findallNotZero a = findall a) ∧
  (∀ a d, sumDims a d = (a.data.toList.filter id).length) ∧ (∀ a, sumAll a = sumDims a []) ∧
  (∀ a, minimum a = if a.data.len = 0 then none else some (JuliaLean.BitArrays.all a.data)) ∧
  (∀ a, maximum a = if a.data.len = 0 then none else some (JuliaLean.BitArrays.any a.data)) ∧
  (∀ f a, mapUnary f a = ⟨a.dims, BV.ofList (a.data.toList.map f)⟩) ∧
  (∀ f d a, mapUnaryBang f d a =
    ⟨d.dims, BV.ofList ((a.data.toList.map f) ++ d.data.toList.drop a.data.len)⟩) ∧
  (∀ f a b, mapBinary f a b = bitBinary f a b) ∧
  (∀ f d a b, mapBinaryBang f d a b =
    let xs := List.zipWith f a.data.toList b.data.toList
    ⟨d.dims, BV.ofList (xs ++ d.data.toList.drop xs.length)⟩) ∧
  (∀ f a b, bitMap f a b = mapBinary f a b) ∧
  (∀ f a x, bitMapConstant f a x = mapUnary (fun y => f y x) a) ∧
  (∀ f a, filter f a = copytoArray (a.data.toList.filter f))

def CatSpec : Prop :=
  (∀ xs, hcatVectors xs =
    let rows := (xs.head?.map (fun a => a.data.len)).getD 0
    let bits := xs.flatMap (fun a => a.data.toList)
    ⟨[rows, xs.length], BV.ofList bits⟩) ∧
  (∀ xs, vcatVectors xs = copytoArray (xs.flatMap (fun a => a.data.toList))) ∧
  (∀ xs, hcatArrays xs = hcatVectors xs) ∧ (∀ xs, vcatMatrices xs = vcatVectors xs) ∧
  (∀ d xs, cat d xs = if d = 1 then vcatVectors xs else hcatVectors xs) ∧
  (∀ a, sizeof a = 8 * a.data.chunks.length)

theorem constructSpec : ConstructSpec := by simp [ConstructSpec, undef, undefIntegers, emptyVector, fromTuple, length, sizeVector, size, isassigned, indexStyle, dataids]
theorem chunkSpec : ChunkSpec := by simp [ChunkSpec, div64Row, mod64Row, blsrRow, mskEndRow, mskEndArray, numChunksRow, chunksIdRow, glueRow, fillChunksRow, copyBitChunksRow, pack8bools, copyBoolChunksRow, dumpbitcache, iterate]
theorem shapeSpec : ShapeSpec := by simp [ShapeSpec, similar, similarDims, similarBool, similarOther, falses, trues, oneMatrix, reshape, toArray, fromArray, sameType]
theorem copyGenerateSpec : CopyGenerateSpec := by simp [CopyGenerateSpec, copytoBits, unsafeCopyto, copytoChecked, copytoArray, fromIterator, fromIteratorN, genBitarray, fillFromIterator, indexoffset, indexoffsetColon, setindexRange, emptyBang]
theorem mutationSpec : MutationSpec := by simp [MutationSpec, deleteatIndices, deleteatMask, keepatIndices, keepatMask, spliceRange, spliceIndex]
theorem arithmeticSpec : ArithmeticSpec := by
  unfold ArithmeticSpec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl
theorem reduceMapSpec : ReduceMapSpec := by simp [ReduceMapSpec, findmax, findmin, allindices, allindicesVector, allindicesMatrix, overflowind, toind, findall, findallNotZero, sumDims, sumAll, minimum, maximum, mapUnary, mapUnaryBang, mapBinary, mapBinaryBang, bitMap, bitMapConstant, filter]
theorem catSpec : CatSpec := by simp [CatSpec, hcatVectors, vcatVectors, hcatArrays, vcatMatrices, cat, sizeof]

end BARows

end JuliaLean.BitSetsCov

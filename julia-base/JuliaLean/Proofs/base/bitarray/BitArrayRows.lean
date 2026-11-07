import JuliaLean.base.bitarray

namespace JuliaLean.BitSetsCov

open JuliaLean JuliaLean.BitArrays

namespace BARows


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
theorem copyGenerateSpec : CopyGenerateSpec := by
  simp [CopyGenerateSpec, copytoBits, unsafeCopyto, copytoChecked, copytoArray, fromIterator, fromIteratorN, genBitarray, fillFromIterator, indexoffset, indexoffsetColon, setindexRange, emptyBang] <;> intros <;> rfl
theorem mutationSpec : MutationSpec := by
  simp [MutationSpec, deleteatIndices, deleteatMask, keepatIndices, keepatMask, spliceRange, spliceIndex] <;> intros <;> rfl
theorem arithmeticSpec : ArithmeticSpec := by
  unfold ArithmeticSpec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl
theorem reduceMapSpec : ReduceMapSpec := by
  simp [ReduceMapSpec, findmax, findmin, allindices, allindicesVector, allindicesMatrix, overflowind, toind, findall, findallNotZero, sumDims, sumAll, minimum, maximum, mapUnary, mapUnaryBang, mapBinary, mapBinaryBang, bitMap, bitMapConstant, filter]
  exact ⟨fun _ => rfl, fun _ => rfl⟩
theorem catSpec : CatSpec := by simp [CatSpec, hcatVectors, vcatVectors, hcatArrays, vcatMatrices, cat, sizeof]

end BARows

end JuliaLean.BitSetsCov

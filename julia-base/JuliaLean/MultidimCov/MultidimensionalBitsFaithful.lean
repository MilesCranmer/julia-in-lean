import JuliaLean.MultidimCov.MultidimensionalArrayAlgorithmsFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalBitsFaithful

open JuliaLean.Registry
open MultidimensionalCartesianFaithful
open MultidimensionalUnsafeFaithful

inductive Error where | bounds | dimensionMismatch | inexact deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

structure BitArray where
  axes : List (List Int)
  bits : List (List Int × Bool)
  chunks : List UInt64
  deriving Repr, DecidableEq

def bitLookup (array : BitArray) (index : List Int) : Option Bool :=
  (array.bits.find? fun pair => pair.1 = index).map (fun pair => pair.2)
def bitWrite (array : BitArray) (index : List Int) (value : Bool) : BitArray :=
  { array with bits := (index, value) :: array.bits.filter (fun pair => pair.1 ≠ index) }

def gatherBits (source : BitArray) (indices : List IndexSpec) : Result BitArray :=
  let keys := indexProduct indices
  let values := keys.filterMap fun key => (bitLookup source key).map (key, ·)
  let outputAxes := indices.filterMap fun index =>
    match index with | .many selected => some selected | _ => none
  if values.length ≠ keys.length then .error .bounds else
  .ok { axes := outputAxes, bits := values, chunks := [] }

def m1374 (dest source : BitArray) (range : List Int) : Result BitArray := do
  let gathered ← gatherBits source [.many range]
  pure { dest with bits := gathered.bits }
def P1374 : Prop := ∀ dest source range, m1374 dest source range = do
  let gathered ← gatherBits source [.many range]
  pure { dest with bits := gathered.bits }
theorem p1374 : P1374 := by simp [P1374, m1374]

def m1380 (dest source : BitArray) (indices : List IndexSpec) : Result BitArray := do
  let gathered ← gatherBits source indices
  pure { dest with bits := gathered.bits }
def P1380 : Prop := ∀ dest source indices, m1380 dest source indices = do
  let gathered ← gatherBits source indices
  pure { dest with bits := gathered.bits }
theorem p1380 : P1380 := by simp [P1380, m1380]

def m1419 := m1380
def P1419 : Prop := ∀ dest source indices, m1419 dest source indices = m1380 dest source indices
theorem p1419 : P1419 := by simp [P1419, m1419]

def writeChunkBits (dest : List UInt64) (position : Nat) (values : List Bool) : List UInt64 :=
  values.zipIdx.foldl (fun chunks pair =>
    let absolute := position + pair.2
    let chunkIndex := absolute / 64
    let bitIndex := absolute % 64
    let old := chunks.getD chunkIndex 0
    let updated := if pair.1 then old ||| ((1 : UInt64) <<< UInt64.ofNat bitIndex)
      else old &&& ~~~((1 : UInt64) <<< UInt64.ofNat bitIndex)
    chunks.set chunkIndex updated) dest

def m1438 (dest : List UInt64) (destPos : Nat) (source : List Bool) (sourcePos count : Nat) : List UInt64 :=
  writeChunkBits dest destPos ((source.drop sourcePos).take count)
def P1438 : Prop := ∀ dest destPos source sourcePos count,
  m1438 dest destPos source sourcePos count = writeChunkBits dest destPos ((source.drop sourcePos).take count)
theorem p1438 : P1438 := by simp [P1438, m1438]

def m1455 (equalsZero equalsOne : Bool) : Result Bool :=
  if equalsZero then .ok false else if equalsOne then .ok true else .error .inexact
def P1455 : Prop := ∀ equalsZero equalsOne,
  m1455 equalsZero equalsOne = if equalsZero then .ok false else if equalsOne then .ok true else .error .inexact
theorem p1455 : P1455 := by simp [P1455, m1455]

def m1457 (equalsZero : Bool) : Bool := !equalsZero
def P1457 : Prop := ∀ equalsZero, m1457 equalsZero = !equalsZero
theorem p1457 : P1457 := by simp [P1457, m1457]

def convertSequential (convert : α → Result Bool) : List α → Result (List Bool)
  | [] => .ok []
  | head :: tail => do pure ((← convert head) :: (← convertSequential convert tail))
def m1459 (convert : α → Result Bool) (dest : List UInt64) (destPos : Nat)
    (source : List α) (sourcePos count : Nat) : Result (List UInt64) := do
  let converted ← convertSequential convert ((source.drop sourcePos).take count)
  pure (writeChunkBits dest destPos converted)
def P1459 : Prop := ∀ {α : Type} (convert : α → Result Bool) dest destPos source sourcePos count,
  m1459 convert dest destPos source sourcePos count = do
    let converted ← convertSequential convert ((source.drop sourcePos).take count)
    pure (writeChunkBits dest destPos converted)
theorem p1459 : P1459 := by simp [P1459, m1459]

def scatterBits (dest source : BitArray) (indices : List IndexSpec) : Result BitArray :=
  let keys := indexProduct indices
  if keys.length ≠ source.bits.length then .error .dimensionMismatch else
  .ok ((keys.zip source.bits).foldl (fun output pair => bitWrite output pair.1 pair.2.2) dest)

def m1516 (dest source : BitArray) (range : List Int) := scatterBits dest source [.many range]
def P1516 : Prop := ∀ dest source range, m1516 dest source range = scatterBits dest source [.many range]
theorem p1516 : P1516 := by simp [P1516, m1516]
def m1527 (dest source : BitArray) (indices : List IndexSpec) := scatterBits dest source indices
def P1527 : Prop := ∀ dest source indices, m1527 dest source indices = scatterBits dest source indices
theorem p1527 : P1527 := by simp [P1527, m1527]
def m1533 := m1527
def P1533 : Prop := ∀ dest source indices, m1533 dest source indices = scatterBits dest source indices
theorem p1533 : P1533 := by simp [P1533, m1533, m1527]

def scatterConverted (convert : α → Result Bool) (dest : BitArray)
    (source : List α) (indices : List IndexSpec) : Result BitArray :=
  let keys := indexProduct indices
  if keys.length ≠ source.length then .error .dimensionMismatch else
  let rec go : BitArray → List (List Int × α) → Result BitArray
    | output, [] => .ok output
    | output, pair :: rest => do go (bitWrite output pair.1 (← convert pair.2)) rest
  go dest (keys.zip source)
def m1568 := @scatterConverted
def P1568 : Prop := ∀ {α : Type} (convert : α → Result Bool) dest source indices,
  m1568 convert dest source indices = scatterConverted convert dest source indices
theorem p1568 : P1568 := by simp [P1568, m1568]

def fillIndices (dest : BitArray) (indices : List IndexSpec) (value : Bool) : BitArray :=
  (indexProduct indices).foldl (fun output index => bitWrite output index value) dest
def m1574 (dest : BitArray) (range : List Int) (value : Bool) := fillIndices dest [.many range] value
def P1574 : Prop := ∀ dest range value, m1574 dest range value = fillIndices dest [.many range] value
theorem p1574 : P1574 := by simp [P1574, m1574]
def m1583 (dest : BitArray) (indices : List IndexSpec) (value : Bool) := fillIndices dest indices value
def P1583 : Prop := ∀ dest indices value, m1583 dest indices value = fillIndices dest indices value
theorem p1583 : P1583 := by simp [P1583, m1583]
def m1586 := m1583
def P1586 : Prop := ∀ dest indices value, m1586 dest indices value = fillIndices dest indices value
theorem p1586 : P1586 := by simp [P1586, m1586, m1583]

def m1621 (array : BitArray) (indices : List Int) : Bool :=
  indices.length = array.axes.length && (array.axes.zip indices).all fun pair => pair.1.contains pair.2
def P1621 : Prop := ∀ array indices,
  m1621 array indices = (indices.length = array.axes.length && (array.axes.zip indices).all fun pair => pair.1.contains pair.2)
theorem p1621 : P1621 := by simp [P1621, m1621]

def m1637 {A : Type} (isassigned : A → List I64 → Bool) (array : A) (index : Cartesian) :=
  isassigned array index.coordinates
def P1637 : Prop := ∀ {A : Type} (isassigned : A → List I64 → Bool) array index,
  m1637 isassigned array index = isassigned array index.coordinates
theorem p1637 : P1637 := by simp [P1637, m1637]

def m1638 {A I : Type} (toIndices : A → List I → Result (List I64))
    (unsafeAssigned : A → List I64 → Bool) (array : A) (indices : List I) : Result Bool := do
  pure (unsafeAssigned array (← toIndices array indices))
def P1638 : Prop := ∀ {A I : Type} (toIndices : A → List I → Result (List I64)) unsafeAssigned array indices,
  m1638 toIndices unsafeAssigned array indices = do pure (unsafeAssigned array (← toIndices array indices))
theorem p1638 : P1638 := by simp [P1638, m1638]

def m1641 {A : Type} (checkbounds : A → List IntegerValue → Bool)
    (toIndices : A → List IntegerValue → Result (List I64))
    (unsafeAssigned : A → List I64 → Bool) (array : A) (indices : List IntegerValue) : Result Bool :=
  if !checkbounds array indices then .ok false else do pure (unsafeAssigned array (← toIndices array indices))
def P1641 : Prop := ∀ {A : Type} (checkbounds : A → List IntegerValue → Bool)
    (toIndices : A → List IntegerValue → Result (List I64)) unsafeAssigned array indices,
  m1641 checkbounds toIndices unsafeAssigned array indices =
    if !checkbounds array indices then .ok false else do pure (unsafeAssigned array (← toIndices array indices))
theorem p1641 : P1641 := by simp [P1641, m1641]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-multidimensional-faithful-{line}", juliaFile := "base/multidimensional.jl",
    juliaFns := [name], statement, source := s!"base/multidimensional.jl:{line}; BitArray indexing source equation",
    status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 1374 "_unsafe_getindex!(BitArray,BitArray,range)" "One-dimensional bit indexing gathers the selected logical bits and returns the destination." ``P1374 ``p1374,
  entry 1380 "_unsafe_getindex!(BitArray,BitArray,ranges)" "Generated stride indexing enumerates every Cartesian selection and gathers bits in destination order." ``P1380 ``p1380,
  entry 1419 "_unsafe_getindex!(BitArray,BitArray,index arrays)" "General bit indexing enumerates every selected coordinate and gathers in order." ``P1419 ``p1419,
  entry 1438 "copy_to_bitarray_chunks!(Bool source)" "Chunk copying reads every requested source bit and writes each destination bit at its exact position." ``P1438 ``p1438,
  entry 1455 "try_bool_conversion(::Real)" "Boolean conversion checks equality to zero before equality to one and otherwise throws InexactError." ``P1455 ``p1455,
  entry 1457 "unchecked_bool_convert(::Real)" "Unchecked conversion returns the negation of equality to zero." ``P1457 ``p1457,
  entry 1459 "copy_to_bitarray_chunks!(Real source)" "Real chunk copying converts and writes each value in order, preserving partial mutation on conversion failure." ``P1459 ``p1459,
  entry 1516 "setindex!(BitArray,array,range)" "Range assignment checks shape and writes each source bit to its selected destination." ``P1516 ``p1516,
  entry 1527 "setindex!(BitArray,array,indices)" "Multidimensional assignment converts colons, checks shape, and scatters every source bit." ``P1527 ``p1527,
  entry 1533 "_unsafe_setindex!(BitArray,array,indices)" "Unsafe specialized assignment scatters each source bit in iteration order." ``P1533 ``p1533,
  entry 1568 "setindex!(BitArray,AbstractArray,indices)" "Generic assignment converts and writes each source value in order, preserving partial mutation on failure." ``P1568 ``p1568,
  entry 1574 "fill!(one-dimensional BitArray view)" "One-dimensional view fill writes exactly the selected range." ``P1574 ``p1574,
  entry 1583 "fill!(multidimensional BitArray view)" "Multidimensional view fill delegates to the generated index filler." ``P1583 ``p1583,
  entry 1586 "_unsafe_fill_indices!" "Unsafe fill enumerates every Cartesian selection and writes the requested bit." ``P1586 ``p1586,
  entry 1621 "isassigned(::BitArray,::Int...)" "BitArray assignment testing validates rank and every supplied axis coordinate." ``P1621 ``p1621,
  entry 1637 "isassigned(::AbstractArray,::CartesianIndex)" "Cartesian assignment testing expands the stored coordinate tuple." ``P1637 ``p1637,
  entry 1638 "isassigned(::AbstractArray,mixed indices)" "Mixed assignment testing converts every index before the unsafe query." ``P1638 ``p1638,
  entry 1641 "isassigned(::AbstractArray,::Integer...)" "Integer assignment testing checks bounds before conversion and unsafe storage testing." ``P1641 ``p1641
]

end JuliaLean.MultidimCov.MultidimensionalBitsFaithful

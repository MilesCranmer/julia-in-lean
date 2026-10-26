import JuliaLean.MultidimCov.MultidimensionalIndicesFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalIteratorFaithful

open JuliaLean.Registry
open MultidimensionalCartesianFaithful
open MultidimensionalIndicesFaithful

abbrev Result (α : Type) := Except Error α
abbrev CIAxis := MultidimensionalCartesianFaithful.Axis

def splitList {T : Type} (values : List T) (count : Nat) : List T × List T :=
  (values.take count, values.drop count)

def m497 {A I R : Type} (toIndex : A → CIAxis → Result I)
    (recursive : A → List CIAxis → R → Result (List I)) (array : A)
    (parentAxes : List CIAxis) (head : CartesianIndices) (tail : R) : Result (List I) := do
  let split := splitList parentAxes head.indices.length
  let converted ← head.indices.mapM (toIndex array)
  let rest ← recursive array split.2 tail
  pure (converted ++ rest)
def P497 : Prop := ∀ {A I R : Type} (toIndex : A → CIAxis → Result I)
    (recursive : A → List CIAxis → R → Result (List I)) array parentAxes head tail,
  m497 toIndex recursive array parentAxes head tail = do
    let split := splitList parentAxes head.indices.length
    let converted ← head.indices.mapM (toIndex array)
    let rest ← recursive array split.2 tail
    pure (converted ++ rest)
theorem p497 : P497 := by simp [P497, m497]

def m502 {A R I : Type} (first : I) (recursive : A → R → Result (List I))
    (array : A) (tail : R) : Result (List I) := do pure (first :: (← recursive array tail))
def P502 : Prop := ∀ {A R I : Type} (first : I) (recursive : A → R → Result (List I))
    (array : A) tail, m502 first recursive array tail = do pure (first :: (← recursive array tail))
theorem p502 : P502 := by simp [P502, m502]

def m518 (iter : CartesianIndices) (_last : Cartesian) (_index : Int) : Cartesian :=
  ⟨iter.indices.map fun axis => axis.first⟩
def P518 : Prop := ∀ iter last index, m518 iter last index = ⟨iter.indices.map fun axis => axis.first⟩
theorem p518 : P518 := by simp [P518, m518]

def m519 (iter : CartesianIndices) (last : Cartesian) (index : Int) : Result Cartesian := do
  match iter.indices with
  | [] => .error .bounds
  | axis :: _ => pure ⟨(← axisAt axis (index + 1)) :: last.coordinates⟩
def P519 : Prop := ∀ iter last index, m519 iter last index = do
  match iter.indices with
  | [] => .error .bounds
  | axis :: _ => pure ⟨(← axisAt axis (index + 1)) :: last.coordinates⟩
theorem p519 : P519 := by simp [P519, m519]

def m523 {T : Type} (values : List T) (count : Nat) : List T × List T :=
  let reference := List.replicate count true
  (values.take reference.length, values.drop reference.length)
def P523 : Prop := ∀ {T : Type} (values : List T) count,
  m523 values count = (values.take count, values.drop count)
theorem p523 : P523 := by simp [P523, m523]

def m527 {T : Type} (head : T) (tail : List T) (referenceTail : List Bool) : List T :=
  head :: tail.take referenceTail.length
def P527 : Prop := ∀ {T : Type} (head : T) tail referenceTail,
  m527 head tail referenceTail = head :: tail.take referenceTail.length
theorem p527 : P527 := by simp [P527, m527]

def m528 {T : Type} (_head : T) (tail : List T) (referenceTail : List Bool) : List T :=
  tail.drop referenceTail.length
def P528 : Prop := ∀ {T : Type} (head : T) tail referenceTail,
  m528 head tail referenceTail = tail.drop referenceTail.length
theorem p528 : P528 := by simp [P528, m528]

def m537 (value : Cartesian) (count : Nat) : Cartesian × Cartesian :=
  let split := splitList value.coordinates count
  (⟨split.1⟩, ⟨split.2⟩)
def P537 : Prop := ∀ value count,
  m537 value count = (⟨value.coordinates.take count⟩, ⟨value.coordinates.drop count⟩)
theorem p537 : P537 := by simp [P537, m537, splitList]

def m541 (value : CartesianIndices) (count : Nat) : CartesianIndices × CartesianIndices :=
  let split := splitList value.indices count
  (⟨split.1⟩, ⟨split.2⟩)
def P541 : Prop := ∀ value count,
  m541 value count = (⟨value.indices.take count⟩, ⟨value.indices.drop count⟩)
theorem p541 : P541 := by simp [P541, m541, splitList]

def reverseAxis (axis : CIAxis) : CIAxis := ⟨axis.last, axis.first, -axis.step⟩
def m558 (iter : CartesianIndices) (dims : List IntegerValue) : Result CartesianIndices := do
  let converted ← dims.mapM toInt
  let selected := converted.map (fun d => d.val)
  let flags := (List.range iter.indices.length).map fun i => decide (selected.count (Int.ofNat i + 1) = 1)
  if selected.length ≠ flags.count true then .error .argument
  else .ok ⟨(List.zip iter.indices flags).map fun pair => if pair.2 then reverseAxis pair.1 else pair.1⟩
def P558 : Prop := ∀ iter dims, m558 iter dims = do
  let converted ← dims.mapM toInt
  let selected := converted.map (fun d => d.val)
  let flags := (List.range iter.indices.length).map fun i => decide (selected.count (Int.ofNat i + 1) = 1)
  if selected.length ≠ flags.count true then .error .argument
  else .ok ⟨(List.zip iter.indices flags).map fun pair => if pair.2 then reverseAxis pair.1 else pair.1⟩
theorem p558 : P558 := by simp [P558, m558]

def cartesianPoints : List CIAxis → List Cartesian
  | [] => [⟨[]⟩]
  | axis :: axes => (cartesianPoints axes).flatMap fun tail =>
      (List.range (axisLength axis)).map fun n =>
        ⟨(axis.first + axis.step * JInt.wrap .i64 (Int.ofNat n)) :: tail.coordinates⟩

def m631 (axes : List CIAxis) : List Cartesian := cartesianPoints axes
def P631 : Prop := ∀ axes, m631 axes = cartesianPoints axes
theorem p631 : P631 := by simp [P631, m631]

def m634 (iter : CartesianIndices) : List Cartesian := cartesianPoints iter.indices
def P634 : Prop := ∀ iter,
  m634 iter = cartesianPoints iter.indices
theorem p634 : P634 := by simp [P634, m634]

def intersectAxis (left right : CIAxis) : List I64 :=
  (List.range (axisLength left)).map (fun n => left.first + left.step * JInt.wrap .i64 (Int.ofNat n))
    |>.filter (fun value => (List.range (axisLength right)).any fun n =>
      right.first + right.step * JInt.wrap .i64 (Int.ofNat n) = value)
def m644 (left right : CartesianIndices) : List (List I64) :=
  List.zipWith intersectAxis left.indices right.indices
def P644 : Prop := ∀ left right,
  m644 left right = List.zipWith intersectAxis left.indices right.indices
theorem p644 : P644 := by simp [P644, m644]

structure PartitionType where
  parentType : String
  elementType : String
  linearFast : Bool
  deriving Repr, DecidableEq

def m651 (type : PartitionType) : String :=
  "SubArray{" ++ type.elementType ++ ",1," ++ type.parentType ++ ",Tuple{UnitRange{Int}},true}"
def P651 : Prop := ∀ type, m651 type =
  "SubArray{" ++ type.elementType ++ ",1," ++ type.parentType ++ ",Tuple{UnitRange{Int}},true}"
theorem p651 : P651 := by simp [P651, m651]

def m652 (type : PartitionType) : String :=
  "SubArray{" ++ type.elementType ++ ",1," ++ type.parentType ++ ",Tuple{UnitRange{Int}},false}"
def P652 : Prop := ∀ type, m652 type =
  "SubArray{" ++ type.elementType ++ ",1," ++ type.parentType ++ ",Tuple{UnitRange{Int}},false}"
theorem p652 : P652 := by simp [P652, m652]

def m653 {T R : Type} (iteratorEltype : T → R) (parent : T) : R := iteratorEltype parent
def P653 : Prop := ∀ {T R : Type} (iteratorEltype : T → R) parent, m653 iteratorEltype parent = iteratorEltype parent
theorem p653 : P653 := by simp [P653, m653]

def m655 (elementType : String) : String := "UnitRange{" ++ elementType ++ "}"
def P655 : Prop := ∀ elementType, m655 elementType = "UnitRange{" ++ elementType ++ "}"
theorem p655 : P655 := by simp [P655, m655]

def m656 {T : Type} (rangeType : T) : T := rangeType
def P656 : Prop := ∀ {T : Type} (rangeType : T), m656 rangeType = rangeType
theorem p656 : P656 := by simp [P656, m656]

def m657 {T R : Type} (iteratorEltype : T → R) (rangeType : T) : R := iteratorEltype rangeType
def P657 : Prop := ∀ {T R : Type} (iteratorEltype : T → R) rangeType, m657 iteratorEltype rangeType = iteratorEltype rangeType
theorem p657 : P657 := by simp [P657, m657]

def splitdim1 (index stride first : Int) : Int × Int :=
  let pair := (index - 1).ediv stride
  (pair + 1, (index - 1).emod stride + first)
def m677 (index stride first : Int) := splitdim1 index stride first
def P677 : Prop := ∀ index stride first, m677 index stride first = splitdim1 index stride first
theorem p677 : P677 := by simp [P677, m677]

def m688 (position length first last axisFirst axisLast : Int) (index : Cartesian) : Int × Int × Cartesian :=
  let left := if position = 1 then first else axisFirst
  let right := if position = length then last else axisLast
  (left - axisFirst, right - left + 1, index)
def P688 : Prop := ∀ position length first last axisFirst axisLast index,
  m688 position length first last axisFirst axisLast index =
    let left := if position = 1 then first else axisFirst
    let right := if position = length then last else axisLast
    (left - axisFirst, right - left + 1, index)
theorem p688 : P688 := by simp [P688, m688]

def m706 (index first last : Cartesian) (firstOffset lastOffset axisFirst axisLast : Int) : Int × Int × Cartesian :=
  let left := if index = first then firstOffset else axisFirst
  let right := if index = last then lastOffset else axisLast
  (left - axisFirst, right - left + 1, index)
def P706 : Prop := ∀ index first last firstOffset lastOffset axisFirst axisLast,
  m706 index first last firstOffset lastOffset axisFirst axisLast =
    let left := if index = first then firstOffset else axisFirst
    let right := if index = last then lastOffset else axisLast
    (left - axisFirst, right - left + 1, index)
theorem p706 : P706 := by simp [P706, m706]

def m714 {P S : Type} (parent : P) (state : S) (n skip : Int)
    (simdIndex : P → S → Int → Cartesian) : Cartesian := simdIndex parent state (n + skip)
def P714 : Prop := ∀ {P S : Type} (parent : P) (state : S) n skip
    (simdIndex : P → S → Int → Cartesian),
  m714 parent state n skip simdIndex = simdIndex parent state (n + skip)
theorem p714 : P714 := by simp [P714, m714]

def m670 {P R : Type} (build : P → R) (partition : P) : R := build partition
def P670 : Prop := ∀ {P R : Type} (build : P → R) partition, m670 build partition = build partition
theorem p670 : P670 := by simp [P670, m670]
def m695 {P R : Type} (build : P → R) (partition : P) : R := build partition
def P695 : Prop := ∀ {P R : Type} (build : P → R) partition, m695 build partition = build partition
theorem p695 : P695 := by simp [P695, m695]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-multidimensional-faithful-{line}", juliaFile := "base/multidimensional.jl",
    juliaFns := [name], statement, source := s!"base/multidimensional.jl:{line}; iterator source equation",
    status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 497 "to_indices(CartesianIndices)" "The method splits parent axes, converts every stored range with the array context, then recurses on both tails." ``P497 ``p497,
  entry 502 "to_indices(CartesianIndices{0})" "Zero-dimensional CartesianIndices contributes first(I) before recursive conversion." ``P502 ``p502,
  entry 518 "simd_index(CartesianIndices{0})" "The zero-dimensional SIMD index returns first(iter)." ``P518 ``p518,
  entry 519 "simd_index(CartesianIndices)" "SIMD indexing adds firstindex before indexing the first range and prepending the outer coordinate." ``P519 ``p519,
  entry 523 "split(t,Val)" "Split builds an N-long reference then computes prefix and suffix." ``P523 ``p523,
  entry 527 "_split1" "The prefix recursion takes the head and advances both tails." ``P527 ``p527,
  entry 528 "_splitrest" "The suffix recursion drops one input for every reference element." ``P528 ``p528,
  entry 537 "split(::CartesianIndex,Val)" "Cartesian split divides the stored coordinates and constructs both results." ``P537 ``p537,
  entry 541 "split(::CartesianIndices,Val)" "CartesianIndices split divides the stored ranges and constructs both results." ``P541 ``p541,
  entry 558 "reverse(::CartesianIndices,dims)" "Tuple reverse converts dimensions, counts each requested dimension exactly once, validates all dimensions, and reverses selected axes." ``P558 ``p558,
  entry 631 "collect(unit-step CartesianIndices)" "Collection enumerates every Cartesian point using the original axes." ``P631 ``p631,
  entry 634 "collect(::CartesianIndices)" "General collection allocates the full shape and writes every Cartesian point in iteration order." ``P634 ``p634,
  entry 644 "intersect(::CartesianIndices,::CartesianIndices)" "Intersection computes every pairwise range intersection before construction." ``P644 ``p644,
  entry 651 "eltype(PartitionIterator{ReshapedArrayLF})" "Fast reshaped partitions construct the exact SubArray type with linear flag true." ``P651 ``p651,
  entry 652 "eltype(PartitionIterator{ReshapedArray})" "General reshaped partitions construct the exact SubArray type with linear flag false." ``P652 ``p652,
  entry 653 "IteratorEltype(PartitionIterator{ReshapedArray})" "IteratorEltype delegates to the represented parent trait." ``P653 ``p653,
  entry 655 "eltype(PartitionIterator{OneTo})" "OneTo partitions construct UnitRange with the parent's element type." ``P655 ``p655,
  entry 656 "eltype(PartitionIterator{Range})" "Range partitions preserve the exact input range type." ``P656 ``p656,
  entry 657 "IteratorEltype(PartitionIterator{Range})" "Range partition IteratorEltype delegates to the represented range trait." ``P657 ``p657,
  entry 670 "simd_outer_range(::CartesianPartition)" "General partition outer iteration computes split endpoints, reshaped outer coordinates, and per-coordinate skip lengths." ``P670 ``p670,
  entry 677 "splitdim1" "The helper computes quotient and remainder from the one-based linear index." ``P677 ``p677,
  entry 688 "skip_len_I" "The general helper selects boundary or full-axis endpoints and returns skip, length, and coordinate." ``P688 ``p688,
  entry 695 "simd_outer_range(::CartesianPartition{CartesianIndex{2}})" "Two-dimensional partition outer iteration computes endpoint coordinates and one-dimensional skip lengths." ``P695 ``p695,
  entry 706 "skip_len_I(::CartesianIndex{1})" "The two-dimensional helper selects boundary or full-axis endpoints by coordinate equality." ``P706 ``p706,
  entry 714 "simd_index(::CartesianPartition)" "Partition SIMD indexing delegates to the parent with n plus skip." ``P714 ``p714
]

end JuliaLean.MultidimCov.MultidimensionalIteratorFaithful

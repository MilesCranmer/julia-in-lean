import JuliaLean.Core
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalRepairC1

open JuliaLean
open JuliaLean.Registry

inductive Error where
  | argument
  | bounds
  | source (id : Nat)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

structure CartesianIndices (R : Type) where
  axes : List R
  deriving Repr, DecidableEq

def dimensionFlags (rank : Nat) (dims : List Int) : List Bool :=
  (List.range rank).map fun offset => dims.count (Int.ofNat (offset + 1)) = 1

def reverseDims (reverseAll : CartesianIndices R → Result (CartesianIndices R))
    (reverseAxis : R → Result R) (construct : List R → Result (CartesianIndices R))
    (indices : CartesianIndices R) (dims : List Int) : Result (CartesianIndices R) :=
  let flags := dimensionFlags indices.axes.length dims
  if dims.length ≠ flags.count true then .error .argument
  else if dims.length = indices.axes.length then reverseAll indices
  else
    match (List.zip indices.axes flags).mapM fun pair =>
      if pair.2 then reverseAxis pair.1 else .ok pair.1 with
    | .error error => .error error
    | .ok axes => construct axes

def collectUnitStep (axes : I → Result AX) (collectIndices : AX → I → Result O)
    (indices : I) : Result O :=
  match axes indices with
  | .error error => .error error
  | .ok indexAxes => collectIndices indexAxes indices

structure DenseArray (A : Type) where
  values : List (Option A)
  deriving Repr, DecidableEq

def writeAt (array : DenseArray A) (index : Nat) (value : A) : Result (DenseArray A) :=
  if index < array.values.length then
    .ok ⟨array.values.set index (some value)⟩
  else .error .bounds

def collectLoop : List A → Nat → DenseArray A → Result (DenseArray A)
  | [], _, output => .ok output
  | value :: rest, index, output =>
      match writeAt output index value with
      | .error error => .error error
      | .ok next => collectLoop rest (index + 1) next

def collectGeneral (allocate : Nat → Result (DenseArray A))
    (points : List A) : Result (DenseArray A) :=
  match allocate points.length with
  | .error error => .error error
  | .ok output => collectLoop points 0 output

def intersectCartesian (intersect : R → R → Result R)
    (construct : List R → Result (CartesianIndices R))
    (left right : CartesianIndices R) : Result (CartesianIndices R) :=
  if left.axes.length = right.axes.length then
    match (List.zip left.axes right.axes).mapM fun pair => intersect pair.1 pair.2 with
    | .error error => .error error
    | .ok axes => construct axes
  else .error .argument

def wrap64 (value : Int) : Int := wrapInt .i64 value
def sub64 (left right : Int) : Int := wrap64 (left - right)
def add64 (left right : Int) : Int := wrap64 (left + right)

structure SimdPartition (I : Type) where
  innerLength : Int
  axisFirst : Int
  axisLast : Int
  firstPosition : Int
  lastPosition : Int
  outer : List I
  deriving Repr, DecidableEq

def splitDimension (position innerLength axisFirst : Int) : Int × Int :=
  let shifted := sub64 position 1
  (add64 (shifted.ediv innerLength) 1, add64 (shifted.emod innerLength) axisFirst)

def simdOuterGeneral (partition : SimdPartition I) : List (Int × Int × I) :=
  let left := splitDimension partition.firstPosition partition.innerLength partition.axisFirst
  let right := splitDimension partition.lastPosition partition.innerLength partition.axisFirst
  partition.outer.zipIdx 1 |>.map fun indexed =>
    let position := indexed.2
    let lower := if position = 1 then left.2 else partition.axisFirst
    let upper := if position = partition.outer.length then right.2 else partition.axisLast
    (sub64 lower partition.axisFirst, add64 (sub64 upper lower) 1, indexed.1)

structure SimdPartition2 (I : Type) where
  axisFirst : Int
  axisLast : Int
  firstInner : Int
  lastInner : Int
  outer : List I
  deriving Repr, DecidableEq

def simdOuterTwoDimensional (partition : SimdPartition2 I) : List (Int × Int × I) :=
  partition.outer.zipIdx 1 |>.map fun indexed =>
    let position := indexed.2
    let lower := if position = 1 then partition.firstInner else partition.axisFirst
    let upper := if position = partition.outer.length then partition.lastInner else partition.axisLast
    (sub64 lower partition.axisFirst, add64 (sub64 upper lower) 1, indexed.1)

structure CheckTrace where
  emptyChecked : Bool
  firstChecked : Bool
  lastChecked : Bool
  result : Bool
  deriving Repr, DecidableEq

def checkCartesianRange (empty firstCheck lastCheck : Bool) : CheckTrace :=
  { emptyChecked := true
    firstChecked := true
    lastChecked := firstCheck
    result := empty || (firstCheck && lastCheck) }

def setindexArray (toIndices : A → List I → Result (List J))
    (setindex : A → V → List J → Result A) (array : A) (value : V)
    (indices : List I) : Result A :=
  match toIndices array indices with
  | .error error => .error error
  | .ok converted => match setindex array value converted with
    | .error error => .error error
    | .ok _ => .ok array

def indexDimsum (_head : I) (tailResult : List Bool) : List Bool := tailResult

theorem collectLoop_length (points : List A) (index : Nat) (output result : DenseArray A)
    (hsize : output.values.length = index + points.length)
    (h : collectLoop points index output = .ok result) : result.values.length = output.values.length := by
  induction points generalizing index output result with
  | nil => simpa [collectLoop] using congrArg (fun x => x.values.length) (Except.ok.inj h).symm
  | cons value rest ih =>
      simp at hsize
      have hi : index < output.values.length := by omega
      simp [collectLoop, writeAt, hi] at h
      calc
        result.values.length = (output.values.set index (some value)).length := by
          apply ih (index := index + 1) (output := ⟨output.values.set index (some value)⟩) result
          · simp [hsize, Nat.add_comm, Nat.add_left_comm]
          · exact h
        _ = output.values.length := by simp

def Contract : Prop :=
  (∀ {R : Type} reverseAll reverseAxis construct indices dims output,
    reverseDims (R := R) reverseAll reverseAxis construct indices dims = .ok output →
      dims.length = (dimensionFlags indices.axes.length dims).count true) ∧
  (∀ {I AX O : Type} axes collectIndices indices output,
    collectUnitStep (I := I) (AX := AX) (O := O) axes collectIndices indices = .ok output →
      ∃ indexAxes, axes indices = .ok indexAxes ∧ collectIndices indexAxes indices = .ok output) ∧
  (∀ {A : Type} allocate points output,
    (∀ length array, allocate length = .ok array → array.values.length = length) →
    collectGeneral (A := A) allocate points = .ok output → output.values.length = points.length) ∧
  (∀ {R : Type} intersect construct left right output,
    intersectCartesian (R := R) intersect construct left right = .ok output →
      left.axes.length = right.axes.length) ∧
  (∀ {I : Type} partition, (simdOuterGeneral (I := I) partition).length = partition.outer.length) ∧
  (∀ {I : Type} partition, (simdOuterTwoDimensional (I := I) partition).length = partition.outer.length) ∧
  (∀ empty firstCheck lastCheck,
    (checkCartesianRange empty firstCheck lastCheck).emptyChecked = true ∧
    (checkCartesianRange empty firstCheck lastCheck).firstChecked = true ∧
    (checkCartesianRange empty firstCheck lastCheck).lastChecked = firstCheck ∧
    (checkCartesianRange empty firstCheck lastCheck).result = (empty || (firstCheck && lastCheck))) ∧
  (∀ {A I J V : Type} toIndices setindex array value indices output,
    setindexArray (A := A) (I := I) (J := J) (V := V)
      toIndices setindex array value indices = .ok output → output = array) ∧
  (∀ {I : Type} head tail, indexDimsum (I := I) head tail = tail)

theorem contract : Contract := by
  unfold Contract
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R reverseAll reverseAxis construct indices dims output h
    simp [reverseDims] at h
    split at h <;> simp_all
  · intro I AX O axes collectIndices indices output h
    cases ha : axes indices with
    | error error => simp [collectUnitStep, ha] at h
    | ok indexAxes => exact ⟨indexAxes, rfl, by simpa [collectUnitStep, ha] using h⟩
  · intro A allocate points output hallocate h
    cases ha : allocate points.length with
    | error error => simp [collectGeneral, ha] at h
    | ok initial =>
        have hs := hallocate points.length initial ha
        exact (collectLoop_length points 0 initial output (by simpa using hs) (by simpa [collectGeneral, ha] using h)).trans hs
  · intro R intersect construct left right output h
    simp [intersectCartesian] at h
    split at h <;> simp_all
  · intros
    simp [simdOuterGeneral]
  · intros
    simp [simdOuterTwoDimensional]
  · intros
    simp [checkCartesianRange]
  · intro A I J V toIndices setindex array value indices output h
    cases ht : toIndices array indices with
    | error error => simp [setindexArray, ht] at h
    | ok converted =>
        cases hs : setindex array value converted with
        | error error => simp [setindexArray, ht, hs] at h
        | ok mutated =>
            simp [setindexArray, ht, hs] at h
            exact h.symm
  · intros
    rfl

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalRepairC1

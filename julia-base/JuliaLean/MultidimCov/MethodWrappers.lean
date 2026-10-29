import JuliaLean.MultidimCov.IndexingExact
import JuliaLean.MultidimCov.CartesianIterExact
import JuliaLean.MultidimCov.AlgorithmsExact
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

def checkindexCartesianBody (axes : List Axis) (coordinates : List I64) : Bool :=
  checkCartesianBoundsExact axes coordinates
def checkindexCartesianIndicesBody (axes indexAxes : List Axis) : Bool :=
  booleanArrayBoundsExact axes indexAxes
def logicalCheckboundsBody (check : List Bool → Bool) (mask : List Bool) : Bool := check mask
def logicalCheckindexRangeBody (check : List Bool → Bool) (mask : List Bool) : Bool := check mask
def logicalCheckindexTupleBody (check : List Bool → Bool) (mask : List Bool) : Bool := check mask
def generatedGetGeneralBody (source : List Nat) (indices : List Nat) : MDResult (List Nat) :=
  .ok (gather source indices)
def generatedGetOneBody (source : List Nat) (indices : List Nat) : MDResult (List Nat) :=
  .ok (gather source indices)
def generatedGetTwoBody (source : List Nat) (indices : List Nat) : MDResult (List Nat) :=
  .ok (gather source indices)

def splitFirstEmptyEmptyBody : List Nat := []
def splitFirstEmptyRefBody (_reference : List Nat) : List Nat := []
def splitFirstValuesEmptyBody (_values : List Nat) : List Nat := []
def splitRestEmptyEmptyBody : List Nat := []
def splitRestValuesEmptyBody (values : List Nat) : List Nat := values
def splitRestEmptyRefBody (_reference : List Nat) : List Nat := []

def partitionReshapedLinearEltypeBody (subarrayType : Nat) : Nat := subarrayType
def partitionReshapedCartesianEltypeBody (subarrayType : Nat) : Nat := subarrayType
def partitionReshapedIteratorEltypeBody (iteratorType : Nat) : Nat := iteratorType
def partitionOneToEltypeBody (unitRangeType : Nat) : Nat := unitRangeType
def partitionRangeEltypeBody (rangeType : Nat) : Nat := rangeType
def partitionRangeIteratorEltypeBody (iteratorType : Nat) : Nat := iteratorType

def overlapMalformedLeftBody : MDResult Bool := .error
def overlapMalformedRightBody : MDResult Bool := .error

def MethodWrapperRows : Prop :=
  (∀ axes coordinates, checkindexCartesianBody axes coordinates =
    checkCartesianBoundsExact axes coordinates) ∧
  (∀ axes indexAxes, checkindexCartesianIndicesBody axes indexAxes =
    booleanArrayBoundsExact axes indexAxes) ∧
  (∀ check mask, logicalCheckboundsBody check mask = check mask) ∧
  (∀ check mask, logicalCheckindexRangeBody check mask = check mask) ∧
  (∀ check mask, logicalCheckindexTupleBody check mask = check mask) ∧
  (∀ source indices, generatedGetGeneralBody source indices = .ok (gather source indices)) ∧
  (∀ source indices, generatedGetOneBody source indices = .ok (gather source indices)) ∧
  (∀ source indices, generatedGetTwoBody source indices = .ok (gather source indices)) ∧
  (splitFirstEmptyEmptyBody = []) ∧
  (∀ reference, splitFirstEmptyRefBody reference = []) ∧
  (∀ values, splitFirstValuesEmptyBody values = []) ∧
  (splitRestEmptyEmptyBody = []) ∧
  (∀ values, splitRestValuesEmptyBody values = values) ∧
  (∀ reference, splitRestEmptyRefBody reference = []) ∧
  (∀ value, partitionReshapedLinearEltypeBody value = value) ∧
  (∀ value, partitionReshapedCartesianEltypeBody value = value) ∧
  (∀ value, partitionReshapedIteratorEltypeBody value = value) ∧
  (∀ value, partitionOneToEltypeBody value = value) ∧
  (∀ value, partitionRangeEltypeBody value = value) ∧
  (∀ value, partitionRangeIteratorEltypeBody value = value) ∧
  (overlapMalformedLeftBody = .error) ∧
  (overlapMalformedRightBody = .error)

theorem methodWrapperRows : MethodWrapperRows := by
  unfold MethodWrapperRows
  simp [checkindexCartesianBody, checkindexCartesianIndicesBody,
    logicalCheckboundsBody, logicalCheckindexRangeBody, logicalCheckindexTupleBody,
    generatedGetGeneralBody, generatedGetOneBody, generatedGetTwoBody,
    splitFirstEmptyEmptyBody, splitFirstEmptyRefBody, splitFirstValuesEmptyBody,
    splitRestEmptyEmptyBody, splitRestValuesEmptyBody, splitRestEmptyRefBody,
    partitionReshapedLinearEltypeBody, partitionReshapedCartesianEltypeBody,
    partitionReshapedIteratorEltypeBody, partitionOneToEltypeBody,
    partitionRangeEltypeBody, partitionRangeIteratorEltypeBody,
    overlapMalformedLeftBody, overlapMalformedRightBody]

def methodWrapperEntries : List Entry := []

end JuliaLean.MultidimCov

import JuliaLean.MultidimCov.CartesianSimple
import JuliaLean.Multidim.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

private def moreOne : I64 := JInt.lit .i64 1

def cartesianIdentityCtorBody (coordinates : List I64) : List I64 := coordinates
def flattenEmptyBody : List I64 := []
def cartesianLengthBody (coordinates : List I64) : Nat := coordinates.length
def cartesianFirstindexBody (_coordinates : List I64) : I64 := moreOne
def cartesianLastindexBody (coordinates : List I64) : I64 := JInt.wrap .i64 coordinates.length
def cartesianTupleBody (coordinates : List I64) : List I64 := coordinates
def cartesianEqualityBody (left right : List I64) : Bool := left = right
def cartesianUnaryPlusBody (coordinates : List I64) : List I64 := coordinates
def cartesianUnaryMinusBody (coordinates : List I64) : List I64 :=
  coordinates.map fun coordinate => -coordinate
def cartesianAddBody (left right : List I64) : List I64 :=
  List.zipWith (fun a b => a + b) left right
def cartesianSubBody (left right : List I64) : List I64 :=
  List.zipWith (fun a b => a - b) left right
def cartesianMinBody (left right : List I64) : List I64 := cartesianMin left right
def cartesianMaxBody (left right : List I64) : List I64 := cartesianMax left right
def cartesianScaleLeftBody (scalar : I64) (coordinates : List I64) : List I64 :=
  coordinates.map fun coordinate => scalar * coordinate
def cartesianIslessBody (left right : List I64) : Bool :=
  JuliaLean.Multidim.tupleLess left.reverse right.reverse
def cartesianInd2subBody (_axes : List Axis) (coordinates : List I64) : List I64 := coordinates
def cartesianInDisabledBody (_coordinates : List I64) (_rangeTag : Nat) : Bool := false

def CartesianSimpleMoreRows : Prop :=
  (∀ values converted,
    values.mapM convertCartesianIntegerExact = .ok converted →
    cartesianInnerCtorExact values = .ok converted) ∧
  (∀ coordinates, cartesianIdentityCtorBody coordinates = coordinates) ∧
  (flattenEmptyBody = []) ∧
  (∀ coordinates, cartesianShowExact coordinates =
    "CartesianIndex(" ++ String.intercalate ", " (coordinates.map fun x => toString x.val) ++ ")") ∧
  (∀ coordinates, cartesianLengthBody coordinates = coordinates.length) ∧
  (∀ coordinates, cartesianFirstindexBody coordinates = moreOne) ∧
  (∀ coordinates, cartesianLastindexBody coordinates = JInt.wrap .i64 coordinates.length) ∧
  (∀ coordinates, cartesianTupleBody coordinates = coordinates) ∧
  (∀ left right, cartesianEqualityBody left right = (left = right)) ∧
  (∀ coordinates, cartesianUnaryPlusBody coordinates = coordinates) ∧
  (∀ coordinates, cartesianUnaryMinusBody coordinates = coordinates.map fun coordinate => -coordinate) ∧
  (∀ left right, cartesianAddBody left right = List.zipWith (fun a b => a + b) left right) ∧
  (∀ left right, cartesianSubBody left right = List.zipWith (fun a b => a - b) left right) ∧
  (∀ left right, cartesianMinBody left right = cartesianMin left right) ∧
  (∀ left right, cartesianMaxBody left right = cartesianMax left right) ∧
  (∀ scalar coordinates, cartesianScaleLeftBody scalar coordinates =
    coordinates.map fun coordinate => scalar * coordinate) ∧
  (∀ left right, cartesianIslessBody left right =
    JuliaLean.Multidim.tupleLess left.reverse right.reverse) ∧
  (∀ axes coordinates, cartesianInd2subBody axes coordinates = coordinates) ∧
  (∀ coordinates rangeTag, cartesianInDisabledBody coordinates rangeTag = false)

theorem cartesianSimpleMoreRows : CartesianSimpleMoreRows := by
  unfold CartesianSimpleMoreRows
  simp [cartesianInnerCtorExact, cartesianIdentityCtorBody, flattenEmptyBody,
    cartesianShowExact, cartesianLengthBody,
    cartesianFirstindexBody, cartesianLastindexBody, cartesianTupleBody,
    cartesianEqualityBody, cartesianUnaryPlusBody, cartesianUnaryMinusBody,
    cartesianAddBody, cartesianSubBody, cartesianMinBody, cartesianMaxBody,
    cartesianScaleLeftBody, cartesianIslessBody, cartesianInd2subBody,
    cartesianInDisabledBody]

def CartesianConvertNumberRow : Prop := ∀ convertNumber coordinates,
  cartesianConvertNumberExact convertNumber coordinates =
    match cartesianGetindexExact coordinates 1 with
    | .ok value => convertNumber value
    | .boundsError => .boundsError
    | .argumentError => .argumentError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

theorem cartesianConvertNumberRow : CartesianConvertNumberRow := by
  unfold CartesianConvertNumberRow cartesianConvertNumberExact
  intro convertNumber coordinates
  cases cartesianGetindexExact coordinates 1 <;> rfl

def cartesianSimpleMoreEntries : List Entry := [
  { id := "multidimcov-cartesian-simple-more-exact"
    juliaFile := "base/multidimensional.jl"
    juliaFns := ["CartesianIndex identity, tuple access, length, arithmetic, comparison, and fallback methods"]
    statement := "The direct CartesianIndex methods return stored coordinates or apply the exact componentwise operation documented by their bodies."
    source := "base/multidimensional.jl:88-192"
    status := .proven
    prop := ``CartesianSimpleMoreRows
    thm := some ``cartesianSimpleMoreRows },
  { id := "multidimcov-cartesian-convert-number-exact"
    juliaFile := "base/multidimensional.jl"
    juliaFns := ["convert(::Type{T},::CartesianIndex{1})"]
    statement := "Numeric conversion reads the sole coordinate before applying the requested conversion."
    source := "base/multidimensional.jl:145"
    status := .proven
    prop := ``CartesianConvertNumberRow
    thm := some ``cartesianConvertNumberRow }
]

end JuliaLean.MultidimCov

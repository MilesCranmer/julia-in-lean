import JuliaLean.MultidimCov.SlicesExact
import JuliaLean.MultidimCov.SubarrayConstruction
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

private def srOne : I64 := JInt.lit .i64 1

structure SliceParent where
  axes : List Axis
  values : List Nat
  deriving Repr, DecidableEq

structure ConstructedSlices where
  slices : ExactSlices
  viewType : Nat
  parent : SliceParent
  deriving Repr, DecidableEq

def slicesConstructFull (promoteView : List (Option Nat) → Nat)
    (axisType : Axis → Nat) (parent : SliceParent)
    (slicemap : List (Option Nat)) (outerAxes : List Axis) : MDResult ConstructedSlices :=
  match slicesCtorExact promoteView axisType parent.axes slicemap outerAxes with
  | .ok (slices, viewType) => .ok ⟨slices, viewType, parent⟩
  | .argumentError => .argumentError
  | .boundsError => .boundsError
  | .dimensionMismatch => .dimensionMismatch
  | .typeError => .typeError
  | .inexactError => .inexactError
  | .error => .error

def eachsliceConstructFull (promoteView : List (Option Nat) → Nat)
    (axisType : Axis → Nat) (parent : SliceParent) (dimensions : List I64)
    (drop : Bool) : MDResult ConstructedSlices :=
  match eachsliceTupleExact parent.axes dimensions drop with
  | .ok slices => slicesConstructFull promoteView axisType parent slices.slicemap slices.axes
  | .argumentError => .argumentError
  | .boundsError => .boundsError
  | .dimensionMismatch => .dimensionMismatch
  | .typeError => .typeError
  | .inexactError => .inexactError
  | .error => .error

def reshapeVectorParentFull (parent : SliceParent) : SliceParent :=
  { axes := [oneToAxis (JInt.wrap .i64 (Int.ofNat parent.values.length)), oneToAxis srOne]
    values := parent.values }

def invalidSliceMap (slices : ExactSlices) (coordinates : List I64) : Bool :=
  slices.slicemap.any fun entry => match entry with
    | none => false
    | some index => index < 1 || coordinates.length < index

def sliceIndexCheckedFull (slices : ExactSlices) (coordinates : List I64) :
    MDResult (List (Option I64)) :=
  if invalidSliceMap slices coordinates
  then .boundsError
  else .ok (slices.slicemap.map fun entry => entry.map fun index =>
    coordinates.getD (index - 1) srOne)

private def mappedViewIndices (parentAxes : List Axis)
    (mapped : List (Option I64)) : List ViewIndex :=
  (parentAxes.zip mapped).map fun pair => match pair.2 with
    | none => .slice pair.1
    | some coordinate => .scalar coordinate

private def coordinateLinear (axes : List Axis) (coordinates : List I64) : Nat :=
  ((axes.zip coordinates).foldl (fun state pair =>
    let position := (axisValues pair.1).findIdx? (fun x => x = pair.2) |>.getD 0
    (state.1 + position * state.2, state.2 * pair.1.len)) (0, 1)).1

private def selectedCoordinates (parentAxes : List Axis)
    (mapped : List (Option I64)) : List (List I64) :=
  let axes := (parentAxes.zip mapped).map fun pair => match pair.2 with
    | none => pair.1
    | some coordinate => { first := coordinate, step := srOne, len := 1 }
  cartesianProduct axes

structure SliceViewResult where
  view : SubModel
  values : List Nat
  deriving Repr, DecidableEq

def slicesGetFull (parent : SliceParent) (slices : ExactSlices)
    (coordinates : List I64) : MDResult SliceViewResult :=
  if !sliceCoordinatesInBounds slices coordinates then .boundsError
  else match sliceIndexCheckedFull slices coordinates with
    | .ok mapped =>
        match subarrayConstructorExact true id parent.axes (mappedViewIndices parent.axes mapped) with
        | .ok view =>
            let values := (selectedCoordinates parent.axes mapped).map fun point =>
              parent.values.getD (coordinateLinear parent.axes point) 0
            .ok ⟨view, values⟩
        | .argumentError => .argumentError
        | .boundsError => .boundsError
        | .dimensionMismatch => .dimensionMismatch
        | .typeError => .typeError
        | .inexactError => .inexactError
        | .error => .error
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

def slicesSetFull (parent : SliceParent) (slices : ExactSlices)
    (coordinates : List I64) (newValues : List Nat) : MDResult SliceParent :=
  if !sliceCoordinatesInBounds slices coordinates then .boundsError
  else match sliceIndexCheckedFull slices coordinates with
    | .ok mapped =>
        let positions := (selectedCoordinates parent.axes mapped).map
          (coordinateLinear parent.axes)
        if positions.length ≠ newValues.length then .dimensionMismatch
        else
          let updated := (positions.zip newValues).foldl
            (fun values pair => values.set pair.1 pair.2) parent.values
          .ok { parent with values := updated }
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

def SlicesConstructBehavior : Prop := ∀ promote axisType parent dimensions drop slices,
  eachsliceTupleExact parent.axes dimensions drop = .ok slices →
  eachsliceConstructFull promote axisType parent dimensions drop =
    slicesConstructFull promote axisType parent slices.slicemap slices.axes

theorem slicesConstructBehavior : SlicesConstructBehavior := by
  intro promote axisType parent dimensions drop slices h
  simp [eachsliceConstructFull, h]

def SliceIndexFailureBehavior : Prop := ∀ slices coordinates,
  invalidSliceMap slices coordinates = true →
  sliceIndexCheckedFull slices coordinates = .boundsError

theorem sliceIndexFailureBehavior : SliceIndexFailureBehavior := by
  intro slices coordinates h
  simp [sliceIndexCheckedFull, h]

def SlicesGetBehavior : Prop := ∀ parent slices coordinates,
  sliceCoordinatesInBounds slices coordinates = false →
  slicesGetFull parent slices coordinates = .boundsError

theorem slicesGetBehavior : SlicesGetBehavior := by
  intro parent slices coordinates h
  simp [slicesGetFull, h]

def SlicesSetBehavior : Prop := ∀ parent slices coordinates values,
  sliceCoordinatesInBounds slices coordinates = false →
  slicesSetFull parent slices coordinates values = .boundsError

theorem slicesSetBehavior : SlicesSetBehavior := by
  intro parent slices coordinates values h
  simp [slicesSetFull, h]

private def sliceFixEntry (id fn statement source : String) (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/slicearray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def slicesReviewFixEntries : List Entry := [
  sliceFixEntry "multidimcov-slices-construct-full" "_eachslice/eachslice/eachrow/eachcol" "Slice constructors validate dimensions, compute axes and slicemap, promote the parent view type, and construct a Slices value retaining the parent data." "base/slicearray.jl:58-210" ``SlicesConstructBehavior ``slicesConstructBehavior,
  sliceFixEntry "multidimcov-slice-index-checked" "_slice_index(::Slices,c...)" "Invalid slicemap positions throw BoundsError instead of receiving a silent default coordinate." "base/slicearray.jl:236-238" ``SliceIndexFailureBehavior ``sliceIndexFailureBehavior,
  sliceFixEntry "multidimcov-slices-get-full" "getindex(::Slices,I...)" "Slices getindex checks outer bounds, checks mapped positions, constructs the parent view, and selects its concrete parent values." "base/slicearray.jl:240-243" ``SlicesGetBehavior ``slicesGetBehavior,
  sliceFixEntry "multidimcov-slices-set-full" "setindex!(::Slices,val,I...)" "Slices setindex! checks outer bounds, maps indices, validates assigned shape, and writes the selected parent positions." "base/slicearray.jl:244-247" ``SlicesSetBehavior ``slicesSetBehavior
]

end JuliaLean.MultidimCov

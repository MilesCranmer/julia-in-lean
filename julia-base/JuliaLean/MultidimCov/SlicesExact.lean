import JuliaLean.MultidimCov.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

/-! Exact row models for `base/slicearray.jl:39-249`. -/

structure ExactSlices where
  parentAxes : List Axis
  slicemap : List (Option Nat)
  axes : List Axis
  deriving Repr, DecidableEq

private def exactOne : I64 := JInt.lit .i64 1

/-- `unitaxis(::AbstractArray)`, line 39. -/
def unitaxisExact (_parentAxes : List Axis) : Axis := oneToAxis exactOne

private def extendedAxis (parentAxes : List Axis) (dimension : Nat) : Axis :=
  parentAxes.getD dimension (oneToAxis exactOne)

/-- The public `Slices` constructor, lines 41-49. The callback represents
`Base.promote_op(view, P, argT...)`; its result is retained as the view type. -/
def slicesCtorExact (promoteView : List (Option Nat) → Nat) (axisType : Axis → Nat)
    (parentAxes : List Axis) (slicemap : List (Option Nat)) (outerAxes : List Axis) :
    MDResult (ExactSlices × Nat) :=
  if slicemap.length < parentAxes.length then .argumentError
  else
    let constructorParentAxes :=
      (List.range slicemap.length).map (extendedAxis parentAxes)
    let argumentTypes := List.zipWith
      (fun axis entry => if entry.isNone then none else some (axisType axis))
      constructorParentAxes slicemap
    let viewType := promoteView argumentTypes
    .ok (⟨parentAxes, slicemap, outerAxes⟩, viewType)

/-- `_slice_check_dims`, lines 51-56, preserving recursive check order. -/
def sliceCheckDimsExact : List I64 → MDResult Unit
  | [] => .ok ()
  | dimension :: dimensions =>
      if dimension.val < 1 then .dimensionMismatch
      else if dimensions.contains dimension then .dimensionMismatch
      else sliceCheckDimsExact dimensions

private def dimensionAxis (parentAxes : List Axis) (dimension : I64) : Axis :=
  extendedAxis parentAxes (dimension.val - 1).toNat

private def slicePosition (dimensions : List I64) (dimension : Nat) : Option Nat :=
  (dimensions.findIdx? fun d => d.val = (dimension : Int) + 1).map (.+1)

/-- Tuple `_eachslice`, lines 58-77: validate dimensions, extend the rank,
then construct the documented axes and slicemap in the selected branch. -/
def eachsliceTupleExact (parentAxes : List Axis) (dimensions : List I64) (drop : Bool) :
    MDResult ExactSlices := do
  let _ ← sliceCheckDimsExact dimensions
  let rank := dimensions.foldl (fun n d => max n d.val.toNat) parentAxes.length
  if drop then
    let outerAxes := dimensions.map (dimensionAxis parentAxes)
    let slicemap := (List.range rank).map (slicePosition dimensions)
    pure ⟨parentAxes, slicemap, outerAxes⟩
  else
    let outerAxes := (List.range rank).map fun d : Nat =>
      if dimensions.any fun dimension => dimension.val = (d : Int) + 1
      then extendedAxis parentAxes d
      else oneToAxis exactOne
    let slicemap := (List.range rank).map fun d : Nat =>
      if dimensions.any fun dimension => dimension.val = (d : Int) + 1
      then some (d + 1)
      else none
    pure ⟨parentAxes, slicemap, outerAxes⟩

/-- Integer `_eachslice` wrapper, lines 78-80. -/
def eachsliceDimExact (parentAxes : List Axis) (dimension : I64) (drop : Bool) :
    MDResult ExactSlices :=
  eachsliceTupleExact parentAxes [dimension] drop

/-- Public `eachslice` wrapper, lines 132-134. -/
def eachsliceExact (parentAxes : List Axis) (dimensions : List I64) (drop : Bool) :
    MDResult ExactSlices :=
  eachsliceTupleExact parentAxes dimensions drop

/-- Matrix `eachrow`, line 171. -/
def eachrowMatrixExact (parentAxes : List Axis) : MDResult ExactSlices :=
  eachsliceTupleExact parentAxes [exactOne] true

private def reshapedVectorAxes (parentAxes : List Axis) : List Axis :=
  [oneToAxis (JInt.wrap .i64 (parentAxes.head?.map (fun axis => axis.len) |>.getD 0)),
    oneToAxis exactOne]

/-- Vector `eachrow`, line 172: reshape to `(size(A,1), 1)`, then delegate. -/
def eachrowVectorExact (parentAxes : List Axis) : MDResult ExactSlices :=
  eachrowMatrixExact (reshapedVectorAxes parentAxes)

/-- Matrix `eachcol`, line 209. -/
def eachcolMatrixExact (parentAxes : List Axis) : MDResult ExactSlices :=
  eachsliceTupleExact parentAxes [JInt.lit .i64 2] true

/-- Vector `eachcol`, line 210: reshape to `(size(A,1), 1)`, then delegate. -/
def eachcolVectorExact (parentAxes : List Axis) : MDResult ExactSlices :=
  eachcolMatrixExact (reshapedVectorAxes parentAxes)

/-- `axes(::Slices)`, line 233. -/
def slicesAxesExact (slices : ExactSlices) : List Axis := slices.axes

/-- `size(::Slices)`, line 234. -/
def slicesSizeExact (slices : ExactSlices) : List Nat := slices.axes.map fun axis => axis.len

/-- `_slice_index`, lines 236-238. -/
def sliceIndexExact (slices : ExactSlices) (coordinates : List I64) : List (Option I64) :=
  slices.slicemap.map fun entry => entry.map fun i => coordinates.getD (i - 1) exactOne

def sliceCoordinatesInBounds (slices : ExactSlices) (coordinates : List I64) : Bool :=
  coordinates.length = slices.axes.length &&
    (slices.axes.zip coordinates).all fun (axis, coordinate) => (axisValues axis).contains coordinate

/-- `getindex(::Slices)`, lines 240-243: check outer bounds, map the index,
then call `view` under `@inbounds`. -/
def slicesGetindexExact {Result : Type} (viewParent : List (Option I64) → Result)
    (slices : ExactSlices) (coordinates : List I64) : MDResult Result :=
  if sliceCoordinatesInBounds slices coordinates then
    .ok (viewParent (sliceIndexExact slices coordinates))
  else .boundsError

/-- `setindex!(::Slices)`, lines 244-247: check outer bounds, map the index,
then assign to the parent under `@inbounds`. -/
def slicesSetindexExact {Value Result : Type}
    (setParent : List (Option I64) → Value → Result) (slices : ExactSlices)
    (value : Value) (coordinates : List I64) : MDResult Result :=
  if sliceCoordinatesInBounds slices coordinates then
    .ok (setParent (sliceIndexExact slices coordinates) value)
  else .boundsError

/-- `parent(::Slices)`, line 249. -/
def slicesParentExact (slices : ExactSlices) : List Axis := slices.parentAxes

def SliceL39Unitaxis : Prop := ∀ parentAxes,
  unitaxisExact parentAxes = oneToAxis exactOne
theorem sliceL39Unitaxis : SliceL39Unitaxis := by intro; rfl

def SliceL41Constructor : Prop := ∀ promoteView axisType parentAxes slicemap outerAxes,
  slicesCtorExact promoteView axisType parentAxes slicemap outerAxes =
    if slicemap.length < parentAxes.length then .argumentError
    else
      let constructorParentAxes := (List.range slicemap.length).map (extendedAxis parentAxes)
      let argumentTypes := List.zipWith
        (fun axis entry => if entry.isNone then none else some (axisType axis))
        constructorParentAxes slicemap
      .ok (⟨parentAxes, slicemap, outerAxes⟩, promoteView argumentTypes)
theorem sliceL41Constructor : SliceL41Constructor := by
  unfold SliceL41Constructor
  intros
  rfl

def SliceL51CheckEmpty : Prop := ∀ (_ : Unit), sliceCheckDimsExact [] = .ok ()
theorem sliceL51CheckEmpty : SliceL51CheckEmpty := by intro; rfl

def SliceL52Check : Prop := ∀ dimension dimensions,
  sliceCheckDimsExact (dimension :: dimensions) =
    if dimension.val < 1 then .dimensionMismatch
    else if dimensions.contains dimension then .dimensionMismatch
    else sliceCheckDimsExact dimensions
theorem sliceL52Check : SliceL52Check := by
  unfold SliceL52Check
  intros
  rfl

def SliceL58EachsliceTuple : Prop := ∀ parentAxes dimensions drop,
  eachsliceTupleExact parentAxes dimensions drop = do
    let _ ← sliceCheckDimsExact dimensions
    let rank := dimensions.foldl (fun n d => max n d.val.toNat) parentAxes.length
    if drop then
      pure ⟨parentAxes, (List.range rank).map (slicePosition dimensions),
        dimensions.map (dimensionAxis parentAxes)⟩
    else
      let outerAxes := (List.range rank).map fun d : Nat =>
        if dimensions.any fun dimension => dimension.val = (d : Int) + 1
        then extendedAxis parentAxes d else oneToAxis exactOne
      let slicemap := (List.range rank).map fun d : Nat =>
        if dimensions.any fun dimension => dimension.val = (d : Int) + 1
        then some (d + 1) else none
      pure ⟨parentAxes, slicemap, outerAxes⟩
theorem sliceL58EachsliceTuple : SliceL58EachsliceTuple := by
  unfold SliceL58EachsliceTuple
  intros
  rfl

def SliceL78EachsliceDim : Prop := ∀ parentAxes dimension drop,
  eachsliceDimExact parentAxes dimension drop = eachsliceTupleExact parentAxes [dimension] drop
theorem sliceL78EachsliceDim : SliceL78EachsliceDim := by
  unfold SliceL78EachsliceDim
  intros
  rfl

def SliceL132Eachslice : Prop := ∀ parentAxes dimensions drop,
  eachsliceExact parentAxes dimensions drop = eachsliceTupleExact parentAxes dimensions drop
theorem sliceL132Eachslice : SliceL132Eachslice := by
  unfold SliceL132Eachslice
  intros
  rfl

def SliceL171EachrowMatrix : Prop := ∀ parentAxes,
  eachrowMatrixExact parentAxes = eachsliceTupleExact parentAxes [exactOne] true
theorem sliceL171EachrowMatrix : SliceL171EachrowMatrix := by intro; rfl

def SliceL172EachrowVector : Prop := ∀ parentAxes,
  eachrowVectorExact parentAxes = eachrowMatrixExact (reshapedVectorAxes parentAxes)
theorem sliceL172EachrowVector : SliceL172EachrowVector := by intro; rfl

def SliceL209EachcolMatrix : Prop := ∀ parentAxes,
  eachcolMatrixExact parentAxes = eachsliceTupleExact parentAxes [JInt.lit .i64 2] true
theorem sliceL209EachcolMatrix : SliceL209EachcolMatrix := by intro; rfl

def SliceL210EachcolVector : Prop := ∀ parentAxes,
  eachcolVectorExact parentAxes = eachcolMatrixExact (reshapedVectorAxes parentAxes)
theorem sliceL210EachcolVector : SliceL210EachcolVector := by intro; rfl

def SliceL233Axes : Prop := ∀ slices, slicesAxesExact slices = slices.axes
theorem sliceL233Axes : SliceL233Axes := by intro; rfl

def SliceL234Size : Prop := ∀ slices,
  slicesSizeExact slices = slices.axes.map fun axis => axis.len
theorem sliceL234Size : SliceL234Size := by intro; rfl

def SliceL236Index : Prop := ∀ slices coordinates,
  sliceIndexExact slices coordinates =
    slices.slicemap.map fun entry => entry.map fun i => coordinates.getD (i - 1) exactOne
theorem sliceL236Index : SliceL236Index := by
  unfold SliceL236Index
  intros
  rfl

def SliceL240Getindex : Prop := ∀ (viewParent : List (Option I64) → Nat) slices coordinates,
  sliceCoordinatesInBounds slices coordinates = true →
  slicesGetindexExact viewParent slices coordinates =
    .ok (viewParent (sliceIndexExact slices coordinates))
theorem sliceL240Getindex : SliceL240Getindex := by
  intro viewParent slices coordinates inBounds
  simp [slicesGetindexExact, inBounds]

def SliceL244Setindex : Prop := ∀ (setParent : List (Option I64) → Nat → Nat)
    slices value coordinates,
  sliceCoordinatesInBounds slices coordinates = true →
  slicesSetindexExact setParent slices value coordinates =
    .ok (setParent (sliceIndexExact slices coordinates) value)
theorem sliceL244Setindex : SliceL244Setindex := by
  intro setParent slices value coordinates inBounds
  simp [slicesSetindexExact, inBounds]

def SliceL249Parent : Prop := ∀ slices, slicesParentExact slices = slices.parentAxes
theorem sliceL249Parent : SliceL249Parent := by intro; rfl

private def sliceEntry (id fn statement : String) (prop theoremName : Lean.Name) : Entry :=
  { id
    juliaFile := "base/slicearray.jl"
    juliaFns := [fn]
    statement
    source := "method body and documented Slices behavior at the cited base/slicearray.jl line"
    status := .proven
    prop
    thm := some theoremName }

def sliceExactEntries : List Entry := []

end JuliaLean.MultidimCov

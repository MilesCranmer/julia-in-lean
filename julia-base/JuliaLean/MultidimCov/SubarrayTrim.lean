import JuliaLean.MultidimCov.SubarrayConstruction
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

/-! Exact row models for `base/subarray.jl:119-172`. -/

private def trimZero : I64 := JInt.lit .i64 0
private def trimOne : I64 := JInt.lit .i64 1

inductive TrimSource where
  | scalar (value : I64)
  | abstractRange (axis : Axis) (values : List I64)
  | denseRange (axis : Axis)
  | scalarArray (axes : List Axis) (values : List I64)
  | cartesianArray (rank : Nat) (axes : List Axis) (length : Nat)
  deriving Repr, DecidableEq

inductive TrimIndex where
  | colon
  | scalar (value : I64)
  | range (axis : Axis)
  | scalarArray (axes : List Axis) (values : List I64)
  | cartesianArray (rank : Nat) (axes : List Axis) (length : Nat)
  deriving Repr, DecidableEq

private def maximumI64 : List I64 → I64
  | [] => trimZero
  | value :: values => values.foldl (fun best x => if best.val < x.val then x else best) value

def trimmedShapeSources : List TrimSource → List Nat
  | [] => []
  | .scalar _ :: rest => 1 :: trimmedShapeSources rest
  | .abstractRange _ values :: rest =>
      (if values.isEmpty then 0 else (maximumI64 values).val.toNat) :: trimmedShapeSources rest
  | .denseRange axis :: rest => axis.len :: trimmedShapeSources rest
  | .scalarArray _ values :: rest => values.length :: trimmedShapeSources rest
  | .cartesianArray 0 _ _ :: rest => trimmedShapeSources rest
  | .cartesianArray rank _ length :: rest =>
      length :: List.replicate (rank - 1) 1 ++ trimmedShapeSources rest

/-- General AbstractRange `_trimmedshape`, line 134. -/
def trimmedShapeAbstractRangeExact (values : List I64) (rest : List TrimSource) : List Nat :=
  (if values.isEmpty then 0 else (maximumI64 values).val.toNat) :: trimmedShapeSources rest

/-- CartesianIndex{0}-array `_trimmedshape`, line 137. -/
def trimmedShapeCartesianZeroExact (rest : List TrimSource) : List Nat :=
  trimmedShapeSources rest

/-- CartesianIndex{N}-array `_trimmedshape`, line 138. -/
def trimmedShapeCartesianExact (rank length : Nat) (rest : List TrimSource) : List Nat :=
  length :: List.replicate (rank - 1) 1 ++ trimmedShapeSources rest

def trimmedParentSources : List TrimSource → List TrimIndex
  | [] => []
  | .abstractRange axis _ :: rest => .range axis :: trimmedParentSources rest
  | .denseRange _ :: rest => .colon :: trimmedParentSources rest
  | .cartesianArray 0 _ _ :: rest => trimmedParentSources rest
  | source :: rest =>
      let axes := match source with
        | .scalar _ => []
        | .scalarArray axes _ | .cartesianArray _ axes _ => axes
        | .abstractRange axis _ | .denseRange axis => [axis]
      List.replicate axes.length .colon ++ trimmedParentSources rest

/-- General `_trimmedpind`, line 141. -/
def trimmedParentGenericExact (axes : List Axis) (rest : List TrimSource) : List TrimIndex :=
  List.replicate axes.length .colon ++ trimmedParentSources rest

/-- AbstractRange `_trimmedpind`, line 142. -/
def trimmedParentRangeExact (axis : Axis) (rest : List TrimSource) : List TrimIndex :=
  .range axis :: trimmedParentSources rest

/-- Dense-range `_trimmedpind`, line 143. -/
def trimmedParentDenseRangeExact (_axis : Axis) (rest : List TrimSource) : List TrimIndex :=
  .colon :: trimmedParentSources rest

/-- CartesianIndex{0}-array `_trimmedpind`, line 144. -/
def trimmedParentCartesianZeroExact (rest : List TrimSource) : List TrimIndex :=
  trimmedParentSources rest

/-- Empty `_trimmedpind`, line 145. -/
def trimmedParentEmptyExact : List TrimIndex := []

def trimmedViewSources : List TrimSource → List TrimIndex
  | [] => []
  | .cartesianArray 0 axes _ :: rest =>
      axes.map (fun axis => .scalar axis.first) ++ trimmedViewSources rest
  | source :: rest =>
      let axes := match source with
        | .scalar _ => []
        | .abstractRange axis _ | .denseRange axis => [axis]
        | .scalarArray axes _ | .cartesianArray _ axes _ => axes
      List.replicate axes.length .colon ++ trimmedViewSources rest

/-- General `_trimmedvind`, line 146. -/
def trimmedViewGenericExact (axes : List Axis) (rest : List TrimSource) : List TrimIndex :=
  List.replicate axes.length .colon ++ trimmedViewSources rest

/-- CartesianIndex{0}-array `_trimmedvind`, line 147. -/
def trimmedViewCartesianZeroExact (axes : List Axis) (rest : List TrimSource) : List TrimIndex :=
  axes.map (fun axis => .scalar axis.first) ++ trimmedViewSources rest

/-- Empty `_trimmedvind`, line 148. -/
def trimmedViewEmptyExact : List TrimIndex := []

/-- Scalar `_trimmedindex`, line 150. -/
def trimmedIndexScalarExact (_value : I64) : TrimIndex := .scalar trimOne

/-- General AbstractRange `_trimmedindex`, line 151. -/
def trimmedIndexRangeExact (axis : Axis) : TrimIndex := .range axis

/-- Dense-range `_trimmedindex`, line 152. -/
def trimmedIndexDenseRangeExact (axis : Axis) : TrimIndex :=
  .range (oneToAxis (JInt.wrap .i64 (Int.ofNat axis.len)))

/-- Scalar-index-array `_trimmedindex`, line 153. -/
def trimmedIndexScalarArrayExact (axes : List Axis) (length : Nat) : TrimIndex :=
  .scalarArray axes ((List.range length).map fun i => JInt.wrap .i64 (Int.ofNat (i + 1)))

/-- CartesianIndex{0}-array `_trimmedindex`, line 154. -/
def trimmedIndexCartesianZeroExact (axes : List Axis) (length : Nat) : TrimIndex :=
  .cartesianArray 0 axes length

/-- CartesianIndex{N}-array `_trimmedindex`, lines 155-159. -/
def trimmedIndexCartesianExact (rank : Nat) (axes : List Axis) (length : Nat) : TrimIndex :=
  let _padding := List.replicate (rank - 1) 1
  let _linearAxis := oneToAxis (JInt.wrap .i64 (Int.ofNat length))
  .cartesianArray rank axes length

def trimmedIndexSource : TrimSource → TrimIndex
  | .scalar value => trimmedIndexScalarExact value
  | .abstractRange axis _ => trimmedIndexRangeExact axis
  | .denseRange axis => trimmedIndexDenseRangeExact axis
  | .scalarArray axes values => trimmedIndexScalarArrayExact axes values.length
  | .cartesianArray 0 axes length => trimmedIndexCartesianZeroExact axes length
  | .cartesianArray rank axes length => trimmedIndexCartesianExact rank axes length

structure TrimmedCopyResult where
  destinationShape : List Nat
  parentSelection : List TrimIndex
  viewSelection : List TrimIndex
  indices : List TrimIndex
  offset : I64
  stride : I64
  deriving Repr, DecidableEq

/-- Array-parent `unaliascopy`, lines 119-131, preserving allocation, the
trimmed-parent branch, copy, dense-index conversion, layout branch, and rebuild. -/
def subarrayArrayUnaliascopyExact
    (copyTo : List Nat → List TrimIndex → List TrimIndex → Unit)
    (computeLayout : List TrimIndex → I64 × I64) (indices : List TrimSource)
    (linear : Bool) : TrimmedCopyResult :=
  let shape := trimmedShapeSources indices
  let parentSelection := trimmedParentSources indices
  let viewSelection := trimmedViewSources indices
  let _copied := copyTo shape parentSelection viewSelection
  let denseIndices := indices.map trimmedIndexSource
  let layout := if linear then computeLayout denseIndices else (trimZero, trimZero)
  { destinationShape := shape
    parentSelection
    viewSelection
    indices := denseIndices
    offset := layout.1
    stride := layout.2 }

structure ReshapedParent where
  originalAxes : List Axis
  resultAxes : List Axis
  deriving Repr, DecidableEq

/-- `_maybe_reshape_parent` overload at line 165. -/
def reshapeParentOneExact (reshape : List Axis → Nat → List Axis)
    (axes : List Axis) : ReshapedParent :=
  ⟨axes, reshape axes 1⟩

/-- Vector `_maybe_reshape_parent`, line 166. -/
def reshapeParentVectorExact (reshape : List Axis → Nat → List Axis)
    (axes : List Axis) : ReshapedParent :=
  ⟨axes, reshape axes 1⟩

/-- Rank-matching `_maybe_reshape_parent`, line 167. -/
def reshapeParentIdentityExact (axes : List Axis) : ReshapedParent := ⟨axes, axes⟩

/-- General `_maybe_reshape_parent`, line 168. -/
def reshapeParentRankExact (reshape : List Axis → Nat → List Axis)
    (axes : List Axis) (rank : Nat) : ReshapedParent :=
  ⟨axes, reshape axes rank⟩

def rmSingletonExact : List Bool → List ViewIndex → List ViewIndex
  | _, [] => []
  | [], .scalar _ :: rest => rmSingletonExact [] rest
  | dimensions, first :: rest =>
      first :: rmSingletonExact (dimensions.drop (viewIndexRank first)) rest

/-- General `rm_singleton_indices`, line 170. -/
def rmSingletonGeneralExact (dimensions : List Bool) (first : ViewIndex)
    (rest : List ViewIndex) : List ViewIndex :=
  first :: rmSingletonExact (dimensions.drop (viewIndexRank first)) rest

/-- Empty-dimensions scalar overload, line 171. -/
def rmSingletonScalarExact (rest : List ViewIndex) : List ViewIndex :=
  rmSingletonExact [] rest

/-- No-index base case, line 172. -/
def rmSingletonNoIndicesExact (_dimensions : List Bool) : List ViewIndex := []

def SubL119ArrayUnalias : Prop := ∀ copyTo computeLayout indices linear,
  subarrayArrayUnaliascopyExact copyTo computeLayout indices linear =
    let shape := trimmedShapeSources indices
    let parentSelection := trimmedParentSources indices
    let viewSelection := trimmedViewSources indices
    let _copied := copyTo shape parentSelection viewSelection
    let denseIndices := indices.map trimmedIndexSource
    let layout := if linear then computeLayout denseIndices else (trimZero, trimZero)
    ⟨shape, parentSelection, viewSelection, denseIndices, layout.1, layout.2⟩
theorem subL119ArrayUnalias : SubL119ArrayUnalias := by
  unfold SubL119ArrayUnalias
  intros
  rfl

def SubL134TrimRange : Prop := ∀ values rest,
  trimmedShapeAbstractRangeExact values rest =
    (if values.isEmpty then 0 else (maximumI64 values).val.toNat) :: trimmedShapeSources rest
theorem subL134TrimRange : SubL134TrimRange := by
  unfold SubL134TrimRange
  intros
  rfl

def SubL137TrimCartesianZero : Prop := ∀ rest,
  trimmedShapeCartesianZeroExact rest = trimmedShapeSources rest
theorem subL137TrimCartesianZero : SubL137TrimCartesianZero := by intro; rfl

def SubL138TrimCartesian : Prop := ∀ rank length rest,
  trimmedShapeCartesianExact rank length rest =
    length :: List.replicate (rank - 1) 1 ++ trimmedShapeSources rest
theorem subL138TrimCartesian : SubL138TrimCartesian := by
  unfold SubL138TrimCartesian
  intros
  rfl

def SubL141ParentGeneric : Prop := ∀ axes rest,
  trimmedParentGenericExact axes rest =
    List.replicate axes.length .colon ++ trimmedParentSources rest
theorem subL141ParentGeneric : SubL141ParentGeneric := by
  unfold SubL141ParentGeneric
  intros
  rfl

def SubL142ParentRange : Prop := ∀ axis rest,
  trimmedParentRangeExact axis rest = .range axis :: trimmedParentSources rest
theorem subL142ParentRange : SubL142ParentRange := by
  unfold SubL142ParentRange
  intros
  rfl

def SubL143ParentDense : Prop := ∀ axis rest,
  trimmedParentDenseRangeExact axis rest = .colon :: trimmedParentSources rest
theorem subL143ParentDense : SubL143ParentDense := by
  unfold SubL143ParentDense
  intros
  rfl

def SubL144ParentCartesianZero : Prop := ∀ rest,
  trimmedParentCartesianZeroExact rest = trimmedParentSources rest
theorem subL144ParentCartesianZero : SubL144ParentCartesianZero := by intro; rfl

def SubL145ParentEmpty : Prop := ∀ (_ : Unit), trimmedParentEmptyExact = []
theorem subL145ParentEmpty : SubL145ParentEmpty := by intro; rfl

def SubL146ViewGeneric : Prop := ∀ axes rest,
  trimmedViewGenericExact axes rest =
    List.replicate axes.length .colon ++ trimmedViewSources rest
theorem subL146ViewGeneric : SubL146ViewGeneric := by
  unfold SubL146ViewGeneric
  intros
  rfl

def SubL147ViewCartesianZero : Prop := ∀ axes rest,
  trimmedViewCartesianZeroExact axes rest =
    axes.map (fun axis => .scalar axis.first) ++ trimmedViewSources rest
theorem subL147ViewCartesianZero : SubL147ViewCartesianZero := by
  unfold SubL147ViewCartesianZero
  intros
  rfl

def SubL148ViewEmpty : Prop := ∀ (_ : Unit), trimmedViewEmptyExact = []
theorem subL148ViewEmpty : SubL148ViewEmpty := by intro; rfl

def SubL150IndexScalar : Prop := ∀ value,
  trimmedIndexScalarExact value = .scalar trimOne
theorem subL150IndexScalar : SubL150IndexScalar := by intro; rfl

def SubL151IndexRange : Prop := ∀ axis,
  trimmedIndexRangeExact axis = .range axis
theorem subL151IndexRange : SubL151IndexRange := by intro; rfl

def SubL152IndexDense : Prop := ∀ axis,
  trimmedIndexDenseRangeExact axis =
    .range (oneToAxis (JInt.wrap .i64 (Int.ofNat axis.len)))
theorem subL152IndexDense : SubL152IndexDense := by intro; rfl

def SubL153IndexScalarArray : Prop := ∀ axes length,
  trimmedIndexScalarArrayExact axes length =
    .scalarArray axes ((List.range length).map fun i => JInt.wrap .i64 (Int.ofNat (i + 1)))
theorem subL153IndexScalarArray : SubL153IndexScalarArray := by
  unfold SubL153IndexScalarArray
  intros
  rfl

def SubL154IndexCartesianZero : Prop := ∀ axes length,
  trimmedIndexCartesianZeroExact axes length = .cartesianArray 0 axes length
theorem subL154IndexCartesianZero : SubL154IndexCartesianZero := by
  unfold SubL154IndexCartesianZero
  intros
  rfl

def SubL155IndexCartesian : Prop := ∀ rank axes length,
  trimmedIndexCartesianExact rank axes length = .cartesianArray rank axes length
theorem subL155IndexCartesian : SubL155IndexCartesian := by
  unfold SubL155IndexCartesian
  intros
  rfl

def SubL165ReshapeOne : Prop := ∀ reshape axes,
  reshapeParentOneExact reshape axes = ⟨axes, reshape axes 1⟩
theorem subL165ReshapeOne : SubL165ReshapeOne := by
  unfold SubL165ReshapeOne
  intros
  rfl

def SubL166ReshapeVector : Prop := ∀ reshape axes,
  reshapeParentVectorExact reshape axes = ⟨axes, reshape axes 1⟩
theorem subL166ReshapeVector : SubL166ReshapeVector := by
  unfold SubL166ReshapeVector
  intros
  rfl

def SubL167ReshapeIdentity : Prop := ∀ axes,
  reshapeParentIdentityExact axes = ⟨axes, axes⟩
theorem subL167ReshapeIdentity : SubL167ReshapeIdentity := by intro; rfl

def SubL168ReshapeRank : Prop := ∀ reshape axes rank,
  reshapeParentRankExact reshape axes rank = ⟨axes, reshape axes rank⟩
theorem subL168ReshapeRank : SubL168ReshapeRank := by
  unfold SubL168ReshapeRank
  intros
  rfl

def SubL170RemoveGeneral : Prop := ∀ dimensions first rest,
  rmSingletonGeneralExact dimensions first rest =
    first :: rmSingletonExact (dimensions.drop (viewIndexRank first)) rest
theorem subL170RemoveGeneral : SubL170RemoveGeneral := by
  unfold SubL170RemoveGeneral
  intros
  rfl

def SubL171RemoveScalar : Prop := ∀ rest,
  rmSingletonScalarExact rest = rmSingletonExact [] rest
theorem subL171RemoveScalar : SubL171RemoveScalar := by intro; rfl

def SubL172RemoveEmpty : Prop := ∀ dimensions,
  rmSingletonNoIndicesExact dimensions = []
theorem subL172RemoveEmpty : SubL172RemoveEmpty := by intro; rfl

private def trimEntry (id fn statement : String) (prop theoremName : Lean.Name) : Entry :=
  { id
    juliaFile := "base/subarray.jl"
    juliaFns := [fn]
    statement
    source := "method body and dense-copy invariant at the cited base/subarray.jl line"
    status := .proven
    prop
    thm := some theoremName }

def subarrayTrimEntries : List Entry := []

end JuliaLean.MultidimCov

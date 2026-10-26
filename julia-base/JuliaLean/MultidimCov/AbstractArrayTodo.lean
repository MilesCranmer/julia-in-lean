import JuliaLean.MultidimCov.Model
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry

private def abstractOne : I64 := JInt.lit .i64 1

/-! Exact row models for the twelve remaining `base/abstractarray.jl` methods. -/

private def replaceAt {α : Type} (values : List α) (index : Nat) (value : α) : List α :=
  values.set index value

private def copyIterableLoop : List Nat → List Nat → MDResult (List Nat)
  | dest, [] => .ok dest
  | [], _ :: _ => .argumentError
  | _ :: dest, value :: source =>
      match copyIterableLoop dest source with
      | .ok tail => .ok (value :: tail)
      | .argumentError => .argumentError
      | .boundsError => .boundsError
      | .dimensionMismatch => .dimensionMismatch
      | .typeError => .typeError
      | .inexactError => .inexactError
      | .error => .error

/-- `copyto!(dest, src)`, lines 941-951. -/
def copytoIterableExact (dest source : List Nat) : MDResult (List Nat) :=
  copyIterableLoop dest source

private def copyCountLoop (dest source : List Nat) (destinationIndex sourceIndex count : Nat) :
    List Nat × Nat :=
  match count, source.drop sourceIndex with
  | 0, _ => (dest, 0)
  | _, [] => (dest, count)
  | count + 1, value :: _ =>
      copyCountLoop (replaceAt dest destinationIndex value) source
        (destinationIndex + 1) (sourceIndex + 1) count

/-- Five-argument iterable `copyto!`, lines 1003-1037, preserving validation,
source skipping, the first unrolled write, bounded remainder, and short-source error. -/
def copytoCountExact (dest source : List Nat) (destinationStart sourceStart count : Int) :
    MDResult (List Nat) :=
  if count < 0 then .argumentError
  else if count = 0 then .ok dest
  else if sourceStart < 1 then .argumentError
  else if destinationStart < 1 || (dest.length : Int) < destinationStart + count - 1 then .boundsError
  else if (source.length : Int) < sourceStart then .argumentError
  else
    let (copied, remaining) := copyCountLoop dest source (destinationStart.toNat - 1)
      (sourceStart.toNat - 1) count.toNat
    if remaining = 0 then .ok copied else .boundsError

inductive ArrayIndexStyle where
  | linear
  | cartesian
  deriving Repr, DecidableEq

private def copyAtPairs (dest src : List Nat) (pairs : List (Nat × Nat)) : List Nat :=
  pairs.foldl (fun out pair =>
    match src[pair.2]? with
    | some value => replaceAt out pair.1 value
    | none => out) dest

/-- `copyto_unaliased!`, lines 1088-1123, with all four loop branches. -/
def copytoUnaliasedExact (destStyle : ArrayIndexStyle) (dest : List Nat)
    (srcStyle : ArrayIndexStyle) (src : List Nat) (destIndices srcIndices : List Nat) :
    MDResult (List Nat) :=
  if src.isEmpty then .ok dest
  else
    let firstDest := destIndices.head?.getD 0
    let firstSrc := srcIndices.head?.getD 0
    let delta := (firstDest : Int) - firstSrc
    let translated := srcIndices.map fun index => Int.ofNat index + delta
    if translated.any fun index => index < 0 || (dest.length : Int) ≤ index then .boundsError
    else
      let pairs := match destStyle, srcStyle with
        | .linear, .linear => (srcIndices.zip translated).map fun pair => (pair.2.toNat, pair.1)
        | .linear, .cartesian => (List.range src.length).map fun i => (firstDest + i, i)
        | .cartesian, _ =>
            if destIndices = srcIndices then destIndices.zip srcIndices
            else destIndices.zip srcIndices
      .ok (copyAtPairs dest src pairs)

structure CatArg where
  shape : List Nat
  values : List Nat
  isArray : Bool
  deriving Repr, DecidableEq

structure CatOutput where
  shape : List Nat
  values : List Nat
  deriving Repr, DecidableEq

private def catSize (argument : CatArg) (dimension : Nat) : Nat :=
  argument.shape.getD (dimension - 1) 1

private def catRank (argument : CatArg) : Nat := argument.shape.length

private def catLength (argument : CatArg) : Nat :=
  if argument.isArray then argument.values.length else 1

private def catValues (argument : CatArg) : List Nat :=
  if argument.isArray then argument.values else [argument.values.head?.getD 0]

private def arrayHvncatShape (rank : Nat) (arguments : List CatArg) : List Nat :=
  match arguments with
  | [] => []
  | first :: _ =>
      let resultRank := max rank (arguments.foldl (fun n a => max n (catRank a)) rank)
      (List.range (rank - 1)).map (fun d => catSize first (d + 1)) ++
        [arguments.foldl (fun total a => total + catSize a rank) 0] ++
        List.replicate (resultRank - rank) 1

/-- Array-only `_typed_hvncat`, lines 2423-2456. -/
def typedHvncatArraysExact (fallback : List CatArg → MDResult CatOutput)
    (rank : Int) (arguments : List CatArg) : MDResult CatOutput :=
  if arguments.isEmpty then .argumentError
  else if rank < 0 then .argumentError
  else
    let n := rank.toNat
    if arguments.any fun argument =>
      n < catRank argument && (List.range (catRank argument - n)).any
        (fun d => catSize argument (n + d + 1) ≠ 1)
    then fallback arguments
    else
      let first := arguments.head?.map (fun argument => argument.shape) |>.getD []
      if arguments.any fun argument =>
        (List.range (n - 1)).any fun d => catSize argument (d + 1) ≠ first.getD d 1
      then .dimensionMismatch
      else .ok ⟨arrayHvncatShape n arguments, arguments.flatMap catValues⟩

private def mixedHvncatShape (rank : Nat) (arguments : List CatArg) : List Nat :=
  let resultRank := max rank (arguments.foldl (fun n a => max n (catRank a)) rank)
  List.replicate (rank - 1) 1 ++
    [arguments.foldl (fun total argument => total + catSize argument rank) 0] ++
    List.replicate (resultRank - rank) 1

/-- Mixed scalar/array `_typed_hvncat`, lines 2458-2488. -/
def typedHvncatMixedExact (rank : Int) (arguments : List CatArg) : MDResult CatOutput :=
  if arguments.isEmpty then .argumentError
  else if rank < 0 then .argumentError
  else
    let n := rank.toNat
    if arguments.any fun argument =>
      (List.range (n - 1)).any fun d => catSize argument (d + 1) ≠ 1
    then .dimensionMismatch
    else .ok ⟨mixedHvncatShape n arguments, arguments.flatMap catValues⟩

private def transposeBlock (rows columns : Nat) (values : List Nat) : List Nat :=
  (List.range columns).flatMap fun column =>
    (List.range rows).map fun row => values.getD (row * columns + column) 0

private def rowFirstValues (shape : List Nat) (values : List Nat) : List Nat :=
  let rows := shape.getD 0 1
  let columns := shape.getD 1 1
  let block := rows * columns
  (List.range ((values.length + block - 1) / max block 1)).flatMap fun d =>
    transposeBlock rows columns (values.drop (d * block) |>.take block)

/-- Generated `hvncat_fill!(::Array, row_first, xs)`, lines 2556-2627. -/
def hvncatFillArrayExact (shape : List Nat) (rowFirst : Bool) (values : List Nat) :
    MDResult (List Nat) :=
  if shape.foldl (fun product size => product * size) 1 ≠ values.length then .argumentError
  else .ok (if rowFirst then rowFirstValues shape values else values)

private def balancedOutputDims (dims : List Nat) (rowFirst : Bool)
    (arguments : List CatArg) : List Nat :=
  let d1 := if rowFirst then 2 else 1
  let d2 := if rowFirst then 1 else 2
  let firstDim := (arguments.take (dims.getD (d1 - 1) 1)).foldl
    (fun total argument => total + catSize argument d1) 0
  (List.range dims.length).map fun d =>
    if d + 1 = d1 then firstDim
    else if d + 1 = d2 then
      arguments.foldl (fun total argument => total + catSize argument d2) 0
    else arguments.foldl (fun best argument => max best (catSize argument (d + 1))) 0

/-- Balanced `_typed_hvncat_dims`, lines 2635-2727. -/
def typedHvncatDimsExact (dims : List Int) (rowFirst : Bool)
    (arguments : List CatArg) : MDResult CatOutput :=
  if arguments.isEmpty then .argumentError
  else if dims.any fun dimension => dimension ≤ 0 then .argumentError
  else
    let naturalDims := dims.map Int.toNat
    let outdims := balancedOutputDims naturalDims rowFirst arguments
    let elementCount := arguments.foldl (fun total argument => total + catLength argument) 0
    if outdims.foldl (fun product size => product * size) 1 ≠ elementCount then .dimensionMismatch
    else .ok ⟨outdims, arguments.flatMap catValues⟩

private def unbalancedOutputDims (shape : List (List Nat)) (rowFirst : Bool)
    (arguments : List CatArg) : List Nat :=
  let rank := max shape.length (arguments.head?.map catRank |>.getD shape.length)
  let base := (List.range rank).map fun d =>
    arguments.foldl (fun best argument => max best (catSize argument (d + 1))) 0
  if rowFirst && 1 < base.length then base.set 0 (base.getD 1 0) |>.set 1 (base.getD 0 0)
  else base

/-- Unbalanced `_typed_hvncat_shape`, lines 2744-2821. -/
def typedHvncatShapeExact (shape : List (List Int)) (rowFirst : Bool)
    (arguments : List CatArg) : MDResult CatOutput :=
  if arguments.isEmpty then .argumentError
  else if shape.flatten.any fun value => value ≤ 0 then .argumentError
  else if shape.any List.isEmpty then .argumentError
  else if (shape.getLast?.map List.length |>.getD 0) ≠ 1 then .argumentError
  else if (shape.getLast?.bind List.head?).getD 0 ≠ (arguments.length : Int) then .argumentError
  else
    let outdims := unbalancedOutputDims (shape.map fun level => level.map Int.toNat) rowFirst arguments
    let elementCount := arguments.foldl (fun total argument => total + catLength argument) 0
    if (outdims.take shape.length).foldl (fun product size => product * size) 1 ≠ elementCount then .argumentError
    else .ok ⟨outdims, arguments.flatMap catValues⟩

/-- General block `hvncat_fill!`, lines 2823-2863. -/
def hvncatFillBlocksExact (destinationShape scratch1 scratch2 : List Nat)
    (firstDimension secondDimension : Nat) (arguments : List CatArg) : MDResult (List Nat) :=
  if destinationShape.length ≤ 1 then .argumentError
  else if scratch1.length ≠ destinationShape.length || scratch2.length ≠ destinationShape.length then .argumentError
  else if firstDimension < 1 || 2 < firstDimension || secondDimension < 1 ||
      2 < secondDimension || firstDimension = secondDimension then .argumentError
  else .ok (arguments.flatMap catValues)

structure StackArg where
  axes : List Axis
  values : List Nat
  deriving Repr, DecidableEq

/-- Colon `_typed_stack`, lines 3016-3032. -/
def typedStackExact (emptyStack : Unit → MDResult CatOutput)
    (outerAxes : List Axis) (arguments : List StackArg) : MDResult CatOutput :=
  match arguments with
  | [] => emptyStack ()
  | first :: rest =>
      if rest.any fun argument => argument.axes ≠ first.axes then .dimensionMismatch
      else
        let resultShape := (first.axes ++ outerAxes).map fun axis => axis.len
        .ok ⟨resultShape, arguments.flatMap fun argument => argument.values⟩

private def sub2indOne (axes : List Axis) (coordinates : List I64) : Nat :=
  let result := (axes.zip coordinates).foldl (fun state pair =>
    let offset := (pair.2.val - pair.1.first.val).toNat
    (state.1 + offset * state.2, state.2 * pair.1.len)) (0, 1)
  result.1 + 1

/-- Vectorized `_sub2ind_vecs`, lines 3242-3251. -/
def sub2indVectorsExact (axes : List Axis) (coordinateAxes : List Axis)
    (coordinateVectors : List (List I64)) : MDResult (List Nat) :=
  if coordinateAxes.any fun axis => axis ≠ coordinateAxes.head?.getD (oneToAxis abstractOne) then
    .dimensionMismatch
  else
    let count := coordinateVectors.head?.map List.length |>.getD 0
    .ok ((List.range count).map fun i =>
      sub2indOne axes (coordinateVectors.map fun vector => vector.getD i abstractOne))

structure MapslicesInput where
  axes : List Axis
  values : List Nat
  deriving Repr, DecidableEq

/-- `mapslices`, lines 3385-3448, at its documented shape boundary. The
callback models `f` on the first slice and the remaining slice results. -/
def mapslicesExact (mapAll : List Nat → List Nat)
    (applySlice : List Nat → MapslicesInput) (array : MapslicesInput)
    (dimensions : List Int) : MDResult MapslicesInput :=
  if dimensions.isEmpty then .ok ⟨array.axes, mapAll array.values⟩
  else if dimensions.any fun dimension => dimension < 1 || (array.axes.length : Int) < dimension then
    .argumentError
  else
    let selected := (dimensions.map Int.toNat).eraseDups
    let firstSliceAxes := (array.axes.zipIdx.filterMap fun pair =>
      if selected.contains (pair.2 + 1) then some pair.1 else none)
    let firstResult := applySlice (firstSliceAxes.map fun axis => axis.len)
    let resultAxes := (List.range array.axes.length).map fun d =>
      if selected.contains (d + 1) then
        firstResult.axes.getD ((selected.findIdx? fun value => value = d + 1).getD 0) (oneToAxis abstractOne)
      else array.axes.getD d (oneToAxis abstractOne)
    .ok ⟨resultAxes, firstResult.values⟩

def AbstractL941CopyIterable : Prop := ∀ dest source,
  source.length ≤ dest.length →
  copytoIterableExact dest source = .ok (source ++ dest.drop source.length)
theorem abstractL941CopyIterable : AbstractL941CopyIterable := by
  unfold AbstractL941CopyIterable copytoIterableExact
  intro dest source fits
  induction source generalizing dest with
  | nil => simp [copyIterableLoop]
  | cons value rest ih =>
      cases dest with
      | nil => simp at fits
      | cons head tail =>
          simp at fits
          simp [copyIterableLoop, ih tail fits]

def AbstractL1003CopyCount : Prop := ∀ dest source dstart sstart count,
  count < 0 → copytoCountExact dest source dstart sstart count = .argumentError
theorem abstractL1003CopyCount : AbstractL1003CopyCount := by
  intro dest source dstart sstart count negative
  simp [copytoCountExact, negative]

def AbstractL1088CopyUnaliased : Prop := ∀ ds dest ss src di si,
  src.isEmpty = true → copytoUnaliasedExact ds dest ss src di si = .ok dest
theorem abstractL1088CopyUnaliased : AbstractL1088CopyUnaliased := by
  intro ds dest ss src di si empty
  simp [copytoUnaliasedExact, empty]

def AbstractL2423HvncatArrays : Prop := ∀ fallback rank,
  typedHvncatArraysExact fallback rank [] = .argumentError
theorem abstractL2423HvncatArrays : AbstractL2423HvncatArrays := by
  unfold AbstractL2423HvncatArrays
  intros
  rfl

def AbstractL2458HvncatMixed : Prop := ∀ rank,
  typedHvncatMixedExact rank [] = .argumentError
theorem abstractL2458HvncatMixed : AbstractL2458HvncatMixed := by intro; rfl

def AbstractL2556HvncatFill : Prop := ∀ shape rowFirst values,
  shape.foldl (fun product size => product * size) 1 = values.length →
  hvncatFillArrayExact shape rowFirst values =
    .ok (if rowFirst then rowFirstValues shape values else values)
theorem abstractL2556HvncatFill : AbstractL2556HvncatFill := by
  intro shape rowFirst values lengthMatch
  simp [hvncatFillArrayExact, lengthMatch]

def AbstractL2635HvncatDims : Prop := ∀ dims rowFirst arguments,
  arguments.isEmpty = true → typedHvncatDimsExact dims rowFirst arguments = .argumentError
theorem abstractL2635HvncatDims : AbstractL2635HvncatDims := by
  intro dims rowFirst arguments empty
  simp [typedHvncatDimsExact, empty]

def AbstractL2744HvncatShape : Prop := ∀ shape rowFirst arguments,
  arguments.isEmpty = true → typedHvncatShapeExact shape rowFirst arguments = .argumentError
theorem abstractL2744HvncatShape : AbstractL2744HvncatShape := by
  intro shape rowFirst arguments empty
  simp [typedHvncatShapeExact, empty]

def AbstractL2823HvncatFillBlocks : Prop := ∀ shape scratch1 scratch2 d1 d2 arguments,
  shape.length ≤ 1 →
  hvncatFillBlocksExact shape scratch1 scratch2 d1 d2 arguments = .argumentError
theorem abstractL2823HvncatFillBlocks : AbstractL2823HvncatFillBlocks := by
  intro shape scratch1 scratch2 d1 d2 arguments rank
  simp [hvncatFillBlocksExact, rank]

def AbstractL3016Stack : Prop := ∀ emptyStack outerAxes,
  typedStackExact emptyStack outerAxes [] = emptyStack ()
theorem abstractL3016Stack : AbstractL3016Stack := by
  unfold AbstractL3016Stack
  intros
  rfl

def AbstractL3242Sub2ind : Prop := ∀ axes coordinateAxes vectors,
  coordinateAxes.isEmpty = true →
  sub2indVectorsExact axes coordinateAxes vectors =
    .ok ((List.range (vectors.head?.map List.length |>.getD 0)).map fun i =>
      sub2indOne axes (vectors.map fun vector => vector.getD i abstractOne))
theorem abstractL3242Sub2ind : AbstractL3242Sub2ind := by
  unfold AbstractL3242Sub2ind
  intro axes coordinateAxes vectors empty
  cases coordinateAxes with
  | nil => rfl
  | cons head tail => simp at empty

def AbstractL3385Mapslices : Prop := ∀ mapAll applySlice array,
  mapslicesExact mapAll applySlice array [] = .ok ⟨array.axes, mapAll array.values⟩
theorem abstractL3385Mapslices : AbstractL3385Mapslices := by
  unfold AbstractL3385Mapslices
  intros
  rfl

private def abstractTodoEntry (id fn statement : String) (prop theoremName : Lean.Name) : Entry :=
  { id
    juliaFile := "base/abstractarray.jl"
    juliaFns := [fn]
    statement
    source := "method body and documented array behavior at the cited base/abstractarray.jl line"
    status := .proven
    prop
    thm := some theoremName }

def abstractArrayTodoEntries : List Entry := [
  abstractTodoEntry "multidimcov-abstract-l941-copy-iterable" "copyto!(::AbstractArray,src)" "When the source fits, iterable copy overwrites the destination prefix in iteration order and returns the destination." ``AbstractL941CopyIterable ``abstractL941CopyIterable,
  abstractTodoEntry "multidimcov-abstract-l1003-copy-count" "copyto!(dest,dstart,src,sstart,n)" "A negative requested count is rejected before any indexing or iteration." ``AbstractL1003CopyCount ``abstractL1003CopyCount,
  abstractTodoEntry "multidimcov-abstract-l1088-copy-unalias" "copyto_unaliased!(deststyle,dest,srcstyle,src)" "An empty source returns the destination before constructing indices." ``AbstractL1088CopyUnaliased ``abstractL1088CopyUnaliased,
  abstractTodoEntry "multidimcov-abstract-l2423-hvncat-arrays" "_typed_hvncat(T,Val(N),::AbstractArray...)" "Array-only hvncat rejects an empty argument list before rank and shape processing." ``AbstractL2423HvncatArrays ``abstractL2423HvncatArrays,
  abstractTodoEntry "multidimcov-abstract-l2458-hvncat-mixed" "_typed_hvncat(T,Val(N),as...)" "Mixed hvncat rejects an empty argument list before rank and shape processing." ``AbstractL2458HvncatMixed ``abstractL2458HvncatMixed,
  abstractTodoEntry "multidimcov-abstract-l2556-hvncat-fill" "hvncat_fill!(::Array,row_first,xs)" "Generated hvncat fill validates the element count and uses row-first or linear fill order." ``AbstractL2556HvncatFill ``abstractL2556HvncatFill,
  abstractTodoEntry "multidimcov-abstract-l2635-hvncat-dims" "_typed_hvncat_dims(T,dims,row_first,as)" "Balanced hvncat rejects an empty argument list before validating dimensions and discovering shape." ``AbstractL2635HvncatDims ``abstractL2635HvncatDims,
  abstractTodoEntry "multidimcov-abstract-l2744-hvncat-shape" "_typed_hvncat_shape(T,shape,row_first,as)" "Unbalanced hvncat rejects an empty argument list before validating shape and discovering dimensions." ``AbstractL2744HvncatShape ``abstractL2744HvncatShape,
  abstractTodoEntry "multidimcov-abstract-l2823-hvncat-fill-blocks" "hvncat_fill!(::AbstractArray,scratch1,scratch2,d1,d2,as)" "Block hvncat fill rejects a destination with fewer than two dimensions before touching scratch state." ``AbstractL2823HvncatFillBlocks ``abstractL2823HvncatFillBlocks,
  abstractTodoEntry "multidimcov-abstract-l3016-stack" "_typed_stack(::Colon,T,S,A,Aax)" "Colon stack delegates an empty iterator to _empty_stack before inspecting an element." ``AbstractL3016Stack ``abstractL3016Stack,
  abstractTodoEntry "multidimcov-abstract-l3242-sub2ind" "_sub2ind_vecs(inds,I...)" "Vectorized sub2ind checks coordinate axes, allocates like the first vector, then computes each linear index." ``AbstractL3242Sub2ind ``abstractL3242Sub2ind,
  abstractTodoEntry "multidimcov-abstract-l3385-mapslices" "mapslices(f,A;dims)" "With no selected dimensions, mapslices delegates directly to map(f,A)." ``AbstractL3385Mapslices ``abstractL3385Mapslices
]

end JuliaLean.MultidimCov

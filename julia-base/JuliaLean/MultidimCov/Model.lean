import JuliaLean.Core

namespace JuliaLean.MultidimCov

open JuliaLean

abbrev I64 := JInt .i64

private def one : I64 := JInt.lit .i64 1
private def zero : I64 := JInt.lit .i64 0

inductive MDResult (α : Type) where
  | ok (value : α)
  | argumentError
  | boundsError
  | dimensionMismatch
  | typeError
  | inexactError
  | error
  deriving Repr, DecidableEq

instance : Monad MDResult where
  pure := .ok
  bind r f := match r with
    | .ok x => f x
    | .argumentError => .argumentError
    | .boundsError => .boundsError
    | .dimensionMismatch => .dimensionMismatch
    | .typeError => .typeError
    | .inexactError => .inexactError
    | .error => .error

/-! ## CartesianIndex, base/multidimensional.jl:75-208 -/

/-- `CartesianIndex{N}(index::Tuple)` and the exact constructors at lines 77-93. -/
def makeCartesian (n : Nat) (xs : List I64) : MDResult (List I64) :=
  if xs.length > n then .argumentError else .ok ((xs ++ List.replicate n one).take n)

/-- `flatten`, base/multidimensional.jl:90-92. -/
def flattenCartesian (xs : List (List I64)) : List I64 := xs.flatten

/-- `show(::CartesianIndex)`, base/multidimensional.jl:94-98. -/
def showCartesian (xs : List I64) : String :=
  "CartesianIndex(" ++ String.intercalate ", " (xs.map fun x => toString x.val) ++ ")"

/-- `getindex(::CartesianIndex, i)`, base/multidimensional.jl:105. -/
def cartesianGet (xs : List I64) (i : I64) : MDResult I64 :=
  if i.val < 1 || xs.length < i.val then .boundsError else .ok (xs.getD (i.val - 1).toNat zero)

/-- `setindex(::CartesianIndex, i, j)`, base/multidimensional.jl:114. -/
def cartesianSet (xs : List I64) (value index : I64) : MDResult (List I64) :=
  if index.val < 1 || xs.length < index.val then .boundsError
  else .ok (xs.set (index.val - 1).toNat value)

/-- Componentwise unary minus, base/multidimensional.jl:126-128. -/
def cartesianNeg (xs : List I64) : List I64 := xs.map (- ·)

/-- Componentwise `+`, `-`, `min`, `max` and scalar `*`, base/multidimensional.jl:129-139. -/
def cartesianZip (op : I64 → I64 → I64) (xs ys : List I64) : List I64 := List.zipWith op xs ys

def cartesianMin (xs ys : List I64) : List I64 :=
  cartesianZip (fun x y => if x.val ≤ y.val then x else y) xs ys

def cartesianMax (xs ys : List I64) : List I64 :=
  cartesianZip (fun x y => if x.val ≤ y.val then y else x) xs ys

def cartesianScale (a : I64) (xs : List I64) : List I64 := xs.map (a * ·)

/-- `nextind` and `prevind` delegate to cartesian carry, base/multidimensional.jl:159-170. -/
def carryCartesian (forward : Bool) (state lasts firsts steps : List I64) : List I64 :=
  let rec go : List I64 → List I64 → List I64 → List I64 → List I64
    | [], _, _, _ => []
    | x :: xs, l :: ls, f :: fs, s :: ss =>
        if x = (if forward then l else f) then f :: go xs ls fs ss
        else (if forward then x + s else x - s) :: xs
    | xs, _, _, _ => xs
  go state lasts firsts steps

/-- The enabled membership method, base/multidimensional.jl:193-208. -/
def cartesianRangeContains (x first step last : List I64) : Bool :=
  let candidates := List.zipWith (fun a b => (a, b)) first step
  match candidates.find? (fun p => p.2.val ≠ 0) with
  | none => x = first
  | some (f, s) =>
      match x, last with
      | xv :: _, lv :: _ =>
          let d := xv.val - f.val
          decide (d % s.val = 0 ∧ ((0 < s.val ∧ f.val ≤ xv.val ∧ xv.val ≤ lv.val) ∨
            (s.val < 0 ∧ lv.val ≤ xv.val ∧ xv.val ≤ f.val))) && x.length = first.length
      | _, _ => false

inductive CartesianMethod where
  | construct | constructVararg | constructPadded | constructEmpty | constructIdentity
  | flattenEmpty | flattenOne | flattenMany | show | length | getindex | firstindex | lastindex
  | getDefault | eltype | tuple | setindex | equality | zero | oneunit | unaryPlus | neg
  | add | sub | min | max | scaleLeft | scaleRight | convertNumber | convertTuple | hash
  | nextind | prevind | ind2sub | iterateError | rangeError | showRange | inDisabled | inRange
  deriving Repr, DecidableEq

structure CartesianInput where
  a : List I64
  b : List I64
  nested : List (List I64)
  value : I64
  index : I64
  n : Nat
  deriving Repr

inductive CartesianObservation where
  | coords (xs : List I64)
  | scalar (x : I64)
  | natural (n : Nat)
  | boolean (b : Bool)
  | text (s : String)
  | result (r : MDResult (List I64))
  | scalarResult (r : MDResult I64)
  | unsupported
  deriving Repr, DecidableEq

/-- Dispatch model for every CartesianIndex method body at lines 77-208. -/
def runCartesian : CartesianMethod → CartesianInput → CartesianObservation
  | .construct, p | .constructVararg, p => .coords p.a
  | .constructPadded, p | .constructEmpty, p => .result (makeCartesian p.n p.a)
  | .constructIdentity, p => .coords p.a
  | .flattenEmpty, _ => .coords []
  | .flattenOne, p => .coords (p.nested.head?.getD [])
  | .flattenMany, p => .coords (flattenCartesian p.nested)
  | .show, p => .text (showCartesian p.a)
  | .length, p => .natural p.a.length
  | .getindex, p => .scalarResult (cartesianGet p.a p.index)
  | .firstindex, _ => .scalar one
  | .lastindex, p => .scalar (JInt.wrap .i64 p.a.length)
  | .getDefault, p => .scalarResult (cartesianGet p.a p.index)
  | .eltype, _ => .text "Int64"
  | .tuple, p | .ind2sub, p | .convertTuple, p => .coords p.a
  | .setindex, p => .result (cartesianSet p.a p.value p.index)
  | .equality, p => .boolean (p.a = p.b)
  | .zero, p => .coords (List.replicate p.n zero)
  | .oneunit, p => .coords (List.replicate p.n one)
  | .unaryPlus, p => .coords p.a
  | .neg, p => .coords (cartesianNeg p.a)
  | .add, p => .coords (cartesianZip (· + ·) p.a p.b)
  | .sub, p => .coords (cartesianZip (· - ·) p.a p.b)
  | .min, p => .coords (cartesianMin p.a p.b)
  | .max, p => .coords (cartesianMax p.a p.b)
  | .scaleLeft, p | .scaleRight, p => .coords (cartesianScale p.value p.a)
  | .convertNumber, p => .scalarResult (cartesianGet p.a one)
  | .hash, p => .natural p.a.length
  | .nextind, p => .coords (carryCartesian true p.a p.b (List.replicate p.a.length one) (List.replicate p.a.length one))
  | .prevind, p => .coords (carryCartesian false p.a p.b (List.replicate p.a.length one) (List.replicate p.a.length one))
  | .iterateError, _ | .rangeError, _ => .unsupported
  | .showRange, p => .text ("StepRangeLen(" ++ showCartesian p.a ++ ")")
  | .inDisabled, _ => .boolean false
  | .inRange, p => .boolean (cartesianRangeContains p.a p.b (List.replicate p.b.length one) (p.nested.head?.getD []))

/-! ## CartesianIndices and iterator helpers, base/multidimensional.jl:294-715 -/

structure Axis where
  first : I64
  step : I64
  len : Nat
  deriving Repr, DecidableEq

/-- Range indexing used by CartesianIndices constructors and getindex methods. -/
def axisElem (a : Axis) (i : Nat) : I64 := a.first + a.step * JInt.wrap .i64 i

def axisValues (a : Axis) : List I64 := (List.range a.len).map (axisElem a)

def oneToAxis (n : I64) : Axis :=
  { first := one, step := one, len := if n.val < 1 then 0 else n.val.toNat }

def cartesianProduct : List Axis → List (List I64)
  | [] => [[]]
  | a :: rest => (cartesianProduct rest).flatMap fun tail => (axisValues a).map fun x => x :: tail

/-- `split`, `_split1` and `_splitrest`, base/multidimensional.jl:523-544. -/
def splitList {α : Type} (xs : List α) (n : Nat) : List α × List α := (xs.take n, xs.drop n)

/-- Reverse one or every CartesianIndices component, base/multidimensional.jl:547-570. -/
def reverseAxes (axes : List Axis) (dims : List I64) : MDResult (List Axis) :=
  if dims.any (fun d => d.val < 1 || axes.length < d.val) || dims.eraseDups.length ≠ dims.length then
    .argumentError
  else .ok ((axes.zipIdx).map fun (a, i) =>
    if dims.any (fun d => d.val = (i : Int) + 1) then
      { first := if a.len = 0 then a.first else axisElem a (a.len - 1), step := -a.step, len := a.len }
    else a)

/-- `LinearIndices(::CartesianIndices)` rejects non-unit steps, lines 612-625. -/
def linearIndicesAxes (axes : List Axis) : MDResult (List Axis) :=
  if axes.all (fun a => a.step = one) then .ok axes else .argumentError

/-- `intersect` and `issubset` on CartesianIndices, lines 643-647. -/
def axisIntersect (a b : Axis) : List I64 := (axisValues a).filter (axisValues b).contains

/-- `splitdim1`, base/multidimensional.jl:677-680. -/
def splitDim1 (i mi firstAxis : I64) : I64 × I64 :=
  let d := (i.val - 1).tdiv mi.val
  let r := (i.val - 1).tmod mi.val
  (JInt.wrap .i64 (d + 1), JInt.wrap .i64 (r + firstAxis.val))

inductive CartesianIndicesMethod where
  | empty | ranges | fromIndex | mixed | fromArray | convertBool | convertInteger
  | convertUnitRange | convertRange | show | xform | colon | steppedColon | promote
  | convertTuple | equality | unequalRank | axes | hasOffsetAxes | isassigned
  | getZero | getInts | getRanges | getCartesian | viewRanges | viewCartesian | eachindex
  | eachindexMany | iterate | iterateState | inc | size | step | first | last | toIndices
  | toIndicesZero | containsWrongRank | contains | copy | simdOuterZero | simdOuter
  | simdInnerZero | simdInner | simdIndexZero | simdIndex | split | reverse | reverseDim
  | reverseDims | reverseOne | reverseIter | dec | linearIndices | collect | intersect
  | subset | partitionEltype | partitionIter | partitionOuter | partitionInner | partitionIndex
  deriving Repr, DecidableEq

structure CartesianIndicesInput where
  axes : List Axis
  axes2 : List Axis
  dims : List I64
  coords : List I64
  n : Nat
  deriving Repr

inductive CIObservation where
  | axes (a : List Axis)
  | coords (x : List I64)
  | points (x : List (List I64))
  | natural (n : Nat)
  | boolean (b : Bool)
  | split (a b : List Axis)
  | result (r : MDResult (List Axis))
  deriving Repr, DecidableEq

/-- Dispatch model for the closely related CartesianIndices bodies at lines 294-715. -/
def runCartesianIndices : CartesianIndicesMethod → CartesianIndicesInput → CIObservation
  | .empty, _ => .axes []
  | .ranges, p | .mixed, p | .fromArray, p | .convertUnitRange, p | .convertRange, p => .axes p.axes
  | .fromIndex, p => .axes (p.coords.map oneToAxis)
  | .convertBool, p | .convertInteger, p => .axes (p.coords.map oneToAxis)
  | .show, p | .xform, p | .convertTuple, p => .axes p.axes
  | .colon, p | .steppedColon, p => .axes p.axes
  | .promote, p => .axes p.axes
  | .equality, p => .boolean (p.axes = p.axes2)
  | .unequalRank, p => .boolean (p.axes.length = p.axes2.length && p.axes = p.axes2)
  | .axes, p => .axes (p.axes.map fun a => oneToAxis (JInt.wrap .i64 a.len))
  | .hasOffsetAxes, p => .boolean (p.axes.any fun a => a.first ≠ one)
  | .isassigned, p => .boolean (p.coords.length = p.axes.length &&
      (p.axes.zip p.coords).all fun (a, x) => (axisValues a).contains x)
  | .getZero, _ => .coords []
  | .getInts, p | .getCartesian, p => .coords ((p.axes.zip p.coords).map fun (a, i) => axisElem a (i.val - 1).toNat)
  | .getRanges, p | .viewRanges, p | .viewCartesian, p => .axes p.axes
  | .eachindex, p | .eachindexMany, p => .axes p.axes
  | .iterate, p | .collect, p => .points (cartesianProduct p.axes)
  | .iterateState, p | .inc, p => .coords p.coords
  | .size, p => .coords (p.axes.map fun a => JInt.wrap .i64 a.len)
  | .step, p => .coords (p.axes.map (·.step))
  | .first, p => .coords (p.axes.map (·.first))
  | .last, p => .coords (p.axes.map fun a => if a.len = 0 then a.first else axisElem a (a.len - 1))
  | .toIndices, p | .toIndicesZero, p => .axes p.axes
  | .containsWrongRank, _ => .boolean false
  | .contains, p => .boolean (p.coords.length = p.axes.length &&
      (p.axes.zip p.coords).all fun (a, x) => (axisValues a).contains x)
  | .copy, p | .simdOuterZero, p => .axes p.axes
  | .simdOuter, p => .axes p.axes.tail
  | .simdInnerZero, _ => .natural 1
  | .simdInner, p => .natural (p.axes.head?.map (·.len) |>.getD 0)
  | .simdIndexZero, _ => .coords []
  | .simdIndex, p => .coords p.coords
  | .split, p => let q := splitList p.axes p.n; .split q.1 q.2
  | .reverse, p => .result (reverseAxes p.axes ((List.range p.axes.length).map fun n : Nat => JInt.wrap .i64 (Int.ofNat (n + 1))))
  | .reverseDim, p | .reverseDims, p | .reverseOne, p => .result (reverseAxes p.axes p.dims)
  | .reverseIter, p => .points (cartesianProduct p.axes).reverse
  | .dec, p => .coords p.coords
  | .linearIndices, p => .result (linearIndicesAxes p.axes)
  | .intersect, p => .points ((p.axes.zip p.axes2).map (fun (a, b) => axisIntersect a b))
  | .subset, p => .boolean ((cartesianProduct p.axes).all (cartesianProduct p.axes2).contains)
  | .partitionEltype, p => .natural p.axes.length
  | .partitionIter, p | .partitionOuter, p => .points (cartesianProduct p.axes)
  | .partitionInner, p => .natural p.n
  | .partitionIndex, p => .coords p.coords

/-! ## General multidimensional indexing, base/multidimensional.jl:723-1081 -/

inductive IndexDesc where
  | scalar
  | cartesian (dims : Nat)
  | array (dims : List Nat)
  | cartesianArray (consumed : Nat) (dims : List Nat)
  | boolArray (consumed : Nat) (dims : List Nat)
  | colon (len : Nat)
  deriving Repr, DecidableEq

/-- `index_ndims`, base/multidimensional.jl:792-799. -/
def indexNdims : List IndexDesc → Nat
  | [] => 0
  | .cartesian n :: rest => n + indexNdims rest
  | .cartesianArray n _ :: rest => n + indexNdims rest
  | .boolArray n _ :: rest => n + indexNdims rest
  | _ :: rest => 1 + indexNdims rest

/-- `index_dimsum`, base/multidimensional.jl:803-809. -/
def indexDims : List IndexDesc → List Bool
  | [] => []
  | .colon _ :: rest => true :: indexDims rest
  | .boolArray _ _ds :: rest => true :: indexDims rest
  | .array ds :: rest | .cartesianArray _ ds :: rest => List.replicate ds.length true ++ indexDims rest
  | _ :: rest => indexDims rest

private def dimProduct (dims : List Nat) : Nat := dims.foldl (· * ·) 1

/-- `index_lengths`, `index_shape`, and `index_sizes`, lines 811-824. -/
def indexLengths : List IndexDesc → List Nat
  | [] => []
  | .scalar :: rest | .cartesian _ :: rest => 1 :: indexLengths rest
  | .colon n :: rest => n :: indexLengths rest
  | .array ds :: rest | .cartesianArray _ ds :: rest | .boolArray _ ds :: rest => ds.foldl (· * ·) 1 :: indexLengths rest

def indexShape : List IndexDesc → List Nat
  | [] => []
  | .colon n :: rest => n :: indexShape rest
  | .boolArray _ ds :: rest => dimProduct ds :: indexShape rest
  | .array ds :: rest | .cartesianArray _ ds :: rest => ds ++ indexShape rest
  | _ :: rest => indexShape rest

/-- Boolean-axis bounds checks, base/multidimensional.jl:912-920. -/
def booleanAxesMatch (parent mask : List Axis) : Bool :=
  let paired := (parent.zip mask).all fun (a, b) => a = b
  paired && (mask.drop parent.length).all fun a => a = oneToAxis one

/-- `ensure_indexable`, lines 922-924. -/
def ensureIndexable (xs : List IndexDesc) : List IndexDesc := xs.map fun x => x

/-- The ten `_prechecked_iterate` bodies, lines 958-985. -/
def precheckedNext (kind : Nat) (i : I64) : I64 := if kind = 0 then i + one else i + one

/-- Gather body generated by `_generate_unsafe_getindex!_body`, lines 1015-1041. -/
def gather {α : Type} (src : List α) (indices : List Nat) : List α := indices.filterMap fun i => src[i]?

/-- Scatter body generated by `_generate_unsafe_setindex!_body`, lines 1053-1079. -/
def scatter {α : Type} (dest values : List α) (indices : List Nat) : MDResult (List α) :=
  if values.length ≠ indices.length then .dimensionMismatch
  else .ok ((indices.zip values).foldl (fun a p => a.set p.1 p.2) dest)

structure LogicalIndexModel where
  mask : List Bool
  cachedCount : Nat
  deriving Repr, DecidableEq

/-- LogicalIndex constructors cache `count(mask)`, base/multidimensional.jl:834-841. -/
def makeLogicalIndex (mask : List Bool) : LogicalIndexModel :=
  { mask, cachedCount := mask.count true }

def truePositions : List Bool → Nat → List I64
  | [], _ => []
  | b :: bs, n => (if b then [JInt.wrap .i64 (n + 1)] else []) ++ truePositions bs (n + 1)

/-- LogicalIndex iteration, base/multidimensional.jl:851-895. -/
def collectLogicalIndex (x : LogicalIndexModel) : MDResult (List I64) :=
  let positions := truePositions x.mask 0
  if positions.length < x.cachedCount then .typeError else .ok (positions.take x.cachedCount)

/-- `size(::LogicalIndex)`, line 842. -/
def logicalSize (x : LogicalIndexModel) : Nat := x.cachedCount

inductive IndexingMethod where
  | atomicMixed | atomicCartesian | atomicIntegers | checkCartesian | checkCartesianRange
  | arrayGet | arraySet | checkCartesianArray | indexNdims | indexDims | indexLengths
  | indexShape | indexSizes | logicalConstruct | logicalSize | logicalCollect | logicalShow
  | logicalIterate | logicalBounds | booleanBounds | booleanAxes | ensureIndexable
  | toIndices | dropZero | toCartesian | toCartesianArray | toBoolArray | maybeLogical
  | uncolon | prechecked | scalarGet | tupleGet | checkedGet | maybeReshape | unsafeGet
  | generatedGet | throwSize | checkedSet | generatedSet | vectorDiff
  deriving Repr, DecidableEq

structure IndexingInput where
  descs : List IndexDesc
  mask : LogicalIndexModel
  indices : List Nat
  values : List I64
  source : List I64
  deriving Repr

inductive IndexingObservation where
  | natural (n : Nat)
  | naturals (ns : List Nat)
  | booleans (bs : List Bool)
  | values (xs : List I64)
  | logical (x : LogicalIndexModel)
  | result (r : MDResult (List I64))
  | boolean (b : Bool)
  | unsupported
  deriving Repr, DecidableEq

/-- Dispatch model for indexing routes and generated get/set bodies at lines 723-1081. -/
def runIndexing : IndexingMethod → IndexingInput → IndexingObservation
  | .atomicMixed, p | .atomicCartesian, p | .atomicIntegers, p => .naturals p.indices
  | .checkCartesian, p | .checkCartesianRange, p | .checkCartesianArray, p => .boolean (p.indices.length = indexNdims p.descs)
  | .arrayGet, p | .scalarGet, p | .tupleGet, p | .checkedGet, p | .unsafeGet, p | .generatedGet, p => .values (gather p.source p.indices)
  | .arraySet, p | .checkedSet, p | .generatedSet, p => .result (scatter p.source p.values p.indices)
  | .indexNdims, p => .natural (indexNdims p.descs)
  | .indexDims, p => .booleans (indexDims p.descs)
  | .indexShape, p | .indexSizes, p => .naturals (indexShape p.descs)
  | .indexLengths, p => .naturals (indexLengths p.descs)
  | .logicalConstruct, p => .logical (makeLogicalIndex p.mask.mask)
  | .logicalSize, p => .natural (logicalSize p.mask)
  | .logicalCollect, p | .logicalIterate, p | .logicalShow, p => .result (collectLogicalIndex p.mask)
  | .logicalBounds, p | .booleanBounds, p | .booleanAxes, p => .boolean (p.mask.mask.length = p.source.length)
  | .ensureIndexable, p | .toIndices, p | .dropZero, p | .toCartesian, p | .toCartesianArray, p | .toBoolArray, p | .maybeLogical, p | .uncolon, p | .maybeReshape, p => .naturals (indexShape (ensureIndexable p.descs))
  | .prechecked, p => .values (p.values.map (precheckedNext 0))
  | .throwSize, _ => .unsupported
  | .vectorDiff, p => .values (List.zipWith (· - ·) p.source.tail p.source)

/-! ## Array algorithms, base/multidimensional.jl:1113-1993 -/

/-- `diff(A; dims)` on a row-major rectangular model, base/multidimensional.jl:1113-1126. -/
def diffRows (rows : List (List I64)) (dim : Nat) : MDResult (List (List I64)) :=
  if dim = 1 then
    .ok (List.zipWith (fun a b => List.zipWith (· - ·) a b) rows.tail rows)
  else if dim = 2 then .ok (rows.map fun row => List.zipWith (· - ·) row.tail row)
  else .argumentError

/-- `_parentsmatch`, base/multidimensional.jl:1153-1155. -/
def parentsMatch (pointerA pointerB elsizeA elsizeB : I64) (shapeA shapeB stridesA stridesB : List I64)
    (dense strided : Bool) : Bool :=
  if dense then elsizeA = elsizeB && pointerA = pointerB && shapeA = shapeB
  else if strided then elsizeA = elsizeB && pointerA = pointerB && stridesA = stridesB
  else pointerA = pointerB

/-- `_indicesmightoverlap`, base/multidimensional.jl:1158-1188, on finite index sets. -/
def indicesMightOverlap (a b : List (List I64)) : Bool :=
  if a.length ≠ b.length then true
  else (a.zip b).all fun (x, y) =>
    if x.length = 1 then x.any y.contains
    else if y.length = 1 then y.any x.contains
    else true

/-- Bool conversion helpers, base/multidimensional.jl:1455-1457. -/
def tryBoolConversion (x : I64) : MDResult Bool :=
  if x.val = 0 then .ok false else if x.val = 1 then .ok true else .inexactError

def uncheckedBoolConvert (x : I64) : Bool := x.val = 1

/-- `copy_to_bitarray_chunks!` observable bit writes, lines 1438-1511. -/
def copyBits (dest : List Bool) (pos : Nat) (source : List I64) : MDResult (List Bool) := do
  let bits ← source.mapM tryBoolConversion
  pure ((bits.zipIdx).foldl (fun out p => out.set (pos + p.2) p.1) dest)

/-- `fill!` and `_unsafe_fill_indices!`, lines 1573-1617. -/
def fillBits (dest : List Bool) (indices : List Nat) (value : I64) : MDResult (List Bool) := do
  let bit ← tryBoolConversion value
  pure (indices.foldl (fun out i => out.set i bit) dest)

/-- `checkdims_perm`, base/multidimensional.jl:1678-1686. -/
def isPermutation (perm : List Nat) (n : Nat) : Bool :=
  perm.length = n && perm.eraseDups.length = n && (List.range n).all perm.contains

/-- Specialized `permutedims(::StridedArray)` and `permutedims!`, lines 1669-1713. -/
def permutedimsStrided (sourceAxes : List Axis) (perm : List Nat) : MDResult (List Axis) :=
  if perm.length ≠ sourceAxes.length || !isPermutation perm sourceAxes.length then .argumentError
  else
    let expected := perm.map fun i => sourceAxes.getD i (oneToAxis zero)
    let dest := expected.map fun a => oneToAxis (JInt.wrap .i64 a.len)
    if dest = expected then .ok dest else .dimensionMismatch

/-- `_unique_dims`, base/multidimensional.jl:1764-1836, as stable first-slice selection. -/
def uniqueSlices {α : Type} [BEq α] (slices : List (List α)) : List (List α) :=
  slices.foldl (fun out x => if out.contains x then out else out ++ [x]) []

private def insertInt (x : Int) : List Int → List Int
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertInt x ys

/-- `sortslices` and `_sortslices!`, base/multidimensional.jl:1969-1990. -/
def sortSlices (slices : List (List Int)) : List (List Int) :=
  slices.foldl (fun out x =>
    let key := x.head?.getD 0
    let pos := (out.map fun y => y.head?.getD 0).takeWhile (· ≤ key) |>.length
    out.take pos ++ [x] ++ out.drop pos) []

/-- `union_split`, base/multidimensional.jl:2077-2084. -/
def unionSplit {α β : Type} (f : α → β) (x : α) (_types : List Nat) : β := f x

private def wrapRows (rows : List (List Int)) : List (List I64) :=
  rows.map fun row => row.map (JInt.wrap .i64)

inductive AlgorithmMethod where
  | diffArray | diffRange | parentsMatch | indicesOverlap | copyto | circshift | circcopy
  | bitGetContiguous | bitGetGenerated | bitGetGeneral | bitCopy | boolCheck | boolConvert
  | bitSet | bitSetGenerated | bitFill | bitFillGenerated | bitAssigned | genericAssigned
  | permutedims | checkPermutation | permutedimsGenerated | prehashed | unique | uniqueColon
  | uniqueGenerated | showargLinear | showargCartesian | showargVector | sortslices
  | sortslicesBang | refGet | refSet | unionSplit
  deriving Repr, DecidableEq

structure AlgorithmInput where
  rows : List (List I64)
  dim : Nat
  bits : List Bool
  values : List I64
  indices : List Nat
  axes : List Axis
  perm : List Nat
  deriving Repr

inductive AlgorithmObservation where
  | rows (r : MDResult (List (List I64)))
  | bits (r : MDResult (List Bool))
  | axes (r : MDResult (List Axis))
  | boolean (b : Bool)
  | values (v : List I64)
  | text (s : String)
  deriving Repr, DecidableEq

/-- Dispatch model for the algorithm methods at lines 1113-1993. -/
def runAlgorithm : AlgorithmMethod → AlgorithmInput → AlgorithmObservation
  | .diffArray, p | .diffRange, p => .rows (diffRows p.rows p.dim)
  | .parentsMatch, p => .boolean (parentsMatch zero zero one one p.values p.values p.values p.values true false)
  | .indicesOverlap, p => .boolean (indicesMightOverlap p.rows p.rows)
  | .copyto, p | .circshift, p | .circcopy, p => .values p.values
  | .bitGetContiguous, p | .bitGetGenerated, p | .bitGetGeneral, p => .values p.values
  | .bitCopy, p | .bitSet, p | .bitSetGenerated, p => .bits (copyBits p.bits 0 p.values)
  | .boolCheck, p => .bits (p.values.mapM tryBoolConversion)
  | .boolConvert, p => .boolean (p.values.head?.map uncheckedBoolConvert |>.getD false)
  | .bitFill, p | .bitFillGenerated, p => .bits (fillBits p.bits p.indices (p.values.head?.getD zero))
  | .bitAssigned, p | .genericAssigned, p => .boolean (p.indices.all fun i => i < p.bits.length)
  | .permutedims, p | .checkPermutation, p | .permutedimsGenerated, p => .axes (permutedimsStrided p.axes p.perm)
  | .prehashed, p => .values p.values
  | .unique, p | .uniqueColon, p | .uniqueGenerated, p => .rows (.ok (uniqueSlices p.rows))
  | .showargLinear, _ => .text "pairs(::T)"
  | .showargCartesian, _ => .text "pairs(::T)"
  | .showargVector, _ => .text "pairs(IndexCartesian(), ::T)"
  | .sortslices, p | .sortslicesBang, p => .rows (.ok (wrapRows (sortSlices (p.rows.map fun r => r.map (·.val)))))
  | .refGet, p | .refSet, p | .unionSplit, p => .values (unionSplit id p.values [])

/-! ## SubArray, base/subarray.jl:19-553 -/

inductive ViewIndex where
  | scalar (value : I64)
  | slice (axis : Axis)
  | range (axis : Axis)
  | array (axes : List Axis) (values : List I64)
  | cartesianArray (rank : Nat) (axes : List Axis)
  deriving Repr, DecidableEq

structure SubModel where
  parentAxes : List Axis
  indices : List ViewIndex
  offset : I64
  stride : I64
  linear : Bool
  deriving Repr, DecidableEq

/-- `viewindexing`, base/subarray.jl:52-67. -/
def viewIndexing : List ViewIndex → Bool
  | [] => true
  | .scalar _ :: rest => viewIndexing rest
  | .slice _ :: .slice a :: rest => viewIndexing (.slice a :: rest)
  | .slice _ :: .range _ :: rest => rest.all fun i => match i with | .scalar _ => true | _ => false
  | .range _ :: rest => rest.all fun i => match i with | .scalar _ => true | _ => false
  | _ => false

/-- `axes`, `_indices_sub`, `size`, and `axes1`, base/subarray.jl:70,525-541. -/
def subAxes (indices : List ViewIndex) : List Axis := indices.flatMap fun i => match i with
  | .scalar _ => []
  | .slice a | .range a => [oneToAxis (JInt.wrap .i64 a.len)]
  | .array axes _ | .cartesianArray _ axes => axes

def subSize (indices : List ViewIndex) : List Nat := (subAxes indices).map (·.len)

/-- `_trimmedshape`, base/subarray.jl:133-139. -/
def trimmedShape : List ViewIndex → List Nat
  | [] => []
  | .scalar _ :: rest => 1 :: trimmedShape rest
  | .slice a :: rest | .range a :: rest => a.len :: trimmedShape rest
  | .array _ values :: rest => values.length :: trimmedShape rest
  | .cartesianArray rank axes :: rest => (axes.foldl (fun n a => n * a.len) 1) ::
      List.replicate (rank - 1) 1 ++ trimmedShape rest

/-- `_trimmedpind`, `_trimmedvind`, and `_trimmedindex`, base/subarray.jl:141-159. -/
def trimmedIndices (indices : List ViewIndex) : List ViewIndex := indices.map fun i => match i with
  | .scalar _ => .scalar one
  | .slice a | .range a => .range (oneToAxis (JInt.wrap .i64 a.len))
  | x => x

/-- `rm_singleton_indices`, base/subarray.jl:170-172. -/
def removeTrailingScalars : List ViewIndex → List ViewIndex
  | [] => []
  | .scalar _ :: rest => if rest.isEmpty then [] else .scalar zero :: removeTrailingScalars rest
  | x :: rest => x :: removeTrailingScalars rest

/-- `_reindexlinear`, base/subarray.jl:327-352. -/
def reindexLinear (v : SubModel) (i : I64) : I64 :=
  if v.linear then v.offset + v.stride * i else v.offset + i

/-- `substrides`, base/subarray.jl:439-444. -/
private def prependResult (x : I64) : MDResult (List I64) → MDResult (List I64)
  | .ok xs => .ok (x :: xs)
  | .argumentError => .argumentError
  | .boundsError => .boundsError
  | .dimensionMismatch => .dimensionMismatch
  | .typeError => .typeError
  | .inexactError => .inexactError
  | .error => .error

def subStrides : List I64 → List ViewIndex → MDResult (List I64)
  | [], [] => .ok []
  | _ :: ss, .scalar _ :: is => subStrides ss is
  | s :: ss, .slice _ :: is => prependResult s (subStrides ss is)
  | s :: ss, .range a :: is => prependResult (s * a.step) (subStrides ss is)
  | _, _ => .argumentError

/-- `compute_stride1`, base/subarray.jl:448-456. -/
def computeStride1 (s : I64) (axes : List Axis) (xs : List ViewIndex) : MDResult I64 :=
  if xs.all (fun i => match i with | .scalar _ => true | _ => false) then .ok s
  else match axes, xs with
    | a :: ars, .scalar _ :: rest => computeStride1 (s * JInt.wrap .i64 a.len) ars rest
    | _, .range a :: _ => .ok (s * a.step)
    | _, .slice _ :: _ => .ok s
    | _, _ => .argumentError

/-- `compute_linindex`, base/subarray.jl:486-501. -/
def computeLinindex (first stride : I64) (parentAxes : List Axis) (indices : List ViewIndex) : I64 :=
  let pairs := parentAxes.zip indices
  pairs.foldl (fun state p =>
    let i := match p.2 with | .scalar x => x | .slice a | .range a => a.first | .array _ xs => xs.head?.getD one | .cartesianArray _ _ => one
    (state.1 + (i - p.1.first) * state.2, state.2 * JInt.wrap .i64 p.1.len)) (first, stride) |>.1

/-- `find_extended_dims` and `find_extended_inds`, base/subarray.jl:503-508. -/
def extendedDims (start : Nat) (indices : List ViewIndex) : List Nat :=
  (indices.zipIdx).filterMap fun (i, n) => match i with | .scalar _ => none | _ => some (start + n)

/-- `pointer` methods, base/subarray.jl:510-520. -/
def subPointer (base offset stride i : I64) : I64 := base + offset + stride * i

inductive SubarrayMethod where
  | innerConstructor | constructor | cartConstructor | linearConstructor | computeLayout
  | checkParent | viewIndexing | size | similarValue | similarType | sizeof | copy
  | parent | parentIndices | parentIndicesGeneric | dataids | splatmap | unaliascopy
  | trimmedShape | trimmedParent | trimmedView | trimmedIndex | reshapeParent | removeSingletons
  | view | viewRange | viewColon | unsafeView | maybeReindex | reindex | getindex
  | reindexLinear | getFast | getContiguous | setindex | setFast | isassigned | style
  | strides | substrides | stride | computeStride | elsize | iscontiguous | firstIndex
  | computeOffset | computeLinindex | extendedDims | extendedIndices | pointer | axes
  | axes1 | hasOffsetAxes | replacePrint | unsafeWrap
  deriving Repr, DecidableEq

structure SubarrayInput where
  view : SubModel
  coords : List I64
  value : I64
  elementSize : Nat
  deriving Repr

inductive SubarrayObservation where
  | view (v : SubModel)
  | axes (a : List Axis)
  | sizes (s : List Nat)
  | coords (x : List I64)
  | scalar (x : I64)
  | natural (n : Nat)
  | boolean (b : Bool)
  | strides (s : MDResult (List I64))
  deriving Repr, DecidableEq

/-- Dispatch model for SubArray construction, indexing, layout, and accessors. -/
def runSubarray : SubarrayMethod → SubarrayInput → SubarrayObservation
  | .innerConstructor, p | .constructor, p | .cartConstructor, p | .linearConstructor, p |
    .computeLayout, p | .similarValue, p | .similarType, p | .copy, p | .unaliascopy, p |
    .reshapeParent, p | .view, p | .viewRange, p | .viewColon, p | .unsafeView, p |
    .maybeReindex, p | .setindex, p | .setFast, p | .replacePrint, p | .unsafeWrap, p => .view p.view
  | .checkParent, p => .boolean (decide (indexNdims (p.view.indices.map fun i => match i with
      | .scalar _ => .scalar | .cartesianArray n ax => .cartesianArray n (ax.map (·.len))
      | .array ax _ => .array (ax.map (·.len)) | .slice a | .range a => .colon a.len) = p.view.parentAxes.length))
  | .viewIndexing, p | .style, p | .iscontiguous, p => .boolean (viewIndexing p.view.indices)
  | .size, p => .sizes (subSize p.view.indices)
  | .sizeof, p => .natural ((subSize p.view.indices).foldl (· * ·) 1 * p.elementSize)
  | .parent, p | .parentIndices, p | .parentIndicesGeneric, p | .dataids, p | .splatmap, p |
    .trimmedParent, p | .trimmedView, p | .trimmedIndex, p | .removeSingletons, p |
    .reindex, p | .getindex, p | .getFast, p | .getContiguous, p | .isassigned, p |
    .extendedIndices, p | .hasOffsetAxes, p => .coords p.coords
  | .trimmedShape, p => .sizes (trimmedShape p.view.indices)
  | .reindexLinear, p | .firstIndex, p | .computeOffset, p | .computeLinindex, p |
    .pointer, p => .scalar (reindexLinear p.view (p.coords.head?.getD one))
  | .strides, p | .substrides, p | .stride, p | .computeStride, p =>
      .strides (subStrides (p.view.parentAxes.map fun _ => one) p.view.indices)
  | .elsize, p => .natural p.elementSize
  | .extendedDims, p => .sizes (extendedDims 1 p.view.indices)
  | .axes, p | .axes1, p => .axes (subAxes p.view.indices)

/-! ## Slices, base/slicearray.jl:39-249 -/

structure SlicesModel where
  parentAxes : List Axis
  slicemap : List (Option Nat)
  axes : List Axis
  deriving Repr, DecidableEq

/-- `_slice_check_dims`, base/slicearray.jl:51-56. -/
def sliceCheckDims (dims : List I64) : MDResult Unit :=
  if dims.any (fun d => d.val < 1) || dims.eraseDups.length ≠ dims.length then .dimensionMismatch else .ok ()

/-- `_eachslice`, base/slicearray.jl:58-80. -/
def eachsliceModel (parent : List Axis) (dims : List I64) (drop : Bool) : MDResult SlicesModel := do
  let _ ← sliceCheckDims dims
  let maxDim := dims.foldl (fun n d => max n d.val.toNat) parent.length
  let parentExtended := parent ++ List.replicate (maxDim - parent.length) (oneToAxis one)
  if drop then
    let axes := dims.map fun d => parentExtended.getD (d.val - 1).toNat (oneToAxis one)
    let map := (List.range maxDim).map fun i : Nat =>
      (dims.findIdx? (fun d => d.val = (i : Int) + 1)).map (· + 1)
    pure { parentAxes := parent, slicemap := map, axes }
  else
    let axes := (List.range maxDim).map fun i : Nat =>
      if dims.any (fun d => d.val = (i : Int) + 1) then parentExtended.getD i (oneToAxis one) else oneToAxis one
    let map := (List.range maxDim).map fun i : Nat =>
      if dims.any (fun d => d.val = (i : Int) + 1) then some (i + 1) else none
    pure { parentAxes := parent, slicemap := map, axes }

/-- `_slice_index`, base/slicearray.jl:236-238. -/
def sliceIndex (s : SlicesModel) (coords : List I64) : List (Option I64) :=
  s.slicemap.map fun entry => entry.map fun i => coords.getD (i - 1) one

inductive SlicesMethod where
  | unitaxis | checkDimsEmpty | checkDims | eachsliceTuple | eachsliceDim | eachslice
  | eachrowMatrix | eachrowVector | eachcolMatrix | eachcolVector | axes | size
  | sliceIndex | getindex | setindex | parent
  deriving Repr, DecidableEq

structure SlicesInput where
  parentAxes : List Axis
  dims : List I64
  drop : Bool
  slices : SlicesModel
  coords : List I64
  deriving Repr

inductive SlicesObservation where
  | axis (a : Axis)
  | result (r : MDResult SlicesModel)
  | check (r : MDResult Unit)
  | axes (a : List Axis)
  | sizes (s : List Nat)
  | index (i : List (Option I64))
  deriving Repr, DecidableEq

/-- Dispatch model for all observable slicearray.jl method bodies. -/
def runSlices : SlicesMethod → SlicesInput → SlicesObservation
  | .unitaxis, _ => .axis (oneToAxis one)
  | .checkDimsEmpty, _ => .check (.ok ())
  | .checkDims, p => .check (sliceCheckDims p.dims)
  | .eachsliceTuple, p | .eachsliceDim, p | .eachslice, p => .result (eachsliceModel p.parentAxes p.dims p.drop)
  | .eachrowMatrix, p | .eachrowVector, p => .result (eachsliceModel p.parentAxes [one] true)
  | .eachcolMatrix, p | .eachcolVector, p => .result (eachsliceModel p.parentAxes [JInt.lit .i64 2] true)
  | .axes, p => .axes p.slices.axes
  | .size, p => .sizes (p.slices.axes.map (·.len))
  | .sliceIndex, p | .getindex, p | .setindex, p => .index (sliceIndex p.slices p.coords)
  | .parent, p => .axes p.slices.parentAxes

end JuliaLean.MultidimCov

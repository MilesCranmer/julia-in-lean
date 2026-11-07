import JuliaLean.base.error
import JuliaLean.Core
import JuliaLean.base.show

section
/-!
# Model of `base/arrayshow.jl`

Typed model of Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Array indexing, element display, and terminal text operations are explicit inputs;
IO context and stream writes use `JuliaLean.base.show`.
-/
namespace JuliaLean.base.arrayshow

open JuliaLean

structure Alignment where
  left : JInt64
  right : JInt64
  deriving Repr, DecidableEq

structure Axis where
  values : List JInt64
  first : JInt64
  last : JInt64
  length : JInt64

inductive ArrayShowError where
  | errorException (message : String)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except ArrayShowError α

end JuliaLean.base.arrayshow
end

section
namespace JuliaLean.base.arrayshow.Model

-- Source: base/arrayshow.jl:573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def typeinfoEltypeArrayDispatch {m : Type → Type} [Monad m] {Ty : Type}
    (eltype : Ty → m Ty) (typeinfo : Ty) : m (Option Ty) := do
  return some (← eltype typeinfo)

-- Source: base/arrayshow.jl:574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def typeinfoEltypeDictDispatch {m : Type → Type} [Monad m] {Ty : Type}
    (eltype : Ty → m Ty) (typeinfo : Ty) : m (Option Ty) := do
  return some (← eltype typeinfo)

-- Source: base/arrayshow.jl:575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def typeinfoEltypeSetDispatch {m : Type → Type} [Monad m] {Ty : Type}
    (eltype : Ty → m Ty) (typeinfo : Ty) : m (Option Ty) := do
  return some (← eltype typeinfo)

open JuliaLean JuliaLean.base.show

-- Source: base/arrayshow.jl:165-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def printMatrixDispatch {m : Type → Type} [Monad m] {Io V A Ax Axis Text H W R : Type}
    (axes : A → JInt64 → m Ax) (unitrange : Ax → m Axis)
    (impl : JIO Io V → A → Text → Text → Text → Text → Text → Text → H → W → Axis → Axis → m R)
    (io : JIO Io V) (array : A) (pre sep post hdots vdots ddots : Text)
    (hmod : H) (vmod : W) : m R := do
  let rows ← unitrange (← axes array (i64 1))
  let cols ← unitrange (← axes array (i64 2))
  impl io array pre sep post hdots vdots ddots hmod vmod rows cols

-- Source: base/arrayshow.jl:366-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def printArrayZeroDispatch {m : Type → Type} [Monad m] [MonadExceptOf ShowError m]
    {Io V A X R : Type} (p : IOPrims m Io V)
    (isassigned : A → m Bool) (getindex : A → m X)
    (showElement : JIO Io V → X → m R) (io : JIO Io V) (array : A) : m (Option R) := do
  if ← isassigned array then
    return some (← showElement io (← getindex array))
  else
    printStr p io undef_ref_str
    pure none

-- Source: base/arrayshow.jl:368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def printArrayVecOrMatDispatch {m : Type → Type} {Io V A R : Type}
    (printMatrix : JIO Io V → A → m R) (io : JIO Io V) (array : A) : m R :=
  printMatrix io array

-- Source: base/arrayshow.jl:369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def printArrayHigherDispatch {m : Type → Type} {Io V A Slice R S : Type}
    (showNd : JIO Io V → A → (JIO Io V → Slice → m S) → Bool → m R)
    (printMatrix : JIO Io V → Slice → m S) (io : JIO Io V) (array : A) : m R :=
  showNd io array printMatrix true

-- Source: base/arrayshow.jl:438-439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showNonemptyMatrixDispatch {m : Type → Type} [Monad m] {Io V A Ax R : Type}
    (axes : A → m Ax)
    (impl : JIO Io V → A → String → Bool → Ax → m R)
    (io : JIO Io V) (array : A) (typePrefix : String) : m R := do
  impl io array typePrefix false (← axes array)

-- Source: base/arrayshow.jl:499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showNonemptyZeroDispatch {m : Type → Type} {Io V A R : Type}
    (printArray : JIO Io V → A → m R) (io : JIO Io V) (array : A) : m R :=
  printArray io array

-- Source: base/arrayshow.jl:506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showEmptyAbstractDispatch {m : Type → Type} {Io V A R : Type}
    (summary : JIO Io V → A → m R) (io : JIO Io V) (array : A) : m R :=
  summary io array

-- Source: base/arrayshow.jl:526-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showZeroArrayDispatch {m : Type → Type} [Monad m] [MonadExceptOf ShowError m]
    {Io V A X Ty R S : Type} (p : IOPrims m Io V)
    (isassigned : A → m Bool) (getindex : A → m X)
    (showElement : JIO Io V → X → m R) (printType : JIO Io V → Ty → m S)
    (io : JIO Io V) (array : A) (type : Ty) : m Unit := do
  if ← isassigned array then
    printStr p io "fill("
    let _ ← showElement io (← getindex array)
  else
    printAll p io [printStr p io "Array{", do let _ ← printType io type; pure (),
      printStr p io ", 0}("]
    show_UndefInitializer p io
  printStr p io ")"

open JuliaLean
open JuliaLean.base.show
open JuliaLean.base.arrayshow

abbrev R (α : Type) := Except ArrayShowError α
structure ArrayOps (m : Type → Type) (A X Ty : Type) where
  axes : A → List Axis
  ndims : A → JInt64
  isempty : A → Bool
  isvector : A → Bool
  isDictionary : A → Bool
  typeof : A → Ty
  eltype : A → Ty
  keytype : A → Ty
  valtype : A → Ty
  isType : A → Ty → Bool
  isassigned : A → List JInt64 → Bool
  getindex : A → List JInt64 → Option X
  replaceInPrintMatrix : A → JInt64 → JInt64 → Bytes → m Bytes

structure CellOps (m : Type → Type) (Io V X : Type) where
  showTextPlain : JIO Io V → X → m Unit
  showElement : JIO Io V → X → m Unit
  sprintTextPlain : JIO Io V → X → m Bytes
  sprintShow : JIO Io V → X → m Bytes
  alignment : JIO Io V → X → m Alignment
  stringLength : String → JInt64
  textwidth : String → JInt64
  textwidthBytes : Bytes → JInt64
  hasNewline : Bytes → Bool
  repeatText : String → JInt64 → m Bytes
  truncateAtWidthOrChars : Bool → Bytes → JInt64 → m Bytes
  assertion : Bool → String → m Unit
structure TypeDisplayOps (m : Type → Type) (Io V Ty : Type) where
  showType : JIO Io V → Ty → m Unit
  sprintType : JIO Io V → Ty → m String
  sprintTypeName : JIO Io V → Ty → m String

structure ShowArrayOps (m : Type → Type) (Io V A Ty : Type) where
  summary : JIO Io V → A → m Unit
  sprintSummary : JIO Io V → A → m Bytes
  sprintShow : JIO Io V → A → JInt64 → m Bytes
  showUndef : JIO Io V → m Unit
  ofAny : A → V

structure ShowVectorOps (m : Type → Type) (Io V I Ty : Type) where
  length : I → JInt64
  axis1 : I → Axis
  eltype : I → Ty
  typeinfoPrefix : JIO Io V → I → m (String × Bool)
  showDelimited : JIO Io V → I → String → String → String → Bool → JInt64 → JInt64 → m Unit
  ofTypeinfo : Ty → m (JIO Io V)

structure ShowNdOps (m : Type → Type) (Io V A Slice : Type) where
  view : A → Axis → Axis → List JInt64 → m Slice
  showNonempty : JIO Io V → Slice → String → m Unit
  printMatrix : JIO Io V → Slice → m Unit


structure TypeTraits (Ty : Type) where
  float64 : Ty
  int : Ty
  char : Ty
  string : Ty
  symbol : Ty
  method : Ty
  array : Ty
  bitArray : Ty
  abstractArray : Ty
  tuple : Ty
  namedTuple : Ty
  pair : Ty
  abstractDict : Ty
  abstractSet : Ty
  isBottom : Ty → Bool
  fieldTypes : Ty → List Ty
  singleton : Ty → Bool
  concrete : Ty → Bool
  eltype : Ty → Ty
  keytype : Ty → Ty
  valtype : Ty → Ty
  printWithoutParams : Ty → Bool
  unwrapUnionAll : Ty → Ty

def intLength {α : Type} (xs : List α) : JInt64 :=
  JInt.wrap .i64 xs.length

def intMax (x y : JInt64) : JInt64 := if x.val < y.val then y else x

def intMin (x y : JInt64) : JInt64 := if x.val < y.val then x else y

def axisValues (axis : Axis) : List JInt64 := axis.values

def axisFirst (axis : Axis) : JInt64 := axis.first

def axisLast (axis : Axis) : JInt64 := axis.last

def axisLength (axis : Axis) : JInt64 := axis.length
def sliceEnds {α : Type} (values : List α) (front back : Nat) : List α :=
  values.take front ++ values.drop (values.length - back)

def axisAt (axes : List Axis) (dimension : JInt64) : Axis :=
  (axes[dimension.val.toNat - 1]?).getD
    ⟨[i64 1], i64 1, i64 1, i64 1⟩

def alignmentWidth (alignments : List Alignment) : JInt64 :=
  alignments.foldl (fun width alignment => width + alignment.left + alignment.right) (i64 0)

def listIndex1 {m : Type → Type} [Monad m] [MonadExceptOf ShowError m]
    (values : List JInt64) (index : JInt64) : m JInt64 := do
  if index.val < 1 then throwShow (.jl .boundsError)
  else match values[index.val.toNat - 1]? with
    | some value => pure value
    | none => throwShow (.jl .boundsError)

def intDiv {m : Type → Type} [Monad m] [MonadExceptOf ShowError m]
    (a b : JInt64) : m JInt64 :=
  ofJl (JuliaLean.JInt.div a b)

def intRem {m : Type → Type} [Monad m] [MonadExceptOf ShowError m]
    (a b : JInt64) : m JInt64 :=
  ofJl (JuliaLean.JInt.remInt a b)
def intMod {m : Type → Type} [Monad m] [MonadExceptOf ShowError m]
    (a b : JInt64) : m JInt64 :=
  ofJl (JuliaLean.JInt.mod a b)

def listHeadD {α : Type} (values : List α) (default : α) : α :=
  match values with
  | [] => default
  | value :: _ => value

def listLastD {α : Type} (values : List α) (default : α) : α :=
  values.foldl (fun _ value => value) default

def axisFromValues (values : List JInt64) (emptyFirst emptyLast : JInt64) : Axis :=
  ⟨values, listHeadD values emptyFirst, listLastD values emptyLast, intLength values⟩

def axisPrefix (axis : Axis) (count : Nat) : Axis :=
  axisFromValues (axis.values.take count) axis.first (axis.first - i64 1)

def axisSuffix (axis : Axis) (count : Nat) : Axis :=
  axisFromValues (axis.values.drop (axis.values.length - count)) axis.first (axis.first - i64 1)

inductive NdSliceDecision where
  | render
  | skip
  | dots (semicolons : JInt64)
  deriving Repr, DecidableEq

structure NdSliceState where
  lastIndices : List JInt64
  reachedLastDimension : Bool

def axisInterior (axis : Axis) (index : JInt64) : Bool :=
  if axis.length > i64 10 then
    let lower := (axis.values[2]?).getD (i64 0)
    let upper := (axis.values[axis.values.length - 4]?).getD (i64 0)
    lower < index && index ≤ upper
  else false

def hasInteriorIndex (axes : List Axis) (indices : List JInt64) : Bool :=
  (axes.zip indices).any fun (axis, index) => axisInterior axis index

def ndSliceDecisionAux (axes : List Axis) (indices : List JInt64)
    (priorAxes : List Axis) (priorIndices : List JInt64) (dimension : Nat) : NdSliceDecision :=
  match axes, indices with
  | axis :: restAxes, index :: restIndices =>
    let allFirst := (priorAxes.zip priorIndices).all fun (prior, value) => prior.first == value
    if axis.length > i64 10 then
      let fourth := (axis.values[3]?).getD (i64 0)
      if index == fourth && allFirst then
        if hasInteriorIndex restAxes restIndices then .skip
        else .dots (i64 (dimension + 2))
      else if axisInterior axis index then
        .skip
      else
        ndSliceDecisionAux restAxes restIndices (axis :: priorAxes) (index :: priorIndices) (dimension + 1)
    else
      ndSliceDecisionAux restAxes restIndices (axis :: priorAxes) (index :: priorIndices) (dimension + 1)
  | _, _ => .render

def ndSliceDecision (axes : List Axis) (indices : List JInt64) : NdSliceDecision :=
  ndSliceDecisionAux axes indices [] [] 1

def cartesianLoop {m : Type → Type} {S : Type} [Monad m] (axes : List Axis) (indexPrefix : List JInt64)
    (state : S) (step : S → List JInt64 → m S) : m S := do
  match axes with
  | [] => step state indexPrefix
  | axis :: rest =>
    let mut current := state
    for index in axis.values do
      current ← cartesianLoop rest (index :: indexPrefix) current step
    pure current
termination_by axes.length
decreasing_by simp_wf

def lastIncreasingDimensionAux (previous current : List JInt64) (position : Nat)
    (found : Option JInt64) : Option JInt64 :=
  match previous, current with
  | old :: previousRest, new :: currentRest =>
    let found := if old.val < new.val then some (i64 (position + 3)) else found
    lastIncreasingDimensionAux previousRest currentRest (position + 1) found
  | _, _ => found

def lastIncreasingDimension (previous current : List JInt64) : Option JInt64 :=
  lastIncreasingDimensionAux previous current 0 none



def printNdLabel {m : Type → Type} {Io V : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (stringInt : JInt64 → m Bytes) (io : JIO Io V)
    (indices : List JInt64) : m Unit := do
  printStr p io "[:, :, "
  for index in indices.take (indices.length - 1) do
    printBytes p io (← stringInt index)
    printStr p io ", "
  let lastIndex ← listIndex1 indices (intLength indices)
  println p io [printBytes p io (← stringInt lastIndex), printStr p io "] ="]
def popAlignment {m : Type → Type} [Monad m] [MonadExceptOf ShowError m]
    (alignments : List Alignment) : m (Alignment × List Alignment) :=
  match alignments with
  | alignment :: rest => pure (alignment, rest)
  | [] => throwShow (.jl (.argumentError "collection must be non-empty"))

/--
Julia source: base/arrayshow.jl:46-98 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

const undef_ref_alignment = (3,3)

"""
`alignment(io, X, rows, cols, cols_if_complete, cols_otherwise, sep)` returns the
alignment for specified parts of array `X`, returning the (left,right) info.
It will look in X's `rows`, `cols` (both lists of indices)
and figure out what's needed to be fully aligned, for example looking all
the way down a column and finding out the maximum size of each element.
Parameter `sep::Integer` is number of spaces to put between elements.
`cols_if_complete` and `cols_otherwise` indicate screen width to use.
Alignment is reported as a vector of (left,right) tuples, one for each
column going across the screen.
"""
function alignment(io::IO, @nospecialize(X::AbstractVecOrMat),
        rows::AbstractVector{T}, cols::AbstractVector{V},
        cols_if_complete::Integer, cols_otherwise::Integer, sep::Integer,
        #= `size(X) may not infer, set this in caller =# ncols::Integer=size(X, 2)) where {T,V}
    a = Tuple{T, V}[]
    width = 0
    for j in cols # need to go down each column one at a time
        l = r = 0
        for i in rows # plumb down and see what largest element sizes are
            if isassigned(X,i,j)
                aij = alignment(io, X[i,j])::Tuple{Int,Int}
            else
                aij = undef_ref_alignment
            end
            l = max(l, aij[1]) # left characters
            r = max(r, aij[2]) # right characters
        end
        push!(a, (l, r)) # one tuple per column of X, pruned to screen width
        width += l + r + sep
        if length(a) > 1 && width >= cols_if_complete
            width -= sum(pop!(a)) + sep # remove this latest tuple if we're already beyond screen width
            break
        end
    end
    if 1 < length(a) < ncols
        while width >= cols_otherwise
            width -= sum(pop!(a)) + sep
        end
    end
    return a
end

"""
`print_matrix_row(io, X, A, i, cols, sep)` produces the aligned output for
a single matrix row X[i, cols] where the desired list of columns is given.
The corresponding alignment A is used, and the separation between elements
is specified as string sep.
`print_matrix_row` will also respect compact output for elements.
"""
```
-/
def alignmentMatrix {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X) (io : JIO Io V) (array : A)
    (rows columns : List JInt64) (colsIfComplete colsOtherwise separator ncols : JInt64) :
    m (List Alignment) := do
  let mut alignments := []
  let mut width := i64 0
  for column in columns do
    let mut left := i64 0
    let mut right := i64 0
    for row in rows do
      let alignment ←
        if ops.isassigned array [row, column] then
          match ops.getindex array [row, column] with
          | some value => cells.alignment io value
          | none => throwShow (.jl .boundsError)
        else
          pure ⟨i64 3, i64 3⟩
      left := intMax left alignment.left
      right := intMax right alignment.right
    alignments := ⟨left, right⟩ :: alignments
    width := width + left + right + separator
    if 1 < intLength alignments && width ≥ colsIfComplete then
      let (removed, rest) ← popAlignment alignments
      alignments := rest
      width := width - removed.left - removed.right - separator
      break
  if 1 < intLength alignments && intLength alignments < ncols then
    while width ≥ colsOtherwise do
      let (removed, rest) ← popAlignment alignments
      alignments := rest
      width := width - removed.left - removed.right - separator
  pure alignments.reverse

def printMatrixRowLoop {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X)
    (io : JIO Io V) (array : A) (row : JInt64) (separator : String) (lastColumn count k : JInt64)
    (alignments : List Alignment) (columns : List JInt64) : m Unit := do
  match alignments, columns with
  | alignment :: restAlignments, column :: restColumns =>
    let (actual, text) ←
      if ops.isassigned array [row, column] then
        let value ← match ops.getindex array [row, column] with
          | some value => pure value
          | none => throwShow (.jl .boundsError)
        let actual ← cells.alignment io value
        let text ← cells.sprintTextPlain io value
        let text ← if cells.hasNewline text then cells.sprintShow io value else pure text
        pure (actual, text)
      else
        pure (⟨i64 3, i64 3⟩, lit undef_ref_str)
    let left ← cells.repeatText " " (alignment.left - actual.left)
    let right ← if column = lastColumn then pure [] else cells.repeatText " " (alignment.right - actual.right)
    let text ← ops.replaceInPrintMatrix array row column text
    printAll p io [printBytes p io left, printBytes p io text, printBytes p io right]
    if k < count then printStr p io separator
    printMatrixRowLoop p ops cells io array row separator lastColumn count (k + i64 1)
      restAlignments restColumns
  | _, _ => pure ()
termination_by alignments.length
decreasing_by simp_wf


def printMatrixVdotsLoop {m : Type → Type} {Io V M R : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (repeatText : String → JInt64 → m Bytes) (stringLength : String → JInt64)
    (remainder : JInt64 → M → m R) (equal : R → M → Bool) (io : JIO Io V)
    (dots separator : String) (modulus residue : M) (padRight : Bool) (count k : JInt64)
    (alignments : List Alignment) : m Unit := do
  match alignments with
  | alignment :: rest =>
    let width := alignment.left + alignment.right
    if equal (← remainder k modulus) residue then
      let leftWidth := intMax (i64 0) (alignment.left - stringLength dots)
      let left ← repeatText " " leftWidth
      let right ← if k = count && !padRight then pure []
        else repeatText " " (intMax (i64 0) (width - stringLength dots - leftWidth))
      printAll p io [printBytes p io left, printStr p io dots, printBytes p io right]
    else if k ≠ count || padRight then
      let spaces ← repeatText " " width
      printBytes p io spaces
    if k < count then printStr p io separator
    printMatrixVdotsLoop p repeatText stringLength remainder equal io dots separator modulus residue padRight
      count (k + i64 1) rest
  | [] => pure ()
termination_by alignments.length
decreasing_by simp_wf

def printMatrixVdotsBody {m : Type → Type} {Io V M R : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (repeatText : String → JInt64 → m Bytes) (stringLength : String → JInt64)
    (remainder : JInt64 → M → m R) (equal : R → M → Bool) (io : JIO Io V)
    (dots separator : String) (modulus residue : M) (padRight : Bool)
    (alignments : List Alignment) : m Unit :=
  printMatrixVdotsLoop p repeatText stringLength remainder equal io dots separator modulus residue padRight
    (intLength alignments) (i64 1) alignments



-- Reason: this range contains file-level license text and documentation, not method bodies.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:1-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- # methods related to array printing
-- 
-- # Printing a value requires to take into account the :typeinfo property
-- # from the IO context; this property encodes (as a type) the type information
-- # that is supposed to have already been displayed concerning this value,
-- # so that redundancy can be avoided. For example, when printing an array of
-- # `Float16` values, the header "Float16" will be printed, and the values
-- # can simply be printed with the decimal representations:
-- # show(Float16(1)) -> "Float16(1.0)"
-- # show([Float16(1)]) -> "Float16[1.0]" (instead of "Float16[Float16(1.0)]")
-- # Similarly:
-- # show([[Float16(1)]]) -> "Array{Float16}[[1.0]]" (instead of "Array{Float16}[Float16[1.0]]")
-- #
-- # The array printing methods here can be grouped into two categories (and are annotated as such):
-- # 1) "typeinfo aware" : these are "API boundaries" functions, which will read the typeinfo
-- #    property from the context, and pass down to their value an updated property
-- #    according to its eltype; at each layer of nesting, only one "typeinfo aware"
-- #    function must be called;
-- # 2) "typeinfo agnostic": these are helper functions used by the first category; hence
-- #    they don't manipulate the typeinfo property, and let the printing routines
-- #    for their elements read directly the property set by their callers
-- #
-- # Non-annotated functions are even lower level (e.g. print_matrix_row), so they fall
-- # by default into category 2.
-- #
-- # The basic organization of this file is
-- # 1) printing with `display`
-- # 2) printing with `show`
-- # 3) Logic for displaying type information
-- 
-- 
-- ## printing with `display`
-- 
-- """
-- Unexported convenience function used in body of `replace_in_print_matrix`
-- methods. By default returns a string of the same width as original with a
-- centered cdot, used in printing of structural zeros of structured matrices.
-- Accept keyword args `c` for alternate single character marker.
-- """
-- /Source

/--
Julia source: base/arrayshow.jl:42-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function replace_with_centered_mark(s::AbstractString;c::AbstractChar = '⋅')
    N = textwidth(ANSIIterator(s))
    return N == 0 ? string(c) : join(setindex!([" " for i=1:N],string(c),ceil(Int,N/2)))
end
```
-/
def replaceWithCenteredMark (textwidthANSI : String → Nat) (s : String) (marker : String := "⋅") : String :=
  let width := textwidthANSI s
  if width = 0 then marker
  else String.intercalate "" ((List.replicate width " ").set ((width - 1) / 2) marker)

structure MatrixCell where
  text : String
  actual : Alignment
  assigned : Bool := true
  deriving Repr, DecidableEq


/--
Julia source: base/arrayshow.jl:99-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_matrix_row(io::IO,
        @nospecialize(X::AbstractVecOrMat), A::Vector,
        i::Integer, cols::AbstractVector, sep::AbstractString,
        #= `axes(X)` may not infer, set this in caller =# idxlast::Integer=last(axes(X, 2)))
    for (k, j) = enumerate(cols)
        k > length(A) && break
        if isassigned(X,i,j)
            x = X[i,j]
            a = alignment(io, x)::Tuple{Int,Int}

            # First try 3-arg show
            sx = sprint(show, MIME"text/plain"(), x, context=io, sizehint=0)

            # If the output contains line breaks, try 2-arg show instead.
            if occursin('\n', sx)
                sx = sprint(show, x, context=io, sizehint=0)
            end
        else
            a = undef_ref_alignment
            sx = undef_ref_str
        end
        l = repeat(" ", A[k][1]-a[1]) # pad on left and right as needed
        r = j == idxlast ? "" : repeat(" ", A[k][2]-a[2])
        prettysx = replace_in_print_matrix(X,i,j,sx)
        print(io, l, prettysx, r)
        if k < length(A); print(io, sep); end
    end
end
```
-/
def printMatrixRow {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X)
    (io : JIO Io V) (array : A) (alignments : List Alignment) (row : JInt64)
    (columns : List JInt64) (separator : String) (idxlast : Option JInt64 := none) : m Unit :=
  printMatrixRowLoop p ops cells io array row separator
    (idxlast.getD (axisLast (axisAt (ops.axes array) (i64 2)))) (intLength alignments) (i64 1)
    alignments columns


-- Reason: this range is only documentation for the vertical-ellipsis method.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:127-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- """
-- `print_matrix_vdots` is used to show a series of vertical ellipsis instead
-- of a bunch of rows for long matrices. Not only is the string vdots shown
-- but it also repeated every M elements if desired.
-- """
-- /Source

/--
Julia source: base/arrayshow.jl:134-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_matrix_vdots(io::IO, vdots::AbstractString,
                            A::Vector, sep::AbstractString, M::Integer, m::Integer,
                            pad_right::Bool = true)
    for k = 1:length(A)
        w = A[k][1] + A[k][2]
        if k % M == m
            l = repeat(" ", max(0, A[k][1]-length(vdots)))
            r = k == length(A) && !pad_right ?
                "" :
                repeat(" ", max(0, w-length(vdots)-length(l)))
            print(io, l, vdots, r)
        else
            (k != length(A) || pad_right) && print(io, repeat(" ", w))
        end
        if k < length(A); print(io, sep); end
    end
end
```
-/
def printMatrixVdots {m : Type → Type} {Io V Mod R : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (repeatText : String → JInt64 → m Bytes) (stringLength : String → JInt64)
    (remainder : JInt64 → Mod → m R) (equal : R → Mod → Bool) (io : JIO Io V)
    (vdots separator : String) (alignments : List Alignment) (modulus residue : Mod)
    (padRight : Bool := true) : m Unit :=
  printMatrixVdotsBody p repeatText stringLength remainder equal io vdots separator modulus residue padRight alignments


-- Reason: this range is only documentation for the matrix-printing methods.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:151-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # typeinfo agnostic
-- """
--     print_matrix(io::IO, mat, pre, sep, post, hdots, vdots, ddots, hmod, vmod)
-- 
-- Prints a matrix with limited output size. If `io` sets `:limit` to true,
-- then only the corners of the matrix are printed, separated with vertical,
-- horizontal, and diagonal ellipses as appropriate.
-- Optional arguments are string pre (printed before the matrix, e.g. an opening bracket)
-- which will cause a corresponding same-size indent on following rows, and
-- string post (printed at the end of the last row of the matrix).
-- Also options to use different ellipsis characters hdots, vdots, ddots.
-- These are repeated every hmod or vmod elements.
-- """
-- /Source

-- Reason: this is a source boundary marker, not executable Julia code.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:175-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/arrayshow.jl:176-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _print_matrix(io, @nospecialize(X::AbstractVecOrMat), pre, sep, post, hdots, vdots, ddots, hmod, vmod, rowsA, colsA)
    hmod, vmod = Int(hmod)::Int, Int(vmod)::Int
    ncols, idxlast = length(colsA), last(colsA)
    if !(get(io, :limit, false)::Bool)
        screenheight = screenwidth = typemax(Int)
    else
        sz = displaysize(io)::Tuple{Int,Int}
        screenheight, screenwidth = sz[1] - 4, sz[2]
    end
    screenwidth -= length(pre)::Int + length(post)::Int
    presp = repeat(" ", length(pre)::Int)  # indent each row to match pre string
    postsp = ""
    @assert textwidth(hdots) == textwidth(ddots) "hdots and ddots must have same textwidth"
    sepsize = length(sep)::Int
    m, n = length(rowsA), length(colsA)
    # To figure out alignments, only need to look at as many rows as could
    # fit down screen. If screen has at least as many rows as A, look at A.
    # If not, then we only need to look at the first and last chunks of A,
    # each half a screen height in size.
    halfheight = div(screenheight,2)
    if m > screenheight
        rowsA = [rowsA[(0:halfheight-1) .+ firstindex(rowsA)]; rowsA[(end-div(screenheight-1,2)+1):end]]
    else
        rowsA = [rowsA;]
    end
    # Similarly for columns, only necessary to get alignments for as many
    # columns as could conceivably fit across the screen
    maxpossiblecols = div(screenwidth, 1+sepsize)
    if n > maxpossiblecols
        colsA = [colsA[(0:maxpossiblecols-1) .+ firstindex(colsA)]; colsA[(end-maxpossiblecols+1):end]]
    else
        colsA = [colsA;]
    end
    A = alignment(io, X, rowsA, colsA, screenwidth, screenwidth, sepsize, ncols)
    # Nine-slicing is accomplished using print_matrix_row repeatedly
    if m <= screenheight # rows fit vertically on screen
        if n <= length(A) # rows and cols fit so just print whole matrix in one piece
            for i in rowsA
                print(io, i == first(rowsA) ? pre : presp)
                print_matrix_row(io, X,A,i,colsA,sep,idxlast)
                print(io, i == last(rowsA) ? post : postsp)
                if i != last(rowsA); println(io); end
            end
        else # rows fit down screen but cols don't, so need horizontal ellipsis
            c = div(screenwidth-length(hdots)::Int+1,2)+1  # what goes to right of ellipsis
            Ralign = reverse(alignment(io, X, rowsA, reverse(colsA), c, c, sepsize, ncols)) # alignments for right
            c = screenwidth - sum(map(sum,Ralign)) - (length(Ralign)-1)*sepsize - length(hdots)::Int
            Lalign = alignment(io, X, rowsA, colsA, c, c, sepsize, ncols) # alignments for left of ellipsis
            for i in rowsA
                print(io, i == first(rowsA) ? pre : presp)
                print_matrix_row(io, X,Lalign,i,colsA[1:length(Lalign)],sep,idxlast)
                print(io, (i - first(rowsA)) % hmod == 0 ? hdots : repeat(" ", length(hdots)::Int))
                print_matrix_row(io, X, Ralign, i, (n - length(Ralign)) .+ colsA, sep, idxlast)
                print(io, i == last(rowsA) ? post : postsp)
                if i != last(rowsA); println(io); end
            end
        end
    else # rows don't fit so will need vertical ellipsis
        if n <= length(A) # rows don't fit, cols do, so only vertical ellipsis
            for i in rowsA
                print(io, i == first(rowsA) ? pre : presp)
                print_matrix_row(io, X,A,i,colsA,sep,idxlast)
                print(io, i == last(rowsA) ? post : postsp)
                if i != rowsA[end] || i == rowsA[halfheight]; println(io); end
                if i == rowsA[halfheight]
                    print(io, i == first(rowsA) ? pre : presp)
                    print_matrix_vdots(io, vdots, A, sep, vmod, 1, false)
                    print(io, i == last(rowsA) ? post : postsp * '\n')
                end
            end
        else # neither rows nor cols fit, so use all 3 kinds of dots
            c = div(screenwidth-length(hdots)::Int+1,2)+1
            Ralign = reverse(alignment(io, X, rowsA, reverse(colsA), c, c, sepsize, ncols))
            c = screenwidth - sum(map(sum,Ralign)) - (length(Ralign)-1)*sepsize - length(hdots)::Int
            Lalign = alignment(io, X, rowsA, colsA, c, c, sepsize, ncols)
            r = mod((length(Ralign)-n+1),vmod) # where to put dots on right half
            for i in rowsA
                print(io, i == first(rowsA) ? pre : presp)
                print_matrix_row(io, X,Lalign,i,colsA[1:length(Lalign)],sep,idxlast)
                print(io, (i - first(rowsA)) % hmod == 0 ? hdots : repeat(" ", length(hdots)::Int))
                print_matrix_row(io, X,Ralign,i,(n-length(Ralign)).+colsA,sep,idxlast)
                print(io, i == last(rowsA) ? post : postsp)
                if i != rowsA[end] || i == rowsA[halfheight]; println(io); end
                if i == rowsA[halfheight]
                    print(io, i == first(rowsA) ? pre : presp)
                    print_matrix_vdots(io, vdots, Lalign, sep, vmod, 1, true)
                    print(io, ddots)
                    print_matrix_vdots(io, vdots, Ralign, sep, vmod, r, false)
                    print(io, i == last(rowsA) ? post : postsp * '\n')
                end
            end
        end
        if isempty(rowsA)
            print(io, pre)
            print(io, vdots)
            length(colsA) > 1 && print(io, "    ", ddots)
            print(io, post)
        end
    end
end
```
-/
def printMatrixImpl {m : Type → Type} {Io V A X Ty HM VM : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X)
    (toIntH : HM → m JInt64) (toIntV : VM → m JInt64) (io : JIO Io V) (array : A)
    (pre separator post hdots vdots ddots : String) (hmod : HM) (vmod : VM)
    (rowsAxis colsAxis : Axis) : m Unit := do
  let hmod ← toIntH hmod
  let vmod ← toIntV vmod
  let ncols := axisLength colsAxis
  let idxlast := axisLast colsAxis
  let limited ← assertBool a (getIO p io "limit" false)
  let (screenheight, initialScreenwidth) ←
    if limited then do
      let (height, width) ← displaysize p a io
      pure (height - i64 4, width)
    else
      pure (typemaxInt, typemaxInt)
  let screenwidth := initialScreenwidth - cells.stringLength pre - cells.stringLength post
  let presp ← cells.repeatText " " (cells.stringLength pre)
  cells.assertion (cells.textwidth hdots == cells.textwidth ddots)
    "hdots and ddots must have same textwidth"
  let sepsize := cells.stringLength separator
  let m := axisLength rowsAxis
  let n := axisLength colsAxis
  let halfheight ← intDiv screenheight (i64 2)
  let backheight ← intDiv (screenheight - i64 1) (i64 2)
  let allRows := axisValues rowsAxis
  let rowsA := if m > screenheight then
    sliceEnds allRows halfheight.val.toNat backheight.val.toNat
  else
    allRows
  let maxpossiblecols ← intDiv screenwidth (i64 1 + sepsize)
  let allColumns := axisValues colsAxis
  let colsA := if n > maxpossiblecols then
    sliceEnds allColumns maxpossiblecols.val.toNat maxpossiblecols.val.toNat
  else
    allColumns
  let aligned ← alignmentMatrix ops cells io array rowsA colsA screenwidth screenwidth sepsize ncols
  let firstRow := listHeadD rowsA (i64 0)
  let lastRow := listLastD rowsA (i64 0)
  if m ≤ screenheight then
    if n ≤ intLength aligned then
      for row in rowsA do
        printStr p io (if row = firstRow then pre else "")
        printBytes p io (if row = firstRow then [] else presp)
        printMatrixRow p ops cells io array aligned row colsA separator (some idxlast)
        printStr p io (if row = lastRow then post else "")
        if row ≠ lastRow then println p io []
    else
      let c1 ← intDiv (screenwidth - cells.stringLength hdots + i64 1) (i64 2)
      let c := c1 + i64 1
      let rightAlignments ← alignmentMatrix ops cells io array rowsA colsA.reverse c c sepsize ncols
      let rightAlignments := rightAlignments.reverse
      let c := screenwidth - alignmentWidth rightAlignments -
        (intLength rightAlignments - i64 1) * sepsize - cells.stringLength hdots
      let leftAlignments ← alignmentMatrix ops cells io array rowsA colsA c c sepsize ncols
      let leftColumns := colsA.take leftAlignments.length
      let rightOffset := n - intLength rightAlignments
      let rightColumns := colsA.map (fun column => rightOffset + column)
      for row in rowsA do
        printStr p io (if row = firstRow then pre else "")
        printBytes p io (if row = firstRow then [] else presp)
        printMatrixRow p ops cells io array leftAlignments row leftColumns separator (some idxlast)
        if (← intRem (row - firstRow) hmod) = i64 0 then
          printStr p io hdots
        else
          printBytes p io (← cells.repeatText " " (cells.stringLength hdots))
        printMatrixRow p ops cells io array rightAlignments row rightColumns separator (some idxlast)
        printStr p io (if row = lastRow then post else "")
        if row ≠ lastRow then println p io []
  else
    if n ≤ intLength aligned then
      for row in rowsA do
        printStr p io (if row = firstRow then pre else "")
        printBytes p io (if row = firstRow then [] else presp)
        printMatrixRow p ops cells io array aligned row colsA separator (some idxlast)
        printStr p io (if row = lastRow then post else "")
        if row ≠ lastRow then
          println p io []
        else
          let middle ← listIndex1 rowsA halfheight
          if row = middle then println p io []
        let middle ← listIndex1 rowsA halfheight
        if row = middle then
          printStr p io (if row = firstRow then pre else "")
          printBytes p io (if row = firstRow then [] else presp)
          printMatrixVdots p cells.repeatText cells.stringLength intRem
            (fun remainder residue => remainder == residue) io vdots separator aligned vmod (i64 1) false
          if row = lastRow then printStr p io post else printStr p io "\n"
    else
      let c1 ← intDiv (screenwidth - cells.stringLength hdots + i64 1) (i64 2)
      let c := c1 + i64 1
      let rightAlignments ← alignmentMatrix ops cells io array rowsA colsA.reverse c c sepsize ncols
      let rightAlignments := rightAlignments.reverse
      let c := screenwidth - alignmentWidth rightAlignments -
        (intLength rightAlignments - i64 1) * sepsize - cells.stringLength hdots
      let leftAlignments ← alignmentMatrix ops cells io array rowsA colsA c c sepsize ncols
      let rightResidue ← intMod (intLength rightAlignments - n + i64 1) vmod
      let leftColumns := colsA.take leftAlignments.length
      let rightOffset := n - intLength rightAlignments
      let rightColumns := colsA.map (fun column => rightOffset + column)
      for row in rowsA do
        printStr p io (if row = firstRow then pre else "")
        printBytes p io (if row = firstRow then [] else presp)
        printMatrixRow p ops cells io array leftAlignments row leftColumns separator (some idxlast)
        if (← intRem (row - firstRow) hmod) = i64 0 then
          printStr p io hdots
        else
          printBytes p io (← cells.repeatText " " (cells.stringLength hdots))
        printMatrixRow p ops cells io array rightAlignments row rightColumns separator (some idxlast)
        printStr p io (if row = lastRow then post else "")
        if row ≠ lastRow then
          println p io []
        else
          let middle ← listIndex1 rowsA halfheight
          if row = middle then println p io []
        let middle ← listIndex1 rowsA halfheight
        if row = middle then
          printStr p io (if row = firstRow then pre else "")
          printBytes p io (if row = firstRow then [] else presp)
          printMatrixVdots p cells.repeatText cells.stringLength intRem
            (fun remainder residue => remainder == residue) io vdots separator leftAlignments vmod (i64 1) true
          printStr p io ddots
          printMatrixVdots p cells.repeatText cells.stringLength intRem
            (fun remainder residue => remainder == residue) io vdots separator rightAlignments vmod rightResidue false
          if row = lastRow then printStr p io post else printStr p io "\n"
    if rowsA.isEmpty then
      printStr p io pre
      printStr p io vdots
      if 1 < intLength colsA then printStr p io "    " *> printStr p io ddots
      printStr p io post

/--
Julia source: base/arrayshow.jl:165-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_matrix(io::IO, X::AbstractVecOrMat,
                      pre::AbstractString = " ",  # pre-matrix string
                      sep::AbstractString = "  ", # separator between elements
                      post::AbstractString = "",  # post-matrix string
                      hdots::AbstractString = "  \u2026  ",
                      vdots::AbstractString = "\u22ee",
                      ddots::AbstractString = "  \u22f1  ",
                      hmod::Integer = 5, vmod::Integer = 5)
    _print_matrix(io, inferencebarrier(X), pre, sep, post, hdots, vdots, ddots, hmod, vmod, unitrange(axes(X,1)), unitrange(axes(X,2)))
end
```
-/
def printMatrix {m : Type → Type} {Io V A X Ty HM VM : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X)
    (toIntH : HM → m JInt64) (toIntV : VM → m JInt64) (io : JIO Io V) (array : A)
    (pre separator post hdots vdots ddots : String) (hmod : HM) (vmod : VM) : m Unit :=
  printMatrixDispatch (fun array dim => pure (axisAt (ops.axes array) dim)) pure
    (printMatrixImpl p a ops cells toIntH toIntV) io array
    pre separator post hdots vdots ddots hmod vmod

def printMatrixDefault {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X)
    (toInt : JInt64 → m JInt64) (io : JIO Io V) (array : A) : m Unit :=
  printMatrix p a ops cells toInt toInt io array " " "  " "" "  …  " "⋮" "  ⋱  " (i64 5) (i64 5)


-- Reason: this range contains section headings and comments only.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:276-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # typeinfo agnostic
-- # n-dimensional arrays
-- /Source

-- Reason: this is a source boundary marker, not executable Julia code.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:281-281 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/arrayshow.jl:282-351 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _show_nd(io::IO, @nospecialize(a::AbstractArray), print_matrix::Function, show_full::Bool, axs::Tuple{Vararg{AbstractUnitRange}})
    limit = get(io, :limit, false)::Bool
    if isempty(a)
        return
    end
    tailinds = tail(tail(axs))
    nd = ndims(a)-2
    show_full || print(io, "[")
    Is = CartesianIndices(tailinds)
    lastidxs = first(Is).I
    reached_last_d = false
    for I in Is
        idxs = I.I
        @label entry begin
            if limit
                for i = 1:nd
                    ii = idxs[i]
                    ind = tailinds[i]
                    if length(ind) > 10
                        all_first = true
                        for d = 1:i-1
                            if idxs[d] != first(tailinds[d])
                                all_first = false
                                break
                            end
                        end
                        if ii == ind[firstindex(ind)+3] && all_first
                            for j=i+1:nd
                                szj = length(axs[j+2])
                                indj = tailinds[j]
                                if szj>10 && first(indj)+2 < idxs[j] <= last(indj)-3
                                    break entry
                                end
                            end
                            print(io, ";"^(i+2))
                            print(io, " \u2026 ")
                            show_full && print(io, "\n\n")
                            break entry
                        end
                        if ind[firstindex(ind)+2] < ii <= ind[end-3]
                            break entry
                        end
                    end
                end
            end
            if show_full
                _show_nd_label(io, a, idxs)
            end
            slice = view(a, axs[1], axs[2], idxs...)
            if show_full
                print_matrix(io, slice)
                print(io, idxs == map(last,tailinds) ? "" : "\n\n")
            else
                idxdiff = lastidxs .- idxs .< 0
                if any(idxdiff)
                    lastchangeindex = 2 + findlast(idxdiff)
                    print(io, ";"^lastchangeindex)
                    lastchangeindex == ndims(a) && (reached_last_d = true)
                    print(io, " ")
                end
                print_matrix(io, slice)
            end
        end
        lastidxs = idxs
    end
    if !show_full
        reached_last_d || print(io, ";"^(nd+2))
        print(io, "]")
    end
end
```
-/

def showNdCore {m : Type → Type} {Io V A X Ty Slice : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X)
    (stringInt : JInt64 → m Bytes) (io : JIO Io V) (array : A) (showFull : Bool)
    (axes : List Axis) (display : ShowNdOps m Io V A Slice) : m Unit := do
  let limit ← assertBool a (getIO p io "limit" false)
  if !ops.isempty array then
    let tailAxes := axes.drop 2
    let nd := ops.ndims array - i64 2
    if !showFull then printStr p io "["
    let initial : NdSliceState := ⟨tailAxes.map axisFirst, false⟩
    let finalIndices := tailAxes.map axisLast
    let result ← cartesianLoop tailAxes.reverse [] initial fun state indices => do
      match if limit then ndSliceDecision tailAxes indices else .render with
      | .skip =>
        pure { state with lastIndices := indices }
      | .dots semicolons =>
        printBytes p io (← cells.repeatText ";" semicolons)
        printStr p io " … "
        if showFull then printStr p io "\n\n"
        pure { state with lastIndices := indices }
      | .render =>
        if showFull then
          printNdLabel p stringInt io indices
          let slice ← display.view array (axisAt axes (i64 1)) (axisAt axes (i64 2)) indices
          display.printMatrix io slice
          if indices != finalIndices then printStr p io "\n\n"
          pure { state with lastIndices := indices }
        else
          let changedAt := lastIncreasingDimension state.lastIndices indices
          match changedAt with
          | some semicolons =>
            printBytes p io (← cells.repeatText ";" semicolons)
            printStr p io " "
          | none => pure ()
          let reached := state.reachedLastDimension ||
            (changedAt == some (ops.ndims array))
          let slice ← display.view array (axisAt axes (i64 1)) (axisAt axes (i64 2)) indices
          display.printMatrix io slice
          pure { lastIndices := indices, reachedLastDimension := reached }
    if !showFull then
      if !result.reachedLastDimension then
        printBytes p io (← cells.repeatText ";" (nd + i64 2))
      printStr p io "]"



/--
Julia source: base/arrayshow.jl:279-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_nd(io::IO, a::AbstractArray, print_matrix::Function, show_full::Bool) =
    _show_nd(io, inferencebarrier(a), print_matrix, show_full, map(unitrange, axes(a)))
```
-/
def showNd {m : Type → Type} {Io V A X Ty Slice : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X)
    (stringInt : JInt64 → m Bytes) (io : JIO Io V) (array : A) (showFull : Bool)
    (display : ShowNdOps m Io V A Slice) : m Unit :=
  showNdCore p a ops cells stringInt io array showFull (ops.axes array) display

-- Reason: this is a source boundary marker, not executable Julia code.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:352-352 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/arrayshow.jl:353-359 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _show_nd_label(io::IO, a::AbstractArray, idxs)
    print(io, "[:, :, ")
    for i = 1:length(idxs)-1
        print(io, idxs[i], ", ")
    end
    println(io, idxs[end], "] =")
end
```
-/
def showNdLabel {m : Type → Type} {Io V A : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (stringInt : JInt64 → m Bytes) (io : JIO Io V) (_array : A)
    (indices : List JInt64) : m Unit :=
  printNdLabel p stringInt io indices


-- Reason: this range contains section headings and comments only.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:360-365 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # print_array: main helper functions for show(io, text/plain, array)
-- # typeinfo agnostic
-- # Note that this is for showing the content inside the array, and for `MIME"text/plain".
-- # There are `show(::IO, ::A) where A<:AbstractArray` methods that don't use this
-- # e.g. show_vector, show_zero_dim
-- /Source

/--
Julia source: base/arrayshow.jl:366-367 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print_array(io::IO, X::AbstractArray{<:Any, 0}) =
    isassigned(X) ? show(io, X[]) : print(io, undef_ref_str)
```
-/
def printArrayZero {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X)
    (io : JIO Io V) (array : A) : m Unit := do
  let _ ← printArrayZeroDispatch p (fun array => pure (ops.isassigned array []))
    (fun array => match ops.getindex array [] with
      | some value => pure value
      | none => throwShow (.jl .boundsError)) cells.showElement io array
  pure ()
def printArrayVecOrMatImpl {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty)
    (cells : CellOps m Io V X) (toInt : JInt64 → m JInt64) (io : JIO Io V)
    (array : A) : m Unit :=
  printMatrixDefault p a ops cells toInt io array
def printArrayHigherImpl {m : Type → Type} {Io V A X Ty Slice : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty)
    (cells : CellOps m Io V X) (stringInt : JInt64 → m Bytes) (io : JIO Io V)
    (array : A) (display : ShowNdOps m Io V A Slice) : m Unit :=
  showNd p a ops cells stringInt io array true display

def printArray {m : Type → Type} {Io V A X Ty Slice : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty)
    (cells : CellOps m Io V X) (toInt : JInt64 → m JInt64) (stringInt : JInt64 → m Bytes)
    (io : JIO Io V) (array : A) (display : ShowNdOps m Io V A Slice) : m Unit := do
  if ops.ndims array == i64 0 then
    printArrayZero p ops cells io array
  else if ops.ndims array ≤ i64 2 then
    printArrayVecOrMatImpl p a ops cells toInt io array
  else
    printArrayHigherImpl p a ops cells stringInt io array display

/--
Julia source: base/arrayshow.jl:368-368 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print_array(io::IO, X::AbstractVecOrMat) = print_matrix(io, X)
```
-/
def printArrayVecOrMat {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty)
    (cells : CellOps m Io V X) (toInt : JInt64 → m JInt64) (io : JIO Io V)
    (array : A) : m Unit :=
  printArrayVecOrMatDispatch (printArrayVecOrMatImpl p a ops cells toInt) io array

/--
Julia source: base/arrayshow.jl:369-369 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print_array(io::IO, X::AbstractArray) = show_nd(io, X, print_matrix, true)
```
-/
def printArrayHigher {m : Type → Type} {Io V A X Ty Slice : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty)
    (cells : CellOps m Io V X) (stringInt : JInt64 → m Bytes) (io : JIO Io V)
    (array : A) (display : ShowNdOps m Io V A Slice) : m Unit :=
  printArrayHigherDispatch
    (fun io array printMatrix full => showNd p a ops cells stringInt io array full
      { display with printMatrix := printMatrix }) display.printMatrix io array


-- Reason: this range contains section headings and comments only.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:370-372 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # typeinfo aware
-- # implements: show(io::IO, ::MIME"text/plain", X::AbstractArray)
-- /Source

/--
Julia source: base/arrayshow.jl:373-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ::MIME"text/plain", X::AbstractArray)
    if isempty(X) && (get(io, :compact, false)::Bool || X isa AbstractVector)
        return show(io, X)
    end
    # 1) show summary before setting :compact
    summary(io, X)
    isempty(X) && return
    print(io, ":")
    show_circular(io, X) && return

    # 2) compute new IOContext
    if !haskey(io, :compact) && length(axes(X, 2)) > 1
        io = IOContext(io, :compact => true)
    end
    if get(io, :limit, false)::Bool && eltype(X) === Method
        # override usual show method for Vector{Method}: don't abbreviate long lists
        io = IOContext(io, :limit => false)
    end

    if get(io, :limit, false)::Bool
        # when there is no vertical room to show even one row of entries
        # plus a vertical ellipsis, show as many entries as fit on a single
        # line, truncated to the terminal width (#58323)
        screenheight = displaysize(io)[1] - 4
        if screenheight <= 0 || (screenheight == 1 && (ndims(X) > 2 || size(X, 1) > 1))
            print(io, ' ')
            return _show_oneline_truncated(io, X)
        end
    end
    println(io)

    # 3) update typeinfo
    #
    # it must come after printing the summary, which can exploit :typeinfo itself
    # (e.g. views)
    # we assume this function is always called from top-level, i.e. that it's not nested
    # within another "show" method; hence we always print the summary, without
    # checking for current :typeinfo (this could be changed in the future)
    io = IOContext(io, :typeinfo => eltype(X))

    # 4) show actual content
    recur_io = IOContext(io, :SHOWN_SET => X)
    print_array(recur_io, X)
end
```
-/
def showArrayPlain {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty) (traits : TypeTraits Ty)
    (ops : ArrayOps m A X Ty) (showOps : ShowArrayOps m Io V A Ty)
    (printstyled : PrintStyled m Io V) (stringInt : JInt64 → m Bytes)
    (printArray : JIO Io V → A → m Unit) (showTwoArg showOneLine : JIO Io V → A → m Unit)
    (io : JIO Io V) (array : A) : m Unit := do
  let compact ← assertBool a (getIO p io "compact" false)
  if ops.isempty array && (compact || ops.isvector array) then
    showTwoArg io array
  else
    showOps.summary io array
    if ops.isempty array then
      pure ()
    else do
      printStr p io ":"
      let circular ← show_circular p printstyled stringInt
        (fun value item => a.egal value (showOps.ofAny item)) io array
      if circular then
        pure ()
      else do
        let mut context := io
        if !haskey io "compact" && axisLength (axisAt (ops.axes array) (i64 2)) > i64 1 then
          context ← withBool p a context "compact" true
        let limited ← assertBool a (getIO p context "limit" false)
        if limited && t.egal (ops.eltype array) traits.method then
          context ← withBool p a context "limit" false
        let limited ← assertBool a (getIO p context "limit" false)
        if limited then
          let (height, _) ← displaysize p a context
          let screenHeight := height - i64 4
          let firstAxisLength := axisLength (axisAt (ops.axes array) (i64 1))
          if screenHeight ≤ i64 0 ||
              (screenHeight == i64 1 && (ops.ndims array > i64 2 || firstAxisLength > i64 1)) then
            printStr p context " "
            showOneLine context array
          else
            println p context []
            let typed ← withTypeinfo p a context (ops.eltype array)
            let shown ← withShownSet p a showOps.ofAny typed array
            printArray shown array
        else
          println p context []
          let typed ← withTypeinfo p a context (ops.eltype array)
          let shown ← withShownSet p a showOps.ofAny typed array
          printArray shown array

-- Reason: this is a source boundary marker, not executable Julia code.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

/--
Julia source: base/arrayshow.jl:418-425 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _show_oneline_truncated(io::IO, X::AbstractArray)
    cols = displaysize(io)[2]
    used = textwidth(sprint(summary, X; context=io)) + 2
    width = max(cols - used, 8)
    ctx = IOContext(io, :typeinfo => typeof(X), :compact => true)
    str = sprint(show, X; context=ctx, sizehint=min(4width, 4096))
    print(io, _truncate_at_width_or_chars(get(io, :color, false)::Bool, str, width))
end
```
-/
def showOnelineTruncated {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty)
    (cells : CellOps m Io V X) (showOps : ShowArrayOps m Io V A Ty)
    (io : JIO Io V) (array : A) : m Unit := do
  let (_, columns) ← displaysize p a io
  let summary ← showOps.sprintSummary io array
  let width := intMax (columns - cells.textwidthBytes summary - i64 2) (i64 8)
  let typed ← withTypeinfo p a io (ops.typeof array)
  let compact ← withBool p a typed "compact" true
  let sizehint := intMin (i64 4 * width) (i64 4096)
  let shown ← showOps.sprintShow compact array sizehint
  let color ← assertBool a (getIO p compact "color" false)
  printBytes p io (← cells.truncateAtWidthOrChars color shown width)

-- Reason: this range contains section headings and comments only.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:426-437 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ## printing with `show`
-- 
-- ### non-Vector arrays
-- 
-- # _show_nonempty & _show_empty: main helper functions for show(io, X)
-- # typeinfo agnostic
-- 
-- """
-- `_show_nonempty(io, X::AbstractMatrix, prefix)` prints matrix X with opening and closing square brackets,
-- preceded by `prefix`, supposed to encode the type of the elements.
-- """
-- /Source

-- Reason: this is a source boundary marker, not executable Julia code.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:440-440 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

def showNonemptyMatrixImpl {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty)
    (cells : CellOps m Io V X) (io : JIO Io V) (array : A) (typePrefix : String)
    (dropBrackets : Bool) (rowsAxis colsAxis : Axis) : m Unit := do
  cells.assertion (!ops.isempty array) "X should be non-empty"
  let limit ← assertBool a (getIO p io "limit" false)
  let nr := axisLength rowsAxis
  let nc := axisLength colsAxis
  let rowDots := limit && nr > i64 4
  let columnDots := limit && nc > i64 4
  let rowFront := if rowDots then axisPrefix rowsAxis 2 else rowsAxis
  let rowBack := if rowDots then axisSuffix rowsAxis 2 else ⟨[], i64 1, i64 0, i64 0⟩
  let columnFront := if columnDots then axisPrefix colsAxis 2 else colsAxis
  let columnBack := if columnDots then axisSuffix colsAxis 2
    else ⟨[], colsAxis.first, colsAxis.first - i64 1, i64 0⟩
  if !dropBrackets then
    printStr p io typePrefix
    printStr p io "["
  for rows in [rowFront, rowBack] do
    for row in rows.values do
      for columns in [columnFront, columnBack] do
        for column in columns.values do
          if column > columns.first then printStr p io " "
          if !ops.isassigned array [row, column] then
            printStr p io "#undef"
          else
            match ops.getindex array [row, column] with
            | some value => cells.showElement io value
            | none => throwShow (.jl .boundsError)
        if columns.last == colsAxis.last then
          if row < rowsAxis.last then printStr p io "; "
        else if columnDots then
          printStr p io " … "
    if rows.last != rowsAxis.last && rowDots then printStr p io "… ; "
  if !dropBrackets then
    if nc ≤ i64 1 then printStr p io ";;"
    printStr p io "]"

/--
Julia source: base/arrayshow.jl:441-487 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _show_nonempty(io::IO, @nospecialize(X::AbstractMatrix), prefix::String, drop_brackets::Bool, axs::Tuple{AbstractUnitRange,AbstractUnitRange})
    @assert !isempty(X) "X should be non-empty"
    limit = get(io, :limit, false)::Bool
    indr, indc = axs
    nr, nc = length(indr), length(indc)
    rdots, cdots = false, false
    rr1, rr2 = unitrange(indr), 1:0
    cr1 = unitrange(indc)
    cr2 = first(cr1) .+ (0:-1)
    if limit
        if nr > 4
            rr1, rr2 = rr1[1:2], rr1[nr-1:nr]
            rdots = true
        end
        if nc > 4
            cr1, cr2 = cr1[1:2], cr1[nc-1:nc]
            cdots = true
        end
    end
    drop_brackets || print(io, prefix, "[")
    for rr in (rr1, rr2)
        for i in rr
            for cr in (cr1, cr2)
                for j in cr
                    j > first(cr) && print(io, " ")
                    if !isassigned(X,i,j)
                        print(io, undef_ref_str)
                    else
                        el = X[i,j]
                        show(io, el)
                    end
                end
                if last(cr) == last(indc)
                    i < last(indr) && print(io, "; ")
                elseif cdots
                    print(io, " \u2026 ")
                end
            end
        end
        last(rr) != last(indr) && rdots && print(io, "\u2026 ; ")
    end
    if !drop_brackets
        nc > 1 || print(io, ";;")
        print(io, "]")
    end
    return nothing
end
```
-/
def showNonemptyMatrixWithAxes {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty)
    (cells : CellOps m Io V X) (io : JIO Io V) (array : A) (typePrefix : String)
    (dropBrackets : Bool) (rowsAxis colsAxis : Axis) : m Unit :=
  showNonemptyMatrixImpl p a ops cells io array typePrefix dropBrackets rowsAxis colsAxis

/--
Julia source: base/arrayshow.jl:438-439 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_show_nonempty(io::IO, X::AbstractMatrix, prefix::String) =
    _show_nonempty(io, inferencebarrier(X), prefix, false, axes(X))
```
-/
def showNonemptyMatrix {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty)
    (cells : CellOps m Io V X) (io : JIO Io V) (array : A) (typePrefix : String) : m Unit :=
  showNonemptyMatrixDispatch (fun array => pure (ops.axes array))
    (fun io array typePrefix drop axes => showNonemptyMatrixWithAxes p a ops cells io array typePrefix drop
      (axisAt axes (i64 1)) (axisAt axes (i64 2))) io array typePrefix

-- Reason: this is a source boundary marker, not executable Julia code.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:488-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source

/--
Julia source: base/arrayshow.jl:490-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _show_nonempty(io::IO, X::AbstractArray, prefix::String)
    print(io, prefix)
    show_nd(io, X, (io, slice) -> _show_nonempty(io, inferencebarrier(slice), prefix, true, axes(slice)), false)
end
```
-/
def showNonemptyHigher {m : Type → Type} {Io V A X Ty Slice : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty)
    (cells : CellOps m Io V X) (stringInt : JInt64 → m Bytes) (io : JIO Io V)
    (array : A) (typePrefix : String) (display : ShowNdOps m Io V A Slice) : m Unit := do
  printStr p io typePrefix
  let nested : ShowNdOps m Io V A Slice :=
    { view := display.view
      showNonempty := display.showNonempty
      printMatrix := fun nestedIO slice => display.showNonempty nestedIO slice typePrefix }
  showNd p a ops cells stringInt io array false nested

-- Reason: this range contains a comment introducing the vector-specific call path.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:494-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # a specific call path is used to show vectors (show_vector)
-- /Source

/--
Julia source: base/arrayshow.jl:496-497 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_show_nonempty(::IO, ::AbstractVector, ::String) =
    error("_show_nonempty(::IO, ::AbstractVector, ::String) is not implemented")
```
-/
def showNonemptyVector : R Unit := .error (.errorException "_show_nonempty(::IO, ::AbstractVector, ::String) is not implemented")

/--
Julia source: base/arrayshow.jl:499-499 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_show_nonempty(io::IO, X::AbstractArray{T,0} where T, prefix::String) = print_array(io, X)
```
-/
def showNonemptyZero {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X)
    (io : JIO Io V) (array : A) : m Unit :=
  showNonemptyZeroDispatch (printArrayZero p ops cells) io array

-- Reason: the blank separator and explanatory note do not define a method.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:498-498 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Reason: explanatory note about the :typeinfo attribute.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:500-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # NOTE: it's not clear how this method could use the :typeinfo attribute
-- /Source

/--
Julia source: base/arrayshow.jl:502-505 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _show_empty(io::IO, X::Array)
    show(io, typeof(X))
    print(io, "(undef, ", join(size(X),", "), ')')
end
```
-/
def showEmptyArray {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (ops : ArrayOps m A X Ty) (display : TypeDisplayOps m Io V Ty)
    (stringInt : JInt64 → m Bytes) (io : JIO Io V) (array : A) : m Unit := do
  display.showType io (ops.typeof array)
  printStr p io "(undef, "
  let mut first := true
  for axis in ops.axes array do
    if !first then printStr p io ", "
    printBytes p io (← stringInt (axisLength axis))
    first := false
  printStr p io ")"

/--
Julia source: base/arrayshow.jl:506-506 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_show_empty(io, X::AbstractArray) = summary(io, X)
```
-/
def showEmptyAbstract {m : Type → Type} {Io V A Ty : Type} [Monad m]
    (showOps : ShowArrayOps m Io V A Ty) (io : JIO Io V) (array : A) : m Unit :=
  showEmptyAbstractDispatch showOps.summary io array


-- Reason: this range contains section headings and comments only.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:507-508 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # typeinfo aware (necessarily)
-- /Source

/--
Julia source: base/arrayshow.jl:509-522 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, X::AbstractArray)
    ndims(X) == 0 && return show_zero_dim(io, X)
    ndims(X) == 1 && return show_vector(io, X)
    prefix, implicit = typeinfo_prefix(io, X)
    if !implicit
        io = IOContext(io, :typeinfo => eltype(X))
    end
    if isempty(X)
        return _show_empty(io, X)
    end
    show_circular(io, X) && return
    recur_io = IOContext(io, :SHOWN_SET => X)
    _show_nonempty(recur_io, X, prefix)
end
```
-/
def showArrayTwoArg {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ArrayOps m A X Ty)
    (showOps : ShowArrayOps m Io V A Ty) (printstyled : PrintStyled m Io V)
    (stringInt : JInt64 → m Bytes) (typeinfoPrefix : JIO Io V → A → m (String × Bool))
    (showZero showVector showEmpty : JIO Io V → A → m Unit)
    (showNonemptyMatrix showNonemptyHigher : JIO Io V → A → String → m Unit)
    (io : JIO Io V) (array : A) : m Unit := do
  if ops.ndims array == i64 0 then
    showZero io array
  else if ops.ndims array == i64 1 then
    showVector io array
  else
    let (typePrefix, implicit) ← typeinfoPrefix io array
    let context ← if implicit then pure io else withTypeinfo p a io (ops.eltype array)
    if ops.isempty array then
      showEmpty context array
    else
      let circular ← show_circular p printstyled stringInt
        (fun value item => a.egal value (showOps.ofAny item)) context array
      if circular then
        pure ()
      else
        let shown ← withShownSet p a showOps.ofAny context array
        if ops.ndims array == i64 2 then
          showNonemptyMatrix shown array typePrefix
        else
          showNonemptyHigher shown array typePrefix

-- Reason: this range contains section headings and comments only.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:523-524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ### 0-dimensional arrays (#31481)
-- /Source

/--
Julia source: base/arrayshow.jl:525-525 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show_zero_dim(io::IO, X::BitArray{0}) = print(io, "BitArray(", Int(X[]), ")")
```
-/
def showZeroBit {m : Type → Type} {Io V : Type} [Monad m]
    (p : IOPrims m Io V) (stringInt : JInt64 → m Bytes) (io : JIO Io V) (value : Bool) : m Unit := do
  printStr p io "BitArray("
  printBytes p io (← stringInt (if value then i64 1 else i64 0))
  printStr p io ")"

/--
Julia source: base/arrayshow.jl:526-535 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_zero_dim(io::IO, X::AbstractArray{T, 0}) where T
    if isassigned(X)
        print(io, "fill(")
        show(io, X[])
    else
        print(io, "Array{", T, ", 0}(")
        show(io, undef)
    end
    print(io, ")")
end
```
-/
def showZeroArray {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X)
    (showOps : ShowArrayOps m Io V A Ty) (display : TypeDisplayOps m Io V Ty)
    (io : JIO Io V) (array : A) : m Unit := do
  showZeroArrayDispatch p (fun array => pure (ops.isassigned array []))
    (fun array => match ops.getindex array [] with
      | some value => pure value
      | none => throwShow (.jl .boundsError)) cells.showElement display.showType
    io array (ops.eltype array)

def showZeroDim {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (ops : ArrayOps m A X Ty) (cells : CellOps m Io V X)
    (showOps : ShowArrayOps m Io V A Ty) (typeDisplay : TypeDisplayOps m Io V Ty)
    (stringInt : JInt64 → m Bytes) (isBitArray : A → Bool) (toBool : X → Bool)
    (io : JIO Io V) (array : A) : m Unit := do
  if isBitArray array then
    match ops.getindex array [] with
    | some value => showZeroBit p stringInt io (toBool value)
    | none => throwShow (.jl .boundsError)
  else
    showZeroArray p ops cells showOps typeDisplay io array

-- Reason: this range contains section headings and comments only.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:536-541 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- ### Vector arrays
-- 
-- # typeinfo aware
-- # NOTE: v is not constrained to be a vector, as this function can work with iterables
-- # in general (it's used e.g. by show(::IO, ::Set))
-- /Source

/--
Julia source: base/arrayshow.jl:542-560 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_vector(io::IO, v, opn='[', cls=']')
    prefix, implicit = typeinfo_prefix(io, v)
    print(io, prefix)
    # directly or indirectly, the context now knows about eltype(v)
    if !implicit
        io = IOContext(io, :typeinfo => eltype(v))
    end
    limited = get(io, :limit, false)::Bool

    if limited && length(v) > 20
        axs1 = axes1(v)
        f, l = first(axs1), last(axs1)
        show_delim_array(io, v, opn, ",", "", false, f, f+9)
        print(io, "  …  ")
        show_delim_array(io, v, "", ",", cls, false, l-9, l)
    else
        show_delim_array(io, v, opn, ",", cls, false)
    end
end
```
-/
def showVector {m : Type → Type} {Io V I Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (ops : ShowVectorOps m Io V I Ty)
    (io : JIO Io V) (value : I) (opening : String := "[") (closing : String := "]") : m Unit := do
  let (typePrefix, implicit) ← ops.typeinfoPrefix io value
  printStr p io typePrefix
  let context ← if implicit then pure io else ops.ofTypeinfo (ops.eltype value)
  let limited ← assertBool a (getIO p context "limit" false)
  let firstAxis := ops.axis1 value
  if limited && ops.length value > i64 20 then
    let first := axisFirst firstAxis
    let last := axisLast firstAxis
    ops.showDelimited context value opening "," "" false first (first + i64 9)
    printStr p context "  …  "
    ops.showDelimited context value "" "," closing false (last - i64 9) last
  else
    ops.showDelimited context value opening "," closing false (axisFirst firstAxis) (axisLast firstAxis)


-- Reason: this range contains section headings and comments only.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:561-569 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- ## Logic for displaying type information
-- 
-- # given type `typeinfo` extracted from context, assuming a collection
-- # is being displayed, deduce the elements type; in spirit this is
-- # similar to `eltype` (except that we don't want a default fall-back
-- # returning Any, as this would cause incorrect printing in e.g. `Vector[Any[1]]`,
-- # because eltype(Vector) == Any so `Any` wouldn't be printed in `Any[1]`)
-- /Source

/--
Julia source: base/arrayshow.jl:570-570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typeinfo_eltype(typeinfo) = nothing # element type not precisely known
```
-/
def typeinfoEltypeFallback {Ty : Type} (_typeinfo : Ty) : Option Ty := none
/--
Julia source: base/arrayshow.jl:571-571 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typeinfo_eltype(typeinfo::Type{Union{}}) = nothing
```
-/
def typeinfoEltypeBottom {Ty : Type} (_typeinfo : Ty) : Option Ty := none
/--
Julia source: base/arrayshow.jl:572-572 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typeinfo_eltype(::Type{Union{}}, slurp...) = throw(MethodError(typeinfo_eltype, (Union{}, slurp...)))
```
-/
def typeinfoEltypeBottomSlurp {m : Type → Type} [Monad m] [MonadExceptOf ShowError m] {Ty : Type}
    (_typeinfo : Ty) (_args : List Ty) : m (Option Ty) :=
  throwShow (.jl (.methodError "typeinfo_eltype"))

/--
Julia source: base/arrayshow.jl:573-573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typeinfo_eltype(typeinfo::Type{<:AbstractArray{T}}) where {T} = eltype(typeinfo)
```
-/
def typeinfoEltypeArray {Ty : Type} (traits : TypeTraits Ty) (typeinfo : Ty) : Option Ty :=
  Id.run (typeinfoEltypeArrayDispatch (m := Id) traits.eltype typeinfo)

/--
Julia source: base/arrayshow.jl:574-574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typeinfo_eltype(typeinfo::Type{<:AbstractDict{K,V}}) where {K,V} = eltype(typeinfo)
```
-/
def typeinfoEltypeDict {Ty : Type} (traits : TypeTraits Ty) (typeinfo : Ty) : Option Ty :=
  Id.run (typeinfoEltypeDictDispatch (m := Id) traits.eltype typeinfo)

/--
Julia source: base/arrayshow.jl:575-575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
typeinfo_eltype(typeinfo::Type{<:AbstractSet{T}}) where {T} = eltype(typeinfo)
```
-/
def typeinfoEltypeSet {Ty : Type} (traits : TypeTraits Ty) (typeinfo : Ty) : Option Ty :=
  Id.run (typeinfoEltypeSetDispatch (m := Id) traits.eltype typeinfo)

-- Reason: the remaining lines explain type-info dispatch.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:576-581 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # This is a fancy way to make de-specialize a call to `typeinfo_implicit(T)`
-- # which is unfortunately invalidated by Dates
-- #  (https://github.com/JuliaLang/julia/issues/56080)
-- #
-- # This makes the call less efficient, but avoids being invalidated by Dates.
-- /Source

def typeinfoEltypeModel {m : Type → Type} [Monad m] {Ty : Type} (t : TypeOps m Ty) (traits : TypeTraits Ty)
    (typeinfo : Ty) : m (Option Ty) := do
  if traits.isBottom typeinfo then
    return typeinfoEltypeBottom typeinfo
  else if ← t.subtype typeinfo traits.abstractArray then
    return typeinfoEltypeArray traits typeinfo
  else if ← t.subtype typeinfo traits.abstractDict then
    return typeinfoEltypeDict traits typeinfo
  else if ← t.subtype typeinfo traits.abstractSet then
    return typeinfoEltypeSet traits typeinfo
  else
    return typeinfoEltypeFallback typeinfo

/--
Julia source: base/arrayshow.jl:582-582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_typeinfo_implicit(@nospecialize(T)) = Base.invoke_in_world(Base.tls_world_age(), typeinfo_implicit, T)::Bool
```
-/
def typeinfoImplicitInvoke {Ty : Type} (invoke : Ty → Bool) (typeinfo : Ty) : Bool :=
  invoke typeinfo

-- Reason: this range contains explanatory comments for type-info display.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:583-584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # types that can be parsed back accurately from their un-decorated representations
-- /Source

/--
Julia source: base/arrayshow.jl:585-594 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function typeinfo_implicit(@nospecialize(T))
    if T === Float64 || T === Int || T === Char || T === String || T === Symbol ||
        issingletontype(T)
        return true
    end
    return isconcretetype(T) &&
        ((T <: Array && _typeinfo_implicit(eltype(T))) ||
         ((T <: Tuple || T <: NamedTuple || T <: Pair) && all(_typeinfo_implicit, fieldtypes(T))) ||
         (T <: AbstractDict && _typeinfo_implicit(keytype(T)) && _typeinfo_implicit(valtype(T))))
end
```
-/
def typeinfoImplicit {m : Type → Type} [Monad m] {Ty : Type} (t : TypeOps m Ty) (traits : TypeTraits Ty)
    (recur : Ty → m Bool) (typeinfo : Ty) : m Bool := do
  if t.egal typeinfo traits.float64 || t.egal typeinfo traits.int ||
      t.egal typeinfo traits.char || t.egal typeinfo traits.string ||
      t.egal typeinfo traits.symbol || traits.singleton typeinfo then
    return true
  if !traits.concrete typeinfo then
    return false
  if ← t.subtype typeinfo traits.array then
    if ← recur (traits.eltype typeinfo) then return true
  let tupleLike ← do
    if ← t.subtype typeinfo traits.tuple then pure true
    else if ← t.subtype typeinfo traits.namedTuple then pure true
    else t.subtype typeinfo traits.pair
  if tupleLike then
    if ← (traits.fieldTypes typeinfo).allM recur then return true
  if ← t.subtype typeinfo traits.abstractDict then
    if ← recur (traits.keytype typeinfo) then return ← recur (traits.valtype typeinfo)
  return false

-- Reason: this range contains a comment introducing the type-info prefix method.
-- UNTRANSLATED
-- Source: base/arrayshow.jl:595-596 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # X not constrained, can be any iterable (cf. show_vector)
-- /Source

/--
Julia source: base/arrayshow.jl:597-628 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function typeinfo_prefix(io::IO, X)
    typeinfo = get(io, :typeinfo, Any)::Type

    if !(X isa typeinfo)
        typeinfo = Any
    end

    # what the context already knows about the eltype of X:
    eltype_ctx = typeinfo_eltype(typeinfo)
    eltype_X = eltype(X)

    if X isa AbstractDict
        if eltype_X == eltype_ctx
            sprint(show_type_name, typeof(X).name; context=io), false
        elseif !isempty(X) && _typeinfo_implicit(keytype(X)) && _typeinfo_implicit(valtype(X))
            sprint(show_type_name, typeof(X).name; context=io), true
        else
            sprint(print, typeof(X); context=io), false
        end
    else
        # Types hard-coded here are those which are created by default for a given syntax
        if eltype_X == eltype_ctx
            "", false
        elseif !isempty(X) && _typeinfo_implicit(eltype_X)
            "", true
        elseif print_without_params(eltype_X)
            sprint(show_type_name, unwrap_unionall(eltype_X).name; context=io), false # Print "Array" rather than "Array{T,N}"
        else
            sprint(print, eltype_X; context=io), false
        end
    end
end
```
-/
def typeinfoPrefix {m : Type → Type} {Io V A X Ty : Type} [Monad m] [MonadExceptOf ShowError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty) (t : TypeOps m Ty) (traits : TypeTraits Ty)
    (ops : ArrayOps m A X Ty) (display : TypeDisplayOps m Io V Ty) (isImplicit : Ty → m Bool)
    (io : JIO Io V) (array : A) : m (String × Bool) := do
  let typeinfo ← assertType a (getIO p io "typeinfo" t.any)
  let typeinfo := if ops.isType array typeinfo then typeinfo else t.any
  let elementType := ops.eltype array
  let contextElementType ← typeinfoEltypeModel t traits typeinfo
  let sameElementType ←
    match contextElementType with
    | some contextType => t.eq elementType contextType
    | none => pure false
  if ops.isDictionary array then
    if sameElementType then
      return (← display.sprintTypeName io (ops.typeof array), false)
    else if !ops.isempty array then
      let keyImplicit ← typeinfoImplicit t traits isImplicit (ops.keytype array)
      if keyImplicit then
        let valueImplicit ← typeinfoImplicit t traits isImplicit (ops.valtype array)
        if valueImplicit then return (← display.sprintTypeName io (ops.typeof array), true)
      return (← display.sprintType io (ops.typeof array), false)
    else
      return (← display.sprintType io (ops.typeof array), false)
  else if sameElementType then
    return ("", false)
  else if !ops.isempty array then
    if ← isImplicit elementType then return ("", true)
  if traits.printWithoutParams elementType then
    return (← display.sprintTypeName io (traits.unwrapUnionAll elementType), false)
  return (← display.sprintType io elementType, false)
end JuliaLean.base.arrayshow.Model
end



namespace JuliaLean.ErrorShow


/-! ### Array alignment and truncation -/

structure Alignment where
  left : Nat
  right : Nat
  deriving Repr, DecidableEq

/-- Width after the padding at `base/arrayshow.jl:118-121`. -/
def paddedWidth (column cell : Alignment) : Nat :=
  (column.left - cell.left) + cell.left + cell.right + (column.right - cell.right)

structure CornerSlice where
  front : Nat
  back : Nat
  truncated : Bool
  deriving Repr, DecidableEq

/-- Row slicing at `base/arrayshow.jl:193-198`. `screenRows` is the terminal
height after the four header rows have been removed. -/
def rowCorners (rows screenRows : Nat) (limited : Bool) : CornerSlice :=
  if limited && screenRows < rows then
    { front := screenRows / 2, back := (screenRows - 1) / 2, truncated := true }
  else
    { front := rows, back := 0, truncated := false }

/-- Once alignment has determined how many equal-width columns fit, the left
side receives the odd extra column. This is the corner split used by
`base/arrayshow.jl:217-229`. -/
def columnCorners (columns visible : Nat) : CornerSlice :=
  if visible < columns then
    { front := (visible + 1) / 2, back := visible / 2, truncated := true }
  else
    { front := columns, back := 0, truncated := false }

inductive ArrayRoute where
  | twoArgumentShow
  | summaryOnly
  | oneLineTruncated
  | zeroDimensional
  | matrix
  | nDimensional
  deriving Repr, DecidableEq

/-- Branch selection in `show(::MIME\"text/plain\", ::AbstractArray)` and
`print_array`, `base/arrayshow.jl:364-414`. -/
def arrayRoute (rank rows : Nat) (isVector empty compact limited : Bool)
    (screenRows : Nat) : ArrayRoute :=
  if empty && (compact || isVector) then .twoArgumentShow
  else if empty then .summaryOnly
  else if limited && (screenRows = 0 || (screenRows = 1 && (rank > 2 || rows > 1))) then
    .oneLineTruncated
  else if rank = 0 then .zeroDimensional
  else if rank ≤ 2 then .matrix
  else .nDimensional

def zeroDimensionalRepr (element : String) : String := "fill(" ++ element ++ ")"

def zeroDimensionalPlain (summary element : String) : String := summary ++ ":\n" ++ element

end JuliaLean.ErrorShow

namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

/-! ### `base/arrayshow.jl` -/

def centeredMarker (width : Nat) (marker : String) : List String :=
  if width = 0 then [marker]
  else (List.replicate width " ").set (width / 2) marker

def verticalDots (widths : List Alignment) (dots separator : String)
    (modulus residue : Nat) (padRight : Bool) : List String :=
  widths.zipIdx.map fun (alignment, index) =>
    let width := alignment.left + alignment.right
    let content := if modulus != 0 && (index + 1) % modulus = residue then dots else ""
    if index + 1 = widths.length && !padRight then content
    else content ++ String.ofList (List.replicate (width - content.length) ' ') ++
      (if index + 1 < widths.length then separator else "")

structure NDimSlice where
  indices : List Nat
  shown : Bool
  separatorRank : Nat
  deriving Repr, DecidableEq

def ndSliceShown (limited : Bool) (axisLength index : Nat) : Bool :=
  !limited || axisLength ≤ 10 || index ≤ 3 || axisLength - 3 < index

def showNdRoute (empty showFull : Bool) : String :=
  if empty then "empty" else if showFull then "label-and-matrix" else "literal-slices"

def oneLineTruncated (summaryWidth terminalWidth : Nat) : Nat :=
  max (terminalWidth - (summaryWidth + 2)) 8

def showVectorRoute (limited : Bool) (length : Nat) : CornerSlice :=
  if limited && 20 < length then { front := 10, back := 10, truncated := true }
  else { front := length, back := 0, truncated := false }

def showNonemptyVector : Result Unit :=
  .error "_show_nonempty(::IO, ::AbstractVector, ::String) is not implemented"

def matrixLiteralCorners (rows columns : Nat) (limited : Bool) : CornerSlice × CornerSlice :=
  (if limited && 4 < rows then { front := 2, back := 2, truncated := true }
   else { front := rows, back := 0, truncated := false },
   if limited && 4 < columns then { front := 2, back := 2, truncated := true }
   else { front := columns, back := 0, truncated := false })

inductive TypeInfo where
  | unknown
  | bottom
  | array (element : String)
  | dict (key value : String)
  | set (element : String)
  deriving Repr, DecidableEq

def typeinfoElement : TypeInfo → Option String
  | .array element | .set element => some element
  | .dict key value => some ("Pair{" ++ key ++ "," ++ value ++ "}")
  | _ => none

def typeinfoElementCall (bottomWithArguments : Bool) (info : TypeInfo) : Result (Option String) :=
  if bottomWithArguments then .error "MethodError(typeinfo_eltype)" else .ok (typeinfoElement info)

def typeinfoImplicit (singleton kindOrTypeVar unionType : Bool) : Bool :=
  singleton || kindOrTypeVar || unionType

inductive TypePrefix where
  | implicit
  | explicit (text : String)
  deriving Repr, DecidableEq

def typeinfoPrefix (sameElement arrayLike implicit : Bool) (arrayType elementType : String) : TypePrefix :=
  if sameElement then .implicit
  else if arrayLike && implicit then .explicit arrayType
  else .explicit elementType

end JuliaLean.ErrorShow.Coverage


namespace JuliaLean.ErrorShow.ArrayshowFaithful

open JuliaLean.ErrorShow
open JuliaLean.ErrorShow.Coverage

abbrev R (α : Type) := Except String α

def centeredMark (width : Nat) (marker : String) : List String :=
  if width = 0 then [marker] else (List.replicate width " ").set (width / 2) marker

def maxAlignment (cells : List Alignment) : Alignment :=
  cells.foldl (fun current cell => { left := max current.left cell.left, right := max current.right cell.right })
    { left := 0, right := 0 }

def alignment (columns : List (List Alignment)) (completeWidth narrowWidth separator ncols : Nat) : List Alignment :=
  let collected := columns.foldl (fun output column =>
    let next := output ++ [maxAlignment column]
    if 1 < next.length && next.foldl (fun total item => total + item.left + item.right) 0 + separator * next.length ≥ completeWidth
      then output else next) []
  if 1 < collected.length && collected.length < ncols then
    collected.takeWhile (fun _ => collected.foldl (fun total item => total + item.left + item.right) 0 + separator * collected.length < narrowWidth)
  else collected

structure MatrixCell where
  text : String
  actual : Alignment
  assigned : Bool := true
  deriving Repr, DecidableEq

def printMatrixRow (targets : List Alignment) (cells : List MatrixCell) (separator : String) : String :=
  String.intercalate separator ((targets.zip cells).map fun (target, cell) =>
    let text := if cell.assigned then cell.text else "#undef"
    String.ofList (List.replicate (target.left - cell.actual.left) ' ') ++ text ++
      String.ofList (List.replicate (target.right - cell.actual.right) ' '))

def printMatrixVdots (widths : List Alignment) (dots separator : String) (modulus residue : Nat) (padRight : Bool) : String :=
  String.intercalate separator (widths.zipIdx.map fun (target, index) =>
    let width := target.left + target.right
    let content := if modulus != 0 && (index + 1) % modulus = residue then dots else ""
    if index + 1 = widths.length && !padRight then content
    else content ++ String.ofList (List.replicate (width - content.length) ' '))

structure MatrixPlan where
  rowFront : Nat
  rowBack : Nat
  columnFront : Nat
  columnBack : Nat
  verticalDots : Bool
  horizontalDots : Bool
  deriving Repr, DecidableEq

def printMatrixPlan (rows columns screenRows visibleColumns : Nat) (limited : Bool) : MatrixPlan :=
  let rowCut := limited && screenRows < rows
  let columnCut := limited && visibleColumns < columns
  { rowFront := if rowCut then screenRows / 2 else rows
    rowBack := if rowCut then (screenRows - 1) / 2 else 0
    columnFront := if columnCut then (visibleColumns + 1) / 2 else columns
    columnBack := if columnCut then visibleColumns / 2 else 0
    verticalDots := rowCut, horizontalDots := columnCut }

def printMatrix (rows columns screenRows visibleColumns : Nat) (limited : Bool) :=
  printMatrixPlan rows columns screenRows visibleColumns limited

def showNd (slices : List String) (showFull : Bool) : String :=
  if slices.isEmpty then "" else if showFull then String.intercalate "\n\n" slices else "[" ++ String.intercalate ";; " slices ++ "]"

def showNdCore (limited : Bool) (axisLengths indices : List Nat) (slice : String) : Option String :=
  if limited && (axisLengths.zip indices).any (fun (length, index) => 10 < length && 3 < index && index ≤ length - 3)
    then none else some slice

def showNdWrapper (limited : Bool) (axisLengths indices : List Nat) (slice : String) : Option String :=
  showNdCore limited axisLengths indices slice

def showNdLabel (indices : List String) : String := "[:, :, " ++ String.intercalate ", " indices ++ "] =\n"

inductive PrintArrayKind where | zeroDim | vecOrMat | higher deriving Repr, DecidableEq

def printArrayZero (assigned : Bool) (shown : String) : String := if assigned then shown else "#undef"

def printArrayVecOrMat (rows columns screenRows visibleColumns : Nat) (limited : Bool) :=
  printMatrix rows columns screenRows visibleColumns limited

def printArrayHigher (slices : List String) : String := showNd slices true

inductive PlainArrayRoute where | twoArg | summary | oneLine | content deriving Repr, DecidableEq

def showArrayPlainRoute (empty compact vector limited : Bool) (screenRows rank rows : Nat) : PlainArrayRoute :=
  if empty && (compact || vector) then .twoArg else if empty then .summary
  else if limited && (screenRows = 0 || (screenRows = 1 && (rank > 2 || rows > 1))) then .oneLine else .content

def showOnelineWidth (columns summaryWidth : Nat) : Nat := max (columns - (summaryWidth + 2)) 8

def showNonemptyMatrix (rows columns : Nat) (limited : Bool) : CornerSlice × CornerSlice :=
  (if limited && 4 < rows then { front := 2, back := 2, truncated := true } else { front := rows, back := 0, truncated := false },
   if limited && 4 < columns then { front := 2, back := 2, truncated := true } else { front := columns, back := 0, truncated := false })

def showNonemptyMatrixWrapper (rows columns : Nat) (limited : Bool) :=
  showNonemptyMatrix rows columns limited

def showNonemptyHigher (typePrefix ndOutput : String) := typePrefix ++ ndOutput

def showNonemptyVector : R Unit := .error "_show_nonempty(::IO, ::AbstractVector, ::String) is not implemented"

def showNonemptyZero (assigned : Bool) (shown : String) := printArrayZero assigned shown

def showEmptyArray (typeText : String) (dims : List Nat) := typeText ++ "(undef, " ++ String.intercalate ", " (dims.map toString) ++ ")"

def showEmptyAbstract (summary : String) := summary

inductive TwoArgArrayRoute where | zero | vector | empty | circular | nonempty deriving Repr, DecidableEq

def showArrayRoute (rank : Nat) (empty circular : Bool) : TwoArgArrayRoute :=
  if rank = 0 then .zero else if rank = 1 then .vector else if empty then .empty else if circular then .circular else .nonempty

def showZeroBit (value : Bool) := "BitArray(" ++ (if value then "1" else "0") ++ ")"

def showZeroArray (assigned : Bool) (typeText value : String) := if assigned then "fill(" ++ value ++ ")" else "Array{" ++ typeText ++ ", 0}(undef)"

def showVector (limited : Bool) (items : List String) : List String :=
  if limited && 20 < items.length then items.take 10 ++ ["…"] ++ items.drop (items.length - 10) else items

inductive TypeInfoM where | unknown | bottom | array (element : String) | dict (key value : String) | set (element : String) deriving Repr, DecidableEq

def typeinfoEltype : TypeInfoM → Option String
  | .array element | .set element => some element | .dict key value => some ("Pair{" ++ key ++ "," ++ value ++ "}") | _ => none

def typeinfoEltypeFallback (_typeinfo : String) : Option String := none

def typeinfoEltypeBottom (_unit : Unit) : Option String := none

def typeinfoBottomSlurp (_args : List String) : R Unit := .error "MethodError(typeinfo_eltype)"

def typeinfoImplicitInvoke (result : Bool) := result

def typeinfoImplicit (singleton kind typevar union : Bool) := singleton || kind || typevar || union

inductive TypePrefixM where | implicit | explicit (text : String) deriving Repr, DecidableEq

def typeinfoPrefix (sameEltype arrayType implicit : Bool) (arrayName elementName : String) : TypePrefixM :=
  if sameEltype then .implicit else if arrayType && implicit then .explicit arrayName else .explicit elementName

end JuliaLean.ErrorShow.ArrayshowFaithful

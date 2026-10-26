import JuliaLean.ErrorShow.Model
import JuliaLean.ErrorShow.Coverage

/-! Method-specific models for `base/arrayshow.jl` at `bbfa0ce4150`. -/

namespace JuliaLean.ErrorShow.ArrayshowFaithful

open JuliaLean.ErrorShow
open JuliaLean.ErrorShow.Coverage

abbrev R (α : Type) := Except String α

def centeredMark (width : Nat) (marker : String) : List String :=
  if width = 0 then [marker] else (List.replicate width " ").set (width / 2) marker
def CenteredMarkExact : Prop := ∀ width marker, centeredMark width marker =
  if width = 0 then [marker] else (List.replicate width " ").set (width / 2) marker
theorem centeredMarkExact : CenteredMarkExact := by unfold CenteredMarkExact; intros; rfl

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
def AlignmentExact : Prop := ∀ columns completeWidth narrowWidth separator ncols,
  alignment columns completeWidth narrowWidth separator ncols =
    let collected := columns.foldl (fun output column =>
      let next := output ++ [maxAlignment column]
      if 1 < next.length && next.foldl (fun total item => total + item.left + item.right) 0 + separator * next.length ≥ completeWidth
        then output else next) []
    if 1 < collected.length && collected.length < ncols then
      collected.takeWhile (fun _ => collected.foldl (fun total item => total + item.left + item.right) 0 + separator * collected.length < narrowWidth)
    else collected
theorem alignmentExact : AlignmentExact := by unfold AlignmentExact; intros; rfl

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
def PrintMatrixRowExact : Prop := ∀ targets cells separator,
  printMatrixRow targets cells separator =
    String.intercalate separator ((targets.zip cells).map fun (target, cell) =>
      let text := if cell.assigned then cell.text else "#undef"
      String.ofList (List.replicate (target.left - cell.actual.left) ' ') ++ text ++
        String.ofList (List.replicate (target.right - cell.actual.right) ' '))
theorem printMatrixRowExact : PrintMatrixRowExact := by unfold PrintMatrixRowExact; intros; rfl

def printMatrixVdots (widths : List Alignment) (dots separator : String) (modulus residue : Nat) (padRight : Bool) : String :=
  String.intercalate separator (widths.zipIdx.map fun (target, index) =>
    let width := target.left + target.right
    let content := if modulus != 0 && (index + 1) % modulus = residue then dots else ""
    if index + 1 = widths.length && !padRight then content
    else content ++ String.ofList (List.replicate (width - content.length) ' '))
def PrintMatrixVdotsExact : Prop := ∀ widths dots separator modulus residue padRight,
  printMatrixVdots widths dots separator modulus residue padRight =
    String.intercalate separator (widths.zipIdx.map fun (target, index) =>
      let width := target.left + target.right
      let content := if modulus != 0 && (index + 1) % modulus = residue then dots else ""
      if index + 1 = widths.length && !padRight then content
      else content ++ String.ofList (List.replicate (width - content.length) ' '))
theorem printMatrixVdotsExact : PrintMatrixVdotsExact := by unfold PrintMatrixVdotsExact; intros; rfl

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
def PrintMatrixPlanExact : Prop := ∀ rows columns screenRows visibleColumns limited,
  printMatrixPlan rows columns screenRows visibleColumns limited =
    let rowCut := limited && screenRows < rows; let columnCut := limited && visibleColumns < columns
    { rowFront := if rowCut then screenRows / 2 else rows, rowBack := if rowCut then (screenRows - 1) / 2 else 0,
      columnFront := if columnCut then (visibleColumns + 1) / 2 else columns,
      columnBack := if columnCut then visibleColumns / 2 else 0, verticalDots := rowCut, horizontalDots := columnCut }
theorem printMatrixPlanExact : PrintMatrixPlanExact := by unfold PrintMatrixPlanExact; intros; rfl

def printMatrix (rows columns screenRows visibleColumns : Nat) (limited : Bool) :=
  printMatrixPlan rows columns screenRows visibleColumns limited
def PrintMatrixExact : Prop := ∀ rows columns screenRows visibleColumns limited,
  printMatrix rows columns screenRows visibleColumns limited = printMatrixPlan rows columns screenRows visibleColumns limited
theorem printMatrixExact : PrintMatrixExact := by unfold PrintMatrixExact; intros; rfl

def showNd (slices : List String) (showFull : Bool) : String :=
  if slices.isEmpty then "" else if showFull then String.intercalate "\n\n" slices else "[" ++ String.intercalate ";; " slices ++ "]"
def ShowNdExact : Prop := ∀ slices showFull, showNd slices showFull =
  if slices.isEmpty then "" else if showFull then String.intercalate "\n\n" slices else "[" ++ String.intercalate ";; " slices ++ "]"
theorem showNdExact : ShowNdExact := by unfold ShowNdExact; intros; rfl

def showNdCore (limited : Bool) (axisLengths indices : List Nat) (slice : String) : Option String :=
  if limited && (axisLengths.zip indices).any (fun (length, index) => 10 < length && 3 < index && index ≤ length - 3)
    then none else some slice
def ShowNdCoreExact : Prop := ∀ limited axisLengths indices slice, showNdCore limited axisLengths indices slice =
  if limited && (axisLengths.zip indices).any (fun (length, index) => 10 < length && 3 < index && index ≤ length - 3)
    then none else some slice
theorem showNdCoreExact : ShowNdCoreExact := by unfold ShowNdCoreExact; intros; rfl

def showNdWrapper (limited : Bool) (axisLengths indices : List Nat) (slice : String) : Option String :=
  showNdCore limited axisLengths indices slice
def ShowNdWrapperExact : Prop := ∀ limited axisLengths indices slice,
  showNdWrapper limited axisLengths indices slice = showNdCore limited axisLengths indices slice
theorem showNdWrapperExact : ShowNdWrapperExact := by unfold ShowNdWrapperExact; intros; rfl

def showNdLabel (indices : List String) : String := "[:, :, " ++ String.intercalate ", " indices ++ "] =\n"
def ShowNdLabelExact : Prop := ∀ indices, showNdLabel indices = "[:, :, " ++ String.intercalate ", " indices ++ "] =\n"
theorem showNdLabelExact : ShowNdLabelExact := by unfold ShowNdLabelExact; intros; rfl

inductive PrintArrayKind where | zeroDim | vecOrMat | higher deriving Repr, DecidableEq
def printArrayZero (assigned : Bool) (shown : String) : String := if assigned then shown else "#undef"
def PrintArrayZeroExact : Prop := ∀ assigned shown, printArrayZero assigned shown = if assigned then shown else "#undef"
theorem printArrayZeroExact : PrintArrayZeroExact := by unfold PrintArrayZeroExact; intros; rfl
def printArrayVecOrMat (rows columns screenRows visibleColumns : Nat) (limited : Bool) :=
  printMatrix rows columns screenRows visibleColumns limited
def PrintArrayVecOrMatExact : Prop := ∀ rows columns screenRows visibleColumns limited,
  printArrayVecOrMat rows columns screenRows visibleColumns limited =
    printMatrix rows columns screenRows visibleColumns limited
theorem printArrayVecOrMatExact : PrintArrayVecOrMatExact := by unfold PrintArrayVecOrMatExact; intros; rfl
def printArrayHigher (slices : List String) : String := showNd slices true
def PrintArrayHigherExact : Prop := ∀ slices, printArrayHigher slices = showNd slices true
theorem printArrayHigherExact : PrintArrayHigherExact := by unfold PrintArrayHigherExact; intros; rfl

inductive PlainArrayRoute where | twoArg | summary | oneLine | content deriving Repr, DecidableEq
def showArrayPlainRoute (empty compact vector limited : Bool) (screenRows rank rows : Nat) : PlainArrayRoute :=
  if empty && (compact || vector) then .twoArg else if empty then .summary
  else if limited && (screenRows = 0 || (screenRows = 1 && (rank > 2 || rows > 1))) then .oneLine else .content
def ShowArrayPlainRouteExact : Prop := ∀ empty compact vector limited screenRows rank rows,
  showArrayPlainRoute empty compact vector limited screenRows rank rows =
    if empty && (compact || vector) then .twoArg else if empty then .summary
    else if limited && (screenRows = 0 || (screenRows = 1 && (rank > 2 || rows > 1))) then .oneLine else .content
theorem showArrayPlainRouteExact : ShowArrayPlainRouteExact := by unfold ShowArrayPlainRouteExact; intros; rfl

def showOnelineWidth (columns summaryWidth : Nat) : Nat := max (columns - (summaryWidth + 2)) 8
def ShowOnelineWidthExact : Prop := ∀ columns summaryWidth,
  showOnelineWidth columns summaryWidth = max (columns - (summaryWidth + 2)) 8
theorem showOnelineWidthExact : ShowOnelineWidthExact := by unfold ShowOnelineWidthExact; intros; rfl

def showNonemptyMatrix (rows columns : Nat) (limited : Bool) : CornerSlice × CornerSlice :=
  (if limited && 4 < rows then { front := 2, back := 2, truncated := true } else { front := rows, back := 0, truncated := false },
   if limited && 4 < columns then { front := 2, back := 2, truncated := true } else { front := columns, back := 0, truncated := false })
def ShowNonemptyMatrixExact : Prop := ∀ rows columns limited, showNonemptyMatrix rows columns limited =
  (if limited && 4 < rows then { front := 2, back := 2, truncated := true } else { front := rows, back := 0, truncated := false },
   if limited && 4 < columns then { front := 2, back := 2, truncated := true } else { front := columns, back := 0, truncated := false })
theorem showNonemptyMatrixExact : ShowNonemptyMatrixExact := by unfold ShowNonemptyMatrixExact; intros; rfl

def showNonemptyMatrixWrapper (rows columns : Nat) (limited : Bool) :=
  showNonemptyMatrix rows columns limited
def ShowNonemptyMatrixWrapperExact : Prop := ∀ rows columns limited,
  showNonemptyMatrixWrapper rows columns limited = showNonemptyMatrix rows columns limited
theorem showNonemptyMatrixWrapperExact : ShowNonemptyMatrixWrapperExact := by unfold ShowNonemptyMatrixWrapperExact; intros; rfl
def showNonemptyHigher (typePrefix ndOutput : String) := typePrefix ++ ndOutput
def ShowNonemptyHigherExact : Prop := ∀ typePrefix output, showNonemptyHigher typePrefix output = typePrefix ++ output
theorem showNonemptyHigherExact : ShowNonemptyHigherExact := by unfold ShowNonemptyHigherExact; intros; rfl
def showNonemptyVector : R Unit := .error "_show_nonempty(::IO, ::AbstractVector, ::String) is not implemented"
def ShowNonemptyVectorExact : Prop := ∀ _unit : Unit, showNonemptyVector = .error "_show_nonempty(::IO, ::AbstractVector, ::String) is not implemented"
theorem showNonemptyVectorExact : ShowNonemptyVectorExact := by unfold ShowNonemptyVectorExact; intros; rfl
def showNonemptyZero (assigned : Bool) (shown : String) := printArrayZero assigned shown
def ShowNonemptyZeroExact : Prop := ∀ assigned shown,
  showNonemptyZero assigned shown = printArrayZero assigned shown
theorem showNonemptyZeroExact : ShowNonemptyZeroExact := by unfold ShowNonemptyZeroExact; intros; rfl

def showEmptyArray (typeText : String) (dims : List Nat) := typeText ++ "(undef, " ++ String.intercalate ", " (dims.map toString) ++ ")"
def ShowEmptyArrayExact : Prop := ∀ typeText dims, showEmptyArray typeText dims = typeText ++ "(undef, " ++ String.intercalate ", " (dims.map toString) ++ ")"
theorem showEmptyArrayExact : ShowEmptyArrayExact := by unfold ShowEmptyArrayExact; intros; rfl
def showEmptyAbstract (summary : String) := summary
def ShowEmptyAbstractExact : Prop := ∀ summary, showEmptyAbstract summary = summary
theorem showEmptyAbstractExact : ShowEmptyAbstractExact := by unfold ShowEmptyAbstractExact; intros; rfl

inductive TwoArgArrayRoute where | zero | vector | empty | circular | nonempty deriving Repr, DecidableEq
def showArrayRoute (rank : Nat) (empty circular : Bool) : TwoArgArrayRoute :=
  if rank = 0 then .zero else if rank = 1 then .vector else if empty then .empty else if circular then .circular else .nonempty
def ShowArrayRouteExact : Prop := ∀ rank empty circular, showArrayRoute rank empty circular =
  if rank = 0 then .zero else if rank = 1 then .vector else if empty then .empty else if circular then .circular else .nonempty
theorem showArrayRouteExact : ShowArrayRouteExact := by unfold ShowArrayRouteExact; intros; rfl

def showZeroBit (value : Bool) := "BitArray(" ++ (if value then "1" else "0") ++ ")"
def ShowZeroBitExact : Prop := ∀ value, showZeroBit value = "BitArray(" ++ (if value then "1" else "0") ++ ")"
theorem showZeroBitExact : ShowZeroBitExact := by unfold ShowZeroBitExact; intros; rfl
def showZeroArray (assigned : Bool) (typeText value : String) := if assigned then "fill(" ++ value ++ ")" else "Array{" ++ typeText ++ ", 0}(undef)"
def ShowZeroArrayExact : Prop := ∀ assigned typeText value, showZeroArray assigned typeText value =
  if assigned then "fill(" ++ value ++ ")" else "Array{" ++ typeText ++ ", 0}(undef)"
theorem showZeroArrayExact : ShowZeroArrayExact := by unfold ShowZeroArrayExact; intros; rfl

def showVector (limited : Bool) (items : List String) : List String :=
  if limited && 20 < items.length then items.take 10 ++ ["…"] ++ items.drop (items.length - 10) else items
def ShowVectorExact : Prop := ∀ limited items, showVector limited items =
  if limited && 20 < items.length then items.take 10 ++ ["…"] ++ items.drop (items.length - 10) else items
theorem showVectorExact : ShowVectorExact := by unfold ShowVectorExact; intros; rfl

inductive TypeInfoM where | unknown | bottom | array (element : String) | dict (key value : String) | set (element : String) deriving Repr, DecidableEq
def typeinfoEltype : TypeInfoM → Option String
  | .array element | .set element => some element | .dict key value => some ("Pair{" ++ key ++ "," ++ value ++ "}") | _ => none
def typeinfoEltypeFallback (_typeinfo : String) : Option String := none
def TypeinfoEltypeFallbackExact : Prop := ∀ typeinfo, typeinfoEltypeFallback typeinfo = none
theorem typeinfoEltypeFallbackExact : TypeinfoEltypeFallbackExact := by unfold TypeinfoEltypeFallbackExact; intros; rfl
def typeinfoEltypeBottom (_unit : Unit) : Option String := none
def TypeinfoEltypeBottomExact : Prop := ∀ _unit : Unit, typeinfoEltypeBottom _unit = none
theorem typeinfoEltypeBottomExact : TypeinfoEltypeBottomExact := by unfold TypeinfoEltypeBottomExact; intros; rfl
def typeinfoBottomSlurp (_args : List String) : R Unit := .error "MethodError(typeinfo_eltype)"
def TypeinfoBottomSlurpExact : Prop := ∀ args, typeinfoBottomSlurp args = .error "MethodError(typeinfo_eltype)"
theorem typeinfoBottomSlurpExact : TypeinfoBottomSlurpExact := by unfold TypeinfoBottomSlurpExact; intros; rfl
def TypeinfoArrayExact : Prop := ∀ element, typeinfoEltype (.array element) = some element
theorem typeinfoArrayExact : TypeinfoArrayExact := by unfold TypeinfoArrayExact; intros; rfl
def TypeinfoDictExact : Prop := ∀ key value, typeinfoEltype (.dict key value) = some ("Pair{" ++ key ++ "," ++ value ++ "}")
theorem typeinfoDictExact : TypeinfoDictExact := by unfold TypeinfoDictExact; intros; rfl
def TypeinfoSetExact : Prop := ∀ element, typeinfoEltype (.set element) = some element
theorem typeinfoSetExact : TypeinfoSetExact := by unfold TypeinfoSetExact; intros; rfl
def typeinfoImplicitInvoke (result : Bool) := result
def TypeinfoImplicitInvokeExact : Prop := ∀ result, typeinfoImplicitInvoke result = result
theorem typeinfoImplicitInvokeExact : TypeinfoImplicitInvokeExact := by unfold TypeinfoImplicitInvokeExact; intros; rfl
def typeinfoImplicit (singleton kind typevar union : Bool) := singleton || kind || typevar || union
def TypeinfoImplicitExact : Prop := ∀ singleton kind typevar union, typeinfoImplicit singleton kind typevar union = (singleton || kind || typevar || union)
theorem typeinfoImplicitExact : TypeinfoImplicitExact := by unfold TypeinfoImplicitExact; intros; rfl
inductive TypePrefixM where | implicit | explicit (text : String) deriving Repr, DecidableEq
def typeinfoPrefix (sameEltype arrayType implicit : Bool) (arrayName elementName : String) : TypePrefixM :=
  if sameEltype then .implicit else if arrayType && implicit then .explicit arrayName else .explicit elementName
def TypeinfoPrefixExact : Prop := ∀ sameEltype arrayType implicit arrayName elementName, typeinfoPrefix sameEltype arrayType implicit arrayName elementName =
  if sameEltype then .implicit else if arrayType && implicit then .explicit arrayName else .explicit elementName
theorem typeinfoPrefixExact : TypeinfoPrefixExact := by unfold TypeinfoPrefixExact; intros; rfl

end JuliaLean.ErrorShow.ArrayshowFaithful

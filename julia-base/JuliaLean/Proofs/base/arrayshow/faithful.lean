import JuliaLean.base.arrayshow
import JuliaLean.Proofs.base.arrayshow.retainedCoverage

/-! Method-specific models for `base/arrayshow.jl` at `bbfa0ce4150`. -/

namespace JuliaLean.ErrorShow.ArrayshowFaithful

open JuliaLean.ErrorShow
open JuliaLean.ErrorShow.Coverage


def CenteredMarkExact : Prop := ∀ width marker, centeredMark width marker =
  if width = 0 then [marker] else (List.replicate width " ").set (width / 2) marker
theorem centeredMarkExact : CenteredMarkExact := by unfold CenteredMarkExact; intros; rfl


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

def PrintMatrixRowExact : Prop := ∀ targets cells separator,
  printMatrixRow targets cells separator =
    String.intercalate separator ((targets.zip cells).map fun (target, cell) =>
      let text := if cell.assigned then cell.text else "#undef"
      String.ofList (List.replicate (target.left - cell.actual.left) ' ') ++ text ++
        String.ofList (List.replicate (target.right - cell.actual.right) ' '))
theorem printMatrixRowExact : PrintMatrixRowExact := by unfold PrintMatrixRowExact; intros; rfl

def PrintMatrixVdotsExact : Prop := ∀ widths dots separator modulus residue padRight,
  printMatrixVdots widths dots separator modulus residue padRight =
    String.intercalate separator (widths.zipIdx.map fun (target, index) =>
      let width := target.left + target.right
      let content := if modulus != 0 && (index + 1) % modulus = residue then dots else ""
      if index + 1 = widths.length && !padRight then content
      else content ++ String.ofList (List.replicate (width - content.length) ' '))
theorem printMatrixVdotsExact : PrintMatrixVdotsExact := by unfold PrintMatrixVdotsExact; intros; rfl

def PrintMatrixPlanExact : Prop := ∀ rows columns screenRows visibleColumns limited,
  printMatrixPlan rows columns screenRows visibleColumns limited =
    let rowCut := limited && screenRows < rows; let columnCut := limited && visibleColumns < columns
    { rowFront := if rowCut then screenRows / 2 else rows, rowBack := if rowCut then (screenRows - 1) / 2 else 0,
      columnFront := if columnCut then (visibleColumns + 1) / 2 else columns,
      columnBack := if columnCut then visibleColumns / 2 else 0, verticalDots := rowCut, horizontalDots := columnCut }
theorem printMatrixPlanExact : PrintMatrixPlanExact := by unfold PrintMatrixPlanExact; intros; rfl

def PrintMatrixExact : Prop := ∀ rows columns screenRows visibleColumns limited,
  printMatrix rows columns screenRows visibleColumns limited = printMatrixPlan rows columns screenRows visibleColumns limited
theorem printMatrixExact : PrintMatrixExact := by unfold PrintMatrixExact; intros; rfl

def ShowNdExact : Prop := ∀ slices showFull, showNd slices showFull =
  if slices.isEmpty then "" else if showFull then String.intercalate "\n\n" slices else "[" ++ String.intercalate ";; " slices ++ "]"
theorem showNdExact : ShowNdExact := by unfold ShowNdExact; intros; rfl

def ShowNdCoreExact : Prop := ∀ limited axisLengths indices slice, showNdCore limited axisLengths indices slice =
  if limited && (axisLengths.zip indices).any (fun (length, index) => 10 < length && 3 < index && index ≤ length - 3)
    then none else some slice
theorem showNdCoreExact : ShowNdCoreExact := by unfold ShowNdCoreExact; intros; rfl

def ShowNdWrapperExact : Prop := ∀ limited axisLengths indices slice,
  showNdWrapper limited axisLengths indices slice = showNdCore limited axisLengths indices slice
theorem showNdWrapperExact : ShowNdWrapperExact := by unfold ShowNdWrapperExact; intros; rfl

def ShowNdLabelExact : Prop := ∀ indices, showNdLabel indices = "[:, :, " ++ String.intercalate ", " indices ++ "] =\n"
theorem showNdLabelExact : ShowNdLabelExact := by unfold ShowNdLabelExact; intros; rfl

def PrintArrayZeroExact : Prop := ∀ assigned shown, printArrayZero assigned shown = if assigned then shown else "#undef"
theorem printArrayZeroExact : PrintArrayZeroExact := by unfold PrintArrayZeroExact; intros; rfl
def PrintArrayVecOrMatExact : Prop := ∀ rows columns screenRows visibleColumns limited,
  printArrayVecOrMat rows columns screenRows visibleColumns limited =
    printMatrix rows columns screenRows visibleColumns limited
theorem printArrayVecOrMatExact : PrintArrayVecOrMatExact := by unfold PrintArrayVecOrMatExact; intros; rfl
def PrintArrayHigherExact : Prop := ∀ slices, printArrayHigher slices = showNd slices true
theorem printArrayHigherExact : PrintArrayHigherExact := by unfold PrintArrayHigherExact; intros; rfl

def ShowArrayPlainRouteExact : Prop := ∀ empty compact vector limited screenRows rank rows,
  showArrayPlainRoute empty compact vector limited screenRows rank rows =
    if empty && (compact || vector) then .twoArg else if empty then .summary
    else if limited && (screenRows = 0 || (screenRows = 1 && (rank > 2 || rows > 1))) then .oneLine else .content
theorem showArrayPlainRouteExact : ShowArrayPlainRouteExact := by unfold ShowArrayPlainRouteExact; intros; rfl

def ShowOnelineWidthExact : Prop := ∀ columns summaryWidth,
  showOnelineWidth columns summaryWidth = max (columns - (summaryWidth + 2)) 8
theorem showOnelineWidthExact : ShowOnelineWidthExact := by unfold ShowOnelineWidthExact; intros; rfl

def ShowNonemptyMatrixExact : Prop := ∀ rows columns limited, showNonemptyMatrix rows columns limited =
  (if limited && 4 < rows then { front := 2, back := 2, truncated := true } else { front := rows, back := 0, truncated := false },
   if limited && 4 < columns then { front := 2, back := 2, truncated := true } else { front := columns, back := 0, truncated := false })
theorem showNonemptyMatrixExact : ShowNonemptyMatrixExact := by unfold ShowNonemptyMatrixExact; intros; rfl

def ShowNonemptyMatrixWrapperExact : Prop := ∀ rows columns limited,
  showNonemptyMatrixWrapper rows columns limited = showNonemptyMatrix rows columns limited
theorem showNonemptyMatrixWrapperExact : ShowNonemptyMatrixWrapperExact := by unfold ShowNonemptyMatrixWrapperExact; intros; rfl
def ShowNonemptyHigherExact : Prop := ∀ typePrefix output, showNonemptyHigher typePrefix output = typePrefix ++ output
theorem showNonemptyHigherExact : ShowNonemptyHigherExact := by unfold ShowNonemptyHigherExact; intros; rfl
def ShowNonemptyVectorExact : Prop := ∀ _unit : Unit, showNonemptyVector = .error "_show_nonempty(::IO, ::AbstractVector, ::String) is not implemented"
theorem showNonemptyVectorExact : ShowNonemptyVectorExact := by unfold ShowNonemptyVectorExact; intros; rfl
def ShowNonemptyZeroExact : Prop := ∀ assigned shown,
  showNonemptyZero assigned shown = printArrayZero assigned shown
theorem showNonemptyZeroExact : ShowNonemptyZeroExact := by unfold ShowNonemptyZeroExact; intros; rfl

def ShowEmptyArrayExact : Prop := ∀ typeText dims, showEmptyArray typeText dims = typeText ++ "(undef, " ++ String.intercalate ", " (dims.map toString) ++ ")"
theorem showEmptyArrayExact : ShowEmptyArrayExact := by unfold ShowEmptyArrayExact; intros; rfl
def ShowEmptyAbstractExact : Prop := ∀ summary, showEmptyAbstract summary = summary
theorem showEmptyAbstractExact : ShowEmptyAbstractExact := by unfold ShowEmptyAbstractExact; intros; rfl

def ShowArrayRouteExact : Prop := ∀ rank empty circular, showArrayRoute rank empty circular =
  if rank = 0 then .zero else if rank = 1 then .vector else if empty then .empty else if circular then .circular else .nonempty
theorem showArrayRouteExact : ShowArrayRouteExact := by unfold ShowArrayRouteExact; intros; rfl

def ShowZeroBitExact : Prop := ∀ value, showZeroBit value = "BitArray(" ++ (if value then "1" else "0") ++ ")"
theorem showZeroBitExact : ShowZeroBitExact := by unfold ShowZeroBitExact; intros; rfl
def ShowZeroArrayExact : Prop := ∀ assigned typeText value, showZeroArray assigned typeText value =
  if assigned then "fill(" ++ value ++ ")" else "Array{" ++ typeText ++ ", 0}(undef)"
theorem showZeroArrayExact : ShowZeroArrayExact := by unfold ShowZeroArrayExact; intros; rfl

def ShowVectorExact : Prop := ∀ limited items, showVector limited items =
  if limited && 20 < items.length then items.take 10 ++ ["…"] ++ items.drop (items.length - 10) else items
theorem showVectorExact : ShowVectorExact := by unfold ShowVectorExact; intros; rfl

def TypeinfoEltypeFallbackExact : Prop := ∀ typeinfo, typeinfoEltypeFallback typeinfo = none
theorem typeinfoEltypeFallbackExact : TypeinfoEltypeFallbackExact := by unfold TypeinfoEltypeFallbackExact; intros; rfl
def TypeinfoEltypeBottomExact : Prop := ∀ _unit : Unit, typeinfoEltypeBottom _unit = none
theorem typeinfoEltypeBottomExact : TypeinfoEltypeBottomExact := by unfold TypeinfoEltypeBottomExact; intros; rfl
def TypeinfoBottomSlurpExact : Prop := ∀ args, typeinfoBottomSlurp args = .error "MethodError(typeinfo_eltype)"
theorem typeinfoBottomSlurpExact : TypeinfoBottomSlurpExact := by unfold TypeinfoBottomSlurpExact; intros; rfl
def TypeinfoArrayExact : Prop := ∀ element, typeinfoEltype (.array element) = some element
theorem typeinfoArrayExact : TypeinfoArrayExact := by unfold TypeinfoArrayExact; intros; rfl
def TypeinfoDictExact : Prop := ∀ key value, typeinfoEltype (.dict key value) = some ("Pair{" ++ key ++ "," ++ value ++ "}")
theorem typeinfoDictExact : TypeinfoDictExact := by unfold TypeinfoDictExact; intros; rfl
def TypeinfoSetExact : Prop := ∀ element, typeinfoEltype (.set element) = some element
theorem typeinfoSetExact : TypeinfoSetExact := by unfold TypeinfoSetExact; intros; rfl
def TypeinfoImplicitInvokeExact : Prop := ∀ result, typeinfoImplicitInvoke result = result
theorem typeinfoImplicitInvokeExact : TypeinfoImplicitInvokeExact := by unfold TypeinfoImplicitInvokeExact; intros; rfl
def TypeinfoImplicitExact : Prop := ∀ singleton kind typevar union, typeinfoImplicit singleton kind typevar union = (singleton || kind || typevar || union)
theorem typeinfoImplicitExact : TypeinfoImplicitExact := by unfold TypeinfoImplicitExact; intros; rfl
def TypeinfoPrefixExact : Prop := ∀ sameEltype arrayType implicit arrayName elementName, typeinfoPrefix sameEltype arrayType implicit arrayName elementName =
  if sameEltype then .implicit else if arrayType && implicit then .explicit arrayName else .explicit elementName
theorem typeinfoPrefixExact : TypeinfoPrefixExact := by unfold TypeinfoPrefixExact; intros; rfl

end JuliaLean.ErrorShow.ArrayshowFaithful

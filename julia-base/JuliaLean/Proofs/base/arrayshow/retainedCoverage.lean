import JuliaLean.base.arrayshow


namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

def ArrayHelpersExact : Prop :=
  (∀ width marker, centeredMarker width marker =
    if width = 0 then [marker]
    else (List.replicate width " ").set (width / 2) marker) ∧
  (∀ rows columns limited,
    matrixLiteralCorners rows columns limited =
      (if limited && 4 < rows then { front := 2, back := 2, truncated := true }
       else { front := rows, back := 0, truncated := false },
       if limited && 4 < columns then { front := 2, back := 2, truncated := true }
       else { front := columns, back := 0, truncated := false })) ∧
  (∀ widths dots separator modulus residue padRight,
    verticalDots widths dots separator modulus residue padRight =
      widths.zipIdx.map fun (alignment, index) =>
        let width := alignment.left + alignment.right
        let content := if modulus != 0 && (index + 1) % modulus = residue then dots else ""
        if index + 1 = widths.length && !padRight then content
        else content ++ String.ofList (List.replicate (width - content.length) ' ') ++
          (if index + 1 < widths.length then separator else "")) ∧
  (∀ limited axisLength index,
    ndSliceShown limited axisLength index =
      (!limited || axisLength ≤ 10 || index ≤ 3 || axisLength - 3 < index)) ∧
  (∀ empty showFull,
    showNdRoute empty showFull =
      if empty then "empty" else if showFull then "label-and-matrix" else "literal-slices") ∧
  (∀ summaryWidth terminalWidth,
    oneLineTruncated summaryWidth terminalWidth =
      max (terminalWidth - (summaryWidth + 2)) 8) ∧
  (∀ limited length,
    showVectorRoute limited length =
      if limited && 20 < length then { front := 10, back := 10, truncated := true }
      else { front := length, back := 0, truncated := false }) ∧
  showNonemptyVector =
    .error "_show_nonempty(::IO, ::AbstractVector, ::String) is not implemented"

theorem arrayHelpersExact : ArrayHelpersExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ArrayTypeInfoExact : Prop :=
  (∀ info : TypeInfo, typeinfoElement info =
    match info with
    | .array element | .set element => some element
    | .dict key value => some ("Pair{" ++ key ++ "," ++ value ++ "}")
    | _ => none) ∧
  (∀ bottomWithArguments info,
    typeinfoElementCall bottomWithArguments info =
      if bottomWithArguments then .error "MethodError(typeinfo_eltype)"
      else .ok (typeinfoElement info)) ∧
  (∀ singleton kindOrTypeVar unionType,
    typeinfoImplicit singleton kindOrTypeVar unionType =
      (singleton || kindOrTypeVar || unionType)) ∧
  (∀ sameElement arrayLike implicit arrayType elementType,
    typeinfoPrefix sameElement arrayLike implicit arrayType elementType =
      if sameElement then .implicit
      else if arrayLike && implicit then .explicit arrayType
      else .explicit elementType)

theorem arrayTypeInfoExact : ArrayTypeInfoExact := by
  constructor
  · intro info; cases info <;> rfl
  constructor
  · intros; rfl
  constructor <;> intros <;> rfl

end JuliaLean.ErrorShow.Coverage

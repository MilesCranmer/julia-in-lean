import JuliaLean.ErrorShow.Props

namespace JuliaLean.ErrorShow

@[simp] theorem commaPieces_payloads : ∀ values : List String,
    emittedPayloads (commaPieces values) = values
  | [] => rfl
  | [_] => rfl
  | first :: second :: rest => by
      change first :: emittedPayloads (commaPieces (second :: rest)) = first :: second :: rest
      rw [commaPieces_payloads]

@[simp] theorem emittedPayloads_append (left right : List Piece) :
    emittedPayloads (left ++ right) = emittedPayloads left ++ emittedPayloads right := by
  induction left with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [emittedPayloads, ih]

@[simp] theorem emittedPayloads_payload_map (values : List String) :
    emittedPayloads (values.map Piece.payload) = values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [emittedPayloads, ih]

theorem baseExceptionRendering_proven : BaseExceptionRendering := by
  constructor
  · intro error
    cases error <;> simp [renderPieces, errorPayloads, emittedPayloads]
    case parse messageRepr detail => cases detail <;> rfl
    case typeName unionComponentsDiffer => cases unionComponentsDiffer <;> rfl
    case bounds summary indices =>
      cases indices <;> simp [emittedPayloads]
    case domain value message => cases message <;> rfl
    case system sysPrefix errorText extra => cases extra <;> rfl
    case undefVar name scope =>
      cases scope with
      | none => rfl
      | some scope => cases scope <;> rfl
    case inexact functionName typeName typeRepr firstArgument moreArguments =>
      by_cases same : typeName = functionName
      · simp [same, emittedPayloads]
      · simp [same, emittedPayloads]
  · intro error
    exact ⟨renderError error, rfl⟩

theorem fallbackShowAgreement_proven : FallbackShowAgreement := by
  intro shown
  simp [renderError, renderPieces, concatenate, Piece.text]

theorem boundsAndDimensionMessages_proven : BoundsAndDimensionMessages := by
  constructor
  · intro summary indices
    cases indices <;> rfl
  · intro message
    rfl

theorem methodCandidateListing_proven : MethodCandidateListing := by
  intro candidates
  constructor
  · rfl
  constructor
  · exact List.length_take_le 3 (sortCandidates candidates)
  · rfl

theorem methodDisplayModes_proven : MethodDisplayModes := by
  intro method
  simp [showMethod]

theorem matrixColumnAlignment_proven : MatrixColumnAlignment := by
  intro column cell left right
  simp [paddedWidth, Nat.sub_add_cancel left]
  omega

theorem matrixCornerTruncation_proven : MatrixCornerTruncation := by
  constructor
  · intro rows screenRows truncated
    simp [rowCorners, truncated]
  · intro columns visible truncated
    simp [columnCorners, truncated]

theorem printArrayRoutes_proven : PrintArrayRoutes := by
  constructor
  · intro compact screenRows
    simp [arrayRoute]
  constructor
  · intro rank rows screenRows compact limited
    simp [arrayRoute]
  constructor
  · intro rank rows screenRows limited
    simp [arrayRoute]
  · intro rank rows screenRows
    simp [arrayRoute]

theorem stackLookupAndRemoval_proven : StackLookupAndRemoval := by
  constructor
  · intro frames
    rfl
  constructor
  · intro frames
    rfl
  · intro stack names
    rfl

theorem currentExceptionStackExact_proven : CurrentExceptionStackExact := by
  constructor
  · intro rawNewestFirst
    rfl
  constructor
  · intro rootToCurrent
    rfl
  constructor
  · intro rootToCurrent exception
    rfl
  · intro prior current replacement
    simp [applyExceptionAction]

theorem assertMessageConstruction_proven : AssertMessageConstruction := by
  intro conditionText rendered
  simp [assertResult, AssertMessage.text]

theorem mimeConstructionAndPrinting_proven : MimeConstructionAndPrinting := by
  intro text
  simp [makeMime, printMime, showMime]

theorem showableAndDisplayable_proven : ShowableAndDisplayable := by
  constructor
  · intro hasShowMethod
    rfl
  constructor
  · intro stack mime
    rfl
  · intro stack mime
    rfl

end JuliaLean.ErrorShow

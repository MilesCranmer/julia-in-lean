import JuliaLean.base.errorshow
import JuliaLean.Proofs.base.errorshow.payloads


namespace JuliaLean.ErrorShow


def BaseExceptionRendering : Prop :=
  (∀ error : ErrorView,
    emittedPayloads (renderPieces error) = errorPayloads error) ∧
  (∀ error : ErrorView, ∃ output : String, renderError error = output)

def FallbackShowAgreement : Prop := ∀ shown : String,
  renderError (.fallback shown) = shown

def BoundsAndDimensionMessages : Prop :=
  (∀ summary : String, ∀ indices : List String,
    renderPieces (.bounds summary indices) =
      if indices.isEmpty then [.literal "BoundsError: attempt to access ", .payload summary]
      else [.literal "BoundsError: attempt to access ", .payload summary,
        .literal " at index ["] ++ commaPieces indices ++ [.literal "]"]) ∧
  (∀ message : String,
    renderPieces (.message .dimension message) =
      [.literal "DimensionMismatch: ", .payload message])

def MethodCandidateListing : Prop := ∀ candidates : List Candidate,
  closestCandidates candidates = (sortCandidates candidates).take 3 ∧
    (closestCandidates candidates).length ≤ 3 ∧
    candidatesTruncated candidates = decide (candidates.length > 3)

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

end JuliaLean.ErrorShow

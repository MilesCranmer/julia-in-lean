import JuliaLean.ErrorShow.Model

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

def MethodDisplayModes : Prop := ∀ method : MethodView,
  showMethod method true false = methodSignature method ++ " " ++ method.location ∧
    showMethod method false false = methodSignature method ++ "\n    " ++ method.location ∧
    showMethod method false true = methodSignature method

def MatrixColumnAlignment : Prop := ∀ column cell : Alignment,
  cell.left ≤ column.left → cell.right ≤ column.right →
    paddedWidth column cell = column.left + column.right

def MatrixCornerTruncation : Prop :=
  (∀ rows screenRows : Nat, screenRows < rows →
    rowCorners rows screenRows true =
      { front := screenRows / 2, back := (screenRows - 1) / 2, truncated := true }) ∧
  (∀ columns visible : Nat, visible < columns →
    columnCorners columns visible =
      { front := (visible + 1) / 2, back := visible / 2, truncated := true })

def PrintArrayRoutes : Prop :=
  (∀ compact : Bool, ∀ screenRows : Nat,
    arrayRoute 0 1 false false compact false screenRows = .zeroDimensional) ∧
  (∀ rank rows screenRows : Nat, ∀ compact limited : Bool,
    arrayRoute rank rows true true compact limited screenRows = .twoArgumentShow) ∧
  (∀ rank rows screenRows : Nat, ∀ limited : Bool,
    arrayRoute rank rows false true true limited screenRows = .twoArgumentShow) ∧
  (∀ rank rows screenRows : Nat,
    arrayRoute rank rows false true false false screenRows = .summaryOnly)

def StackLookupAndRemoval : Prop :=
  (∀ frames : List Frame, lookupFrames (.raw frames) = frames) ∧
  (∀ frames : List Frame, lookupFrames (.debugTraversal frames) = frames.reverse) ∧
  (∀ stack : List Frame, ∀ names : List String,
    removeFrames stack names =
      (stack.reverse.takeWhile fun frame => !names.contains frame.functionName).reverse)

def CurrentExceptionStackExact : Prop :=
  (∀ rawNewestFirst : List String,
    currentExceptions rawNewestFirst = rawNewestFirst.reverse) ∧
  (∀ rootToCurrent : List String,
    applyExceptionAction rootToCurrent .rethrowCurrent = rootToCurrent) ∧
  (∀ rootToCurrent : List String, ∀ exception : String,
    applyExceptionAction rootToCurrent (.throwNew exception) = rootToCurrent ++ [exception]) ∧
  (∀ prior : List String, ∀ current replacement : String,
    applyExceptionAction (prior ++ [current]) (.rethrowOther replacement) =
      prior ++ [replacement])

def AssertMessageConstruction : Prop := ∀ conditionText rendered : String,
  assertResult false (.default conditionText) = some ("AssertionError: " ++ conditionText) ∧
    assertResult false (.supplied rendered) = some ("AssertionError: " ++ rendered) ∧
    assertResult true (.supplied rendered) = none

def MimeConstructionAndPrinting : Prop := ∀ text : String,
  makeMime text = text ∧ printMime (makeMime text) = text ∧
    showMime (makeMime text) = "MIME type " ++ text

def ShowableAndDisplayable : Prop :=
  (∀ hasShowMethod : Bool, showable hasShowMethod = hasShowMethod) ∧
  (∀ stack : List DisplayBackend, ∀ mime : Mime,
    displayable stack mime = stack.any (fun backend => backend.supported.contains mime)) ∧
  (∀ stack : List DisplayBackend, ∀ mime : Mime,
    topDisplay stack mime = stack.reverse.find? (fun backend => backend.supported.contains mime))

end JuliaLean.ErrorShow

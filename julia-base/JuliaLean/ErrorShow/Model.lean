import JuliaLean.Core

/-!
Executable models for the formatting and control-flow decisions in
`base/errorshow.jl`, `base/methodshow.jl`, `base/arrayshow.jl`,
`base/stacktraces.jl`, `base/error.jl`, and `base/multimedia.jl` at
Julia `bbfa0ce4150`.

Values whose own `show` methods are outside this area enter the model as their
already-rendered text. This keeps the model focused on the separators, ordering,
selection, and dispatch performed by these six files.
-/

namespace JuliaLean.ErrorShow

/-! ### Exception rendering -/

inductive Piece where
  | literal (text : String)
  | payload (text : String)
  deriving Repr, DecidableEq

def Piece.text : Piece → String
  | .literal text | .payload text => text

def concatenate (pieces : List Piece) : String :=
  String.intercalate "" (pieces.map Piece.text)

def emittedPayloads : List Piece → List String
  | [] => []
  | .literal _ :: rest => emittedPayloads rest
  | .payload text :: rest => text :: emittedPayloads rest

inductive FixedError where
  | divide
  | stackOverflow
  | undefRef
  | eof
  | interrupt
  deriving Repr, DecidableEq

def FixedError.text : FixedError → String
  | .divide => "DivideError: integer division error"
  | .stackOverflow => "StackOverflowError:"
  | .undefRef => "UndefRefError: access to undefined reference"
  | .eof => "EOFError: read end of file"
  | .interrupt => "InterruptException:"

inductive MessageError where
  | error
  | argument
  | dimension
  | assertion
  | overflow
  deriving Repr, DecidableEq

def MessageError.prefix : MessageError → String
  | .error => ""
  | .argument => "ArgumentError: "
  | .dimension => "DimensionMismatch: "
  | .assertion => "AssertionError: "
  | .overflow => "OverflowError: "

def commaPieces : List String → List Piece
  | [] => []
  | [value] => [.payload value]
  | value :: rest => .payload value :: .literal ", " :: commaPieces rest

inductive UndefScope where
  | moduleName (rendered : String)
  | staticParameter
  | localKind (rendered : String)
  deriving Repr, DecidableEq

inductive ErrorView where
  | fallback (shown : String)
  | parse (messageRepr : String) (detail : Option String)
  | typeName (unionComponentsDiffer : Bool)
  | bareBounds
  | bounds (summary : String) (indices : List String)
  | typeErrorBoolean (gotType : String)
  | typeErrorDictKey (gotRepr expected : String)
  | typeError (context expected got : String)
  | load (inner file line : String)
  | init (inner moduleName : String)
  | domain (value : String) (message : Option String)
  | system (sysPrefix errorText : String) (extra : Option String)
  | fixed (kind : FixedError)
  | message (kind : MessageError) (message : String)
  | key (keyRepr : String)
  | undefKeyword (name : String)
  | undefVar (name : String) (scope : Option UndefScope)
  | inexact (functionName typeName typeRepr firstArgument : String)
      (moreArguments : List String)
  | canonicalIndex (functionName typeRepr : String)
  | method (signature : String) (hints candidates : List String)
  | field (typeRepr fieldName : String) (hint : Option String)
  deriving Repr, DecidableEq

/-- The output-producing calls of the `showerror` methods at
`base/errorshow.jl:30-443`. Error-hint callbacks enter as rendered strings. -/
def renderPieces : ErrorView → List Piece
  | .fallback shown => [.payload shown]
  | .parse messageRepr none => [.literal "ParseError(", .payload messageRepr, .literal ")"]
  | .parse _ (some detail) => [.payload detail]
  | .typeName true =>
      [.literal "TypeNameError: typename does not apply to unions whose components have different typenames"]
  | .typeName false => [.literal "TypeNameError: typename does not apply to this type"]
  | .bareBounds => [.literal "BoundsError"]
  | .bounds summary [] => [.literal "BoundsError: attempt to access ", .payload summary]
  | .bounds summary indices =>
      [.literal "BoundsError: attempt to access ", .payload summary, .literal " at index ["] ++
        commaPieces indices ++ [.literal "]"]
  | .typeErrorBoolean gotType =>
      [.literal "TypeError: non-boolean (", .payload gotType,
       .literal ") used in boolean context"]
  | .typeErrorDictKey gotRepr expected =>
      [.literal "TypeError: ", .payload gotRepr,
       .literal " is not a valid key for type ", .payload expected]
  | .typeError context expected got =>
      [.literal "TypeError: ", .payload context, .literal ", expected ", .payload expected,
       .literal ", got ", .payload got]
  | .load inner file line =>
      [.literal "LoadError: ", .payload inner, .literal "\nin expression starting at ",
       .payload file, .literal ":", .payload line]
  | .init inner moduleName =>
      [.literal "InitError: ", .payload inner, .literal "\nduring initialization of module ",
       .payload moduleName]
  | .domain value none => [.literal "DomainError with ", .payload value]
  | .domain value (some message) =>
      [.literal "DomainError with ", .payload value, .literal ":\n", .payload message]
  | .system sysPrefix errorText none =>
      [.literal "SystemError: ", .payload sysPrefix, .literal ": ", .payload errorText]
  | .system sysPrefix errorText (some extra) =>
      [.literal "SystemError (with ", .payload extra, .literal "): ", .payload sysPrefix,
       .literal ": ", .payload errorText]
  | .fixed kind => [.literal kind.text]
  | .message kind message => [.literal kind.prefix, .payload message]
  | .key keyRepr => [.literal "KeyError: key ", .payload keyRepr, .literal " not found"]
  | .undefKeyword name =>
      [.literal "UndefKeywordError: keyword argument `", .payload name, .literal "` not assigned"]
  | .undefVar name none => [.literal "UndefVarError: `", .payload name, .literal "` not defined"]
  | .undefVar name (some (.moduleName scope)) =>
      [.literal "UndefVarError: `", .payload name, .literal "` not defined in `",
       .payload scope, .literal "`"]
  | .undefVar name (some .staticParameter) =>
      [.literal "UndefVarError: `", .payload name,
       .literal "` not defined in static parameter matching"]
  | .undefVar name (some (.localKind scope)) =>
      [.literal "UndefVarError: `", .payload name, .literal "` not defined in ",
       .payload scope, .literal " scope"]
  | .inexact functionName typeName typeRepr firstArgument moreArguments =>
      [.literal "InexactError: ", .payload functionName, .literal "("] ++
        (if typeName == functionName then [] else [.payload typeRepr, .literal ", "]) ++
        commaPieces (firstArgument :: moreArguments) ++ [.literal ")"]
  | .canonicalIndex functionName typeRepr =>
      [.literal "CanonicalIndexError: ", .payload functionName,
       .literal " not defined for ", .payload typeRepr]
  | .method signature hints candidates =>
      [.literal "MethodError: no method matching ", .payload signature] ++
        hints.map Piece.payload ++ candidates.map Piece.payload
  | .field typeRepr fieldName hint =>
      [.literal "FieldError: type ", .payload typeRepr, .literal " has no field `",
       .payload fieldName, .literal "`"] ++ hint.toList.map Piece.payload

def renderError (error : ErrorView) : String := concatenate (renderPieces error)

def errorPayloads : ErrorView → List String
  | .fallback shown => [shown]
  | .parse messageRepr none => [messageRepr]
  | .parse _ (some detail) => [detail]
  | .typeName _ => []
  | .bareBounds => []
  | .bounds summary indices => summary :: indices
  | .typeErrorBoolean gotType => [gotType]
  | .typeErrorDictKey gotRepr expected => [gotRepr, expected]
  | .typeError context expected got => [context, expected, got]
  | .load inner file line => [inner, file, line]
  | .init inner moduleName => [inner, moduleName]
  | .domain value none => [value]
  | .domain value (some message) => [value, message]
  | .system sysPrefix errorText none => [sysPrefix, errorText]
  | .system sysPrefix errorText (some extra) => [extra, sysPrefix, errorText]
  | .fixed _ => []
  | .message _ message => [message]
  | .key keyRepr => [keyRepr]
  | .undefKeyword name => [name]
  | .undefVar name none => [name]
  | .undefVar name (some (.moduleName scope)) => [name, scope]
  | .undefVar name (some .staticParameter) => [name]
  | .undefVar name (some (.localKind scope)) => [name, scope]
  | .inexact functionName typeName typeRepr firstArgument moreArguments =>
      functionName :: (if typeName == functionName then [] else [typeRepr]) ++
        firstArgument :: moreArguments
  | .canonicalIndex functionName typeRepr => [functionName, typeRepr]
  | .method signature hints candidates => signature :: hints ++ candidates
  | .field typeRepr fieldName hint => [typeRepr, fieldName] ++ hint.toList

/-! ### Method display and MethodError candidates -/

structure Candidate where
  text : String
  score : Int
  deriving Repr, DecidableEq

def insertCandidate (candidate : Candidate) : List Candidate → List Candidate
  | [] => [candidate]
  | head :: tail =>
      if candidate.score ≤ head.score then candidate :: head :: tail
      else head :: insertCandidate candidate tail

def sortCandidates (candidates : List Candidate) : List Candidate :=
  candidates.foldr insertCandidate []

/-- `show_method_candidates`, `base/errorshow.jl:656-865`, sorts ascending by
the negated match score and prints at most three candidates. -/
def closestCandidates (candidates : List Candidate) : List Candidate :=
  (sortCandidates candidates).take 3

def candidatesTruncated (candidates : List Candidate) : Bool := candidates.length > 3

structure MethodView where
  functionName : String
  arguments : List String
  keywords : List String := []
  whereParameters : List String := []
  location : String
  deriving Repr, DecidableEq

def methodSignature (method : MethodView) : String :=
  let positional := String.intercalate ", " method.arguments
  let keywordText := if method.keywords.isEmpty then ""
    else "; " ++ String.intercalate ", " method.keywords
  let whereText := if method.whereParameters.isEmpty then ""
    else " where {" ++ String.intercalate ", " method.whereParameters ++ "}"
  method.functionName ++ "(" ++ positional ++ keywordText ++ ")" ++ whereText

/-- `show(::Method)` and `show(::MIME\"text/plain\", ::Method)`,
`base/methodshow.jl:235-284`. The location is already rendered by
`print_module_path_file`. -/
def showMethod (method : MethodView) (compact signatureOnly : Bool) : String :=
  let signature := methodSignature method
  if signatureOnly then signature
  else if compact then signature ++ " " ++ method.location
  else signature ++ "\n    " ++ method.location

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

/-! ### Stack traces and active exceptions -/

structure Frame where
  functionName : String
  file : String := ""
  line : Int := 0
  fromC : Bool := false
  deriving Repr, DecidableEq

inductive LookupInput where
  | unknown
  | raw (frames : List Frame)
  | debugTraversal (outermostFirst : List Frame)
  deriving Repr, DecidableEq

/-- The three result paths of `StackTraces.lookup`,
`base/stacktraces.jl:155-195,201-230`. DebugInfo traversal builds the outer
frame first and reverses before returning the documented innermost-first list. -/
def lookupFrames : LookupInput → List Frame
  | .unknown => [{ functionName := "", file := "", line := -1, fromC := true }]
  | .raw frames => frames
  | .debugTraversal frames => frames.reverse

/-- `remove_frames!`, `base/stacktraces.jl:270-277`: retain exactly the frames
after the last matching frame. -/
def removeFrames (stack : List Frame) (names : List String) : List Frame :=
  (stack.reverse.takeWhile fun frame => !names.contains frame.functionName).reverse

/-- `jl_get_excstack` supplies the current exception first; the loop at
`base/error.jl:179-188` reverses it so the root cause is first. -/
def currentExceptions (rawNewestFirst : List String) : List String := rawNewestFirst.reverse

inductive ExceptionAction where
  | rethrowCurrent
  | rethrowOther (replacement : String)
  | throwNew (exception : String)
  deriving Repr, DecidableEq

def applyExceptionAction (rootToCurrent : List String) : ExceptionAction → List String
  | .rethrowCurrent => rootToCurrent
  | .rethrowOther replacement => rootToCurrent.dropLast ++ [replacement]
  | .throwNew exception => rootToCurrent ++ [exception]

/-! ### Assertions -/

inductive AssertMessage where
  | default (conditionText : String)
  | supplied (rendered : String)
  deriving Repr, DecidableEq

def AssertMessage.text : AssertMessage → String
  | .default conditionText | .supplied conditionText => conditionText

/-- Expansion of `@assert`, `base/error.jl:249-267`. Message expressions enter
after their single evaluation and conversion with `string`. -/
def assertResult (condition : Bool) (message : AssertMessage) : Option String :=
  if condition then none else some ("AssertionError: " ++ message.text)

/-! ### MIME, showability, and displayability -/

abbrev Mime := String

/-- `MIME(s) = MIME{Symbol(s)}()` and the `print`/`show` methods,
`base/multimedia.jl:73-82`. -/
def makeMime (text : String) : Mime := text
def printMime (mime : Mime) : String := mime
def showMime (mime : Mime) : String := "MIME type " ++ mime

def showable (hasShowMethod : Bool) : Bool := hasShowMethod

structure DisplayBackend where
  supported : List Mime
  deriving Repr, DecidableEq

def backendDisplayable (backend : DisplayBackend) (mime : Mime) : Bool :=
  backend.supported.contains mime

/-- `displayable(mime)`, `base/multimedia.jl:395-403`. -/
def displayable (stack : List DisplayBackend) (mime : Mime) : Bool :=
  stack.any fun backend => backendDisplayable backend mime

/-- The display loop at `base/multimedia.jl:367-393` checks the stack from the
top, which is the end of the backing vector. -/
def topDisplay (stack : List DisplayBackend) (mime : Mime) : Option DisplayBackend :=
  stack.reverse.find? fun backend => backendDisplayable backend mime

end JuliaLean.ErrorShow

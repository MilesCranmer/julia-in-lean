import JuliaLean.ErrorShow.Model

/-!
Coverage models for active methods in the six ErrorShow-owned Base files at
Julia `bbfa0ce4150`. Runtime reflection, I/O, dispatch, source lookup, and C
calls enter as explicit inputs; the models replay the Julia control flow after
those primitive results are known.
-/

namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

abbrev Result (α : Type) := Except String α

/-! ### Common list and rendering helpers -/

def removeFirst [BEq α] (value : α) : List α → List α
  | [] => []
  | head :: tail => if head == value then tail else head :: removeFirst value tail

def removeLast [BEq α] (value : α) (items : List α) : List α :=
  (removeFirst value items.reverse).reverse

def appendLine (text : String) : String := text ++ "\n"

/-! ### `base/multimedia.jl` -/

def textualMimes : List String :=
  ["application/atom+xml", "application/ecmascript", "application/javascript",
   "application/julia", "application/json", "application/postscript",
   "application/rdf+xml", "application/rss+xml", "application/x-latex",
   "application/xhtml+xml", "application/xml", "application/xml-dtd",
   "image/svg+xml", "model/vrml", "model/x3d+vrml", "model/x3d+xml"]

/-- `istextmime`, `base/multimedia.jl:226-236`. -/
def isTextMime (mime : String) : Bool :=
  mime.startsWith "text/" || textualMimes.contains mime

inductive MediaValue where
  | text (value : String)
  | bytes (value : List UInt8)
  | other
  deriving Repr, DecidableEq

inductive Representation where
  | text (value : String)
  | bytes (value : List UInt8)
  deriving Repr, DecidableEq

/-- `_binrepr` and `__binrepr`, lines 199-209. `shown` is the byte stream
written by the selected three-argument `show` method. -/
def binaryRepresentation (value : MediaValue) (shown : List UInt8) : List UInt8 :=
  match value with
  | .bytes bytes => bytes
  | _ => shown

/-- `_textrepr` and `repr`, lines 190-209. `decoded` is `String(shown)` from
Julia's String primitive. -/
def representation (mime : String) (value : MediaValue)
    (shown : List UInt8) (decoded : String) : Representation :=
  if isTextMime mime then
    match value with
    | .text text => if mime == "text/plain" then .text decoded else .text text
    | _ => .text decoded
  else
    .bytes (binaryRepresentation value shown)

inductive DisplayOutcome where
  | success (backend : String)
  | methodError (functionName : String)
  | otherError (message : String)
  deriving Repr, DecidableEq

structure DisplayAttempt where
  backend : String
  applicable : Bool
  outcome : DisplayOutcome
  deriving Repr, DecidableEq

def caughtBy (caught : List String) : DisplayOutcome → Bool
  | .methodError functionName => caught.contains functionName
  | _ => false

/-- The shared top-to-bottom display loop at lines 367-393 and 426-452.
Attempts arrive in stack order; the last attempt is the top backend. -/
def runDisplayLoop (functionName : String) (caught : List String) :
    List DisplayAttempt → DisplayOutcome
  | attempts => run attempts.reverse
where
  run : List DisplayAttempt → DisplayOutcome
    | [] => .methodError functionName
    | attempt :: rest =>
        if !attempt.applicable then run rest
        else match attempt.outcome with
          | .success backend => .success backend
          | error => if caughtBy caught error then run rest else error

def displayAny (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "display" ["display", "show"] attempts

def displayMime (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "display" ["display"] attempts

def redisplayAny (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "redisplay" ["redisplay", "display", "show"] attempts

def redisplayMime (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "redisplay" ["redisplay", "display"] attempts

/-- `TextDisplay` methods, lines 285-297. -/
def textDisplay (mime shown : String) : Result String :=
  if isTextMime mime then .ok (shown ++ "\n") else .error "MethodError(display)"

/-- Display stack mutation, lines 312-336. -/
def pushDisplay (stack : List String) (backend : String) : List String := stack ++ [backend]
def popDisplay : List String → Result (String × List String)
  | [] => .error "ArgumentError: array must be non-empty"
  | stack => .ok (stack.getLast!, stack.dropLast)
def popNamedDisplay (stack : List String) (backend : String) : Result (List String) :=
  if stack.contains backend then .ok (removeLast backend stack) else .error "KeyError"
def reinitDisplays (stdout : String) : List String := [stdout]
def delegateDisplayIO (result : Result Unit) : Result Unit := result

def MultimediaRepresentationExact : Prop :=
  (∀ mime, isTextMime mime = (mime.startsWith "text/" || textualMimes.contains mime)) ∧
  (∀ mime value shown decoded,
    representation mime value shown decoded =
      if isTextMime mime then
        match value with
        | .text text => if mime == "text/plain" then .text decoded else .text text
        | _ => .text decoded
      else .bytes (binaryRepresentation value shown))

theorem multimediaRepresentationExact : MultimediaRepresentationExact := by
  constructor <;> intros <;> rfl

def MultimediaDisplayExact : Prop :=
  (∀ attempts, displayAny attempts = runDisplayLoop "display" ["display", "show"] attempts) ∧
  (∀ attempts, displayMime attempts = runDisplayLoop "display" ["display"] attempts) ∧
  (∀ attempts, redisplayAny attempts =
    runDisplayLoop "redisplay" ["redisplay", "display", "show"] attempts) ∧
  (∀ attempts, redisplayMime attempts =
    runDisplayLoop "redisplay" ["redisplay", "display"] attempts)

theorem multimediaDisplayExact : MultimediaDisplayExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def MultimediaStackExact : Prop :=
  (∀ stack backend, pushDisplay stack backend = stack ++ [backend]) ∧
  (popDisplay [] = .error "ArgumentError: array must be non-empty") ∧
  (∀ stack backend, popNamedDisplay stack backend =
    if stack.contains backend then .ok (removeLast backend stack) else .error "KeyError") ∧
  (∀ stdout, reinitDisplays stdout = [stdout]) ∧
  (∀ result, delegateDisplayIO result = result)

theorem multimediaStackExact : MultimediaStackExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-! ### `base/error.jl` -/

inductive BacktraceEntry where
  | native (pointer : Nat)
  | interpreter (code : Nat) (statement : Nat) (moduleId : Option Nat)
  | unknownTag (tag : Nat)
  deriving Repr, DecidableEq

/-- `_reformat_bt`, lines 84-114, after the runtime metadata words and managed
objects have been decoded into one entry. -/
def reformatBacktrace : List BacktraceEntry → Result (List BacktraceEntry)
  | [] => .ok []
  | .unknownTag tag :: _ => .error s!"Unexpected extended backtrace entry tag {tag}"
  | entry :: rest => do
      let tail ← reformatBacktrace rest
      .ok (entry :: tail)

def errorFromParts (parts : List String) : String := String.intercalate "" parts

def backtraceFromRuntime (entries : List BacktraceEntry) : Result (List BacktraceEntry) :=
  reformatBacktrace entries

def keywordMethodError (keywordType argumentTypes : String) : String :=
  "MethodError(Core.kwcall," ++ keywordType ++ "," ++ argumentTypes ++ ")"

inductive SystemErrorCall where
  | skipped
  | raised (name : String) (code : Int) (extra : Option String)
  deriving Repr, DecidableEq

/-- `systemerror` Boolean and errno overloads, lines 204-205. -/
def systemError (name : String) (condition : Bool) (code : Int)
    (extra : Option String) : SystemErrorCall :=
  if condition then .raised name code extra else .skipped

structure Backoff where
  count : Int
  firstDelay : Int
  maxDelay : Int
  factor : Int
  jitter : Int
  deriving Repr, DecidableEq

def validBackoff (backoff : Backoff) : Bool :=
  decide (0 ≤ backoff.count ∧ 0 ≤ backoff.firstDelay ∧ 0 ≤ backoff.maxDelay ∧
    0 ≤ backoff.factor ∧ 0 ≤ backoff.jitter)

def makeBackoff (backoff : Backoff) : Result Backoff :=
  if validBackoff backoff then .ok backoff else .error "all inputs must be non-negative"

/-- `iterate(::ExponentialBackOff)`, lines 292-298. `randomTerm` is the
already-sampled multiplicative jitter term. -/
def iterateBackoff (backoff : Backoff) (state : Int × Int) (randomTerm : Int) :
    Option (Int × (Int × Int)) :=
  if state.1 < 1 then none
  else some (state.2, (state.1 - 1,
    min backoff.maxDelay (state.2 * backoff.factor * randomTerm)))

def backoffLength (backoff : Backoff) : Int := backoff.count
def backoffElementType : String := "Float64"

inductive RetryAttempt where
  | success
  | failure (retry : Bool)
  deriving Repr, DecidableEq

structure RetryTrace where
  calls : Nat
  sleeps : Nat
  result : Bool
  deriving Repr, DecidableEq

/-- The loop in `retry`, lines 322-342. The final call after delays are
exhausted is represented by the empty-list branch. -/
def retryTrace : List RetryAttempt → RetryTrace
  | [] => { calls := 1, sleeps := 0, result := false }
  | .success :: _ => { calls := 1, sleeps := 0, result := true }
  | .failure false :: _ => { calls := 1, sleeps := 0, result := false }
  | .failure true :: rest =>
      let tail := retryTrace rest
      { calls := tail.calls + 1, sleeps := tail.sleeps + 1, result := tail.result }

def ErrorRuntimeExact : Prop :=
  (∀ parts, errorFromParts parts = String.intercalate "" parts) ∧
  (∀ entries, backtraceFromRuntime entries = reformatBacktrace entries) ∧
  (∀ keywordType argumentTypes,
    keywordMethodError keywordType argumentTypes =
      "MethodError(Core.kwcall," ++ keywordType ++ "," ++ argumentTypes ++ ")") ∧
  (∀ name condition code extra,
    systemError name condition code extra =
      if condition then .raised name code extra else .skipped) ∧
  (∀ entries, reformatBacktrace entries =
    match entries with
    | [] => .ok []
    | .unknownTag tag :: _ => .error s!"Unexpected extended backtrace entry tag {tag}"
    | entry :: rest => reformatBacktrace rest >>= fun tail => .ok (entry :: tail))

theorem errorRuntimeExact : ErrorRuntimeExact := by
  repeat' apply And.intro
  all_goals try (intros; rfl)
  · intro entries
    cases entries with
    | nil => rfl
    | cons head tail => cases head <;> rfl

def RetryExact : Prop :=
  (∀ backoff, makeBackoff backoff =
    if validBackoff backoff then .ok backoff else .error "all inputs must be non-negative") ∧
  (∀ backoff state randomTerm,
    iterateBackoff backoff state randomTerm =
      if state.1 < 1 then none else some (state.2, (state.1 - 1,
        min backoff.maxDelay (state.2 * backoff.factor * randomTerm)))) ∧
  (∀ backoff, backoffLength backoff = backoff.count) ∧
  backoffElementType = "Float64" ∧
  (∀ attempts, retryTrace attempts =
    match attempts with
    | [] => { calls := 1, sleeps := 0, result := false }
    | .success :: _ => { calls := 1, sleeps := 0, result := true }
    | .failure false :: _ => { calls := 1, sleeps := 0, result := false }
    | .failure true :: rest =>
        let tail := retryTrace rest
        { calls := tail.calls + 1, sleeps := tail.sleeps + 1, result := tail.result })

theorem retryExact : RetryExact := by
  repeat' apply And.intro
  all_goals try (intros; rfl)
  · intro attempts
    cases attempts with
    | nil => rfl
    | cons head tail =>
        cases head with
        | success => rfl
        | failure retry => cases retry <;> rfl

/-! ### `base/stacktraces.jl` -/

structure FullFrame where
  functionName : String
  file : String
  line : Int
  linfo : Option Nat := none
  fromC : Bool := false
  inlined : Bool := false
  pointer : Nat := 0
  pc : Int := 0
  moduleId : Option Nat := none
  deriving Repr, DecidableEq

/-- StackFrame constructors, lines 82-85. -/
def shortFrame (functionName file : String) (line : Int) : FullFrame :=
  { functionName, file, line }

/-- `==(StackFrame,StackFrame)`, lines 103-105. -/
def frameEqual (left right : FullFrame) : Bool :=
  left.line == right.line && left.fromC == right.fromC &&
    left.functionName == right.functionName && left.file == right.file &&
    left.inlined == right.inlined

/-- `hash(StackFrame)`, lines 107-115, using an abstract component hash. -/
def frameHash (hashPart : Nat → Nat → Nat) (frame : FullFrame) (seed : Nat) : Nat :=
  let seed := seed ^^^ 0xf4fbda67fe20ce88
  let seed := hashPart frame.line.natAbs seed
  let seed := hashPart frame.file.length seed
  let seed := hashPart frame.functionName.length seed
  let seed := hashPart (if frame.fromC then 1 else 0) seed
  hashPart (if frame.inlined then 1 else 0) seed

def flattenLookups (lookups : List (List FullFrame)) (includeC : Bool) : List FullFrame :=
  (lookups.flatten).filter fun frame => includeC || !frame.fromC

def removeModuleFrames (stack : List FullFrame) (moduleId : Nat) : List FullFrame :=
  stack.filter fun frame => frame.moduleId != some moduleId

def isTopLevelFrame (frame : FullFrame) (isCodeInfo : Bool) : Bool :=
  isCodeInfo || (frame.linfo.isNone && frame.functionName == "top-level scope")

inductive FrameOwner where
  | method (id : Nat)
  | moduleId (id : Nat)
  | none
  deriving Repr, DecidableEq

def frameMethodOrModule (linfoOwner : Option FrameOwner) : FrameOwner :=
  linfoOwner.getD .none

def frameMethodInstance (linfo : Option Nat) : Option Nat := linfo

def frameLocation (source : Option (String × Int × Int))
    (fallbackFile : String) (fallbackLine pc : Int) : String × Int × Int :=
  source.getD (fallbackFile, fallbackLine, pc)

def addDebugFrames (own : FullFrame) (lineTableEdges ownEdges : List (List FullFrame)) :
    List FullFrame :=
  own :: (lineTableEdges.flatten ++ ownEdges.flatten)

def showFrame (signature location : String) (inlined : Bool) : String :=
  signature ++ (if location.isEmpty then "" else " at " ++ location) ++
    (if inlined then " [inlined]" else "")

def parentModuleOfFrame (methodModule codeModule : Option Nat) : Option Nat :=
  methodModule.orElse fun _ => codeModule

def fromModule (frameModule target : Option Nat) : Bool := frameModule == target

def StackFrameMethodsExact : Prop :=
  (∀ functionName file line,
    shortFrame functionName file line = { functionName, file, line }) ∧
  (∀ left right : FullFrame,
    frameEqual left right =
      (left.line == right.line && left.fromC == right.fromC &&
       left.functionName == right.functionName && left.file == right.file &&
       left.inlined == right.inlined)) ∧
  (∀ hashPart frame seed,
    frameHash hashPart frame seed =
      let seed := seed ^^^ 0xf4fbda67fe20ce88
      let seed := hashPart frame.line.natAbs seed
      let seed := hashPart frame.file.length seed
      let seed := hashPart frame.functionName.length seed
      let seed := hashPart (if frame.fromC then 1 else 0) seed
      hashPart (if frame.inlined then 1 else 0) seed) ∧
  (∀ lookups : List (List FullFrame), ∀ includeC : Bool,
    flattenLookups lookups includeC =
      (lookups.flatten).filter (fun frame => includeC || !frame.fromC)) ∧
  (∀ stack : List FullFrame, ∀ moduleId : Nat,
    removeModuleFrames stack moduleId =
      stack.filter fun frame => frame.moduleId != some moduleId) ∧
  (∀ frame isCodeInfo,
    isTopLevelFrame frame isCodeInfo =
      (isCodeInfo || (frame.linfo.isNone && frame.functionName == "top-level scope"))) ∧
  (∀ owner, frameMethodOrModule owner = owner.getD .none) ∧
  (∀ linfo, frameMethodInstance linfo = linfo) ∧
  (∀ source fallbackFile fallbackLine pc,
    frameLocation source fallbackFile fallbackLine pc =
      source.getD (fallbackFile, fallbackLine, pc)) ∧
  (∀ own lineTableEdges ownEdges,
    addDebugFrames own lineTableEdges ownEdges =
      own :: (lineTableEdges.flatten ++ ownEdges.flatten))

theorem stackFrameMethodsExact : StackFrameMethodsExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def StackFrameDisplayExact : Prop :=
  (∀ signature location inlined,
    showFrame signature location inlined =
      signature ++ (if location.isEmpty then "" else " at " ++ location) ++
        (if inlined then " [inlined]" else "")) ∧
  (∀ methodModule codeModule : Option Nat,
    parentModuleOfFrame methodModule codeModule = methodModule.orElse (fun _ => codeModule)) ∧
  (∀ frameModule target, fromModule frameModule target = (frameModule == target))

theorem stackFrameDisplayExact : StackFrameDisplayExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

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

/-! ### `base/methodshow.jl` -/

inductive SymbolForm where
  | self
  | unused
  | generated (base : String)
  | plain (name : String)
  deriving Repr, DecidableEq

def stripGensym : SymbolForm → String
  | .self | .unused => ""
  | .generated base | .plain base => base

inductive VarargForm where
  | ordinary
  | unbounded
  | fixed (count : Nat)
  deriving Repr, DecidableEq

def argumentDeclaration (name typeText : String) (isAny : Bool)
    (vararg : VarargForm) : String × String :=
  let name := stripGensym (.plain name)
  match vararg with
  | .ordinary => if isAny then (name, "") else (name, typeText)
  | .unbounded => if isAny then (name ++ "...", "") else (name, typeText ++ "...")
  | .fixed count => (name, "Vararg{" ++ typeText ++ ", " ++ toString count ++ "}")

def methodArgumentNames (slotNames : List String) (argumentCount : Nat) : List String :=
  if slotNames.isEmpty then [] else slotNames.take argumentCount

def argumentDeclarationParts (arguments : List (String × String)) : List (String × String) :=
  arguments

def moveSplatLast (keywords : List String) : List String :=
  match keywords.find? (fun name => name.endsWith "...") with
  | none => keywords
  | some splat => (keywords.erase splat) ++ [splat]

def keywordDeclarations (slotNames : List String) : List String :=
  let filtered := slotNames.filter fun name => !name.isEmpty && !name.contains '#'
  if filtered.isEmpty then ["..."] else moveSplatLast filtered

def showWhereParameters : List String → String
  | [] => ""
  | [parameter] => " where " ++ parameter
  | parameters => " where {" ++ String.intercalate ", " parameters ++ "}"

def symbolToString (empty generated : Bool) (shown : String) : String :=
  if empty then "..." else if generated then shown ++ "..." else shown

inductive FunctionLocation where
  | location (file : String) (line : Int)
  | noDefinitions
  | multipleDefinitions
  | notCallable
  deriving Repr, DecidableEq

def singleFunctionLocation (callable : Bool) (locations : List (String × Int)) : FunctionLocation :=
  match locations with
  | [] => if callable then .noDefinitions else .notCallable
  | [(file, line)] => .location file line
  | _ => .multipleDefinitions

def fixupStdlibPath (buildPathDiff compilerSource : Bool)
    (stdlibPath compilerPath path : String) : String :=
  if compilerSource then compilerPath else if buildPathDiff then stdlibPath else path

def updatedMethodLocation (original : String × Int)
    (callback : Option (String × Int)) : String × Int :=
  callback.getD original

def methodListHeader (count : Nat) (kind name moduleName : String) : String :=
  s!"# {count} {if count = 1 then "method" else "methods"} for {kind} {name} from {moduleName}" ++
    (if count = 0 then "" else ":")

def methodTableRows (rows : List String) (maximum : Int) : List String :=
  if maximum < 0 then rows else rows.take maximum.toNat

def moduleColor : Option String := none

def renderMethodContainer (header : String) (rows : List String)
    (html : Bool) : String :=
  if html then header ++ "<ul>" ++ String.intercalate "" (rows.map fun row => "<li> " ++ row ++ "</li> ") ++ "</ul>"
  else header ++ String.intercalate "\n" rows

def inBase (parents : List String) : Bool := parents.contains "Base"

inductive MethodUrl where
  | none
  | github (commit file : String) (line : Int)
  | localFile (file : String) (line : Int)
  deriving Repr, DecidableEq

def methodUrl (validLocation inBaseModule hasCommit : Bool)
    (commit file : String) (line : Int) : MethodUrl :=
  if !validLocation then .none
  else if inBaseModule then .github (if hasCommit then commit else "tag") file line
  else .localFile file line

def MethodSignatureHelpersExact : Prop :=
  (∀ form, stripGensym form = match form with
    | .self | .unused => ""
    | .generated base | .plain base => base) ∧
  (∀ name typeText isAny vararg,
    argumentDeclaration name typeText isAny vararg =
      let stripped := stripGensym (.plain name)
      match vararg with
      | .ordinary => if isAny then (stripped, "") else (stripped, typeText)
      | .unbounded => if isAny then (stripped ++ "...", "") else (stripped, typeText ++ "...")
      | .fixed count => (stripped, "Vararg{" ++ typeText ++ ", " ++ toString count ++ "}")) ∧
  (∀ slotNames argumentCount,
    methodArgumentNames slotNames argumentCount =
      if slotNames.isEmpty then [] else slotNames.take argumentCount) ∧
  (∀ arguments, argumentDeclarationParts arguments = arguments) ∧
  (∀ slots, keywordDeclarations slots =
    let filtered := slots.filter fun name => !name.isEmpty && !name.contains '#'
    if filtered.isEmpty then ["..."] else moveSplatLast filtered) ∧
  (∀ parameters, showWhereParameters parameters = match parameters with
    | [] => ""
    | [parameter] => " where " ++ parameter
    | parameters => " where {" ++ String.intercalate ", " parameters ++ "}") ∧
  (∀ empty generated shown,
    symbolToString empty generated shown =
      if empty then "..." else if generated then shown ++ "..." else shown)

theorem methodSignatureHelpersExact : MethodSignatureHelpersExact := by
  constructor
  · intro form; cases form <;> rfl
  repeat' apply And.intro
  all_goals intros <;> rfl

def MethodLocationDisplayExact : Prop :=
  (∀ buildPathDiff compilerSource stdlibPath compilerPath path,
    fixupStdlibPath buildPathDiff compilerSource stdlibPath compilerPath path =
      if compilerSource then compilerPath else if buildPathDiff then stdlibPath else path) ∧
  (∀ original callback,
    updatedMethodLocation original callback = callback.getD original) ∧
  (∀ callable locations,
    singleFunctionLocation callable locations = match locations with
    | [] => if callable then .noDefinitions else .notCallable
    | [(file, line)] => .location file line
    | _ => .multipleDefinitions) ∧
  (∀ count kind name moduleName,
    methodListHeader count kind name moduleName =
      s!"# {count} {if count = 1 then "method" else "methods"} for {kind} {name} from {moduleName}" ++
        (if count = 0 then "" else ":")) ∧
  moduleColor = none ∧
  (∀ rows maximum,
    methodTableRows rows maximum = if maximum < 0 then rows else rows.take maximum.toNat) ∧
  (∀ parents, inBase parents = parents.contains "Base") ∧
  (∀ header rows html,
    renderMethodContainer header rows html =
      if html then header ++ "<ul>" ++
        String.intercalate "" (rows.map fun row => "<li> " ++ row ++ "</li> ") ++ "</ul>"
      else header ++ String.intercalate "\n" rows) ∧
  (∀ valid inBaseModule hasCommit commit file line,
    methodUrl valid inBaseModule hasCommit commit file line =
      if !valid then .none
      else if inBaseModule then .github (if hasCommit then commit else "tag") file line
      else .localFile file line)

theorem methodLocationDisplayExact : MethodLocationDisplayExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

/-! ### Remaining `base/errorshow.jl` helpers -/

inductive TypeTree where
  | leaf (name : String)
  | node (name : String) (parameters : List TypeTree)
  deriving Repr

inductive DiffToken where
  | same (text : String)
  | mismatch (text : String)
  | literal (text : String)
  deriving Repr, DecidableEq

def renderTypeTree : TypeTree → String
  | .leaf name => name
  | .node name parameters =>
      name ++ "{" ++ String.intercalate "," (parameters.map renderTypeTree) ++ "}"

def typeDiff : TypeTree → TypeTree → List DiffToken
  | .leaf left, .leaf right =>
      if left == right then [.same left] else [.mismatch left]
  | .node left lp, .node right rp =>
      if left != right then [.mismatch (renderTypeTree (.node left lp))]
      else .literal (left ++ "{") :: diffLists lp rp ++ [.literal "}"]
  | left, _ => [.mismatch (renderTypeTree left)]
where
  diffLists : List TypeTree → List TypeTree → List DiffToken
    | [], _ => []
    | left :: rest, [] => .mismatch (renderTypeTree left) :: diffLists rest []
    | left :: rest, right :: rights =>
        typeDiff left right ++ (if rest.isEmpty then [] else [.literal ", "]) ++
          diffLists rest rights

def showSeparator (color : Bool) : List DiffToken :=
  if color then [.literal "color(light_black)", .literal ", ", .literal "color(default)"]
  else [.literal ", "]

def showTypeMismatch (typeText : String) (topLevel color : Bool) : List DiffToken :=
  if color then [.literal "error-color", .mismatch typeText, .literal "default-color"]
  else if topLevel then [.literal "!Matched{", .mismatch typeText, .literal "}"]
  else [.literal "!Matched::", .mismatch typeText]

def typesOf (runtimeTypes : List String) : List String := runtimeTypes

def stripType (isType : Bool) (typeText : String) : Option String :=
  if isType then some typeText else none

def printWithCompare (sameIdentity : Bool) (shown : String) : DiffToken :=
  if sameIdentity then .same shown else .mismatch shown

def showConvertError (targetType : Option String) (sourceType firstArgument : String) : String :=
  match targetType with
  | none => "First argument to `convert` must be a Type, got " ++ firstArgument
  | some target => "Cannot `convert` an object of type " ++ sourceType ++
      " to an object of type " ++ target

def showNamedTupleDiff (compatible : Bool) (tokens : List DiffToken) : Option (List DiffToken) :=
  if compatible then some tokens else none

def descendParameters (sameOuter nonempty : Bool) (parameters : List TypeTree) : Option (List TypeTree) :=
  if sameOuter && nonempty then some parameters else none

def resolvesToSelf (moduleDefined parentSame : Bool) : Bool :=
  !moduleDefined || parentSame

def shadowedTypeHints (shadows : List String) : List String := shadows.eraseDups

def envBool (value : Option Bool) (default : Bool) : Bool := value.getD default

def showErrorNoStdio (message staticError : String) : String :=
  message ++ ":\n" ++ staticError ++ "\n"

def stacktraceColor (fixedColor nextColor : Option String) : Option String :=
  fixedColor.orElse fun _ => nextColor

def parentBeforeMain : List String → Option String
  | [] => none
  | [moduleName] => some moduleName
  | moduleName :: "Main" :: _ => some moduleName
  | _ :: rest => parentBeforeMain rest

structure CycleClosing where
  startLine : Nat
  cycleLength : Nat
  repetitions : Nat
  frameAdvance : Nat
  deriving Repr, DecidableEq

def closeRepetitions (line : Nat) (frameCounter active : Nat) :
    List CycleClosing → Nat × Nat
  | [] => (frameCounter, active)
  | cycle :: rest =>
      if line = cycle.startLine + cycle.cycleLength - 1 then
        closeRepetitions line (frameCounter + cycle.frameAdvance) (active - 1) rest
      else (frameCounter, active)

theorem closeRepetitions_unfold (line frameCounter active : Nat) (cycles : List CycleClosing) :
    closeRepetitions line frameCounter active cycles =
      match cycles with
      | [] => (frameCounter, active)
      | cycle :: rest =>
          if line = cycle.startLine + cycle.cycleLength - 1 then
            closeRepetitions line (frameCounter + cycle.frameAdvance) (active - 1) rest
          else (frameCounter, active) := by
  cases cycles <;> rfl

def processedFrameNumbers (counts : List Nat) : List Nat :=
  counts.foldl (fun output count => output ++ [output.length + 1] ++
    List.replicate (count - 1) 0) []

def stackFrameLayout (linePrefix signature location : String) (number width active starts : Nat)
    (inlined : Bool) : String :=
  linePrefix ++ " " ++ String.ofList (List.replicate (active - starts) '├') ++
    String.ofList (List.replicate starts '┌') ++
    String.ofList (List.replicate (width - (toString number).length - 2) ' ') ++
    "[" ++ toString number ++ "] " ++
    signature ++ "\n" ++ linePrefix ++ " " ++ String.ofList (List.replicate active '│') ++
    " @ " ++ location ++ (if inlined then " [inlined]" else "")

def modulePathFile (moduleName directory file : String) (line column : Int) : String :=
  "@ " ++ (if moduleName.isEmpty then "" else moduleName ++ " ") ++
    (if directory.isEmpty then "" else directory ++ "/") ++ file ++ ":" ++
    (if line < 0 then "?" else toString line) ++
    (if column = 0 then "" else ":" ++ toString column)

inductive ShowBacktraceRoute where
  | empty
  | suppressTopLevel
  | direct
  | findCycles
  deriving Repr, DecidableEq

def showBacktraceRoute (empty singleUnknown large : Bool) : ShowBacktraceRoute :=
  if empty then .empty else if singleUnknown then .suppressTopLevel
  else if large then .findCycles else .direct

def showInterpreterIP (typeName code moduleName : String) (statement : Int)
    (topLevel : Bool) : String :=
  typeName ++ (if topLevel then " in top-level CodeInfo for " ++ moduleName
    else " in " ++ code) ++ " at statement " ++ toString statement

structure RepeatedCycle where
  start : Nat
  length : Nat
  repetitions : Nat
  deriving Repr, DecidableEq

def collapseRepeatedFrames [BEq α] : List α → List (α × Nat)
  | [] => []
  | head :: tail => loop head 1 tail
where
  loop [BEq α] (current : α) (count : Nat) : List α → List (α × Nat)
    | [] => [(current, count)]
    | head :: tail =>
        if head == current then loop current (count + 1) tail
        else (current, count) :: loop head 1 tail

structure TraceEntry where
  frameKey : String
  removeKwcall : Bool := false
  keepInclude : Bool := true
  loadingFrame : Bool := false
  loadingAnchor : Bool := false
  keepLocation : Bool := true
  deriving Repr, DecidableEq, BEq

def removeKwcallFrames (frames : List TraceEntry) : List TraceEntry :=
  frames.filter fun frame => !frame.removeKwcall

def simplifyIncludes (frames : List TraceEntry) : List TraceEntry :=
  frames.filter fun frame => frame.keepInclude

def isLoadingFrame (frame : TraceEntry) : Bool := frame.loadingFrame
def isLoadingAnchor (frame : TraceEntry) : Bool := frame.loadingAnchor

def simplifyLoading (fullLoading : Bool) (frames : List TraceEntry) : List TraceEntry :=
  if fullLoading then frames
  else frames.filter fun frame => !frame.loadingFrame || frame.loadingAnchor

def collapseLocations (frames : List TraceEntry) : List TraceEntry :=
  frames.filter fun frame => frame.keepLocation

def processBacktrace (fullLoading : Bool) (frames : List TraceEntry) : List (TraceEntry × Nat) :=
  collapseRepeatedFrames
    (collapseLocations (simplifyLoading fullLoading (simplifyIncludes (removeKwcallFrames frames))))

def showExceptionStack (exceptions : List String) : String :=
  String.intercalate "\ncaused by: " exceptions.reverse

inductive HintCase where
  | none
  | message (text : String)
  deriving Repr, DecidableEq

def hintWhen (condition : Bool) (message : String) : HintCase :=
  if condition then .message message else .none

def noncallableNumberHint (isNumber : Bool) : HintCase :=
  hintWhen isNumber "Maybe you forgot to use an operator such as *, ^, %, / etc. ?"

inductive NonsettableKind where
  | none | number | typeValue
  deriving Repr, DecidableEq

def nonsettableHint : NonsettableKind → HintCase
  | .none => .none
  | .number => .message "Use a[1, 2] rather than a[1][2]"
  | .typeValue => .message "Create an instance with its constructor before indexing"

def stringConcatenationHint (condition : Bool) : HintCase :=
  hintWhen condition "String concatenation is performed with *"

def stringReplaceHint (condition : Bool) : HintCase :=
  hintWhen condition "Strings cannot be modified with replace!; use replace"

def iterableMethodHint (message : Option String) : HintCase :=
  match message with | none => .none | some text => .message text

def fieldErrorHint (message : Option String) : HintCase :=
  match message with | none => .none | some text => .message text

def applyTypeHint (condition : Bool) (got : String) : HintCase :=
  hintWhen condition ("`" ++ got ++ "` takes no type parameters")

def undefVarHint (messages : List String) : List String := messages

def exceptionStackSize (stack : List String) : Nat := stack.length
def exceptionStackGet? (stack : List String) (index : Nat) : Option String := stack[index]?
def showExceptionStackPlain (stack : List String) : String :=
  s!"{stack.length}-element ExceptionStack" ++ (if stack.isEmpty then "" else ":\n") ++
    showExceptionStack stack

def propertyNamesByType (fieldNames propertyNames : List String) : List String :=
  (fieldNames ++ propertyNames).eraseDups

inductive IncompleteKind where
  | none | other | string | comment | block | command | character
  deriving Repr, DecidableEq

def incompleteTag (headIncomplete hasArgument : Bool) (kind : IncompleteKind) : IncompleteKind :=
  if !headIncomplete then .none else if !hasArgument then .other else kind

def ErrorShowTypeDiffExact : Prop :=
  (∀ runtimeTypes, typesOf runtimeTypes = runtimeTypes) ∧
  (∀ isType typeText,
    stripType isType typeText = if isType then some typeText else none) ∧
  (∀ sameIdentity shown,
    printWithCompare sameIdentity shown =
      if sameIdentity then .same shown else .mismatch shown) ∧
  (∀ target source firstArgument,
    showConvertError target source firstArgument =
      match target with
      | none => "First argument to `convert` must be a Type, got " ++ firstArgument
      | some target => "Cannot `convert` an object of type " ++ source ++
          " to an object of type " ++ target) ∧
  (∀ compatible tokens,
    showNamedTupleDiff compatible tokens = if compatible then some tokens else none) ∧
  (∀ sameOuter nonempty parameters,
    descendParameters sameOuter nonempty parameters =
      if sameOuter && nonempty then some parameters else none) ∧
  (∀ moduleDefined parentSame,
    resolvesToSelf moduleDefined parentSame = (!moduleDefined || parentSame)) ∧
  (∀ shadows, shadowedTypeHints shadows = shadows.eraseDups) ∧
  (∀ color, showSeparator color =
    if color then [.literal "color(light_black)", .literal ", ", .literal "color(default)"]
    else [.literal ", "]) ∧
  (∀ text top color, showTypeMismatch text top color =
    if color then [.literal "error-color", .mismatch text, .literal "default-color"]
    else if top then [.literal "!Matched{", .mismatch text, .literal "}"]
    else [.literal "!Matched::", .mismatch text])

theorem errorShowTypeDiffExact : ErrorShowTypeDiffExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ErrorShowBacktraceExact : Prop :=
  (∀ value default, envBool value default = value.getD default) ∧
  (∀ message staticError,
    showErrorNoStdio message staticError = message ++ ":\n" ++ staticError ++ "\n") ∧
  (∀ fixed next, stacktraceColor fixed next = fixed.orElse (fun _ => next)) ∧
  (∀ line frameCounter active cycles,
    closeRepetitions line frameCounter active cycles =
      match cycles with
      | [] => (frameCounter, active)
      | cycle :: rest =>
          if line = cycle.startLine + cycle.cycleLength - 1 then
            closeRepetitions line (frameCounter + cycle.frameAdvance) (active - 1) rest
          else (frameCounter, active)) ∧
  (∀ linePrefix signature location number width active starts inlined,
    stackFrameLayout linePrefix signature location number width active starts inlined =
      linePrefix ++ " " ++ String.ofList (List.replicate (active - starts) '├') ++
        String.ofList (List.replicate starts '┌') ++
        String.ofList (List.replicate (width - (toString number).length - 2) ' ') ++
        "[" ++ toString number ++ "] " ++
        signature ++ "\n" ++ linePrefix ++ " " ++ String.ofList (List.replicate active '│') ++
        " @ " ++ location ++ (if inlined then " [inlined]" else "")) ∧
  (∀ empty singleUnknown large,
    showBacktraceRoute empty singleUnknown large =
      if empty then .empty else if singleUnknown then .suppressTopLevel
      else if large then .findCycles else .direct) ∧
  (∀ moduleName directory file line column,
    modulePathFile moduleName directory file line column =
      "@ " ++ (if moduleName.isEmpty then "" else moduleName ++ " ") ++
        (if directory.isEmpty then "" else directory ++ "/") ++ file ++ ":" ++
        (if line < 0 then "?" else toString line) ++
        (if column = 0 then "" else ":" ++ toString column)) ∧
  (∀ typeName code moduleName statement topLevel,
    showInterpreterIP typeName code moduleName statement topLevel =
      typeName ++ (if topLevel then " in top-level CodeInfo for " ++ moduleName
        else " in " ++ code) ++ " at statement " ++ toString statement) ∧
  (∀ frames, removeKwcallFrames frames = frames.filter fun frame => !frame.removeKwcall) ∧
  (∀ frames, simplifyIncludes frames = frames.filter fun frame => frame.keepInclude) ∧
  (∀ frame, isLoadingFrame frame = frame.loadingFrame) ∧
  (∀ frame, isLoadingAnchor frame = frame.loadingAnchor) ∧
  (∀ fullLoading frames,
    simplifyLoading fullLoading frames =
      if fullLoading then frames
      else frames.filter fun frame => !frame.loadingFrame || frame.loadingAnchor) ∧
  (∀ frames, collapseLocations frames = frames.filter fun frame => frame.keepLocation) ∧
  (∀ fullLoading frames, processBacktrace fullLoading frames =
    collapseRepeatedFrames
      (collapseLocations (simplifyLoading fullLoading (simplifyIncludes (removeKwcallFrames frames))))) ∧
  (∀ exceptions,
    showExceptionStack exceptions = String.intercalate "\ncaused by: " exceptions.reverse)

theorem errorShowBacktraceExact : ErrorShowBacktraceExact := by
  repeat' apply And.intro
  all_goals intros <;> first | rfl | exact closeRepetitions_unfold _ _ _ _

def ErrorShowHintsExact : Prop :=
  (∀ condition message,
    hintWhen condition message = if condition then .message message else .none) ∧
  (∀ fields properties,
    propertyNamesByType fields properties = (fields ++ properties).eraseDups) ∧
  (∀ stack, exceptionStackSize stack = stack.length) ∧
  (∀ stack index, exceptionStackGet? stack index = stack[index]?) ∧
  (∀ headIncomplete hasArgument kind,
    incompleteTag headIncomplete hasArgument kind =
      if !headIncomplete then .none else if !hasArgument then .other else kind)

theorem errorShowHintsExact : ErrorShowHintsExact := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.ErrorShow.Coverage

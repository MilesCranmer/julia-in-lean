import JuliaLean.ErrorShow.Model
import JuliaLean.ErrorShow.Coverage

/-! Method-specific models for `base/errorshow.jl` at `bbfa0ce4150`. -/

namespace JuliaLean.ErrorShow.ErrorshowFaithful

open JuliaLean.ErrorShow
open JuliaLean.ErrorShow.Coverage

abbrev R (α : Type) := Except String α

def showerrorFallback {α : Type} (showFn : α → String) (value : α) : String := showFn value
def ShowerrorFallbackExact : Prop := ∀ (α : Type) (showFn : α → String) value,
  showerrorFallback showFn value = showFn value
theorem showerrorFallbackExact : ShowerrorFallbackExact := by unfold ShowerrorFallbackExact; intros; rfl

def showIndexAny {α : Type} (showFn : α → String) (value : α) := showFn value
def ShowIndexAnyExact : Prop := ∀ (α : Type) (showFn : α → String) value, showIndexAny showFn value = showFn value
theorem showIndexAnyExact : ShowIndexAnyExact := by unfold ShowIndexAnyExact; intros; rfl
def showIndexSlice (indicesOutput : String) := indicesOutput
def ShowIndexSliceExact : Prop := ∀ output, showIndexSlice output = output
theorem showIndexSliceExact : ShowIndexSliceExact := by unfold ShowIndexSliceExact; intros; rfl
def showIndexLogical (maskSummary : String) := maskSummary
def ShowIndexLogicalExact : Prop := ∀ output, showIndexLogical output = output
theorem showIndexLogicalExact : ShowIndexLogicalExact := by unfold ShowIndexLogicalExact; intros; rfl
def showIndexOneTo (stop : String) := "1:" ++ stop
def ShowIndexOneToExact : Prop := ∀ stop, showIndexOneTo stop = "1:" ++ stop
theorem showIndexOneToExact : ShowIndexOneToExact := by unfold ShowIndexOneToExact; intros; rfl
def showIndexColon (_unit : Unit) := ":"
def ShowIndexColonExact : Prop := ∀ _unit : Unit, showIndexColon _unit = ":"
theorem showIndexColonExact : ShowIndexColonExact := by unfold ShowIndexColonExact; intros; rfl

def showParseError (messageRepr : String) (detail : Option String) : String :=
  detail.getD ("ParseError(" ++ messageRepr ++ ")")
def ShowParseErrorExact : Prop := ∀ messageRepr detail,
  showParseError messageRepr detail = detail.getD ("ParseError(" ++ messageRepr ++ ")")
theorem showParseErrorExact : ShowParseErrorExact := by unfold ShowParseErrorExact; intros; rfl

def showTypeNameError (differentUnionNames : Bool) : String :=
  "TypeNameError: " ++ if differentUnionNames then
    "typename does not apply to unions whose components have different typenames"
  else "typename does not apply to this type"
def ShowTypeNameErrorExact : Prop := ∀ different,
  showTypeNameError different = "TypeNameError: " ++ if different then
    "typename does not apply to unions whose components have different typenames"
  else "typename does not apply to this type"
theorem showTypeNameErrorExact : ShowTypeNameErrorExact := by unfold ShowTypeNameErrorExact; intros; rfl

def showBoundsError (collectionSummary : Option String) (indices : Option (List String)) : String :=
  "BoundsError" ++ match collectionSummary with
  | none => ""
  | some summary => ": attempt to access " ++ summary ++ match indices with
    | none => "" | some values => " at index [" ++ String.intercalate ", " values ++ "]"
def ShowBoundsErrorExact : Prop := ∀ summary indices, showBoundsError summary indices =
  "BoundsError" ++ match summary with
  | none => "" | some text => ": attempt to access " ++ text ++ match indices with
    | none => "" | some values => " at index [" ++ String.intercalate ", " values ++ "]"
theorem showBoundsErrorExact : ShowBoundsErrorExact := by unfold ShowBoundsErrorExact; intros; rfl

inductive TypeErrorCase where
  | booleanContext (gotType : String)
  | dictKey (got expected : String)
  | general (context expected got : String)
  deriving Repr, DecidableEq
def showTypeError : TypeErrorCase → String
  | .booleanContext got => "TypeError: non-boolean (" ++ got ++ ") used in boolean context"
  | .dictKey got expected => "TypeError: " ++ got ++ " is not a valid key for type " ++ expected
  | .general context expected got => "TypeError: " ++ context ++ ", expected " ++ expected ++ ", got " ++ got
def ShowTypeErrorExact : Prop := ∀ input, showTypeError input = match input with
  | .booleanContext got => "TypeError: non-boolean (" ++ got ++ ") used in boolean context"
  | .dictKey got expected => "TypeError: " ++ got ++ " is not a valid key for type " ++ expected
  | .general context expected got => "TypeError: " ++ context ++ ", expected " ++ expected ++ ", got " ++ got
theorem showTypeErrorExact : ShowTypeErrorExact := by unfold ShowTypeErrorExact; intro input; cases input <;> rfl

structure ShowWithBacktraceResult where
  errorText : String
  backtraceText : String
  deriving Repr, DecidableEq
def showErrorWithBacktrace (errorAction : R String) (backtrace : Bool) (backtraceText : String) : R ShowWithBacktraceResult :=
  match errorAction with
  | .ok errorText => .ok { errorText, backtraceText := if backtrace then backtraceText else "" }
  | .error failure => .error (failure ++ if backtrace then backtraceText else "")
def ShowErrorWithBacktraceExact : Prop := ∀ errorAction backtrace backtraceText,
  showErrorWithBacktrace errorAction backtrace backtraceText = match errorAction with
  | .ok errorText => .ok { errorText, backtraceText := if backtrace then backtraceText else "" }
  | .error failure => .error (failure ++ if backtrace then backtraceText else "")
theorem showErrorWithBacktraceExact : ShowErrorWithBacktraceExact := by
  unfold ShowErrorWithBacktraceExact
  intro errorAction backtrace backtraceText
  cases errorAction <;> rfl

def showLoadErrorBacktrace (inner file line backtraceText : String) (backtrace : Bool) : String :=
  "LoadError: " ++ inner ++ (if backtrace then backtraceText else "") ++
    "\nin expression starting at " ++ file ++ ":" ++ line
def ShowLoadErrorBacktraceExact : Prop := ∀ inner file line backtraceText backtrace,
  showLoadErrorBacktrace inner file line backtraceText backtrace = "LoadError: " ++ inner ++
    (if backtrace then backtraceText else "") ++ "\nin expression starting at " ++ file ++ ":" ++ line
theorem showLoadErrorBacktraceExact : ShowLoadErrorBacktraceExact := by unfold ShowLoadErrorBacktraceExact; intros; rfl
def showLoadError (inner file line : String) := showLoadErrorBacktrace inner file line "" false
def ShowLoadErrorExact : Prop := ∀ inner file line, showLoadError inner file line = showLoadErrorBacktrace inner file line "" false
theorem showLoadErrorExact : ShowLoadErrorExact := by unfold ShowLoadErrorExact; intros; rfl

def showInitErrorBacktrace (inner moduleName backtraceText : String) (backtrace : Bool) : String :=
  "InitError: " ++ inner ++ (if backtrace then backtraceText else "") ++ "\nduring initialization of module " ++ moduleName
def ShowInitErrorBacktraceExact : Prop := ∀ inner moduleName backtraceText backtrace,
  showInitErrorBacktrace inner moduleName backtraceText backtrace = "InitError: " ++ inner ++
    (if backtrace then backtraceText else "") ++ "\nduring initialization of module " ++ moduleName
theorem showInitErrorBacktraceExact : ShowInitErrorBacktraceExact := by unfold ShowInitErrorBacktraceExact; intros; rfl
def showInitError (inner moduleName : String) := showInitErrorBacktrace inner moduleName "" false
def ShowInitErrorExact : Prop := ∀ inner moduleName, showInitError inner moduleName = showInitErrorBacktrace inner moduleName "" false
theorem showInitErrorExact : ShowInitErrorExact := by unfold ShowInitErrorExact; intros; rfl

def showDomainError (value : String) (message : Option String) :=
  "DomainError with " ++ value ++ (match message with | none => "" | some text => ":\n" ++ text)
def ShowDomainErrorExact : Prop := ∀ value message, showDomainError value message =
  "DomainError with " ++ value ++ (match message with | none => "" | some text => ":\n" ++ text)
theorem showDomainErrorExact : ShowDomainErrorExact := by unfold ShowDomainErrorExact; intros; rfl

def showSystemError (name errorText : String) (extra : Option String) :=
  match extra with
  | none => "SystemError: " ++ name ++ ": " ++ errorText
  | some text => "SystemError (with " ++ text ++ "): " ++ name ++ ": " ++ errorText
def ShowSystemErrorExact : Prop := ∀ name errorText extra, showSystemError name errorText extra =
  match extra with
  | none => "SystemError: " ++ name ++ ": " ++ errorText
  | some text => "SystemError (with " ++ text ++ "): " ++ name ++ ": " ++ errorText
theorem showSystemErrorExact : ShowSystemErrorExact := by unfold ShowSystemErrorExact; intros; rfl

def showDivideError (_unit : Unit) := "DivideError: integer division error"
def ShowDivideErrorExact : Prop := ∀ u : Unit, showDivideError u = "DivideError: integer division error"
theorem showDivideErrorExact : ShowDivideErrorExact := by unfold ShowDivideErrorExact; intros; rfl
def showStackOverflowError (_unit : Unit) := "StackOverflowError:"
def ShowStackOverflowErrorExact : Prop := ∀ u : Unit, showStackOverflowError u = "StackOverflowError:"
theorem showStackOverflowErrorExact : ShowStackOverflowErrorExact := by unfold ShowStackOverflowErrorExact; intros; rfl
def showUndefRefError (_unit : Unit) := "UndefRefError: access to undefined reference"
def ShowUndefRefErrorExact : Prop := ∀ u : Unit, showUndefRefError u = "UndefRefError: access to undefined reference"
theorem showUndefRefErrorExact : ShowUndefRefErrorExact := by unfold ShowUndefRefErrorExact; intros; rfl
def showEofError (_unit : Unit) := "EOFError: read end of file"
def ShowEofErrorExact : Prop := ∀ u : Unit, showEofError u = "EOFError: read end of file"
theorem showEofErrorExact : ShowEofErrorExact := by unfold ShowEofErrorExact; intros; rfl
def showErrorException (message : String) := message
def ShowErrorExceptionExact : Prop := ∀ message, showErrorException message = message
theorem showErrorExceptionExact : ShowErrorExceptionExact := by unfold ShowErrorExceptionExact; intros; rfl
def showKeyError (keyShown : String) := "KeyError: key " ++ keyShown ++ " not found"
def ShowKeyErrorExact : Prop := ∀ key, showKeyError key = "KeyError: key " ++ key ++ " not found"
theorem showKeyErrorExact : ShowKeyErrorExact := by unfold ShowKeyErrorExact; intros; rfl
def showInterruptException (_unit : Unit) := "InterruptException:"
def ShowInterruptExceptionExact : Prop := ∀ u : Unit, showInterruptException u = "InterruptException:"
theorem showInterruptExceptionExact : ShowInterruptExceptionExact := by unfold ShowInterruptExceptionExact; intros; rfl
def showArgumentError (message : String) := "ArgumentError: " ++ message
def ShowArgumentErrorExact : Prop := ∀ message, showArgumentError message = "ArgumentError: " ++ message
theorem showArgumentErrorExact : ShowArgumentErrorExact := by unfold ShowArgumentErrorExact; intros; rfl
def showDimensionMismatch (message : String) := "DimensionMismatch: " ++ message
def ShowDimensionMismatchExact : Prop := ∀ message, showDimensionMismatch message = "DimensionMismatch: " ++ message
theorem showDimensionMismatchExact : ShowDimensionMismatchExact := by unfold ShowDimensionMismatchExact; intros; rfl
def showAssertionError (message : String) := "AssertionError: " ++ message
def ShowAssertionErrorExact : Prop := ∀ message, showAssertionError message = "AssertionError: " ++ message
theorem showAssertionErrorExact : ShowAssertionErrorExact := by unfold ShowAssertionErrorExact; intros; rfl
def showOverflowError (message : String) := "OverflowError: " ++ message
def ShowOverflowErrorExact : Prop := ∀ message, showOverflowError message = "OverflowError: " ++ message
theorem showOverflowErrorExact : ShowOverflowErrorExact := by unfold ShowOverflowErrorExact; intros; rfl
def showUndefKeywordError (name : String) := "UndefKeywordError: keyword argument `" ++ name ++ "` not assigned"
def ShowUndefKeywordErrorExact : Prop := ∀ name, showUndefKeywordError name = "UndefKeywordError: keyword argument `" ++ name ++ "` not assigned"
theorem showUndefKeywordErrorExact : ShowUndefKeywordErrorExact := by unfold ShowUndefKeywordErrorExact; intros; rfl

inductive UndefScopeM where | absent | moduleName (name : String) | staticParameter | localKind (name : String) deriving Repr, DecidableEq
def showUndefVarError (name : String) : UndefScopeM → String
  | .absent => "UndefVarError: `" ++ name ++ "` not defined"
  | .moduleName scope => "UndefVarError: `" ++ name ++ "` not defined in `" ++ scope ++ "`"
  | .staticParameter => "UndefVarError: `" ++ name ++ "` not defined in static parameter matching"
  | .localKind scope => "UndefVarError: `" ++ name ++ "` not defined in " ++ scope ++ " scope"
def ShowUndefVarErrorExact : Prop := ∀ name scope, showUndefVarError name scope = match scope with
  | .absent => "UndefVarError: `" ++ name ++ "` not defined"
  | .moduleName value => "UndefVarError: `" ++ name ++ "` not defined in `" ++ value ++ "`"
  | .staticParameter => "UndefVarError: `" ++ name ++ "` not defined in static parameter matching"
  | .localKind value => "UndefVarError: `" ++ name ++ "` not defined in " ++ value ++ " scope"
theorem showUndefVarErrorExact : ShowUndefVarErrorExact := by
  unfold ShowUndefVarErrorExact
  intro name scope
  cases scope <;> rfl

def showInexactError (functionName typeName typeShown firstArg : String) (rest : List String) :=
  "InexactError: " ++ functionName ++ "(" ++ (if typeName = functionName then "" else typeShown ++ ", ") ++
    String.intercalate ", " (firstArg :: rest) ++ ")"
def ShowInexactErrorExact : Prop := ∀ functionName typeName typeShown firstArg rest,
  showInexactError functionName typeName typeShown firstArg rest = "InexactError: " ++ functionName ++ "(" ++
    (if typeName = functionName then "" else typeShown ++ ", ") ++ String.intercalate ", " (firstArg :: rest) ++ ")"
theorem showInexactErrorExact : ShowInexactErrorExact := by unfold ShowInexactErrorExact; intros; rfl
def showCanonicalIndexError (functionName typeShown : String) := "CanonicalIndexError: " ++ functionName ++ " not defined for " ++ typeShown
def ShowCanonicalIndexErrorExact : Prop := ∀ f t, showCanonicalIndexError f t = "CanonicalIndexError: " ++ f ++ " not defined for " ++ t
theorem showCanonicalIndexErrorExact : ShowCanonicalIndexErrorExact := by unfold ShowCanonicalIndexErrorExact; intros; rfl

def typesOf (runtimeTypes : List String) := runtimeTypes
def TypesOfExact : Prop := ∀ types, typesOf types = types
theorem typesOfExact : TypesOfExact := by unfold TypesOfExact; intros; rfl

def printWithCompareDataType (sameName : Bool) (name : String) (left right : List TypeTree) : List DiffToken :=
  if sameName then typeDiff (.node name left) (.node name right) else [.mismatch (renderTypeTree (.node name left))]
def PrintWithCompareDataTypeExact : Prop := ∀ sameName name left right, printWithCompareDataType sameName name left right =
  if sameName then typeDiff (.node name left) (.node name right) else [.mismatch (renderTypeTree (.node name left))]
theorem printWithCompareDataTypeExact : PrintWithCompareDataTypeExact := by unfold PrintWithCompareDataTypeExact; intros; rfl
def printWithCompareAny (sameIdentity : Bool) (shown : String) : DiffToken := if sameIdentity then .same shown else .mismatch shown
def PrintWithCompareAnyExact : Prop := ∀ sameIdentity shown, printWithCompareAny sameIdentity shown = if sameIdentity then .same shown else .mismatch shown
theorem printWithCompareAnyExact : PrintWithCompareAnyExact := by unfold PrintWithCompareAnyExact; intros; rfl

def showConvertError (target : Option String) (source firstArgument : String) := match target with
  | none => "First argument to `convert` must be a Type, got " ++ firstArgument
  | some type => "Cannot `convert` an object of type " ++ source ++ " to an object of type " ++ type
def ShowConvertErrorExact : Prop := ∀ target source firstArgument, showConvertError target source firstArgument = match target with
  | none => "First argument to `convert` must be a Type, got " ++ firstArgument
  | some type => "Cannot `convert` an object of type " ++ source ++ " to an object of type " ++ type
theorem showConvertErrorExact : ShowConvertErrorExact := by
  unfold ShowConvertErrorExact
  intro target source firstArgument
  cases target <;> rfl

inductive MethodErrorCase where
  | convert (text : String)
  | abstractConstructor (type : String)
  | noncallable (type : String)
  | standard (signature : String)
  deriving Repr, DecidableEq

def methodErrorCore : MethodErrorCase → String
  | .convert text => text
  | .abstractConstructor type => "no constructors have been defined for " ++ type
  | .noncallable type => "objects of type " ++ type ++ " are not callable."
  | .standard signature => "no method matching " ++ signature
def showMethodError (input : MethodErrorCase) (hints candidates : List String) : String :=
  "MethodError: " ++ methodErrorCore input ++
    String.intercalate "" hints ++ String.intercalate "" candidates
def ShowMethodErrorExact : Prop := ∀ input hints candidates, showMethodError input hints candidates =
  "MethodError: " ++ methodErrorCore input ++
    String.intercalate "" hints ++ String.intercalate "" candidates
theorem showMethodErrorExact : ShowMethodErrorExact := by unfold ShowMethodErrorExact; intros; rfl

def showFieldError (typeName field hint : String) := "FieldError: type " ++ typeName ++ " has no field `" ++ field ++ "`" ++ hint
def ShowFieldErrorExact : Prop := ∀ typeName field hint, showFieldError typeName field hint = "FieldError: type " ++ typeName ++ " has no field `" ++ field ++ "`" ++ hint
theorem showFieldErrorExact : ShowFieldErrorExact := by unfold ShowFieldErrorExact; intros; rfl
def stripTypeYes (typeName : String) : Option String := some typeName
def StripTypeYesExact : Prop := ∀ typeName, stripTypeYes typeName = some typeName
theorem stripTypeYesExact : StripTypeYesExact := by unfold StripTypeYesExact; intros; rfl
def stripTypeNo (_value : String) : Option String := none
def StripTypeNoExact : Prop := ∀ value, stripTypeNo value = none
theorem stripTypeNoExact : StripTypeNoExact := by unfold StripTypeNoExact; intros; rfl
def showAmbiguousError (signature : String) (candidates : List String) (fix : Option String) :=
  "MethodError: " ++ signature ++ " is ambiguous.\n\nCandidates:\n" ++ String.intercalate "\n" candidates ++ fix.getD ""
def ShowAmbiguousErrorExact : Prop := ∀ signature candidates fix, showAmbiguousError signature candidates fix =
  "MethodError: " ++ signature ++ " is ambiguous.\n\nCandidates:\n" ++ String.intercalate "\n" candidates ++ fix.getD ""
theorem showAmbiguousErrorExact : ShowAmbiguousErrorExact := by unfold ShowAmbiguousErrorExact; intros; rfl

def showErrorNoStdio (message staticShown : String) := message ++ ":\n" ++ staticShown ++ "\n"
def ShowErrorNoStdioExact : Prop := ∀ message staticShown,
  showErrorNoStdio message staticShown = message ++ ":\n" ++ staticShown ++ "\n"
theorem showErrorNoStdioExact : ShowErrorNoStdioExact := by unfold ShowErrorNoStdioExact; intros; rfl

def stacktraceExpandBasepaths (environment : Option Bool) : Bool := environment.getD false
def StacktraceExpandBasepathsExact : Prop := ∀ environment, stacktraceExpandBasepaths environment = environment.getD false
theorem stacktraceExpandBasepathsExact : StacktraceExpandBasepathsExact := by unfold StacktraceExpandBasepathsExact; intros; rfl
def stacktraceContractUserdir (environment : Option Bool) : Bool := environment.getD true
def StacktraceContractUserdirExact : Prop := ∀ environment, stacktraceContractUserdir environment = environment.getD true
theorem stacktraceContractUserdirExact : StacktraceContractUserdirExact := by unfold StacktraceContractUserdirExact; intros; rfl
def stacktraceLinebreaks (environment : Option Bool) : Bool := environment.getD false
def StacktraceLinebreaksExact : Prop := ∀ environment, stacktraceLinebreaks environment = environment.getD false
theorem stacktraceLinebreaksExact : StacktraceLinebreaksExact := by unfold StacktraceLinebreaksExact; intros; rfl
def stacktraceFullLoading (environment : Option Bool) : Bool := environment.getD false
def StacktraceFullLoadingExact : Prop := ∀ environment, stacktraceFullLoading environment = environment.getD false
theorem stacktraceFullLoadingExact : StacktraceFullLoadingExact := by unfold StacktraceFullLoadingExact; intros; rfl

def showTypeDiff (signature called : TypeTree) := typeDiff signature called
def ShowTypeDiffExact : Prop := ∀ signature called, showTypeDiff signature called = typeDiff signature called
theorem showTypeDiffExact : ShowTypeDiffExact := by unfold ShowTypeDiffExact; intros; rfl
def showSeparatorFaithful (color : Bool) := showSeparator color
def ShowSeparatorFaithfulExact : Prop := ∀ color, showSeparatorFaithful color = showSeparator color
theorem showSeparatorFaithfulExact : ShowSeparatorFaithfulExact := by unfold ShowSeparatorFaithfulExact; intros; rfl
def showTypeMatch (typeText : String) (color : Bool) : List DiffToken :=
  if color then [.literal "light-black", .same typeText, .literal "default"] else [.same typeText]
def ShowTypeMatchExact : Prop := ∀ typeText color, showTypeMatch typeText color =
  if color then [.literal "light-black", .same typeText, .literal "default"] else [.same typeText]
theorem showTypeMatchExact : ShowTypeMatchExact := by unfold ShowTypeMatchExact; intros; rfl
def showNamedtupleDiff (compatible : Bool) (tokens : List DiffToken) : Option (List DiffToken) := if compatible then some tokens else none
def ShowNamedtupleDiffExact : Prop := ∀ compatible tokens, showNamedtupleDiff compatible tokens = if compatible then some tokens else none
theorem showNamedtupleDiffExact : ShowNamedtupleDiffExact := by unfold ShowNamedtupleDiffExact; intros; rfl
def descendParams (sameName nonempty : Bool) (signature called : List TypeTree) : Option (List TypeTree × List TypeTree) :=
  if sameName && nonempty then some (signature, called) else none
def DescendParamsExact : Prop := ∀ sameName nonempty signature called, descendParams sameName nonempty signature called =
  if sameName && nonempty then some (signature, called) else none
theorem descendParamsExact : DescendParamsExact := by unfold DescendParamsExact; intros; rfl
def showTypeMismatchFaithful (typeText : String) (color topLevel : Bool) := showTypeMismatch typeText topLevel color
def ShowTypeMismatchFaithfulExact : Prop := ∀ typeText color topLevel,
  showTypeMismatchFaithful typeText color topLevel = showTypeMismatch typeText topLevel color
theorem showTypeMismatchFaithfulExact : ShowTypeMismatchFaithfulExact := by unfold ShowTypeMismatchFaithfulExact; intros; rfl
def resolvesToSelf (moduleDefined parentSame : Bool) := !moduleDefined || parentSame
def ResolvesToSelfExact : Prop := ∀ moduleDefined parentSame, resolvesToSelf moduleDefined parentSame = (!moduleDefined || parentSame)
theorem resolvesToSelfExact : ResolvesToSelfExact := by unfold ResolvesToSelfExact; intros; rfl
def showShadowedTypeHint (reported : List String) (candidate : String) : List String :=
  if reported.contains candidate then reported else reported ++ [candidate]
def ShowShadowedTypeHintExact : Prop := ∀ reported candidate, showShadowedTypeHint reported candidate =
  if reported.contains candidate then reported else reported ++ [candidate]
theorem showShadowedTypeHintExact : ShowShadowedTypeHintExact := by unfold ShowShadowedTypeHintExact; intros; rfl

def showMethodCandidates (candidates : List Candidate) : List Candidate := (sortCandidates candidates).take 3
def ShowMethodCandidatesExact : Prop := ∀ candidates, showMethodCandidates candidates = (sortCandidates candidates).take 3
theorem showMethodCandidatesExact : ShowMethodCandidatesExact := by unfold ShowMethodCandidatesExact; intros; rfl

def getStacktraceColor (existing : Option String) (next : String) : String := existing.getD next
def GetStacktraceColorExact : Prop := ∀ existing next, getStacktraceColor existing next = existing.getD next
theorem getStacktraceColorExact : GetStacktraceColorExact := by unfold GetStacktraceColorExact; intros; rfl

structure CycleSummary where
  displayed : List (String × Nat)
  cycles : List RepeatedCycle
  maxNested : Nat
  deriving Repr, DecidableEq
def findAndRemoveCycles (trace : List String) : CycleSummary :=
  let displayed := collapseRepeatedFrames trace
  { displayed, cycles := [], maxNested := if displayed.any (fun item => 1 < item.2) then 1 else 0 }
def FindAndRemoveCyclesExact : Prop := ∀ trace, findAndRemoveCycles trace =
  let displayed := collapseRepeatedFrames trace
  { displayed, cycles := [], maxNested := if displayed.any (fun item => 1 < item.2) then 1 else 0 }
theorem findAndRemoveCyclesExact : FindAndRemoveCyclesExact := by unfold FindAndRemoveCyclesExact; intros; rfl

def repetitionClosings (line frameCounter active : Nat) (cycles : List CycleClosing) :=
  closeRepetitions line frameCounter active cycles
def RepetitionClosingsExact : Prop := ∀ line frameCounter active cycles,
  repetitionClosings line frameCounter active cycles = closeRepetitions line frameCounter active cycles
theorem repetitionClosingsExact : RepetitionClosingsExact := by unfold RepetitionClosingsExact; intros; rfl

def showProcessedBacktrace (frames : List String) (linebreaks : Bool) :=
  "\nStacktrace:\n" ++ String.intercalate (if linebreaks then "\n\n" else "\n") frames
def ShowProcessedBacktraceExact : Prop := ∀ frames linebreaks, showProcessedBacktrace frames linebreaks =
  "\nStacktrace:\n" ++ String.intercalate (if linebreaks then "\n\n" else "\n") frames
theorem showProcessedBacktraceExact : ShowProcessedBacktraceExact := by unfold ShowProcessedBacktraceExact; intros; rfl

def printStackframeColorLookup (moduleColor rendered : String) := (moduleColor, rendered)
def PrintStackframeColorLookupExact : Prop := ∀ color rendered, printStackframeColorLookup color rendered = (color, rendered)
theorem printStackframeColorLookupExact : PrintStackframeColorLookupExact := by unfold PrintStackframeColorLookupExact; intros; rfl
def parentmoduleBeforeMain (parents : List String) : Option String := parentBeforeMain parents
def ParentmoduleBeforeMainExact : Prop := ∀ parents, parentmoduleBeforeMain parents = parentBeforeMain parents
theorem parentmoduleBeforeMainExact : ParentmoduleBeforeMainExact := by unfold ParentmoduleBeforeMainExact; intros; rfl
def parentmoduleBeforeMainObject (parents : List String) := parentmoduleBeforeMain parents
def ParentmoduleBeforeMainObjectExact : Prop := ∀ parents, parentmoduleBeforeMainObject parents = parentmoduleBeforeMain parents
theorem parentmoduleBeforeMainObjectExact : ParentmoduleBeforeMainObjectExact := by unfold ParentmoduleBeforeMainObjectExact; intros; rfl
def printStackframeLayout (linePrefix signature location : String) (number width active starts : Nat) (inlined : Bool) :=
  stackFrameLayout linePrefix signature location number width active starts inlined
def PrintStackframeLayoutExact : Prop := ∀ linePrefix signature location number width active starts inlined,
  printStackframeLayout linePrefix signature location number width active starts inlined =
    stackFrameLayout linePrefix signature location number width active starts inlined
theorem printStackframeLayoutExact : PrintStackframeLayoutExact := by unfold PrintStackframeLayoutExact; intros; rfl
def printModulePathFile (moduleName directory file : String) (line column : Int) := modulePathFile moduleName directory file line column
def PrintModulePathFileExact : Prop := ∀ moduleName directory file line column,
  printModulePathFile moduleName directory file line column = modulePathFile moduleName directory file line column
theorem printModulePathFileExact : PrintModulePathFileExact := by unfold PrintModulePathFileExact; intros; rfl
def showBacktrace (empty singleUnknown large : Bool) := showBacktraceRoute empty singleUnknown large
def ShowBacktraceExact : Prop := ∀ empty singleUnknown large,
  showBacktrace empty singleUnknown large = showBacktraceRoute empty singleUnknown large
theorem showBacktraceExact : ShowBacktraceExact := by unfold ShowBacktraceExact; intros; rfl
def collapseAndCountRepeatedFrames (frames : List TraceEntry) := collapseRepeatedFrames frames
def CollapseAndCountRepeatedFramesExact : Prop := ∀ frames,
  collapseAndCountRepeatedFrames frames = collapseRepeatedFrames frames
theorem collapseAndCountRepeatedFramesExact : CollapseAndCountRepeatedFramesExact := by unfold CollapseAndCountRepeatedFramesExact; intros; rfl
def removeKwcallFramesFaithful (frames : List TraceEntry) := removeKwcallFrames frames
def RemoveKwcallFramesExact : Prop := ∀ frames, removeKwcallFramesFaithful frames = frames.filter fun frame => !frame.removeKwcall
theorem removeKwcallFramesExact : RemoveKwcallFramesExact := by unfold RemoveKwcallFramesExact removeKwcallFramesFaithful; intros; rfl
def simplifyIncludeFrames (frames : List TraceEntry) := simplifyIncludes frames
def SimplifyIncludeFramesExact : Prop := ∀ frames, simplifyIncludeFrames frames = frames.filter fun frame => frame.keepInclude
theorem simplifyIncludeFramesExact : SimplifyIncludeFramesExact := by unfold SimplifyIncludeFramesExact simplifyIncludeFrames; intros; rfl
def isLoadingFrameFaithful (frame : TraceEntry) := isLoadingFrame frame
def IsLoadingFrameExact : Prop := ∀ frame, isLoadingFrameFaithful frame = frame.loadingFrame
theorem isLoadingFrameExact : IsLoadingFrameExact := by unfold IsLoadingFrameExact isLoadingFrameFaithful; intros; rfl
def isLoadingAnchorFaithful (frame : TraceEntry) := isLoadingAnchor frame
def IsLoadingAnchorExact : Prop := ∀ frame, isLoadingAnchorFaithful frame = frame.loadingAnchor
theorem isLoadingAnchorExact : IsLoadingAnchorExact := by unfold IsLoadingAnchorExact isLoadingAnchorFaithful; intros; rfl
def simplifyLoadingFrames (full : Bool) (frames : List TraceEntry) := simplifyLoading full frames
def SimplifyLoadingFramesExact : Prop := ∀ full frames, simplifyLoadingFrames full frames =
  if full then frames else frames.filter fun frame => !frame.loadingFrame || frame.loadingAnchor
theorem simplifyLoadingFramesExact : SimplifyLoadingFramesExact := by unfold SimplifyLoadingFramesExact simplifyLoadingFrames; intros; rfl
def collapseRepeatedLocations (frames : List TraceEntry) := collapseLocations frames
def CollapseRepeatedLocationsExact : Prop := ∀ frames, collapseRepeatedLocations frames = frames.filter fun frame => frame.keepLocation
theorem collapseRepeatedLocationsExact : CollapseRepeatedLocationsExact := by unfold CollapseRepeatedLocationsExact collapseRepeatedLocations; intros; rfl
def processBacktraceFrames (full : Bool) (frames : List TraceEntry) := processBacktrace full frames
def ProcessBacktraceFramesExact : Prop := ∀ full frames, processBacktraceFrames full frames = processBacktrace full frames
theorem processBacktraceFramesExact : ProcessBacktraceFramesExact := by unfold ProcessBacktraceFramesExact; intros; rfl
def processBacktraceCounted (full : Bool) (frames : List TraceEntry) := processBacktrace full frames
def ProcessBacktraceCountedExact : Prop := ∀ full frames, processBacktraceCounted full frames = processBacktrace full frames
theorem processBacktraceCountedExact : ProcessBacktraceCountedExact := by unfold ProcessBacktraceCountedExact; intros; rfl
def showExceptionStackFaithful (exceptions : List String) := showExceptionStack exceptions
def ShowExceptionStackFaithfulExact : Prop := ∀ exceptions,
  showExceptionStackFaithful exceptions = String.intercalate "\ncaused by: " exceptions.reverse
theorem showExceptionStackFaithfulExact : ShowExceptionStackFaithfulExact := by unfold ShowExceptionStackFaithfulExact showExceptionStackFaithful; intros; rfl
def showInterpreterIpFaithful (typeName code moduleName : String) (statement : Int) (topLevel : Bool) :=
  showInterpreterIP typeName code moduleName statement topLevel
def ShowInterpreterIpExact : Prop := ∀ typeName code moduleName statement topLevel,
  showInterpreterIpFaithful typeName code moduleName statement topLevel =
    showInterpreterIP typeName code moduleName statement topLevel
theorem showInterpreterIpExact : ShowInterpreterIpExact := by unfold ShowInterpreterIpExact; intros; rfl

def noncallableNumberHint (isNumber : Bool) : Option String :=
  if isNumber then some "Maybe you forgot to use an operator such as *, ^, %, / etc. ?" else none
def NoncallableNumberHintExact : Prop := ∀ isNumber, noncallableNumberHint isNumber =
  if isNumber then some "Maybe you forgot to use an operator such as *, ^, %, / etc. ?" else none
theorem noncallableNumberHintExact : NoncallableNumberHintExact := by unfold NoncallableNumberHintExact; intros; rfl
inductive NonsettableCase where | none | number | typeValue (name : String) deriving Repr, DecidableEq
def nonsettableHint : NonsettableCase → Option String
  | .none => none | .number => some "Use a[1, 2] rather than a[1][2]"
  | .typeValue name => some ("Construct " ++ name ++ " before indexing it")
def NonsettableHintExact : Prop := ∀ input, nonsettableHint input = match input with
  | .none => none | .number => some "Use a[1, 2] rather than a[1][2]"
  | .typeValue name => some ("Construct " ++ name ++ " before indexing it")
theorem nonsettableHintExact : NonsettableHintExact := by unfold NonsettableHintExact; intro input; cases input <;> rfl
def stringConcatenationHint (condition : Bool) := if condition then some "String concatenation is performed with *" else none
def StringConcatenationHintExact : Prop := ∀ condition, stringConcatenationHint condition = if condition then some "String concatenation is performed with *" else none
theorem stringConcatenationHintExact : StringConcatenationHintExact := by unfold StringConcatenationHintExact; intros; rfl
def stringReplaceHint (condition : Bool) := if condition then some "Strings cannot be modified with replace!; use replace" else none
def StringReplaceHintExact : Prop := ∀ condition, stringReplaceHint condition = if condition then some "Strings cannot be modified with replace!; use replace" else none
theorem stringReplaceHintExact : StringReplaceHintExact := by unfold StringReplaceHintExact; intros; rfl
def methodsOnIterable (maximumMinimum lengthSize : Option String) : List String := maximumMinimum.toList ++ lengthSize.toList
def MethodsOnIterableExact : Prop := ∀ first second, methodsOnIterable first second = first.toList ++ second.toList
theorem methodsOnIterableExact : MethodsOnIterableExact := by unfold MethodsOnIterableExact; intros; rfl
def fieldErrorDictHint (isDict : Bool) (field : String) := if isDict then some ("dict[:" ++ field ++ "]") else none
def FieldErrorDictHintExact : Prop := ∀ isDict field, fieldErrorDictHint isDict field = if isDict then some ("dict[:" ++ field ++ "]") else none
theorem fieldErrorDictHintExact : FieldErrorDictHintExact := by unfold FieldErrorDictHintExact; intros; rfl
def fieldErrorListHint (fields properties : List String) := (fields, properties.filter fun property => !fields.contains property)
def FieldErrorListHintExact : Prop := ∀ fields properties, fieldErrorListHint fields properties =
  (fields, properties.filter fun property => !fields.contains property)
theorem fieldErrorListHintExact : FieldErrorListHintExact := by unfold FieldErrorListHintExact; intros; rfl
def propertyNamesByType (custom : Bool) (inferred : Option (List String)) := if custom then inferred else none
def PropertyNamesByTypeExact : Prop := ∀ custom inferred, propertyNamesByType custom inferred = if custom then inferred else none
theorem propertyNamesByTypeExact : PropertyNamesByTypeExact := by unfold PropertyNamesByTypeExact; intros; rfl
def applyTypeUnionallHint (condition : Bool) (got : String) := if condition then some ("`" ++ got ++ "` takes no type parameters.") else none
def ApplyTypeUnionallHintExact : Prop := ∀ condition got, applyTypeUnionallHint condition got =
  if condition then some ("`" ++ got ++ "` takes no type parameters.") else none
theorem applyTypeUnionallHintExact : ApplyTypeUnionallHintExact := by unfold ApplyTypeUnionallHintExact; intros; rfl
def undefVarErrorHint (scopeMessages baseMessages loadedMessages finalMessages : List String) :=
  scopeMessages ++ baseMessages ++ loadedMessages ++ finalMessages
def UndefVarErrorHintExact : Prop := ∀ a b c d, undefVarErrorHint a b c d = a ++ b ++ c ++ d
theorem undefVarErrorHintExact : UndefVarErrorHintExact := by unfold UndefVarErrorHintExact; intros; rfl
def undefVarWarnFor (warnings : List String) : Bool × List String := (!warnings.isEmpty, warnings)
def UndefVarWarnForExact : Prop := ∀ warnings, undefVarWarnFor warnings = (!warnings.isEmpty, warnings)
theorem undefVarWarnForExact : UndefVarWarnForExact := by unfold UndefVarWarnForExact; intros; rfl
def exceptionStackSize (stack : List String) := stack.length
def ExceptionStackSizeExact : Prop := ∀ stack, exceptionStackSize stack = stack.length
theorem exceptionStackSizeExact : ExceptionStackSizeExact := by unfold ExceptionStackSizeExact; intros; rfl
def exceptionStackGet? (stack : List String) (index : Nat) := stack[index]?
def ExceptionStackGetExact : Prop := ∀ stack index, exceptionStackGet? stack index = stack[index]?
theorem exceptionStackGetExact : ExceptionStackGetExact := by unfold ExceptionStackGetExact; intros; rfl
def showExceptionStackPlain (stack : List String) :=
  toString stack.length ++ "-element ExceptionStack" ++ (if stack.isEmpty then "" else ":\n") ++
    String.intercalate "\ncaused by: " stack.reverse
def ShowExceptionStackPlainExact : Prop := ∀ stack, showExceptionStackPlain stack =
  toString stack.length ++ "-element ExceptionStack" ++ (if stack.isEmpty then "" else ":\n") ++
    String.intercalate "\ncaused by: " stack.reverse
theorem showExceptionStackPlainExact : ShowExceptionStackPlainExact := by unfold ShowExceptionStackPlainExact; intros; rfl
def showExceptionStackCompact (stack : List String) := showExceptionStackPlain stack
def ShowExceptionStackCompactExact : Prop := ∀ stack, showExceptionStackCompact stack = showExceptionStackPlain stack
theorem showExceptionStackCompactExact : ShowExceptionStackCompactExact := by unfold ShowExceptionStackCompactExact; intros; rfl
inductive IncompleteInput where | other | empty | text (kind : String) | nested (tag : String) deriving Repr, DecidableEq
def incompleteTag : IncompleteInput → String
  | .other => "none" | .empty => "other" | .text kind => kind | .nested tag => tag
def IncompleteTagAnyExact : Prop := ∀ _value : String, incompleteTag .other = "none"
theorem incompleteTagAnyExact : IncompleteTagAnyExact := by unfold IncompleteTagAnyExact; intros; rfl
def IncompleteTagExprExact : Prop := ∀ input, incompleteTag input = match input with
  | .other => "none" | .empty => "other" | .text kind => kind | .nested tag => tag
theorem incompleteTagExprExact : IncompleteTagExprExact := by unfold IncompleteTagExprExact; intro input; cases input <;> rfl
def incompleteTagParseError (detail : IncompleteInput) := incompleteTag detail
def IncompleteTagParseErrorExact : Prop := ∀ detail, incompleteTagParseError detail = incompleteTag detail
theorem incompleteTagParseErrorExact : IncompleteTagParseErrorExact := by unfold IncompleteTagParseErrorExact; intros; rfl

end JuliaLean.ErrorShow.ErrorshowFaithful

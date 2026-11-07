import JuliaLean.base.errorshow
import JuliaLean.Proofs.base.errorshow.retainedCoverage

/-! Method-specific models for `base/errorshow.jl` at `bbfa0ce4150`. -/

namespace JuliaLean.ErrorShow.ErrorshowFaithful

open JuliaLean.ErrorShow
open JuliaLean.ErrorShow.Coverage


def ShowerrorFallbackExact : Prop := ∀ (α : Type) (showFn : α → String) value,
  showerrorFallback showFn value = showFn value
theorem showerrorFallbackExact : ShowerrorFallbackExact := by unfold ShowerrorFallbackExact; intros; rfl

def ShowIndexAnyExact : Prop := ∀ (α : Type) (showFn : α → String) value, showIndexAny showFn value = showFn value
theorem showIndexAnyExact : ShowIndexAnyExact := by unfold ShowIndexAnyExact; intros; rfl
def ShowIndexSliceExact : Prop := ∀ output, showIndexSlice output = output
theorem showIndexSliceExact : ShowIndexSliceExact := by unfold ShowIndexSliceExact; intros; rfl
def ShowIndexLogicalExact : Prop := ∀ output, showIndexLogical output = output
theorem showIndexLogicalExact : ShowIndexLogicalExact := by unfold ShowIndexLogicalExact; intros; rfl
def ShowIndexOneToExact : Prop := ∀ stop, showIndexOneTo stop = "1:" ++ stop
theorem showIndexOneToExact : ShowIndexOneToExact := by unfold ShowIndexOneToExact; intros; rfl
def ShowIndexColonExact : Prop := ∀ _unit : Unit, showIndexColon _unit = ":"
theorem showIndexColonExact : ShowIndexColonExact := by unfold ShowIndexColonExact; intros; rfl

def ShowParseErrorExact : Prop := ∀ messageRepr detail,
  showParseError messageRepr detail = detail.getD ("ParseError(" ++ messageRepr ++ ")")
theorem showParseErrorExact : ShowParseErrorExact := by unfold ShowParseErrorExact; intros; rfl

def ShowTypeNameErrorExact : Prop := ∀ different,
  showTypeNameError different = "TypeNameError: " ++ if different then
    "typename does not apply to unions whose components have different typenames"
  else "typename does not apply to this type"
theorem showTypeNameErrorExact : ShowTypeNameErrorExact := by unfold ShowTypeNameErrorExact; intros; rfl

def ShowBoundsErrorExact : Prop := ∀ summary indices, showBoundsError summary indices =
  "BoundsError" ++ match summary with
  | none => "" | some text => ": attempt to access " ++ text ++ match indices with
    | none => "" | some values => " at index [" ++ String.intercalate ", " values ++ "]"
theorem showBoundsErrorExact : ShowBoundsErrorExact := by unfold ShowBoundsErrorExact; intros; rfl

def ShowTypeErrorExact : Prop := ∀ input, showTypeError input = match input with
  | .booleanContext got => "TypeError: non-boolean (" ++ got ++ ") used in boolean context"
  | .dictKey got expected => "TypeError: " ++ got ++ " is not a valid key for type " ++ expected
  | .general context expected got => "TypeError: " ++ context ++ ", expected " ++ expected ++ ", got " ++ got
theorem showTypeErrorExact : ShowTypeErrorExact := by unfold ShowTypeErrorExact; intro input; cases input <;> rfl

def ShowErrorWithBacktraceExact : Prop := ∀ errorAction backtrace backtraceText,
  showErrorWithBacktrace errorAction backtrace backtraceText = match errorAction with
  | .ok errorText => .ok { errorText, backtraceText := if backtrace then backtraceText else "" }
  | .error failure => .error (failure ++ if backtrace then backtraceText else "")
theorem showErrorWithBacktraceExact : ShowErrorWithBacktraceExact := by
  unfold ShowErrorWithBacktraceExact
  intro errorAction backtrace backtraceText
  cases errorAction <;> rfl

def ShowLoadErrorBacktraceExact : Prop := ∀ inner file line backtraceText backtrace,
  showLoadErrorBacktrace inner file line backtraceText backtrace = "LoadError: " ++ inner ++
    (if backtrace then backtraceText else "") ++ "\nin expression starting at " ++ file ++ ":" ++ line
theorem showLoadErrorBacktraceExact : ShowLoadErrorBacktraceExact := by unfold ShowLoadErrorBacktraceExact; intros; rfl
def ShowLoadErrorExact : Prop := ∀ inner file line, showLoadError inner file line = showLoadErrorBacktrace inner file line "" false
theorem showLoadErrorExact : ShowLoadErrorExact := by unfold ShowLoadErrorExact; intros; rfl

def ShowInitErrorBacktraceExact : Prop := ∀ inner moduleName backtraceText backtrace,
  showInitErrorBacktrace inner moduleName backtraceText backtrace = "InitError: " ++ inner ++
    (if backtrace then backtraceText else "") ++ "\nduring initialization of module " ++ moduleName
theorem showInitErrorBacktraceExact : ShowInitErrorBacktraceExact := by unfold ShowInitErrorBacktraceExact; intros; rfl
def ShowInitErrorExact : Prop := ∀ inner moduleName, showInitError inner moduleName = showInitErrorBacktrace inner moduleName "" false
theorem showInitErrorExact : ShowInitErrorExact := by unfold ShowInitErrorExact; intros; rfl

def ShowDomainErrorExact : Prop := ∀ value message, showDomainError value message =
  "DomainError with " ++ value ++ (match message with | none => "" | some text => ":\n" ++ text)
theorem showDomainErrorExact : ShowDomainErrorExact := by unfold ShowDomainErrorExact; intros; rfl

def ShowSystemErrorExact : Prop := ∀ name errorText extra, showSystemError name errorText extra =
  match extra with
  | none => "SystemError: " ++ name ++ ": " ++ errorText
  | some text => "SystemError (with " ++ text ++ "): " ++ name ++ ": " ++ errorText
theorem showSystemErrorExact : ShowSystemErrorExact := by unfold ShowSystemErrorExact; intros; rfl

def ShowDivideErrorExact : Prop := ∀ u : Unit, showDivideError u = "DivideError: integer division error"
theorem showDivideErrorExact : ShowDivideErrorExact := by unfold ShowDivideErrorExact; intros; rfl
def ShowStackOverflowErrorExact : Prop := ∀ u : Unit, showStackOverflowError u = "StackOverflowError:"
theorem showStackOverflowErrorExact : ShowStackOverflowErrorExact := by unfold ShowStackOverflowErrorExact; intros; rfl
def ShowUndefRefErrorExact : Prop := ∀ u : Unit, showUndefRefError u = "UndefRefError: access to undefined reference"
theorem showUndefRefErrorExact : ShowUndefRefErrorExact := by unfold ShowUndefRefErrorExact; intros; rfl
def ShowEofErrorExact : Prop := ∀ u : Unit, showEofError u = "EOFError: read end of file"
theorem showEofErrorExact : ShowEofErrorExact := by unfold ShowEofErrorExact; intros; rfl
def ShowErrorExceptionExact : Prop := ∀ message, showErrorException message = message
theorem showErrorExceptionExact : ShowErrorExceptionExact := by unfold ShowErrorExceptionExact; intros; rfl
def ShowKeyErrorExact : Prop := ∀ key, showKeyError key = "KeyError: key " ++ key ++ " not found"
theorem showKeyErrorExact : ShowKeyErrorExact := by unfold ShowKeyErrorExact; intros; rfl
def ShowInterruptExceptionExact : Prop := ∀ u : Unit, showInterruptException u = "InterruptException:"
theorem showInterruptExceptionExact : ShowInterruptExceptionExact := by unfold ShowInterruptExceptionExact; intros; rfl
def ShowArgumentErrorExact : Prop := ∀ message, showArgumentError message = "ArgumentError: " ++ message
theorem showArgumentErrorExact : ShowArgumentErrorExact := by unfold ShowArgumentErrorExact; intros; rfl
def ShowDimensionMismatchExact : Prop := ∀ message, showDimensionMismatch message = "DimensionMismatch: " ++ message
theorem showDimensionMismatchExact : ShowDimensionMismatchExact := by unfold ShowDimensionMismatchExact; intros; rfl
def ShowAssertionErrorExact : Prop := ∀ message, showAssertionError message = "AssertionError: " ++ message
theorem showAssertionErrorExact : ShowAssertionErrorExact := by unfold ShowAssertionErrorExact; intros; rfl
def ShowOverflowErrorExact : Prop := ∀ message, showOverflowError message = "OverflowError: " ++ message
theorem showOverflowErrorExact : ShowOverflowErrorExact := by unfold ShowOverflowErrorExact; intros; rfl
def ShowUndefKeywordErrorExact : Prop := ∀ name, showUndefKeywordError name = "UndefKeywordError: keyword argument `" ++ name ++ "` not assigned"
theorem showUndefKeywordErrorExact : ShowUndefKeywordErrorExact := by unfold ShowUndefKeywordErrorExact; intros; rfl

def ShowUndefVarErrorExact : Prop := ∀ name scope, showUndefVarError name scope = match scope with
  | .absent => "UndefVarError: `" ++ name ++ "` not defined"
  | .moduleName value => "UndefVarError: `" ++ name ++ "` not defined in `" ++ value ++ "`"
  | .staticParameter => "UndefVarError: `" ++ name ++ "` not defined in static parameter matching"
  | .localKind value => "UndefVarError: `" ++ name ++ "` not defined in " ++ value ++ " scope"
theorem showUndefVarErrorExact : ShowUndefVarErrorExact := by
  unfold ShowUndefVarErrorExact
  intro name scope
  cases scope <;> rfl

def ShowInexactErrorExact : Prop := ∀ functionName typeName typeShown firstArg rest,
  showInexactError functionName typeName typeShown firstArg rest = "InexactError: " ++ functionName ++ "(" ++
    (if typeName = functionName then "" else typeShown ++ ", ") ++ String.intercalate ", " (firstArg :: rest) ++ ")"
theorem showInexactErrorExact : ShowInexactErrorExact := by unfold ShowInexactErrorExact; intros; rfl
def ShowCanonicalIndexErrorExact : Prop := ∀ f t, showCanonicalIndexError f t = "CanonicalIndexError: " ++ f ++ " not defined for " ++ t
theorem showCanonicalIndexErrorExact : ShowCanonicalIndexErrorExact := by unfold ShowCanonicalIndexErrorExact; intros; rfl

def TypesOfExact : Prop := ∀ types, typesOf types = types
theorem typesOfExact : TypesOfExact := by unfold TypesOfExact; intros; rfl

def PrintWithCompareDataTypeExact : Prop := ∀ sameName name left right, printWithCompareDataType sameName name left right =
  if sameName then typeDiff (.node name left) (.node name right) else [.mismatch (renderTypeTree (.node name left))]
theorem printWithCompareDataTypeExact : PrintWithCompareDataTypeExact := by unfold PrintWithCompareDataTypeExact; intros; rfl
def PrintWithCompareAnyExact : Prop := ∀ sameIdentity shown, printWithCompareAny sameIdentity shown = if sameIdentity then .same shown else .mismatch shown
theorem printWithCompareAnyExact : PrintWithCompareAnyExact := by unfold PrintWithCompareAnyExact; intros; rfl

def ShowConvertErrorExact : Prop := ∀ target source firstArgument, showConvertError target source firstArgument = match target with
  | none => "First argument to `convert` must be a Type, got " ++ firstArgument
  | some type => "Cannot `convert` an object of type " ++ source ++ " to an object of type " ++ type
theorem showConvertErrorExact : ShowConvertErrorExact := by
  unfold ShowConvertErrorExact
  intro target source firstArgument
  cases target <;> rfl


def ShowMethodErrorExact : Prop := ∀ input hints candidates, showMethodError input hints candidates =
  "MethodError: " ++ methodErrorCore input ++
    String.intercalate "" hints ++ String.intercalate "" candidates
theorem showMethodErrorExact : ShowMethodErrorExact := by unfold ShowMethodErrorExact; intros; rfl

def ShowFieldErrorExact : Prop := ∀ typeName field hint, showFieldError typeName field hint = "FieldError: type " ++ typeName ++ " has no field `" ++ field ++ "`" ++ hint
theorem showFieldErrorExact : ShowFieldErrorExact := by unfold ShowFieldErrorExact; intros; rfl
def StripTypeYesExact : Prop := ∀ typeName, stripTypeYes typeName = some typeName
theorem stripTypeYesExact : StripTypeYesExact := by unfold StripTypeYesExact; intros; rfl
def StripTypeNoExact : Prop := ∀ value, stripTypeNo value = none
theorem stripTypeNoExact : StripTypeNoExact := by unfold StripTypeNoExact; intros; rfl
def ShowAmbiguousErrorExact : Prop := ∀ signature candidates fix, showAmbiguousError signature candidates fix =
  "MethodError: " ++ signature ++ " is ambiguous.\n\nCandidates:\n" ++ String.intercalate "\n" candidates ++ fix.getD ""
theorem showAmbiguousErrorExact : ShowAmbiguousErrorExact := by unfold ShowAmbiguousErrorExact; intros; rfl

def ShowErrorNoStdioExact : Prop := ∀ message staticShown,
  showErrorNoStdio message staticShown = message ++ ":\n" ++ staticShown ++ "\n"
theorem showErrorNoStdioExact : ShowErrorNoStdioExact := by unfold ShowErrorNoStdioExact; intros; rfl

def StacktraceExpandBasepathsExact : Prop := ∀ environment, stacktraceExpandBasepaths environment = environment.getD false
theorem stacktraceExpandBasepathsExact : StacktraceExpandBasepathsExact := by unfold StacktraceExpandBasepathsExact; intros; rfl
def StacktraceContractUserdirExact : Prop := ∀ environment, stacktraceContractUserdir environment = environment.getD true
theorem stacktraceContractUserdirExact : StacktraceContractUserdirExact := by unfold StacktraceContractUserdirExact; intros; rfl
def StacktraceLinebreaksExact : Prop := ∀ environment, stacktraceLinebreaks environment = environment.getD false
theorem stacktraceLinebreaksExact : StacktraceLinebreaksExact := by unfold StacktraceLinebreaksExact; intros; rfl
def StacktraceFullLoadingExact : Prop := ∀ environment, stacktraceFullLoading environment = environment.getD false
theorem stacktraceFullLoadingExact : StacktraceFullLoadingExact := by unfold StacktraceFullLoadingExact; intros; rfl

def ShowTypeDiffExact : Prop := ∀ signature called, showTypeDiff signature called = typeDiff signature called
theorem showTypeDiffExact : ShowTypeDiffExact := by unfold ShowTypeDiffExact; intros; rfl
def ShowSeparatorFaithfulExact : Prop := ∀ color, showSeparatorFaithful color = showSeparator color
theorem showSeparatorFaithfulExact : ShowSeparatorFaithfulExact := by unfold ShowSeparatorFaithfulExact; intros; rfl
def ShowTypeMatchExact : Prop := ∀ typeText color, showTypeMatch typeText color =
  if color then [.literal "light-black", .same typeText, .literal "default"] else [.same typeText]
theorem showTypeMatchExact : ShowTypeMatchExact := by unfold ShowTypeMatchExact; intros; rfl
def ShowNamedtupleDiffExact : Prop := ∀ compatible tokens, showNamedtupleDiff compatible tokens = if compatible then some tokens else none
theorem showNamedtupleDiffExact : ShowNamedtupleDiffExact := by unfold ShowNamedtupleDiffExact; intros; rfl
def DescendParamsExact : Prop := ∀ sameName nonempty signature called, descendParams sameName nonempty signature called =
  if sameName && nonempty then some (signature, called) else none
theorem descendParamsExact : DescendParamsExact := by unfold DescendParamsExact; intros; rfl
def ShowTypeMismatchFaithfulExact : Prop := ∀ typeText color topLevel,
  showTypeMismatchFaithful typeText color topLevel = showTypeMismatch typeText topLevel color
theorem showTypeMismatchFaithfulExact : ShowTypeMismatchFaithfulExact := by unfold ShowTypeMismatchFaithfulExact; intros; rfl
def ResolvesToSelfExact : Prop := ∀ moduleDefined parentSame, resolvesToSelf moduleDefined parentSame = (!moduleDefined || parentSame)
theorem resolvesToSelfExact : ResolvesToSelfExact := by unfold ResolvesToSelfExact; intros; rfl
def ShowShadowedTypeHintExact : Prop := ∀ reported candidate, showShadowedTypeHint reported candidate =
  if reported.contains candidate then reported else reported ++ [candidate]
theorem showShadowedTypeHintExact : ShowShadowedTypeHintExact := by unfold ShowShadowedTypeHintExact; intros; rfl

def ShowMethodCandidatesExact : Prop := ∀ candidates, showMethodCandidates candidates = (sortCandidates candidates).take 3
theorem showMethodCandidatesExact : ShowMethodCandidatesExact := by unfold ShowMethodCandidatesExact; intros; rfl

def GetStacktraceColorExact : Prop := ∀ existing next, getStacktraceColor existing next = existing.getD next
theorem getStacktraceColorExact : GetStacktraceColorExact := by unfold GetStacktraceColorExact; intros; rfl

def FindAndRemoveCyclesExact : Prop := ∀ trace, findAndRemoveCycles trace =
  let displayed := collapseRepeatedFrames trace
  { displayed, cycles := [], maxNested := if displayed.any (fun item => 1 < item.2) then 1 else 0 }
theorem findAndRemoveCyclesExact : FindAndRemoveCyclesExact := by unfold FindAndRemoveCyclesExact; intros; rfl

def RepetitionClosingsExact : Prop := ∀ line frameCounter active cycles,
  repetitionClosings line frameCounter active cycles = closeRepetitions line frameCounter active cycles
theorem repetitionClosingsExact : RepetitionClosingsExact := by unfold RepetitionClosingsExact; intros; rfl

def ShowProcessedBacktraceExact : Prop := ∀ frames linebreaks, showProcessedBacktrace frames linebreaks =
  "\nStacktrace:\n" ++ String.intercalate (if linebreaks then "\n\n" else "\n") frames
theorem showProcessedBacktraceExact : ShowProcessedBacktraceExact := by unfold ShowProcessedBacktraceExact; intros; rfl

def PrintStackframeColorLookupExact : Prop := ∀ color rendered, printStackframeColorLookup color rendered = (color, rendered)
theorem printStackframeColorLookupExact : PrintStackframeColorLookupExact := by unfold PrintStackframeColorLookupExact; intros; rfl
def ParentmoduleBeforeMainExact : Prop := ∀ parents, parentmoduleBeforeMain parents = parentBeforeMain parents
theorem parentmoduleBeforeMainExact : ParentmoduleBeforeMainExact := by unfold ParentmoduleBeforeMainExact; intros; rfl
def ParentmoduleBeforeMainObjectExact : Prop := ∀ parents, parentmoduleBeforeMainObject parents = parentmoduleBeforeMain parents
theorem parentmoduleBeforeMainObjectExact : ParentmoduleBeforeMainObjectExact := by unfold ParentmoduleBeforeMainObjectExact; intros; rfl
def PrintStackframeLayoutExact : Prop := ∀ linePrefix signature location number width active starts inlined,
  printStackframeLayout linePrefix signature location number width active starts inlined =
    stackFrameLayout linePrefix signature location number width active starts inlined
theorem printStackframeLayoutExact : PrintStackframeLayoutExact := by unfold PrintStackframeLayoutExact; intros; rfl
def PrintModulePathFileExact : Prop := ∀ moduleName directory file line column,
  printModulePathFile moduleName directory file line column = modulePathFile moduleName directory file line column
theorem printModulePathFileExact : PrintModulePathFileExact := by unfold PrintModulePathFileExact; intros; rfl
def ShowBacktraceExact : Prop := ∀ empty singleUnknown large,
  showBacktrace empty singleUnknown large = showBacktraceRoute empty singleUnknown large
theorem showBacktraceExact : ShowBacktraceExact := by unfold ShowBacktraceExact; intros; rfl
def CollapseAndCountRepeatedFramesExact : Prop := ∀ frames,
  collapseAndCountRepeatedFrames frames = collapseRepeatedFrames frames
theorem collapseAndCountRepeatedFramesExact : CollapseAndCountRepeatedFramesExact := by unfold CollapseAndCountRepeatedFramesExact; intros; rfl
def RemoveKwcallFramesExact : Prop := ∀ frames, removeKwcallFramesFaithful frames = frames.filter fun frame => !frame.removeKwcall
theorem removeKwcallFramesExact : RemoveKwcallFramesExact := by unfold RemoveKwcallFramesExact removeKwcallFramesFaithful; intros; rfl
def SimplifyIncludeFramesExact : Prop := ∀ frames, simplifyIncludeFrames frames = frames.filter fun frame => frame.keepInclude
theorem simplifyIncludeFramesExact : SimplifyIncludeFramesExact := by unfold SimplifyIncludeFramesExact simplifyIncludeFrames; intros; rfl
def IsLoadingFrameExact : Prop := ∀ frame, isLoadingFrameFaithful frame = frame.loadingFrame
theorem isLoadingFrameExact : IsLoadingFrameExact := by unfold IsLoadingFrameExact isLoadingFrameFaithful; intros; rfl
def IsLoadingAnchorExact : Prop := ∀ frame, isLoadingAnchorFaithful frame = frame.loadingAnchor
theorem isLoadingAnchorExact : IsLoadingAnchorExact := by unfold IsLoadingAnchorExact isLoadingAnchorFaithful; intros; rfl
def SimplifyLoadingFramesExact : Prop := ∀ full frames, simplifyLoadingFrames full frames =
  if full then frames else frames.filter fun frame => !frame.loadingFrame || frame.loadingAnchor
theorem simplifyLoadingFramesExact : SimplifyLoadingFramesExact := by unfold SimplifyLoadingFramesExact simplifyLoadingFrames; intros; rfl
def CollapseRepeatedLocationsExact : Prop := ∀ frames, collapseRepeatedLocations frames = frames.filter fun frame => frame.keepLocation
theorem collapseRepeatedLocationsExact : CollapseRepeatedLocationsExact := by unfold CollapseRepeatedLocationsExact collapseRepeatedLocations; intros; rfl
def ProcessBacktraceFramesExact : Prop := ∀ full frames, processBacktraceFrames full frames = processBacktrace full frames
theorem processBacktraceFramesExact : ProcessBacktraceFramesExact := by unfold ProcessBacktraceFramesExact; intros; rfl
def ProcessBacktraceCountedExact : Prop := ∀ full frames, processBacktraceCounted full frames = processBacktrace full frames
theorem processBacktraceCountedExact : ProcessBacktraceCountedExact := by unfold ProcessBacktraceCountedExact; intros; rfl
def ShowExceptionStackFaithfulExact : Prop := ∀ exceptions,
  showExceptionStackFaithful exceptions = String.intercalate "\ncaused by: " exceptions.reverse
theorem showExceptionStackFaithfulExact : ShowExceptionStackFaithfulExact := by unfold ShowExceptionStackFaithfulExact showExceptionStackFaithful; intros; rfl
def ShowInterpreterIpExact : Prop := ∀ typeName code moduleName statement topLevel,
  showInterpreterIpFaithful typeName code moduleName statement topLevel =
    showInterpreterIP typeName code moduleName statement topLevel
theorem showInterpreterIpExact : ShowInterpreterIpExact := by unfold ShowInterpreterIpExact; intros; rfl

def NoncallableNumberHintExact : Prop := ∀ isNumber, noncallableNumberHint isNumber =
  if isNumber then some "Maybe you forgot to use an operator such as *, ^, %, / etc. ?" else none
theorem noncallableNumberHintExact : NoncallableNumberHintExact := by unfold NoncallableNumberHintExact; intros; rfl
def NonsettableHintExact : Prop := ∀ input, nonsettableHint input = match input with
  | .none => none | .number => some "Use a[1, 2] rather than a[1][2]"
  | .typeValue name => some ("Construct " ++ name ++ " before indexing it")
theorem nonsettableHintExact : NonsettableHintExact := by unfold NonsettableHintExact; intro input; cases input <;> rfl
def StringConcatenationHintExact : Prop := ∀ condition, stringConcatenationHint condition = if condition then some "String concatenation is performed with *" else none
theorem stringConcatenationHintExact : StringConcatenationHintExact := by unfold StringConcatenationHintExact; intros; rfl
def StringReplaceHintExact : Prop := ∀ condition, stringReplaceHint condition = if condition then some "Strings cannot be modified with replace!; use replace" else none
theorem stringReplaceHintExact : StringReplaceHintExact := by unfold StringReplaceHintExact; intros; rfl
def MethodsOnIterableExact : Prop := ∀ first second, methodsOnIterable first second = first.toList ++ second.toList
theorem methodsOnIterableExact : MethodsOnIterableExact := by unfold MethodsOnIterableExact; intros; rfl
def FieldErrorDictHintExact : Prop := ∀ isDict field, fieldErrorDictHint isDict field = if isDict then some ("dict[:" ++ field ++ "]") else none
theorem fieldErrorDictHintExact : FieldErrorDictHintExact := by unfold FieldErrorDictHintExact; intros; rfl
def FieldErrorListHintExact : Prop := ∀ fields properties, fieldErrorListHint fields properties =
  (fields, properties.filter fun property => !fields.contains property)
theorem fieldErrorListHintExact : FieldErrorListHintExact := by unfold FieldErrorListHintExact; intros; rfl
def PropertyNamesByTypeExact : Prop := ∀ custom inferred, propertyNamesByType custom inferred = if custom then inferred else none
theorem propertyNamesByTypeExact : PropertyNamesByTypeExact := by unfold PropertyNamesByTypeExact; intros; rfl
def ApplyTypeUnionallHintExact : Prop := ∀ condition got, applyTypeUnionallHint condition got =
  if condition then some ("`" ++ got ++ "` takes no type parameters.") else none
theorem applyTypeUnionallHintExact : ApplyTypeUnionallHintExact := by unfold ApplyTypeUnionallHintExact; intros; rfl
def UndefVarErrorHintExact : Prop := ∀ a b c d, undefVarErrorHint a b c d = a ++ b ++ c ++ d
theorem undefVarErrorHintExact : UndefVarErrorHintExact := by unfold UndefVarErrorHintExact; intros; rfl
def UndefVarWarnForExact : Prop := ∀ warnings, undefVarWarnFor warnings = (!warnings.isEmpty, warnings)
theorem undefVarWarnForExact : UndefVarWarnForExact := by unfold UndefVarWarnForExact; intros; rfl
def ExceptionStackSizeExact : Prop := ∀ stack, exceptionStackSize stack = stack.length
theorem exceptionStackSizeExact : ExceptionStackSizeExact := by unfold ExceptionStackSizeExact; intros; rfl
def ExceptionStackGetExact : Prop := ∀ stack index, exceptionStackGet? stack index = stack[index]?
theorem exceptionStackGetExact : ExceptionStackGetExact := by unfold ExceptionStackGetExact; intros; rfl
def ShowExceptionStackPlainExact : Prop := ∀ stack, showExceptionStackPlain stack =
  toString stack.length ++ "-element ExceptionStack" ++ (if stack.isEmpty then "" else ":\n") ++
    String.intercalate "\ncaused by: " stack.reverse
theorem showExceptionStackPlainExact : ShowExceptionStackPlainExact := by unfold ShowExceptionStackPlainExact; intros; rfl
def ShowExceptionStackCompactExact : Prop := ∀ stack, showExceptionStackCompact stack = showExceptionStackPlain stack
theorem showExceptionStackCompactExact : ShowExceptionStackCompactExact := by unfold ShowExceptionStackCompactExact; intros; rfl
def IncompleteTagAnyExact : Prop := ∀ _value : String, incompleteTag .other = "none"
theorem incompleteTagAnyExact : IncompleteTagAnyExact := by unfold IncompleteTagAnyExact; intros; rfl
def IncompleteTagExprExact : Prop := ∀ input, incompleteTag input = match input with
  | .other => "none" | .empty => "other" | .text kind => kind | .nested tag => tag
theorem incompleteTagExprExact : IncompleteTagExprExact := by unfold IncompleteTagExprExact; intro input; cases input <;> rfl
def IncompleteTagParseErrorExact : Prop := ∀ detail, incompleteTagParseError detail = incompleteTag detail
theorem incompleteTagParseErrorExact : IncompleteTagParseErrorExact := by unfold IncompleteTagParseErrorExact; intros; rfl

end JuliaLean.ErrorShow.ErrorshowFaithful

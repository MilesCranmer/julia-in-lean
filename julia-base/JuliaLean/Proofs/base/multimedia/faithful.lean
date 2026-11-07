import JuliaLean.Proofs.base.multimedia.retainedCoverage

/-! Method-specific models for `base/multimedia.jl` at `bbfa0ce4150`. -/

namespace JuliaLean.ErrorShow.MultimediaFaithful

open JuliaLean.ErrorShow.Coverage


def MimeStrExact : Prop := ∀ text, mimeStr text = text
theorem mimeStrExact : MimeStrExact := by unfold MimeStrExact; intros; rfl

def ShowTextPlainFallbackExact : Prop := ∀ shown, showTextPlainFallback shown = shown
theorem showTextPlainFallbackExact : ShowTextPlainFallbackExact := by unfold ShowTextPlainFallbackExact; intros; rfl

def MimeConstructorExact : Prop := ∀ text, mimeConstructor text = text
theorem mimeConstructorExact : MimeConstructorExact := by unfold MimeConstructorExact; intros; rfl

def ShowMimeExact : Prop := ∀ mime, showMime mime = "MIME type " ++ mime
theorem showMimeExact : ShowMimeExact := by unfold ShowMimeExact; intros; rfl

def PrintMimeExact : Prop := ∀ mime, printMime mime = mime
theorem printMimeExact : PrintMimeExact := by unfold PrintMimeExact; intros; rfl

def ShowableMimeExact : Prop := ∀ hasShowMethod, showableMime hasShowMethod = hasShowMethod
theorem showableMimeExact : ShowableMimeExact := by unfold ShowableMimeExact; intros; rfl

def ShowableStringExact : Prop := ∀ mimeText hasShowMethod,
  showableString mimeText hasShowMethod = showableMime (hasShowMethod (mimeConstructor mimeText))
theorem showableStringExact : ShowableStringExact := by unfold ShowableStringExact; intros; rfl

def ShowStringMimeExact : Prop := ∀ mimeText shown,
  showStringMime mimeText shown = shown
theorem showStringMimeExact : ShowStringMimeExact := by unfold ShowStringMimeExact; intros; rfl

def ReprMimeExact : Prop := ∀ mime textResult binaryResult,
  reprMime mime textResult binaryResult =
    if isTextMime mime then .text textResult else .bytes binaryResult
theorem reprMimeExact : ReprMimeExact := by unfold ReprMimeExact; intros; rfl

def ReprStringExact : Prop := ∀ mimeText textResult binaryResult,
  reprString mimeText textResult binaryResult = reprMime (mimeConstructor mimeText) textResult binaryResult
theorem reprStringExact : ReprStringExact := by unfold ReprStringExact; intros; rfl

def TextReprGenericExact : Prop := ∀ decoded, textReprGeneric decoded = decoded
theorem textReprGenericExact : TextReprGenericExact := by unfold TextReprGenericExact; intros; rfl

def TextReprRawStringExact : Prop := ∀ text, textReprRawString text = text
theorem textReprRawStringExact : TextReprRawStringExact := by unfold TextReprRawStringExact; intros; rfl

def TextReprPlainStringExact : Prop := ∀ decoded, textReprPlainString decoded = decoded
theorem textReprPlainStringExact : TextReprPlainStringExact := by unfold TextReprPlainStringExact; intros; rfl

def BinreprBufferExact : Prop := ∀ contextPresent plainShow contextShow,
  binreprBuffer contextPresent plainShow contextShow =
    if contextPresent then contextShow else plainShow
theorem binreprBufferExact : BinreprBufferExact := by unfold BinreprBufferExact; intros; rfl

def BinreprGenericExact : Prop := ∀ bytes, binreprGeneric bytes = bytes
theorem binreprGenericExact : BinreprGenericExact := by unfold BinreprGenericExact; intros; rfl

def BinreprBytesExact : Prop := ∀ bytes, binreprBytes bytes = bytes
theorem binreprBytesExact : BinreprBytesExact := by unfold BinreprBytesExact; intros; rfl

def IsTextMimePrefixExact : Prop := ∀ mime, isTextMimePrefix mime = mime.startsWith "text/"
theorem isTextMimePrefixExact : IsTextMimePrefixExact := by unfold IsTextMimePrefixExact; intros; rfl

def IsTextMimeStringExact : Prop := ∀ mimeText,
  isTextMimeString mimeText = isTextMimePrefix (mimeConstructor mimeText)
theorem isTextMimeStringExact : IsTextMimeStringExact := by unfold IsTextMimeStringExact; intros; rfl

def IsKnownTextMimeExact : Prop := ∀ mime, isKnownTextMime mime = true
theorem isKnownTextMimeExact : IsKnownTextMimeExact := by unfold IsKnownTextMimeExact; intros; rfl

def DisplayBackendStringExact : Prop := ∀ mimeText result,
  displayBackendString mimeText result = result
theorem displayBackendStringExact : DisplayBackendStringExact := by unfold DisplayBackendStringExact; intros; rfl

def DisplayGlobalStringExact : Prop := ∀ mimeText result,
  displayGlobalString mimeText result = result
theorem displayGlobalStringExact : DisplayGlobalStringExact := by unfold DisplayGlobalStringExact; intros; rfl

def DisplayableBackendStringExact : Prop := ∀ mimeText backendCheck,
  displayableBackendString mimeText backendCheck = backendCheck (mimeConstructor mimeText)
theorem displayableBackendStringExact : DisplayableBackendStringExact := by unfold DisplayableBackendStringExact; intros; rfl

def DisplayableGlobalStringExact : Prop := ∀ mimeText globalCheck,
  displayableGlobalString mimeText globalCheck = globalCheck (mimeConstructor mimeText)
theorem displayableGlobalStringExact : DisplayableGlobalStringExact := by unfold DisplayableGlobalStringExact; intros; rfl

def TextDisplayPlainExact : Prop := ∀ shown, textDisplayPlain shown = shown ++ "\n"
theorem textDisplayPlainExact : TextDisplayPlainExact := by unfold TextDisplayPlainExact; intros; rfl

def TextDisplayDefaultExact : Prop := ∀ shownPlain,
  textDisplayDefault shownPlain = textDisplayPlain shownPlain
theorem textDisplayDefaultExact : TextDisplayDefaultExact := by unfold TextDisplayDefaultExact; intros; rfl

def TextDisplayableExact : Prop := ∀ mime, textDisplayable mime = isTextMime mime
theorem textDisplayableExact : TextDisplayableExact := by unfold TextDisplayableExact; intros; rfl

def TextDisplayMimeExact : Prop := ∀ mime shown,
  textDisplayMime mime shown =
    if textDisplayable mime then .ok (shown ++ "\n") else .error "MethodError(display)"
theorem textDisplayMimeExact : TextDisplayMimeExact := by unfold TextDisplayMimeExact; intros; rfl

def FlushTextDisplayExact : Prop := ∀ result, flushTextDisplay result = result
theorem flushTextDisplayExact : FlushTextDisplayExact := by unfold FlushTextDisplayExact; intros; rfl

def CloseTextDisplayExact : Prop := ∀ result, closeTextDisplay result = result
theorem closeTextDisplayExact : CloseTextDisplayExact := by unfold CloseTextDisplayExact; intros; rfl

def PushDisplayExact : Prop := ∀ stack backend, pushDisplayMethod stack backend = stack ++ [backend]
theorem pushDisplayExact : PushDisplayExact := by unfold PushDisplayExact; intros; rfl

def PopDisplayExact : Prop :=
  (popDisplayMethod [] = .error "ArgumentError: array must be non-empty") ∧
  ∀ head tail, popDisplayMethod (head :: tail) =
    .ok ((head :: tail).getLast!, (head :: tail).dropLast)
theorem popDisplayExact : PopDisplayExact := by constructor; rfl; intros; rfl

def PopNamedDisplayExact : Prop := ∀ stack backend,
  popNamedDisplayMethod stack backend =
    if stack.contains backend then .ok (removeLast backend stack) else .error "KeyError"
theorem popNamedDisplayExact : PopNamedDisplayExact := by unfold PopNamedDisplayExact; intros; rfl

def ReinitDisplaysExact : Prop := ∀ stdout, reinitDisplaysMethod stdout = [stdout]
theorem reinitDisplaysExact : ReinitDisplaysExact := by unfold ReinitDisplaysExact; intros; rfl

def XdisplayableExact : Prop := ∀ applicable, xdisplayable applicable = applicable
theorem xdisplayableExact : XdisplayableExact := by unfold XdisplayableExact; intros; rfl

def DisplayAnyExact : Prop := ∀ attempts,
  displayAny attempts = runDisplayLoop "display" ["display", "show"] attempts
theorem displayAnyExact : DisplayAnyExact := by unfold DisplayAnyExact; intros; rfl

def DisplayMimeExact : Prop := ∀ attempts,
  displayMime attempts = runDisplayLoop "display" ["display"] attempts
theorem displayMimeExact : DisplayMimeExact := by unfold DisplayMimeExact; intros; rfl

def DisplayableBackendMimeExact : Prop := ∀ hasMethod, displayableBackendMime hasMethod = hasMethod
theorem displayableBackendMimeExact : DisplayableBackendMimeExact := by unfold DisplayableBackendMimeExact; intros; rfl

def DisplayableGlobalMimeExact : Prop := ∀ backendResults,
  displayableGlobalMime backendResults = backendResults.any id
theorem displayableGlobalMimeExact : DisplayableGlobalMimeExact := by unfold DisplayableGlobalMimeExact; intros; rfl

def RedisplayAnyExact : Prop := ∀ attempts,
  redisplayAny attempts = runDisplayLoop "redisplay" ["redisplay", "display", "show"] attempts
theorem redisplayAnyExact : RedisplayAnyExact := by unfold RedisplayAnyExact; intros; rfl

def RedisplayMimeExact : Prop := ∀ attempts,
  redisplayMime attempts = runDisplayLoop "redisplay" ["redisplay", "display"] attempts
theorem redisplayMimeExact : RedisplayMimeExact := by unfold RedisplayMimeExact; intros; rfl

def RedisplayBackendDefaultExact : Prop := ∀ result, redisplayBackendDefault result = result
theorem redisplayBackendDefaultExact : RedisplayBackendDefaultExact := by unfold RedisplayBackendDefaultExact; intros; rfl

def RedisplayBackendMimeDefaultExact : Prop := ∀ result, redisplayBackendMimeDefault result = result
theorem redisplayBackendMimeDefaultExact : RedisplayBackendMimeDefaultExact := by unfold RedisplayBackendMimeDefaultExact; intros; rfl

end JuliaLean.ErrorShow.MultimediaFaithful

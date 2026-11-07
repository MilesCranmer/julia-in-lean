import JuliaLean.base.logging.logging
import JuliaLean.Proofs.base.logging.ConsoleLogger.LoggingCov
import JuliaLean.Proofs.base.logging.logging.Claims

namespace JuliaLean.ConcurrencyCov.FaithfulLogging

open JuliaLean.ConcurrencyCov

def CatchExceptionsProp : Prop := ∀ logger, catchExceptionsM logger = true

theorem catchExceptions_proven : CatchExceptionsProp := by
  unfold CatchExceptionsProp
  intros
  rfl

def InvokedShouldlogProp : Prop := ∀ invoke logger level mod group id,
  invokedShouldlog invoke logger level mod group id = invoke logger level mod group id

theorem invokedShouldlog_proven : InvokedShouldlogProp := by
  unfold InvokedShouldlogProp
  intros
  rfl

def InvokedMinLevelProp : Prop := ∀ invoke logger, invokedMinLevel invoke logger = invoke logger

theorem invokedMinLevel_proven : InvokedMinLevelProp := by
  unfold InvokedMinLevelProp
  intros
  rfl

def InvokedCatchProp : Prop := ∀ invoke logger, invokedCatch invoke logger = invoke logger

theorem invokedCatch_proven : InvokedCatchProp := by
  unfold InvokedCatchProp
  intros
  rfl

def NullMinLevelProp : Prop := ∀ _u : Unit, nullMinLevel = LoggingCov.aboveMax

theorem nullMinLevel_proven : NullMinLevelProp := by
  unfold NullMinLevelProp
  intros
  rfl

def NullShouldlogProp : Prop := ∀ args, nullShouldlog args = false

theorem nullShouldlog_proven : NullShouldlogProp := by
  unfold NullShouldlogProp
  intros
  rfl

def NullHandleMessageProp : Prop := ∀ args, nullHandleMessage args =
  .error (.errorException "Null logger handle_message() should not be called")

theorem nullHandleMessage_proven : NullHandleMessageProp := by
  unfold NullHandleMessageProp
  intros
  rfl

def LogLevelCopyProp : Prop := ∀ level, logLevelCopy level = level

theorem logLevelCopy_proven : LogLevelCopyProp := by
  unfold LogLevelCopyProp
  intros
  rfl

def LessLevelLevelProp : Prop := ∀ a b, lessLevelLevel a b = decide (a < b)

theorem lessLevelLevel_proven : LessLevelLevelProp := by
  unfold LessLevelLevelProp
  intros
  rfl

def LessLevelIntegerProp : Prop := ∀ a b, lessLevelInteger a b = decide (a < b)

theorem lessLevelInteger_proven : LessLevelIntegerProp := by
  unfold LessLevelIntegerProp
  intros
  rfl

def LessIntegerLevelProp : Prop := ∀ a b, lessIntegerLevel a b = decide (a < b)

theorem lessIntegerLevel_proven : LessIntegerLevelProp := by
  unfold LessIntegerLevelProp
  intros
  rfl

def AddLevelProp : Prop := ∀ level inc, addLevel level inc = JuliaLean.Logging.addInt level inc

theorem addLevel_proven : AddLevelProp := by
  unfold AddLevelProp
  intros
  rfl

def SubLevelProp : Prop := ∀ level inc, subLevel level inc = JuliaLean.Logging.subInt level inc

theorem subLevel_proven : SubLevelProp := by
  unfold SubLevelProp
  intros
  rfl

def ConvertLevelProp : Prop := ∀ level, convertLevelM level = LoggingCov.convertLevel level

theorem convertLevel_proven : ConvertLevelProp := by
  unfold ConvertLevelProp
  intros
  rfl

def ConvertInt32Prop : Prop := ∀ level, convertInt32M level = level

theorem convertInt32_proven : ConvertInt32Prop := by
  unfold ConvertInt32Prop
  intros
  rfl

def ShowLevelProp : Prop := ∀ level, showLevelM level = LoggingCov.showLevel level

theorem showLevel_proven : ShowLevelProp := by
  unfold ShowLevelProp
  intros
  rfl

def SourceInfoProp : Prop := ∀ mod file line,
  sourceInfoM mod file line = ⟨mod, file.getD "?", line⟩

theorem sourceInfo_proven : SourceInfoProp := by
  unfold SourceInfoProp
  intros
  rfl

def LogmsgMacroProp : Prop := ∀ level, logmsgMacro level = level

theorem logmsgMacro_proven : LogmsgMacroProp := by
  unfold LogmsgMacroProp
  intros
  rfl

def DebugMacroProp : Prop := ∀ level, debugMacro level = LoggingCov.debug

theorem debugMacro_proven : DebugMacroProp := by
  unfold DebugMacroProp
  intros
  rfl

def InfoMacroProp : Prop := ∀ level, infoMacro level = LoggingCov.info

theorem infoMacro_proven : InfoMacroProp := by
  unfold InfoMacroProp
  intros
  rfl

def WarnMacroProp : Prop := ∀ level, warnMacro level = LoggingCov.warn

theorem warnMacro_proven : WarnMacroProp := by
  unfold WarnMacroProp
  intros
  rfl

def ErrorMacroProp : Prop := ∀ level, errorMacro level = LoggingCov.error

theorem errorMacro_proven : ErrorMacroProp := by
  unfold ErrorMacroProp
  intros
  rfl

def LogRecordIdProp : Prop := ∀ used hash,
  logRecordIdM used hash = (((List.range (used.length + 1)).map (hash + ·)).find? (· ∉ used)).getD hash

theorem logRecordId_proven : LogRecordIdProp := by
  unfold LogRecordIdProp
  intros
  rfl

def DefaultGroupProp : Prop := ∀ stem, defaultGroupM stem = stem

theorem defaultGroup_proven : DefaultGroupProp := by
  unfold DefaultGroupProp
  intros
  rfl

def IsSimpleProp : Prop := ∀ val, isSimpleM val = LoggingCov.isSimple val

theorem isSimple_proven : IsSimpleProp := by
  unfold IsSimpleProp
  intros
  rfl

def IsSimpleKwProp : Prop := ∀ val, isSimpleKwM val = LoggingCov.isSimpleKw val

theorem isSimpleKw_proven : IsSimpleKwProp := by
  unfold IsSimpleKwProp
  intros
  rfl

def CurrentLoggerForEnvProp : Prop := ∀ minimum std override logger,
  currentLoggerForEnv minimum std override logger = if minimum ≤ std || override then some logger else none

theorem currentLoggerForEnv_proven : CurrentLoggerForEnvProp := by
  unfold CurrentLoggerForEnvProp
  intros
  rfl

def LogmsgCodeProp : Prop := ∀ message kwargs global logger should build,
  logmsgCodeM message kwargs global logger should build =
    let path := LoggingCov.logmsgCode message kwargs
    if !global then ⟨path, false, false, false, false⟩
    else if !logger then ⟨path, true, false, false, false⟩
    else if !should then ⟨path, true, true, false, false⟩
    else ⟨path, true, true, true, build⟩

theorem logmsgCode_proven : LogmsgCodeProp := by
  unfold LogmsgCodeProp
  intros
  rfl

def HandleMessageNothrowProp : Prop := ∀ outcome,
  handleMessageNothrowM outcome = match outcome with | .returned => true | .threw _ => false

theorem handleMessageNothrow_proven : HandleMessageNothrowProp := by intro outcome; cases outcome <;> rfl

def ProcessLogmsgExsProp : Prop := ∀ args,
  processLogmsgExsM args = JuliaLean.Logging.processArgs args

theorem processLogmsgExs_proven : ProcessLogmsgExsProp := by
  unfold ProcessLogmsgExsProp
  intros
  rfl

def DefaultGroupCodeProp : Prop := ∀ literal stem,
  defaultGroupCodeM literal stem = if literal then .constant stem else .memoized

theorem defaultGroupCode_proven : DefaultGroupCodeProp := by
  unfold DefaultGroupCodeProp
  intros
  rfl

def LoggingErrorProp : Prop := ∀ catches real,
  loggingErrorM catches real = if !catches then ⟨.rethrow, false, false, false⟩
  else ⟨.emitError, true, !real, true⟩

theorem loggingError_proven : LoggingErrorProp := by
  unfold LoggingErrorProp
  intros
  rfl

def LogmsgShimProp : Prop := ∀ (α : Type) (kwargs : List α),
  logmsgShimM kwargs = ⟨LoggingCov.pairKeywords kwargs, true, true, true⟩

theorem logmsgShim_proven : LogmsgShimProp := by
  unfold LogmsgShimProp
  intros
  rfl

def LogStateCtorProp : Prop := ∀ minimum logger,
  logStateCtor minimum logger = ⟨minimum, logger⟩

theorem logStateCtor_proven : LogStateCtorProp := by
  unfold LogStateCtorProp
  intros
  rfl

def CurrentLogstateProp : Prop := ∀ localState global,
  currentLogstateM localState global = localState.getD global

theorem currentLogstate_proven : CurrentLogstateProp := by
  unfold CurrentLogstateProp
  intros
  rfl

def WithLogstateProp : Prop := ∀ f state, withLogstate f state = f state

theorem withLogstate_proven : WithLogstateProp := by
  unfold WithLogstateProp
  intros
  rfl

def DisableLoggingProp : Prop := ∀ level,
  disableLoggingM level = JuliaLean.Logging.addInt level 1

theorem disableLogging_proven : DisableLoggingProp := by
  unfold DisableLoggingProp
  intros
  rfl

def EnvOverrideProp : Prop := ∀ config group mod root,
  envOverrideM config group mod root = JuliaLean.Logging.envOverride config group mod root

theorem envOverride_proven : EnvOverrideProp := by
  unfold EnvOverrideProp
  intros
  rfl

def GlobalLoggerProp : Prop := ∀ state, globalLoggerM state = state.logger

theorem globalLogger_proven : GlobalLoggerProp := by
  unfold GlobalLoggerProp
  intros
  rfl

def SetGlobalLoggerProp : Prop := ∀ new minimum state,
  setGlobalLoggerM new minimum state = (state.logger, ⟨minimum, new⟩)

theorem setGlobalLogger_proven : SetGlobalLoggerProp := by
  unfold SetGlobalLoggerProp
  intros
  rfl

def WithLoggerProp : Prop := ∀ previous installed outcome,
  withLoggerM previous installed outcome = ⟨installed, previous, outcome⟩

theorem withLogger_proven : WithLoggerProp := by
  unfold WithLoggerProp
  intros
  rfl

def CurrentLoggerProp : Prop := ∀ state, currentLoggerM state = state.logger

theorem currentLogger_proven : CurrentLoggerProp := by
  unfold CurrentLoggerProp
  intros
  rfl

def SimpleLoggerStreamProp : Prop := ∀ streamOpen minimum,
  (simpleLoggerStream streamOpen minimum).streamOpen = streamOpen ∧
  (simpleLoggerStream streamOpen minimum).minimum = minimum

theorem simpleLoggerStream_proven : SimpleLoggerStreamProp := by
  unfold SimpleLoggerStreamProp
  intros
  exact ⟨rfl, rfl⟩

def SimpleLoggerDefaultProp : Prop := ∀ minimum,
  (simpleLoggerDefault minimum).streamOpen = false ∧ (simpleLoggerDefault minimum).minimum = minimum

theorem simpleLoggerDefault_proven : SimpleLoggerDefaultProp := by
  unfold SimpleLoggerDefaultProp
  intros
  exact ⟨rfl, rfl⟩

def SimpleShouldlogProp : Prop := ∀ logger id,
  simpleShouldlogM logger id = decide (0 < logger.limits id)

theorem simpleShouldlog_proven : SimpleShouldlogProp := by
  unfold SimpleShouldlogProp
  intros
  rfl

def SimpleMinLevelProp : Prop := ∀ logger, simpleMinLevelM logger = logger.minimum

theorem simpleMinLevel_proven : SimpleMinLevelProp := by
  unfold SimpleMinLevelProp
  intros
  rfl

def SimpleCatchProp : Prop := ∀ _logger : Nat, simpleCatchM = false

theorem simpleCatch_proven : SimpleCatchProp := by
  unfold SimpleCatchProp
  intros
  rfl

def SimpleHandleProp : Prop := ∀ remaining messages values streamOpen,
  simpleHandleM remaining messages values streamOpen =
  if remaining = 0 then ⟨0, false, [], [], false⟩
  else ⟨remaining - 1, true, JuliaLean.Logging.simpleMessageLines messages,
    JuliaLean.Logging.simpleValueLines "key" values, !streamOpen⟩

theorem simpleHandle_proven : SimpleHandleProp := by
  unfold SimpleHandleProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulLogging

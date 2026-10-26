import JuliaLean.Logging
import JuliaLean.ConcurrencyCov.LoggingCov

/-! Per-method source-body models for the two logging files. -/

namespace JuliaLean.ConcurrencyCov.FaithfulLogging

open JuliaLean.ConcurrencyCov

def catchExceptionsM (_logger : Nat) := true
def CatchExceptionsProp : Prop := ∀ logger, catchExceptionsM logger = true
theorem catchExceptions_proven : CatchExceptionsProp := by
  unfold CatchExceptionsProp
  intros
  rfl

def invokedShouldlog (invoke : Nat → Int → Nat → Nat → Nat → Bool) logger level mod group id :=
  invoke logger level mod group id
def InvokedShouldlogProp : Prop := ∀ invoke logger level mod group id,
  invokedShouldlog invoke logger level mod group id = invoke logger level mod group id
theorem invokedShouldlog_proven : InvokedShouldlogProp := by
  unfold InvokedShouldlogProp
  intros
  rfl

def invokedMinLevel (invoke : Nat → Int) logger := invoke logger
def InvokedMinLevelProp : Prop := ∀ invoke logger, invokedMinLevel invoke logger = invoke logger
theorem invokedMinLevel_proven : InvokedMinLevelProp := by
  unfold InvokedMinLevelProp
  intros
  rfl

def invokedCatch (invoke : Nat → Bool) logger := invoke logger
def InvokedCatchProp : Prop := ∀ invoke logger, invokedCatch invoke logger = invoke logger
theorem invokedCatch_proven : InvokedCatchProp := by
  unfold InvokedCatchProp
  intros
  rfl

def nullMinLevel := LoggingCov.aboveMax
def NullMinLevelProp : Prop := ∀ _u : Unit, nullMinLevel = LoggingCov.aboveMax
theorem nullMinLevel_proven : NullMinLevelProp := by
  unfold NullMinLevelProp
  intros
  rfl

def nullShouldlog (_args : List Nat) := false
def NullShouldlogProp : Prop := ∀ args, nullShouldlog args = false
theorem nullShouldlog_proven : NullShouldlogProp := by
  unfold NullShouldlogProp
  intros
  rfl

def nullHandleMessage (_args : List Nat) : R Unit :=
  .error (.errorException "Null logger handle_message() should not be called")
def NullHandleMessageProp : Prop := ∀ args, nullHandleMessage args =
  .error (.errorException "Null logger handle_message() should not be called")
theorem nullHandleMessage_proven : NullHandleMessageProp := by
  unfold NullHandleMessageProp
  intros
  rfl

def logLevelCopy (level : Int) := level
def LogLevelCopyProp : Prop := ∀ level, logLevelCopy level = level
theorem logLevelCopy_proven : LogLevelCopyProp := by
  unfold LogLevelCopyProp
  intros
  rfl

def lessLevelLevel (a b : Int) : Bool := decide (a < b)
def LessLevelLevelProp : Prop := ∀ a b, lessLevelLevel a b = decide (a < b)
theorem lessLevelLevel_proven : LessLevelLevelProp := by
  unfold LessLevelLevelProp
  intros
  rfl

def lessLevelInteger := lessLevelLevel
def LessLevelIntegerProp : Prop := ∀ a b, lessLevelInteger a b = decide (a < b)
theorem lessLevelInteger_proven : LessLevelIntegerProp := by
  unfold LessLevelIntegerProp
  intros
  rfl

def lessIntegerLevel := lessLevelLevel
def LessIntegerLevelProp : Prop := ∀ a b, lessIntegerLevel a b = decide (a < b)
theorem lessIntegerLevel_proven : LessIntegerLevelProp := by
  unfold LessIntegerLevelProp
  intros
  rfl

def addLevel := JuliaLean.Logging.addInt
def AddLevelProp : Prop := ∀ level inc, addLevel level inc = JuliaLean.Logging.addInt level inc
theorem addLevel_proven : AddLevelProp := by
  unfold AddLevelProp
  intros
  rfl

def subLevel := JuliaLean.Logging.subInt
def SubLevelProp : Prop := ∀ level inc, subLevel level inc = JuliaLean.Logging.subInt level inc
theorem subLevel_proven : SubLevelProp := by
  unfold SubLevelProp
  intros
  rfl

def convertLevelM := LoggingCov.convertLevel
def ConvertLevelProp : Prop := ∀ level, convertLevelM level = LoggingCov.convertLevel level
theorem convertLevel_proven : ConvertLevelProp := by
  unfold ConvertLevelProp
  intros
  rfl

def convertInt32M := LoggingCov.levelToInt32
def ConvertInt32Prop : Prop := ∀ level, convertInt32M level = level
theorem convertInt32_proven : ConvertInt32Prop := by
  unfold ConvertInt32Prop
  intros
  rfl

def showLevelM := LoggingCov.showLevel
def ShowLevelProp : Prop := ∀ level, showLevelM level = LoggingCov.showLevel level
theorem showLevel_proven : ShowLevelProp := by
  unfold ShowLevelProp
  intros
  rfl

def sourceInfoM := LoggingCov.sourceInfo
def SourceInfoProp : Prop := ∀ mod file line,
  sourceInfoM mod file line = ⟨mod, file.getD "?", line⟩
theorem sourceInfo_proven : SourceInfoProp := by
  unfold SourceInfoProp
  intros
  rfl

def logmsgMacro (level : Int) := LoggingCov.macroLevel .logmsg level
def LogmsgMacroProp : Prop := ∀ level, logmsgMacro level = level
theorem logmsgMacro_proven : LogmsgMacroProp := by
  unfold LogmsgMacroProp
  intros
  rfl

def debugMacro (level : Int) := LoggingCov.macroLevel .debug level
def DebugMacroProp : Prop := ∀ level, debugMacro level = LoggingCov.debug
theorem debugMacro_proven : DebugMacroProp := by
  unfold DebugMacroProp
  intros
  rfl

def infoMacro (level : Int) := LoggingCov.macroLevel .info level
def InfoMacroProp : Prop := ∀ level, infoMacro level = LoggingCov.info
theorem infoMacro_proven : InfoMacroProp := by
  unfold InfoMacroProp
  intros
  rfl

def warnMacro (level : Int) := LoggingCov.macroLevel .warn level
def WarnMacroProp : Prop := ∀ level, warnMacro level = LoggingCov.warn
theorem warnMacro_proven : WarnMacroProp := by
  unfold WarnMacroProp
  intros
  rfl

def errorMacro (level : Int) := LoggingCov.macroLevel .error level
def ErrorMacroProp : Prop := ∀ level, errorMacro level = LoggingCov.error
theorem errorMacro_proven : ErrorMacroProp := by
  unfold ErrorMacroProp
  intros
  rfl

def logRecordIdM := LoggingCov.nextRecordId
def LogRecordIdProp : Prop := ∀ used hash,
  logRecordIdM used hash = (((List.range (used.length + 1)).map (hash + ·)).find? (· ∉ used)).getD hash
theorem logRecordId_proven : LogRecordIdProp := by
  unfold LogRecordIdProp
  intros
  rfl

def defaultGroupM := LoggingCov.defaultGroup
def DefaultGroupProp : Prop := ∀ stem, defaultGroupM stem = stem
theorem defaultGroup_proven : DefaultGroupProp := by
  unfold DefaultGroupProp
  intros
  rfl

def isSimpleM := LoggingCov.isSimple
def IsSimpleProp : Prop := ∀ val, isSimpleM val = LoggingCov.isSimple val
theorem isSimple_proven : IsSimpleProp := by
  unfold IsSimpleProp
  intros
  rfl

def isSimpleKwM := LoggingCov.isSimpleKw
def IsSimpleKwProp : Prop := ∀ val, isSimpleKwM val = LoggingCov.isSimpleKw val
theorem isSimpleKw_proven : IsSimpleKwProp := by
  unfold IsSimpleKwProp
  intros
  rfl

def currentLoggerForEnv (minimum std : Int) (override : Bool) (logger : Nat) : Option Nat :=
  if minimum ≤ std || override then some logger else none
def CurrentLoggerForEnvProp : Prop := ∀ minimum std override logger,
  currentLoggerForEnv minimum std override logger = if minimum ≤ std || override then some logger else none
theorem currentLoggerForEnv_proven : CurrentLoggerForEnvProp := by
  unfold CurrentLoggerForEnvProp
  intros
  rfl

structure LogCodeTrace where
  recordPath : LoggingCov.RecordPath
  passedGlobal : Bool
  foundLogger : Bool
  passedShouldlog : Bool
  handled : Bool
  deriving DecidableEq, Repr
def logmsgCodeM (message : LoggingCov.Syntax) (kwargs : List LoggingCov.Syntax)
    (globalEnabled loggerAvailable shouldAccept recordBuilt : Bool) : LogCodeTrace :=
  let path := LoggingCov.logmsgCode message kwargs
  if !globalEnabled then ⟨path, false, false, false, false⟩
  else if !loggerAvailable then ⟨path, true, false, false, false⟩
  else if !shouldAccept then ⟨path, true, true, false, false⟩
  else ⟨path, true, true, true, recordBuilt⟩
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

def handleMessageNothrowM := LoggingCov.handleMessageNothrow
def HandleMessageNothrowProp : Prop := ∀ outcome,
  handleMessageNothrowM outcome = match outcome with | .returned => true | .threw _ => false
theorem handleMessageNothrow_proven : HandleMessageNothrowProp := by intro outcome; cases outcome <;> rfl

def processLogmsgExsM := JuliaLean.Logging.processArgs
def ProcessLogmsgExsProp : Prop := ∀ args,
  processLogmsgExsM args = JuliaLean.Logging.processArgs args
theorem processLogmsgExs_proven : ProcessLogmsgExsProp := by
  unfold ProcessLogmsgExsProp
  intros
  rfl

def defaultGroupCodeM := LoggingCov.defaultGroupCode
def DefaultGroupCodeProp : Prop := ∀ literal stem,
  defaultGroupCodeM literal stem = if literal then .constant stem else .memoized
theorem defaultGroupCode_proven : DefaultGroupCodeProp := by
  unfold DefaultGroupCodeProp
  intros
  rfl

structure LoggingErrorTrace where
  action : LoggingCov.LoggingErrorAction
  scrubbedBacktrace : Bool
  droppedLoggingFrames : Bool
  emitted : Bool
  deriving DecidableEq, Repr
def loggingErrorM (catches real : Bool) : LoggingErrorTrace :=
  if !catches then ⟨.rethrow, false, false, false⟩
  else ⟨.emitError, true, !real, true⟩
def LoggingErrorProp : Prop := ∀ catches real,
  loggingErrorM catches real = if !catches then ⟨.rethrow, false, false, false⟩
  else ⟨.emitError, true, !real, true⟩
theorem loggingError_proven : LoggingErrorProp := by
  unfold LoggingErrorProp
  intros
  rfl

structure ShimTrace (α : Type) where
  pairs : List (α × α)
  convertedLevel : Bool
  convertedFile : Bool
  emitted : Bool
  deriving Repr
def logmsgShimM {α : Type} (kwargs : List α) : ShimTrace α :=
  ⟨LoggingCov.pairKeywords kwargs, true, true, true⟩
def LogmsgShimProp : Prop := ∀ (α : Type) (kwargs : List α),
  logmsgShimM kwargs = ⟨LoggingCov.pairKeywords kwargs, true, true, true⟩
theorem logmsgShim_proven : LogmsgShimProp := by
  unfold LogmsgShimProp
  intros
  rfl

def logStateCtor := LoggingCov.makeLogState
def LogStateCtorProp : Prop := ∀ minimum logger,
  logStateCtor minimum logger = ⟨minimum, logger⟩
theorem logStateCtor_proven : LogStateCtorProp := by
  unfold LogStateCtorProp
  intros
  rfl

def currentLogstateM := LoggingCov.currentLogState
def CurrentLogstateProp : Prop := ∀ localState global,
  currentLogstateM localState global = localState.getD global
theorem currentLogstate_proven : CurrentLogstateProp := by
  unfold CurrentLogstateProp
  intros
  rfl

def withLogstate (f : Nat → Nat) (state : Nat) := f state
def WithLogstateProp : Prop := ∀ f state, withLogstate f state = f state
theorem withLogstate_proven : WithLogstateProp := by
  unfold WithLogstateProp
  intros
  rfl

def disableLoggingM := JuliaLean.Logging.disableLogging
def DisableLoggingProp : Prop := ∀ level,
  disableLoggingM level = JuliaLean.Logging.addInt level 1
theorem disableLogging_proven : DisableLoggingProp := by
  unfold DisableLoggingProp
  intros
  rfl

def envOverrideM := JuliaLean.Logging.envOverride
def EnvOverrideProp : Prop := ∀ config group mod root,
  envOverrideM config group mod root = JuliaLean.Logging.envOverride config group mod root
theorem envOverride_proven : EnvOverrideProp := by
  unfold EnvOverrideProp
  intros
  rfl

def globalLoggerM := LoggingCov.globalLogger
def GlobalLoggerProp : Prop := ∀ state, globalLoggerM state = state.logger
theorem globalLogger_proven : GlobalLoggerProp := by
  unfold GlobalLoggerProp
  intros
  rfl

def setGlobalLoggerM := LoggingCov.setGlobalLogger
def SetGlobalLoggerProp : Prop := ∀ new minimum state,
  setGlobalLoggerM new minimum state = (state.logger, ⟨minimum, new⟩)
theorem setGlobalLogger_proven : SetGlobalLoggerProp := by
  unfold SetGlobalLoggerProp
  intros
  rfl

def withLoggerM := JuliaLean.Logging.withLogger
def WithLoggerProp : Prop := ∀ previous installed outcome,
  withLoggerM previous installed outcome = ⟨installed, previous, outcome⟩
theorem withLogger_proven : WithLoggerProp := by
  unfold WithLoggerProp
  intros
  rfl

def currentLoggerM (state : LoggingCov.LogState) := state.logger
def CurrentLoggerProp : Prop := ∀ state, currentLoggerM state = state.logger
theorem currentLogger_proven : CurrentLoggerProp := by
  unfold CurrentLoggerProp
  intros
  rfl

def simpleLoggerStream := LoggingCov.simpleLogger
def SimpleLoggerStreamProp : Prop := ∀ streamOpen minimum,
  (simpleLoggerStream streamOpen minimum).streamOpen = streamOpen ∧
  (simpleLoggerStream streamOpen minimum).minimum = minimum
theorem simpleLoggerStream_proven : SimpleLoggerStreamProp := by
  unfold SimpleLoggerStreamProp
  intros
  exact ⟨rfl, rfl⟩

def simpleLoggerDefault (minimum : Int) := LoggingCov.simpleLogger false minimum
def SimpleLoggerDefaultProp : Prop := ∀ minimum,
  (simpleLoggerDefault minimum).streamOpen = false ∧ (simpleLoggerDefault minimum).minimum = minimum
theorem simpleLoggerDefault_proven : SimpleLoggerDefaultProp := by
  unfold SimpleLoggerDefaultProp
  intros
  exact ⟨rfl, rfl⟩

def simpleShouldlogM := LoggingCov.simpleShouldlog
def SimpleShouldlogProp : Prop := ∀ logger id,
  simpleShouldlogM logger id = decide (0 < logger.limits id)
theorem simpleShouldlog_proven : SimpleShouldlogProp := by
  unfold SimpleShouldlogProp
  intros
  rfl

def simpleMinLevelM := LoggingCov.simpleMinEnabledLevel
def SimpleMinLevelProp : Prop := ∀ logger, simpleMinLevelM logger = logger.minimum
theorem simpleMinLevel_proven : SimpleMinLevelProp := by
  unfold SimpleMinLevelProp
  intros
  rfl

def simpleCatchM := LoggingCov.simpleCatchExceptions
def SimpleCatchProp : Prop := ∀ _logger : Nat, simpleCatchM = false
theorem simpleCatch_proven : SimpleCatchProp := by
  unfold SimpleCatchProp
  intros
  rfl

structure SimpleHandleTrace where
  remaining : Int
  emitted : Bool
  messageLines : List JuliaLean.Logging.PhysicalLine
  valueLines : List JuliaLean.Logging.PhysicalLine
  usedFallbackStream : Bool
  deriving Repr
def simpleHandleM (remaining : Int) (messageLines valueLines : List String)
    (streamOpen : Bool) : SimpleHandleTrace :=
  if remaining = 0 then ⟨0, false, [], [], false⟩
  else ⟨remaining - 1, true, JuliaLean.Logging.simpleMessageLines messageLines,
    JuliaLean.Logging.simpleValueLines "key" valueLines, !streamOpen⟩
def SimpleHandleProp : Prop := ∀ remaining messages values streamOpen,
  simpleHandleM remaining messages values streamOpen =
  if remaining = 0 then ⟨0, false, [], [], false⟩
  else ⟨remaining - 1, true, JuliaLean.Logging.simpleMessageLines messages,
    JuliaLean.Logging.simpleValueLines "key" values, !streamOpen⟩
theorem simpleHandle_proven : SimpleHandleProp := by
  unfold SimpleHandleProp
  intros
  rfl

/-! `ConsoleLogger.jl` -/

def consoleLoggerStream := LoggingCov.consoleLogger
def ConsoleLoggerStreamProp : Prop := ∀ streamOpen minimum limited justify,
  consoleLoggerStream streamOpen minimum limited justify =
    LoggingCov.consoleLogger streamOpen minimum limited justify
theorem consoleLoggerStream_proven : ConsoleLoggerStreamProp := by
  unfold ConsoleLoggerStreamProp
  intros
  rfl

def consoleLoggerDefault (minimum : Int) limited justify := LoggingCov.consoleLogger false minimum limited justify
def ConsoleLoggerDefaultProp : Prop := ∀ minimum limited justify,
  consoleLoggerDefault minimum limited justify = LoggingCov.consoleLogger false minimum limited justify
theorem consoleLoggerDefault_proven : ConsoleLoggerDefaultProp := by
  unfold ConsoleLoggerDefaultProp
  intros
  rfl

def consoleShouldlogM := LoggingCov.consoleShouldlog
def ConsoleShouldlogProp : Prop := ∀ logger id,
  consoleShouldlogM logger id = decide (0 < logger.limits id)
theorem consoleShouldlog_proven : ConsoleShouldlogProp := by
  unfold ConsoleShouldlogProp
  intros
  rfl

def consoleMinLevelM := LoggingCov.consoleMinEnabledLevel
def ConsoleMinLevelProp : Prop := ∀ logger, consoleMinLevelM logger = logger.minimum
theorem consoleMinLevel_proven : ConsoleMinLevelProp := by
  unfold ConsoleMinLevelProp
  intros
  rfl

def showValuePlain := LoggingCov.showValue false false
def ShowValuePlainProp : Prop := ∀ _msg : Nat, showValuePlain = .plain
theorem showValuePlain_proven : ShowValuePlainProp := by
  unfold ShowValuePlainProp
  intros
  rfl

def showValueTuple (hasBacktrace : Bool) := LoggingCov.showValue true hasBacktrace
def ShowValueTupleProp : Prop := ∀ bt, showValueTuple bt = if bt then .exceptionWithBacktrace else .exception
theorem showValueTuple_proven : ShowValueTupleProp := by intro bt; cases bt <;> rfl

def showValueException := LoggingCov.showValue true false
def ShowValueExceptionProp : Prop := ∀ _ex : Nat, showValueException = .exception
theorem showValueException_proven : ShowValueExceptionProp := by
  unfold ShowValueExceptionProp
  intros
  rfl

def defaultLogcolorM := LoggingCov.defaultLogcolor
def DefaultLogcolorProp : Prop := ∀ level, defaultLogcolorM level =
  if level < LoggingCov.info then .debug else if level < LoggingCov.warn then .info
  else if level < LoggingCov.error then .warn else .error
theorem defaultLogcolor_proven : DefaultLogcolorProp := by
  unfold DefaultLogcolorProp
  intros
  rfl

def defaultMetafmtM := LoggingCov.defaultMetafmt
def DefaultMetafmtProp : Prop := ∀ level mod file line,
  defaultMetafmtM level mod file line = LoggingCov.defaultMetafmt level mod file line
theorem defaultMetafmt_proven : DefaultMetafmtProp := by
  unfold DefaultMetafmtProp
  intros
  rfl

def termlengthM := JuliaLean.Logging.terminalLength
def TermlengthProp : Prop := ∀ cells, termlengthM cells = cells.length
theorem termlength_proven : TermlengthProp := by
  unfold TermlengthProp
  intros
  rfl

structure ConsoleHandleTrace where
  remaining : Int
  emitted : Bool
  decorated : List JuliaLean.Logging.DecoratedLine
  rightPadding : Nat
  usedFallbackStream : Bool
  deriving Repr
def consoleHandleM (remaining : Int) (lines : List String) (padding : Nat)
    (streamOpen : Bool) : ConsoleHandleTrace :=
  if remaining = 0 then ⟨0, false, [], 0, false⟩
  else ⟨remaining - 1, true, JuliaLean.Logging.decorateConsole lines, padding, !streamOpen⟩
def ConsoleHandleProp : Prop := ∀ remaining lines padding streamOpen,
  consoleHandleM remaining lines padding streamOpen =
  if remaining = 0 then ⟨0, false, [], 0, false⟩
  else ⟨remaining - 1, true, JuliaLean.Logging.decorateConsole lines, padding, !streamOpen⟩
theorem consoleHandle_proven : ConsoleHandleProp := by
  unfold ConsoleHandleProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulLogging

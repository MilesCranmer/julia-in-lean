import JuliaLean.base.logging.ConsoleLogger
import JuliaLean.Proofs.base.logging.ConsoleLogger.LoggingCov
import JuliaLean.Proofs.base.logging.logging.Claims

namespace JuliaLean.ConcurrencyCov.FaithfulLogging

open JuliaLean.ConcurrencyCov

def ConsoleLoggerStreamProp : Prop := ∀ streamOpen minimum limited justify,
  consoleLoggerStream streamOpen minimum limited justify =
    LoggingCov.consoleLogger streamOpen minimum limited justify

theorem consoleLoggerStream_proven : ConsoleLoggerStreamProp := by
  unfold ConsoleLoggerStreamProp
  intros
  rfl

def ConsoleLoggerDefaultProp : Prop := ∀ minimum limited justify,
  consoleLoggerDefault minimum limited justify = LoggingCov.consoleLogger false minimum limited justify

theorem consoleLoggerDefault_proven : ConsoleLoggerDefaultProp := by
  unfold ConsoleLoggerDefaultProp
  intros
  rfl

def ConsoleShouldlogProp : Prop := ∀ logger id,
  consoleShouldlogM logger id = decide (0 < logger.limits id)

theorem consoleShouldlog_proven : ConsoleShouldlogProp := by
  unfold ConsoleShouldlogProp
  intros
  rfl

def ConsoleMinLevelProp : Prop := ∀ logger, consoleMinLevelM logger = logger.minimum

theorem consoleMinLevel_proven : ConsoleMinLevelProp := by
  unfold ConsoleMinLevelProp
  intros
  rfl

def ShowValuePlainProp : Prop := ∀ _msg : Nat, showValuePlain = .plain

theorem showValuePlain_proven : ShowValuePlainProp := by
  unfold ShowValuePlainProp
  intros
  rfl

def ShowValueTupleProp : Prop := ∀ bt, showValueTuple bt = if bt then .exceptionWithBacktrace else .exception

theorem showValueTuple_proven : ShowValueTupleProp := by intro bt; cases bt <;> rfl

def ShowValueExceptionProp : Prop := ∀ _ex : Nat, showValueException = .exception

theorem showValueException_proven : ShowValueExceptionProp := by
  unfold ShowValueExceptionProp
  intros
  rfl

def DefaultLogcolorProp : Prop := ∀ level, defaultLogcolorM level =
  if level < LoggingCov.info then .debug else if level < LoggingCov.warn then .info
  else if level < LoggingCov.error then .warn else .error

theorem defaultLogcolor_proven : DefaultLogcolorProp := by
  unfold DefaultLogcolorProp
  intros
  rfl

def DefaultMetafmtProp : Prop := ∀ level mod file line,
  defaultMetafmtM level mod file line = LoggingCov.defaultMetafmt level mod file line

theorem defaultMetafmt_proven : DefaultMetafmtProp := by
  unfold DefaultMetafmtProp
  intros
  rfl

def TermlengthProp : Prop := ∀ cells, termlengthM cells = cells.length

theorem termlength_proven : TermlengthProp := by
  unfold TermlengthProp
  intros
  rfl

def ConsoleHandleProp : Prop := ∀ remaining lines padding streamOpen,
  consoleHandleM remaining lines padding streamOpen =
  if remaining = 0 then ⟨0, false, [], 0, false⟩
  else ⟨remaining - 1, true, JuliaLean.Logging.decorateConsole lines, padding, !streamOpen⟩

theorem consoleHandle_proven : ConsoleHandleProp := by
  unfold ConsoleHandleProp
  intros
  rfl

end JuliaLean.ConcurrencyCov.FaithfulLogging

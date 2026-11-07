import JuliaLean.base.logging.ConsoleLogger
import JuliaLean.Proofs.base.logging.logging.LoggingCov

namespace JuliaLean.ConcurrencyCov.LoggingCov

open JuliaLean.ConcurrencyCov

/-- ConsoleLogger constructors, filtering, value dispatch, colors, and metadata
formatting preserve their source decisions (`base/logging/ConsoleLogger.jl:37-88`). -/
def ConsoleLoggerSpec : Prop :=
  (∀ streamOpen minimum limited justify,
    (consoleLogger streamOpen minimum limited justify).minimum = minimum ∧
    (consoleLogger streamOpen minimum limited justify).showLimited = limited ∧
    (consoleLogger streamOpen minimum limited justify).rightJustify = justify) ∧
  (∀ logger id, consoleShouldlog logger id = decide (0 < logger.limits id)) ∧
  (∀ logger, consoleMinEnabledLevel logger = logger.minimum) ∧
  showValue false false = .plain ∧ showValue true false = .exception ∧
  showValue true true = .exceptionWithBacktrace ∧
  (∀ level, defaultLogcolor level =
    if level < info then .debug else if level < warn then .info
    else if level < error then .warn else .error) ∧
  (∀ moduleName file line, (defaultMetafmt info moduleName file line).suffixText = "")

theorem consoleLoggerSpec_proven : ConsoleLoggerSpec := by
  refine ⟨fun _ _ _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, fun _ => rfl,
    rfl, rfl, rfl, fun _ => rfl, ?_⟩
  intro moduleName file line
  rfl

end JuliaLean.ConcurrencyCov.LoggingCov

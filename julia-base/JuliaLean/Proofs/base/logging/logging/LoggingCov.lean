import JuliaLean.base.logging.logging
import JuliaLean.Proofs.base.locks_mt.common

namespace JuliaLean.ConcurrencyCov.LoggingCov

open JuliaLean.ConcurrencyCov

/-- Interface defaults, NullLogger, level conversion/display, and invocation
barriers preserve the source results (`base/logging/logging.jl:72-189`). -/
def LoggingInterfaceSpec : Prop :=
  (∀ l, catchExceptions l = (if l = .simple then false else true)) ∧
  (∀ b, invokedShouldlog b = b) ∧
  (∀ l, invokedMinEnabledLevel l = l) ∧
  (∀ l, invokedCatchExceptions l = catchExceptions l) ∧
  nullMinEnabledLevel = aboveMax ∧ nullShouldlog = false ∧
  nullHandleMessage = .error (.errorException "Null logger handle_message() should not be called") ∧
  (∀ l, copyLevel l = l) ∧
  (∀ a b, levelLessInteger a b = decide (a < b) ∧ integerLessLevel a b = decide (a < b)) ∧
  (∀ n, convertLevel n = if IntTy.min .i32 ≤ n ∧ n ≤ IntTy.max .i32 then .ok n else .error .inexactError) ∧
  (∀ l, levelToInt32 l = l) ∧
  showLevel warn = "Warn"

theorem loggingInterfaceSpec_proven : LoggingInterfaceSpec := by
  refine ⟨?_, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl,
    fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ => rfl, by decide⟩
  intro l
  cases l <;> rfl

/-- Macro wrappers select source metadata and levels; syntax classification picks
the constant, explicit-definedness, or try/catch record path; helper shims retain
keyword pairing and logger-state fallback (`base/logging/logging.jl:266-545`). -/
def LoggingMacroSpec : Prop :=
  (∀ m f line, sourceInfo m none line = ⟨m, "?", line⟩ ∧
    sourceInfo m (some f) line = ⟨m, f, line⟩) ∧
  (∀ l, macroLevel .logmsg l = l ∧ macroLevel .debug l = debug ∧
    macroLevel .info l = info ∧ macroLevel .warn l = warn ∧ macroLevel .error l = error) ∧
  (∀ stem, defaultGroup stem = stem) ∧
  (∀ used h, nextRecordId used h =
    (((List.range (used.length + 1)).map (h + ·)).find? (· ∉ used)).getD h) ∧
  (isSimple .string = true ∧ isSimple .symbol = true ∧ isSimple .other = false) ∧
  (∀ x, isSimpleKw (.keyword true x) = isSimple x) ∧
  (∀ message kwargs, logmsgCode message kwargs =
    if message != .symbol && isSimple message && kwargs.isEmpty then .constant
    else if isSimple message && kwargs.all isSimpleKw then .checked else .guarded) ∧
  (handleMessageNothrow .returned = true ∧ ∀ e, handleMessageNothrow (.threw e) = false) ∧
  (∀ literal stem, defaultGroupCode literal stem =
    if literal then .constant (defaultGroup stem) else .memoized) ∧
  (∀ catches, loggingError catches = if catches then .emitError else .rethrow) ∧
  (∀ (α : Type) kwargs, logmsgShim (α := α) kwargs = pairKeywords kwargs) ∧
  (∀ minimum logger, makeLogState minimum logger = ⟨minimum, logger⟩) ∧
  (∀ localState global, currentLogState localState global = localState.getD global)

theorem loggingMacroSpec_proven : LoggingMacroSpec := by
  exact ⟨fun _ _ _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩,
    fun _ => rfl, fun _ _ => rfl, ⟨rfl, rfl, rfl⟩, fun _ => rfl, fun _ _ => rfl,
    ⟨rfl, fun _ => rfl⟩, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- Global and SimpleLogger wrappers return the previous logger, expose minimum
levels, disable exception catching, and decrement built-in `maxlog` limits before
formatting (`base/logging/logging.jl:631-734`). -/
def SimpleLoggerSpec : Prop :=
  (∀ global, globalLogger global = global.logger) ∧
  (∀ new minimum global, (setGlobalLogger new minimum global).1 = global.logger ∧
    (setGlobalLogger new minimum global).2 = ⟨minimum, new⟩) ∧
  (∀ streamOpen minimum, (simpleLogger streamOpen minimum).minimum = minimum) ∧
  (∀ logger, simpleMinEnabledLevel logger = logger.minimum) ∧
  simpleCatchExceptions = false ∧
  (∀ logger id, simpleShouldlog logger id = decide (0 < logger.limits id)) ∧
  (∀ logger id, simpleHandleMessage logger id none = logger)

theorem simpleLoggerSpec_proven : SimpleLoggerSpec := by
  exact ⟨fun _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl,
    fun _ => rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end JuliaLean.ConcurrencyCov.LoggingCov

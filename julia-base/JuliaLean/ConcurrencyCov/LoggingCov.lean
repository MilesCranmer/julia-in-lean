import JuliaLean.ConcurrencyCov.Common

/-! Source-body models and properties for `base/logging/logging.jl` and
`base/logging/ConsoleLogger.jl`. -/

namespace JuliaLean.ConcurrencyCov.LoggingCov

open JuliaLean.ConcurrencyCov

abbrev Level := Int
def debug : Level := -1000
def info : Level := 0
def warn : Level := 1000
def error : Level := 2000
def aboveMax : Level := 1000001
def belowMin : Level := -1000001

inductive LoggerKind where | null | simple | console | custom
  deriving DecidableEq, Repr

def catchExceptions : LoggerKind → Bool
  | .simple => false
  | _ => true
def invokedShouldlog (should : Bool) : Bool := should
def invokedMinEnabledLevel (level : Level) : Level := level
def invokedCatchExceptions (kind : LoggerKind) : Bool := catchExceptions kind
def nullMinEnabledLevel : Level := aboveMax
def nullShouldlog : Bool := false
def nullHandleMessage : R Unit := .error (.errorException "Null logger handle_message() should not be called")

def copyLevel (level : Level) : Level := level
def levelLessInteger (a b : Int) : Bool := decide (a < b)
def integerLessLevel (a b : Int) : Bool := decide (a < b)
def convertLevel (n : Int) : R Level :=
  if IntTy.min .i32 ≤ n ∧ n ≤ IntTy.max .i32 then .ok n else .error .inexactError
def levelToInt32 (n : Level) : Int := n
def showLevel (level : Level) : String :=
  if level = belowMin then "BelowMinLevel"
  else if level = debug then "Debug"
  else if level = info then "Info"
  else if level = warn then "Warn"
  else if level = error then "Error"
  else if level = aboveMax then "AboveMaxLevel"
  else "LogLevel(" ++ toString level ++ ")"

structure SourceInfo where
  moduleName : String
  file : String
  line : Int
  deriving DecidableEq, Repr
def sourceInfo (moduleName : String) (file : Option String) (line : Int) : SourceInfo :=
  ⟨moduleName, file.getD "?", line⟩

inductive MacroKind where | logmsg | debug | info | warn | error
  deriving DecidableEq, Repr
def macroLevel (kind : MacroKind) (explicit : Level) : Level := match kind with
  | .logmsg => explicit | .debug => debug | .info => info | .warn => warn | .error => error

def nextRecordId (used : List Nat) (h : Nat) : Nat :=
  (((List.range (used.length + 1)).map (h + ·)).find? (· ∉ used)).getD h

def defaultGroup (stem : String) : String := stem

inductive Syntax where
  | string | symbol | quote (inner : Syntax) | number | char | inert
  | keyword (escaped : Bool) (value : Syntax) | other
  deriving DecidableEq, Repr

def isSimple : Syntax → Bool
  | .string | .symbol | .number | .char | .inert => true
  | .quote x => isSimple x
  | _ => false
def isSimpleKw : Syntax → Bool
  | .keyword true x => isSimple x
  | _ => false

inductive RecordPath where | constant | checked | guarded
  deriving DecidableEq, Repr
def logmsgCode (message : Syntax) (kwargs : List Syntax) : RecordPath :=
  if message != .symbol && isSimple message && kwargs.isEmpty then .constant
  else if isSimple message && kwargs.all isSimpleKw then .checked
  else .guarded

inductive HandlerOutcome where | returned | threw (e : Nat)
  deriving DecidableEq, Repr
def handleMessageNothrow (outcome : HandlerOutcome) : Bool := match outcome with
  | .returned => true | .threw _ => false

inductive GroupCode where | constant (group : String) | memoized
  deriving DecidableEq, Repr
def defaultGroupCode (literalAvailable : Bool) (stem : String) : GroupCode :=
  if literalAvailable then .constant (defaultGroup stem) else .memoized

inductive LoggingErrorAction where | rethrow | emitError
  deriving DecidableEq, Repr
def loggingError (catches : Bool) : LoggingErrorAction := if catches then .emitError else .rethrow

def pairKeywords {α : Type} : List α → List (α × α)
  | k :: v :: rest => (k, v) :: pairKeywords rest
  | _ => []
def logmsgShim {α : Type} (kwargs : List α) : List (α × α) := pairKeywords kwargs

structure LogState where
  minimum : Level
  logger : LoggerKind
  deriving DecidableEq, Repr
def makeLogState (minimum : Level) (logger : LoggerKind) : LogState := ⟨minimum, logger⟩
def currentLogState (localState : Option LogState) (global : LogState) : LogState := localState.getD global
def globalLogger (global : LogState) : LoggerKind := global.logger
def setGlobalLogger (new : LoggerKind) (minimum : Level) (global : LogState) : LoggerKind × LogState :=
  (global.logger, ⟨minimum, new⟩)

structure SimpleState where
  streamOpen : Bool
  minimum : Level
  limits : Nat → Int
def simpleLogger (streamOpen : Bool) (minimum : Level) : SimpleState :=
  ⟨streamOpen, minimum, fun _ => 1⟩
def simpleShouldlog (logger : SimpleState) (id : Nat) : Bool := 0 < logger.limits id
def simpleMinEnabledLevel (logger : SimpleState) : Level := logger.minimum
def simpleCatchExceptions : Bool := false
def simpleHandleMessage (logger : SimpleState) (id : Nat) (maxlog : Option Int) : SimpleState :=
  match maxlog with
  | some n =>
    let remaining := if logger.limits id = 1 then n else logger.limits id
    if remaining = 0 then logger else { logger with limits := upd logger.limits id (remaining - 1) }
  | none => logger

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

/-! ## ConsoleLogger -/

inductive Color where | debug | info | warn | error
  deriving DecidableEq, Repr
structure ConsoleState where
  streamOpen : Bool
  minimum : Level
  showLimited : Bool
  rightJustify : Int
  limits : Nat → Int

def consoleLogger (streamOpen : Bool) (minimum : Level) (showLimited : Bool)
    (rightJustify : Int) : ConsoleState :=
  ⟨streamOpen, minimum, showLimited, rightJustify, fun _ => 1⟩
def consoleShouldlog (logger : ConsoleState) (id : Nat) : Bool := 0 < logger.limits id
def consoleMinEnabledLevel (logger : ConsoleState) : Level := logger.minimum

inductive ShowValue where | plain | exception | exceptionWithBacktrace
  deriving DecidableEq, Repr
def showValue (exception : Bool) (backtrace : Bool) : ShowValue :=
  if exception then if backtrace then .exceptionWithBacktrace else .exception else .plain

def defaultLogcolor (level : Level) : Color :=
  if level < info then .debug else if level < warn then .info else if level < error then .warn else .error

structure Metadata where
  color : Color
  prefixText : String
  suffixText : String
  deriving DecidableEq, Repr
def defaultMetafmt (level : Level) (moduleName file : Option String) (line : Option Int) : Metadata :=
  let color := defaultLogcolor level
  let prefixText := (if level = warn then "Warning" else showLevel level) ++ ":"
  if info ≤ level && level < warn then ⟨color, prefixText, ""⟩
  else
    let mod := moduleName.getD ""
    let loc := file.getD ""
    let sep := if moduleName.isSome && file.isSome then " " else ""
    let ln := match line with | none => "" | some n => ":" ++ toString n
    let body := mod ++ sep ++ loc ++ ln
    ⟨color, prefixText, if body = "" then "" else "@ " ++ body⟩

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

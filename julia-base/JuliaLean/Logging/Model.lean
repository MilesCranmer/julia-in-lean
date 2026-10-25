import JuliaLean.Core

/-!
Executable model of the control and formatting decisions in Julia's built-in
logging implementation. Text rendering is represented as physical lines; Julia's
`showvalue` remains the producer of those lines.
-/

namespace JuliaLean.Logging

open JuliaLean

/-! ### Log levels and global disabling -/

/-- `LogLevel.level::Int32`, `base/logging/logging.jl:125-137`. -/
abbrev LogLevel := JInt .i32

def Debug : LogLevel := JInt.lit .i32 (-1000)
def Info : LogLevel := JInt.lit .i32 0
def Warn : LogLevel := JInt.lit .i32 1000
def Error : LogLevel := JInt.lit .i32 2000
def AboveMaxLevel : LogLevel := JInt.lit .i32 1000001

/-- `isless(::LogLevel, ::LogLevel)`, `base/logging/logging.jl:131`. -/
def logLess (a b : LogLevel) : Prop := a.val < b.val

/-- `+(::LogLevel, ::Int)` on a 64-bit Julia process, lines 134 and 125-127. -/
def addInt (level : LogLevel) (inc : Int) : Jl LogLevel :=
  JInt.convert .i32 (level.val + inc)

/-- `-(::LogLevel, ::Int)` on a 64-bit Julia process, lines 135 and 125-127. -/
def subInt (level : LogLevel) (inc : Int) : Jl LogLevel :=
  JInt.convert .i32 (level.val - inc)

/-- `disable_logging`, `base/logging/logging.jl:565-567`. -/
def disableLogging (level : LogLevel) : Jl LogLevel := addInt level 1

/-! ### Macro keyword classification -/

inductive Key where
  | moduleKey | groupKey | idKey | fileKey | lineKey
  | maxlog | exception | ordinary
  deriving Repr, DecidableEq, BEq

def Key.isSpecial : Key → Bool
  | .moduleKey | .groupKey | .idKey | .fileKey | .lineKey => true
  | _ => false

inductive LogArg where
  | assignment (key : Key)
  | splat (keys : List Key)
  | positional (key : Key)
  deriving Repr, DecidableEq

structure ProcessedArgs where
  overrides : List Key := []
  kwargs : List Key := []
  deriving Repr, DecidableEq

/-- One iteration of `process_logmsg_exs`, `base/logging/logging.jl:448-474`. -/
def processArg : LogArg → ProcessedArgs
  | .assignment key =>
      if key.isSpecial then { overrides := [key] } else { kwargs := [key] }
  | .splat keys => { kwargs := keys }
  | .positional key => { kwargs := [key] }

def ProcessedArgs.append (a b : ProcessedArgs) : ProcessedArgs :=
  { overrides := a.overrides ++ b.overrides, kwargs := a.kwargs ++ b.kwargs }

def processArgs : List LogArg → ProcessedArgs
  | [] => {}
  | arg :: rest => (processArg arg).append (processArgs rest)

/-! ### Custom level dispatch -/

inductive InputLevel where
  | standard (severity : LogLevel)
  | custom (convertedSeverity : LogLevel)
  deriving Repr, DecidableEq

def standardizedLevel : InputLevel → LogLevel
  | .standard level | .custom level => level

inductive Dispatch where
  | message | loggingError
  deriving Repr, DecidableEq, BEq

/-- The built-in handlers require `LogLevel`, while the macro passes the original level. -/
def builtinDispatch : InputLevel → Dispatch
  | .standard _ => .message
  | .custom _ => .loggingError

/-! ### `JULIA_DEBUG` -/

inductive DebugToken where
  | empty
  | include (name : String)
  | exclude (name : String)
  deriving Repr, DecidableEq

structure DebugConfig where
  includes : List String := []
  excludes : List String := []
  deriving Repr, DecidableEq

def DebugConfig.addToken (config : DebugConfig) : DebugToken → DebugConfig
  | .empty => config
  | .include name => { config with includes := config.includes ++ [name] }
  | .exclude name => if name.isEmpty then config else
      { config with excludes := config.excludes ++ [name] }

/-- Parsing after `split(debug, ',')`, `base/logging/logging.jl:578-590`.
Names are kept exactly, so whitespace remains significant. -/
def DebugConfig.ofTokens (tokens : List DebugToken) : DebugConfig :=
  tokens.foldl DebugConfig.addToken {}

def matchesName (names : List String) (group moduleName rootName : String) : Bool :=
  names.contains group || names.contains moduleName || names.contains rootName

/-- `env_override_minlevel`, `base/logging/logging.jl:593-613`. -/
def envOverride (config : DebugConfig) (group moduleName rootName : String) : Bool :=
  if !config.excludes.contains "all" &&
      (config.includes.contains "all" || !config.excludes.isEmpty) then
    if config.excludes.isEmpty then true
    else !matchesName config.excludes group moduleName rootName
  else
    if config.includes.isEmpty then false
    else matchesName config.includes group moduleName rootName

/-! ### Filtering and built-in loggers -/

inductive Logger where
  | console (minimum : LogLevel)
  | simple (minimum : LogLevel)
  | null
  deriving Repr, DecidableEq

def Logger.minimum : Logger → LogLevel
  | .console level | .simple level => level
  | .null => AboveMaxLevel

def Logger.shouldLog : Logger → Bool → Bool
  | .null, _ => false
  | _, idAvailable => idAvailable

def levelAtLeast (a b : LogLevel) : Bool := decide (b.val ≤ a.val)

/-- Early filtering in `logmsg_code` and `current_logger_for_env`, lines 340-346 and 396-427. -/
def macroEmits (globalMinimum : LogLevel) (logger : Logger) (level : LogLevel)
    (debug : DebugConfig) (group moduleName rootName : String) (idAvailable : Bool) : Bool :=
  levelAtLeast level globalMinimum &&
    (levelAtLeast level logger.minimum || envOverride debug group moduleName rootName) &&
    logger.shouldLog idAvailable

/-! ### `maxlog` -/

inductive IntegerKind where
  | builtin | big
  deriving Repr, DecidableEq

structure LimitState where
  remaining : Option Nat := none
  emissions : Nat := 0
  deriving Repr, DecidableEq

/-- One serialized shouldlog/handle_message step, logging.jl:694-708 and
ConsoleLogger.jl:51-52,114-121. BigInt skips the limiting block. -/
def maxlogCall (kind : IntegerKind) (requested : Nat) (state : LimitState) : LimitState :=
  match kind with
  | .big => { state with emissions := state.emissions + 1 }
  | .builtin =>
      let remaining := state.remaining.getD requested
      if remaining = 0 then { state with remaining := some 0 }
      else { remaining := some (remaining - 1), emissions := state.emissions + 1 }

def runMaxlogFrom (kind : IntegerKind) (requested : Nat) : Nat → LimitState → LimitState
  | 0, state => state
  | calls + 1, state => runMaxlogFrom kind requested calls (maxlogCall kind requested state)

/-- Iteration of the locked per-id transition from an empty dictionary. -/
def runMaxlog (kind : IntegerKind) (requested calls : Nat) : LimitState :=
  runMaxlogFrom kind requested calls {}

/-! ### Dynamic logger scope -/

inductive Outcome where
  | returned | threw
  deriving Repr, DecidableEq

structure ScopeTrace where
  during : Nat
  after : Nat
  outcome : Outcome
  deriving Repr, DecidableEq

/-- `with_logstate` via `ScopedValue`, `base/logging/logging.jl:540-547,657-659`. -/
def withLogger (previous installed : Nat) (outcome : Outcome) : ScopeTrace :=
  { during := installed, after := previous, outcome }

def inheritedLogger (parent : Nat) : Nat := parent

/-! ### Physical-line formatting -/

inductive Box where
  | single | first | middle | last
  deriving Repr, DecidableEq

structure DecoratedLine where
  box : Box
  text : String
  deriving Repr, DecidableEq

def decorateRest : List String → List DecoratedLine
  | [] => []
  | [line] => [{ box := .last, text := line }]
  | line :: rest => { box := .middle, text := line } :: decorateRest rest

/-- ConsoleLogger's `[ `/`┌ `/`│ `/`└ ` choice, ConsoleLogger.jl:178-193. -/
def decorateConsole : List String → List DecoratedLine
  | [] => []
  | [line] => [{ box := .single, text := line }]
  | line :: rest => { box := .first, text := line } :: decorateRest rest

structure PhysicalLine where
  prefixed : Bool
  text : String
  deriving Repr, DecidableEq

/-- SimpleLogger message lines, `base/logging/logging.jl:710-715`. -/
def simpleMessageLines (lines : List String) : List PhysicalLine :=
  lines.map fun line => { prefixed := true, text := line }

/-- SimpleLogger key/value output, `base/logging/logging.jl:716-719`. -/
def simpleValueLines (key : String) : List String → List PhysicalLine
  | [] => [{ prefixed := true, text := key ++ " = " }]
  | first :: rest =>
      { prefixed := true, text := key ++ " = " ++ first } ::
        rest.map fun line => { prefixed := false, text := line }

inductive Cell where
  | ascii | wide | combining
  deriving Repr, DecidableEq

/-- Current `termlength` adds one for every non-ANSI character, ConsoleLogger.jl:92-108. -/
def terminalLength (cells : List Cell) : Nat := cells.length

def displayWidth : List Cell → Nat
  | [] => 0
  | .ascii :: rest => 1 + displayWidth rest
  | .wide :: rest => 2 + displayWidth rest
  | .combining :: rest => displayWidth rest

/-- Width after padding computed from `termlength`, for the branch where the suffix stays
on the message line, ConsoleLogger.jl:169-193. -/
def rightJustifiedWidth (target fixedWidth : Nat) (message : List Cell) : Nat :=
  let measured := fixedWidth + terminalLength message
  fixedWidth + displayWidth message + (target - measured)

end JuliaLean.Logging

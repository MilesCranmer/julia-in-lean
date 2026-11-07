import JuliaLean.base.locks_mt
import JuliaLean.Core
import JuliaLean.base.expr
import JuliaLean.base.reduce
import JuliaLean.base.scopedvalues

/-!
# Model of `base/logging/logging.jl`

Typed model of the logger interface and log levels at Julia
`f755f49a9e41380d7da126b3c1db9fe7f83dd027`. Logger dispatch, integer promotion,
stream output, and exception construction are explicit typed interfaces. Macro
expansion and compile-time source analysis remain visible as untranslated blocks.
-/

namespace JuliaLean.base.logging.logging

open JuliaLean


/--
Julia source: base/logging/logging.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type AbstractLogger ; end
```
-/
abbrev AbstractLogger (Logger : Type) := Logger

/--
Julia source: base/logging/logging.jl:125-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct LogLevel
    level::Int32
end
```
-/
structure LogLevel where
  level : JInt .i32
  deriving Repr, DecidableEq

/-- Integer operations selected by Julia's `Integer` dispatch. -/
structure LogLevelIntegerOps (Integer Error : Type) where
  convertToInt32 : Integer → Except Error (JInt .i32)
  lessInt32Integer : JInt .i32 → Integer → Bool
  lessIntegerInt32 : Integer → JInt .i32 → Bool
  addInt32Integer : JInt .i32 → Integer → Except Error (JInt .i32)
  subInt32Integer : JInt .i32 → Integer → Except Error (JInt .i32)

structure LogLevelShowOps (Io Error : Type) where
  printString : Io → String → Except Error Io
  int32String : JInt .i32 → String

/-- Typed implementations supplied by concrete logger dispatch. -/
structure LoggerOps (m : Type → Type) (Logger Level Module Group Id Message File Keywords : Type) where
  minEnabledLevel : Logger → m LogLevel
  shouldlog : Logger → Level → Module → Group → Id → m Bool
  catchExceptions : Logger → m Bool
  handleMessage : Logger → Level → Message → Module → Group → Id → File → JInt .i64 →
    Keywords → m Unit

/--
Julia source: base/logging/logging.jl:129-129 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogLevel(level::LogLevel) = level
```
-/
def logLevelIdentity (level : LogLevel) : LogLevel := level

/--
Julia source: base/logging/logging.jl:131-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(a::LogLevel, b::LogLevel) = isless(a.level, b.level)
```
-/
def islessLogLevel (a b : LogLevel) : Bool := decide (a.level.val < b.level.val)

/--
Julia source: base/logging/logging.jl:132-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(a::LogLevel, b::Integer) = isless(a.level, b)
```
-/
def islessLogLevelInteger {Integer Error : Type} (ops : LogLevelIntegerOps Integer Error)
    (a : LogLevel) (b : Integer) : Bool := ops.lessInt32Integer a.level b

/--
Julia source: base/logging/logging.jl:133-133 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isless(a::Integer, b::LogLevel) = isless(a, b.level)
```
-/
def islessIntegerLogLevel {Integer Error : Type} (ops : LogLevelIntegerOps Integer Error)
    (a : Integer) (b : LogLevel) : Bool := ops.lessIntegerInt32 a b.level

/--
Julia source: base/logging/logging.jl:134-134 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
+(level::LogLevel, inc::Integer) = LogLevel(level.level+inc)
```
-/
def addLogLevel {Integer Error : Type} (ops : LogLevelIntegerOps Integer Error)
    (level : LogLevel) (increment : Integer) : Except Error LogLevel := do
  pure ⟨← ops.addInt32Integer level.level increment⟩

/--
Julia source: base/logging/logging.jl:135-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
-(level::LogLevel, inc::Integer) = LogLevel(level.level-inc)
```
-/
def subLogLevel {Integer Error : Type} (ops : LogLevelIntegerOps Integer Error)
    (level : LogLevel) (increment : Integer) : Except Error LogLevel := do
  pure ⟨← ops.subInt32Integer level.level increment⟩

/--
Julia source: base/logging/logging.jl:136-136 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{LogLevel}, level::Integer) = LogLevel(level)
```
-/
def convertIntegerLogLevel {Integer Error : Type} (ops : LogLevelIntegerOps Integer Error)
    (level : Integer) : Except Error LogLevel := do
  pure ⟨← ops.convertToInt32 level⟩

/--
Julia source: base/logging/logging.jl:137-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{Int32}, level::LogLevel) = level.level
```
-/
def convertLogLevelInt32 (level : LogLevel) : JInt .i32 := level.level

/--
Julia source: base/logging/logging.jl:144-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const BelowMinLevel = LogLevel(-1000001)
```
-/
def belowMinLevel : LogLevel := ⟨JInt.wrap .i32 (-1000001)⟩

/--
Julia source: base/logging/logging.jl:150-150 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const Debug         = LogLevel(   -1000)
```
-/
def debugLevel : LogLevel := ⟨JInt.wrap .i32 (-1000)⟩

/--
Julia source: base/logging/logging.jl:156-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const Info          = LogLevel(       0)
```
-/
def infoLevel : LogLevel := ⟨JInt.wrap .i32 0⟩

/--
Julia source: base/logging/logging.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const Warn          = LogLevel(    1000)
```
-/
def warnLevel : LogLevel := ⟨JInt.wrap .i32 1000⟩

/--
Julia source: base/logging/logging.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const Error         = LogLevel(    2000)
```
-/
def errorLevel : LogLevel := ⟨JInt.wrap .i32 2000⟩

/--
Julia source: base/logging/logging.jl:174-174 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const AboveMaxLevel = LogLevel( 1000001)
```
-/
def aboveMaxLevel : LogLevel := ⟨JInt.wrap .i32 1000001⟩

-- UNTRANSLATED
-- Source: base/logging/logging.jl:41-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function handle_message end
-- /Source
-- Reason: This is a bodyless generic interface declaration; concrete methods are supplied through `LoggerOps`.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:49-49 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function shouldlog end
-- /Source
-- Reason: This is a bodyless generic interface declaration; concrete methods are supplied through `LoggerOps`.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function min_enabled_level end
-- /Source
-- Reason: This is a bodyless generic interface declaration; concrete methods are supplied through `LoggerOps`.
/--
Julia source: base/logging/logging.jl:72-72 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
catch_exceptions(logger) = true
```
-/
def catchExceptionsDefault {Logger : Type} (_logger : Logger) : Bool := true

/--
Julia source: base/logging/logging.jl:77-84 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.@constprop :none function _invoked_shouldlog(logger, level, _module, group, id)
    @nospecialize
    return invoke(
        shouldlog,
        Tuple{typeof(logger), typeof(level), typeof(_module), typeof(group), typeof(id)},
        logger, level, _module, group, id
    )::Bool
end
```
-/
def invokedShouldlog {m : Type → Type} {Logger Level Module Group Id Message File Keywords : Type}
    (ops : LoggerOps m Logger Level Module Group Id Message File Keywords)
    (logger : Logger) (level : Level) (module : Module) (group : Group) (id : Id) : m Bool :=
  ops.shouldlog logger level module group id

/--
Julia source: base/logging/logging.jl:86-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _invoked_min_enabled_level(@nospecialize(logger))
    return invoke(min_enabled_level, Tuple{typeof(logger)}, logger)::LogLevel
end
```
-/
def invokedMinEnabledLevel {m : Type → Type}
    {Logger Level Module Group Id Message File Keywords : Type}
    (ops : LoggerOps m Logger Level Module Group Id Message File Keywords)
    (logger : Logger) : m LogLevel := ops.minEnabledLevel logger

/--
Julia source: base/logging/logging.jl:90-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _invoked_catch_exceptions(@nospecialize(logger))
    return invoke(catch_exceptions, Tuple{typeof(logger)}, logger)::Bool
end
```
-/
def invokedCatchExceptions {m : Type → Type}
    {Logger Level Module Group Id Message File Keywords : Type}
    (ops : LoggerOps m Logger Level Module Group Id Message File Keywords)
    (logger : Logger) : m Bool := ops.catchExceptions logger

/--
Julia source: base/logging/logging.jl:100-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct NullLogger <: AbstractLogger; end
```
-/
structure NullLogger where

/--
Julia source: base/logging/logging.jl:102-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min_enabled_level(::NullLogger) = AboveMaxLevel
```
-/
def minEnabledLevelNull (_logger : NullLogger) : LogLevel := aboveMaxLevel

/--
Julia source: base/logging/logging.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
shouldlog(::NullLogger, args...) = false
```
-/
def shouldlogNull {Args : Type} (_logger : NullLogger) (_args : Args) : Bool := false

/--
Julia source: base/logging/logging.jl:104-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
handle_message(::NullLogger, args...; kwargs...) =
    (@nospecialize; error("Null logger handle_message() should not be called"))
```
-/
def handleMessageNull {Args Keywords Error : Type} (errorException : String → Error)
    (_logger : NullLogger) (_args : Args) (_keywords : Keywords) : Except Error Unit :=
  .error (errorException "Null logger handle_message() should not be called")

/--
Julia source: base/logging/logging.jl:180-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, level::LogLevel)
    if     level == BelowMinLevel  print(io, "BelowMinLevel")
    elseif level == Debug          print(io, "Debug")
    elseif level == Info           print(io, "Info")
    elseif level == Warn           print(io, "Warn")
    elseif level == Error          print(io, "Error")
    elseif level == AboveMaxLevel  print(io, "AboveMaxLevel")
    else                           print(io, "LogLevel($(level.level))")
    end
end
```
-/
def logLevelEqual (a b : LogLevel) : Bool := decide (a.level.val = b.level.val)

def showLogLevel {Io Error : Type} (ops : LogLevelShowOps Io Error) (io : Io)
    (level : LogLevel) : Except Error Io :=
  if logLevelEqual level belowMinLevel then ops.printString io "BelowMinLevel"
  else if logLevelEqual level debugLevel then ops.printString io "Debug"
  else if logLevelEqual level infoLevel then ops.printString io "Info"
  else if logLevelEqual level warnLevel then ops.printString io "Warn"
  else if logLevelEqual level errorLevel then ops.printString io "Error"
  else if logLevelEqual level aboveMaxLevel then ops.printString io "AboveMaxLevel"
  else ops.printString io ("LogLevel(" ++ ops.int32String level.level ++ ")")

-- UNTRANSLATED
-- Source: base/logging/logging.jl:195-262 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _logmsg_docs = """
--     @debug message  [key=value | value ...]
--     @info  message  [key=value | value ...]
--     @warn  message  [key=value | value ...]
--     @error message  [key=value | value ...]
-- 
--     @logmsg level message [key=value | value ...]
-- 
-- Create a log record with an informational `message`.  For convenience, four
-- logging macros `@debug`, `@info`, `@warn` and `@error` are defined which log at
-- the standard severity levels `Debug`, `Info`, `Warn` and `Error`.  `@logmsg`
-- allows `level` to be set programmatically to any `LogLevel` or custom log level
-- types.
-- 
-- `message` should be an expression which evaluates to a string which is a human
-- readable description of the log event.  By convention, this string will be
-- formatted as markdown when presented.
-- 
-- The optional list of `key=value` pairs supports arbitrary user defined
-- metadata which will be passed through to the logging backend as part of the
-- log record.  If only a `value` expression is supplied, a key representing the
-- expression will be generated using [`Symbol`](@ref). For example, `x` becomes `x=x`,
-- and `foo(10)` becomes `Symbol("foo(10)")=foo(10)`.  For splatting a list of
-- key value pairs, use the normal splatting syntax, `@info "blah" kws...`.
-- 
-- There are some keys which allow automatically generated log data to be
-- overridden:
-- 
--   * `_module=mod` can be used to specify a different originating module from
--     the source location of the message.
--   * `_group=symbol` can be used to override the message group (this is
--     normally derived from the base name of the source file).
--   * `_id=symbol` can be used to override the automatically generated unique
--     message identifier.  This is useful if you need to very closely associate
--     messages generated on different source lines.
--   * `_file=string` and `_line=integer` can be used to override the apparent
--     source location of a log message.
-- 
-- There's also some key value pairs which have conventional meaning:
-- 
--   * `maxlog=integer` should be used as a hint to the backend that the message
--     should be displayed no more than `maxlog` times.
--   * `exception=ex` should be used to transport an exception with a log message,
--     often used with `@error`. An associated backtrace `bt` may be attached
--     using the tuple `exception=(ex,bt)`.
-- 
-- # Examples
-- 
-- ```julia
-- @debug "Verbose debugging information.  Invisible by default"
-- @info  "An informational message"
-- @warn  "Something was odd.  You should pay attention"
-- @error "A non fatal error occurred"
-- 
-- x = 10
-- @info "Some variables attached to the message" x a=42.0
-- 
-- @debug begin
--     sA = sum(A)
--     "sum(A) = \$sA is an expensive operation, evaluated only when `shouldlog` returns true"
-- end
-- 
-- for i=1:10000
--     @info "With the default backend, you will only see (i = \$i) ten times"  maxlog=10
--     @debug "Algorithm1" i progress=i/10000
-- end
-- ```
-- """
-- /Source
-- Reason: This is documentation text shared by the logging macros, not executable method behavior.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:266-272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro _sourceinfo()
--     esc(quote
--         (__module__,
--          __source__.file === nothing ? "?" : String(__source__.file::Symbol),
--          __source__.line)
--     end)
-- end
-- /Source
-- Reason: This macro reads Julia compiler source-location metadata and constructs a Julia tuple at expansion time.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:274-274 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro logmsg(level, exs...) logmsg_code((@_sourceinfo)..., esc(level), exs...) end
-- /Source
-- Reason: This macro expands its arguments into Julia Expr code at compile time.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:275-275 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro debug(exs...) logmsg_code((@_sourceinfo)..., :Debug, exs...) end
-- /Source
-- Reason: This macro expands its arguments into Julia Expr code at compile time.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:276-276 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro  info(exs...) logmsg_code((@_sourceinfo)..., :Info,  exs...) end
-- /Source
-- Reason: This macro expands its arguments into Julia Expr code at compile time.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:277-277 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro  warn(exs...) logmsg_code((@_sourceinfo)..., :Warn,  exs...) end
-- /Source
-- Reason: This macro expands its arguments into Julia Expr code at compile time.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:278-278 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro error(exs...) logmsg_code((@_sourceinfo)..., :Error, exs...) end
-- /Source
-- Reason: This macro expands its arguments into Julia Expr code at compile time.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:281-285 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- @eval @doc $_logmsg_docs :(@logmsg)
-- @eval @doc $_logmsg_docs :(@debug)
-- @eval @doc $_logmsg_docs :(@info)
-- @eval @doc $_logmsg_docs :(@warn)
-- @eval @doc $_logmsg_docs :(@error)
-- /Source
-- Reason: This code attaches shared documentation to macro bindings at compile time.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:287-287 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- _log_record_ids = Set{Symbol}()
-- /Source
-- Reason: This is the process-local mutable registry used by compile-time log identifier generation.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:540-540 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const CURRENT_LOGSTATE = ScopedValue{LogState}()
-- /Source
-- Reason: The task-local scoped-value object identity is an external runtime token.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:619-619 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- global _global_logstate::LogState
-- /Source
-- Reason: This declaration is the mutable global logger state, represented by an explicit state parameter.
-- UNTRANSLATED
-- Source: base/logging/logging.jl:738-738 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- include("logging/ConsoleLogger.jl")
-- /Source
-- Reason: ConsoleLogger is defined in a separate Julia source file and is outside this file model.
/--
Julia source: base/logging/logging.jl:533-536 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct LogState
    min_enabled_level::LogLevel
    logger::AbstractLogger
end
```
-/
structure LogState (Logger : Type) where
  minEnabledLevel : LogLevel
  logger : Logger

abbrev LogM (Error World A : Type) := JuliaLean.base.scopedvalues.M Error World A
def liftExcept {Error World A : Type} (result : Except Error A) : LogM Error World A :=
  fun world =>
    match result with
    | .error error => some (.error (error, world))
    | .ok value => some (.ok (value, world))


structure LogStateOps (Logger Key Level Module Group Id Message File Keywords Error World : Type) where
  loggerOps : LoggerOps (LogM Error World) Logger Level Module Group Id Message File Keywords
  currentKey : Key
  getScoped : Key → LogM Error World (Option (LogState Logger))
  withScoped : {A : Type} → Key → LogState Logger → LogM Error World A → LogM Error World A

structure GlobalLogStateOps (Logger Error World : Type) where
  get : LogM Error World (LogState Logger)
  set : LogState Logger → LogM Error World Unit

structure DebugCache where
  debugString : String
  included : List String
  excluded : List String
  deriving DecidableEq

structure DebugEnvOps (Group Module Error World : Type) where
  getEnv : String → String → LogM Error World String
  splitCommas : String → List String
  startsBang : String → Bool
  dropBang : String → String
  sameStringIdentity : String → String → Bool
  isSymbolGroup : Group → Bool
  symbolName : Group → String
  isModule : Module → Bool
  moduleName : Module → String
  rootModuleName : Module → String

structure LoggingErrorOps
    (Logger Level Module Group Id Message File Backtrace Keywords Error World : Type) where
  catchExceptions : Logger → LogM Error World Bool
  rethrow : Error → LogM Error World Unit
  formatErrorMessage : Module → File → JInt .i64 → LogM Error World Message
  fallbackErrorMessage : Error → LogM Error World Message
  catchBacktrace : LogM Error World Backtrace
  scrubReplBacktrace : Backtrace → LogM Error World Backtrace
  stacktrace : LogM Error World Backtrace
  findLoggingError : Backtrace → Option Nat
  removeThroughLoggingError : Backtrace → Nat → Backtrace
  errorLevel : Level
  errorGroup : Group
  exceptionKeywords : Error → Backtrace → Keywords
  handleMessage : Logger → Level → Message → Module → Group → Id → File → JInt .i64 →
    Keywords → LogM Error World Unit

inductive SimplePrintArg (Module Symbol Any File : Type) where
  | text : String → SimplePrintArg Module Symbol Any File
  | symbol : Symbol → SimplePrintArg Module Symbol Any File
  | moduleValue : Module → SimplePrintArg Module Symbol Any File
  | value : Any → SimplePrintArg Module Symbol Any File
  | int64 : JInt .i64 → SimplePrintArg Module Symbol Any File
  | fileValue : File → SimplePrintArg Module Symbol Any File

structure SimpleLoggerOps
    (Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World : Type) where
  newLock : LogM Error World Lock
  newLimits : LogM Error World Limits
  withLock : {A : Type} → Lock → LogM Error World A → LogM Error World A
  getLimit : Limits → Id → LogM Error World (Option (JInt .i64))
  getOrInsertLimit : Limits → Id → JInt .i64 → LogM Error World (JInt .i64)
  setLimit : Limits → Id → JInt .i64 → LogM Error World Unit
  maxlogSymbol : Symbol
  isMaxlogSymbol : Symbol → Bool
  getKeyword : List (Symbol × Any) → Symbol → Option Any
  isBuiltinInt : Any → Bool
  toInt64 : Any → LogM Error World (JInt .i64)
  newBuffer : LogM Error World Buffer
  makeContext : Buffer → Stream → LogM Error World Context
  stringMessage : Message → LogM Error World String
  convertString : String → LogM Error World String
  chomp : String → String
  splitLines : String → LogM Error World (List String)
  peelLines : List String → LogM Error World (String × List String)
  stringLogLevel : LogLevel → LogM Error World String
  println : Context → List (SimplePrintArg Module Symbol Any File) → LogM Error World Unit
  takeBuffer : Buffer → LogM Error World Bytes
  isopen : Stream → LogM Error World Bool
  stderr : LogM Error World Stream
  write : Stream → Bytes → LogM Error World Unit

structure ClosedStreamOps (Stream Error World : Type) where
  newEmptyIOBuffer : LogM Error World Stream
  close : Stream → LogM Error World Unit

structure GlobalThresholdOps (Error World : Type) where
  atomicStore : JInt .i32 → LogM Error World Unit

structure LogmsgShimOps (InputLevel Message Module Group Id File Any Error World : Type) where
  convertLevel : InputLevel → LogM Error World LogLevel
  fileToString : File → LogM Error World String
  emit : LogLevel → Message → Module → Group → Id → (Unit → LogM Error World String) →
    JInt .i64 → List (Any × Any) → LogM Error World Unit
  boundsError : Error

/--
Julia source: base/logging/logging.jl:314-314 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
default_group(file) = Symbol(splitext(basename(file))[1])
```
-/
structure DefaultGroupOps (File Symbol : Type) where
  basenameSplitExtStem : File → String
  symbol : String → Symbol

def defaultGroup {File Symbol : Type} (ops : DefaultGroupOps File Symbol) (file : File) : Symbol :=
  ops.symbol (ops.basenameSplitExtStem file)

structure SimpleExprOps (Leaf : Type) where
  isString : Leaf → Bool
  isNumber : Leaf → Bool
  isChar : Leaf → Bool

/--
Julia source: base/logging/logging.jl:316-327 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function issimple(@nospecialize val)
    val isa String && return true
    val isa Symbol && return true
    val isa QuoteNode && return true
    val isa Number && return true
    val isa Char && return true
    if val isa Expr
        val.head === :quote && issimple(val.args[1]) && return true
        val.head === :inert && return true
    end
    return false
end
```
-/
def isSimpleExpr {Leaf : Type} (ops : SimpleExprOps Leaf) :
    JuliaLean.base.expr.Value Leaf → JuliaLean.base.expr.ExprResult Bool
  | .leaf value => .ok (ops.isString value || ops.isNumber value || ops.isChar value)
  | .symbol _ => .ok true
  | .quoteNode _ => .ok true
  | .expr head args =>
      if head == "quote" then
        match args with
        | [] => .error (.jl .boundsError)
        | argument :: _ => isSimpleExpr ops argument
      else if head == "inert" then .ok true else .ok false
  | _ => .ok false

/--
Julia source: base/logging/logging.jl:328-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function issimplekw(@nospecialize val)
    if val isa Expr
        if val.head === :kw
            val = val.args[2]
            if val isa Expr && val.head === :escape
                issimple(val.args[1]) && return true
            end
        end
    end
    return false
end
```
-/
def isSimpleKw {Leaf : Type} (ops : SimpleExprOps Leaf) :
    JuliaLean.base.expr.Value Leaf → JuliaLean.base.expr.ExprResult Bool
  | .expr head args => do
      if head != "kw" then return false
      match ← JuliaLean.base.expr.argAt args 2 with
      | .expr escapedHead escapedArgs =>
          if escapedHead != "escape" then return false
          isSimpleExpr ops (← JuliaLean.base.expr.argAt escapedArgs 1)
      | _ => pure false
  | _ => .ok false

def addUniqueString (value : String) (values : List String) : List String :=
  if values.contains value then values else values ++ [value]

def parseDebugGroups {Group Module Error World : Type} (ops : DebugEnvOps Group Module Error World) :
    List String → List String → List String → List String × List String
  | [], included, excluded => (included, excluded)
  | entry :: rest, included, excluded =>
      if entry.isEmpty then parseDebugGroups ops rest included excluded
      else if ops.startsBang entry then
        let name := ops.dropBang entry
        if name.isEmpty then parseDebugGroups ops rest included excluded
        else parseDebugGroups ops rest included (addUniqueString name excluded)
      else parseDebugGroups ops rest (addUniqueString entry included) excluded

/--
Julia source: base/logging/logging.jl:569-616 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
let _debug_groups_include::Vector{Symbol} = Symbol[],
    _debug_groups_exclude::Vector{Symbol} = Symbol[],
    _debug_str::String = ""
global Base.@constprop :none function env_override_minlevel(group, _module)
    debug = get(ENV, "JULIA_DEBUG", "")
    if !(debug === _debug_str)
        _debug_str = debug
        empty!(_debug_groups_include)
        empty!(_debug_groups_exclude)
        for g in split(debug, ',')
            if !isempty(g)
                if startswith(g, "!")
                    if !isempty(g[2:end])
                        push!(_debug_groups_exclude, Symbol(g[2:end]))
                    end
                else
                    push!(_debug_groups_include, Symbol(g))
                end
            end
        end
        unique!(_debug_groups_include)
        unique!(_debug_groups_exclude)
    end

    if !(:all in _debug_groups_exclude) && (:all in _debug_groups_include || !isempty(_debug_groups_exclude))
        if isempty(_debug_groups_exclude)
            return true
        elseif isa(group, Symbol) && group in _debug_groups_exclude
            return false
        elseif isa(_module, Module) && (nameof(_module) in _debug_groups_exclude || nameof(Base.moduleroot(_module)) in _debug_groups_exclude)
            return false
        else
            return true
        end
    else
        if isempty(_debug_groups_include)
            return false
        elseif isa(group, Symbol) && group in _debug_groups_include
            return true
        elseif isa(_module, Module) && (nameof(_module) in _debug_groups_include || nameof(Base.moduleroot(_module)) in _debug_groups_include)
            return true
        else
            return false
        end
    end
    return false
end
end
```
-/
def envOverrideMinlevel {Group Module Error World : Type}
    (ops : DebugEnvOps Group Module Error World) (cache : DebugCache)
    (group : Group) (module : Module) : LogM Error World (Bool × DebugCache) := do
  let debug ← ops.getEnv "JULIA_DEBUG" ""
  let cache ←
    if ops.sameStringIdentity debug cache.debugString then pure cache
    else
      let (included, excluded) := parseDebugGroups ops (ops.splitCommas debug) [] []
      pure { debugString := debug, included, excluded }
  let excludesAll := cache.excluded.contains "all"
  let includesAll := cache.included.contains "all"
  if !excludesAll && (includesAll || !cache.excluded.isEmpty) then
    if cache.excluded.isEmpty then pure (true, cache)
    else if ops.isSymbolGroup group && cache.excluded.contains (ops.symbolName group) then
      pure (false, cache)
    else if ops.isModule module &&
        (cache.excluded.contains (ops.moduleName module) ||
         cache.excluded.contains (ops.rootModuleName module)) then
      pure (false, cache)
    else pure (true, cache)
  else if cache.included.isEmpty then pure (false, cache)
  else if ops.isSymbolGroup group && cache.included.contains (ops.symbolName group) then
    pure (true, cache)
  else if ops.isModule module &&
      (cache.included.contains (ops.moduleName module) ||
       cache.included.contains (ops.rootModuleName module)) then
    pure (true, cache)
  else pure (false, cache)

/--
Julia source: base/logging/logging.jl:538-538 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
LogState(logger) = LogState(LogLevel(_invoked_min_enabled_level(logger)), logger)
```
-/
def makeLogState {Logger Key Level Module Group Id Message File Keywords Error World : Type}
    (ops : LogStateOps Logger Key Level Module Group Id Message File Keywords Error World)
    (logger : Logger) : LogM Error World (LogState Logger) := do
  let minEnabledLevel ← invokedMinEnabledLevel ops.loggerOps logger
  pure ⟨minEnabledLevel, logger⟩

/--
Julia source: base/logging/logging.jl:542-545 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function current_logstate()
    maybe = @inline Base.ScopedValues.get(CURRENT_LOGSTATE)
    return something(maybe, _global_logstate)::LogState
end
```
-/
def currentLogstate {Logger Key Level Module Group Id Message File Keywords Error World : Type}
    (ops : LogStateOps Logger Key Level Module Group Id Message File Keywords Error World)
    (global : LogState Logger) : LogM Error World (LogState Logger) := do
  match ← ops.getScoped ops.currentKey with
  | some state => pure state
  | none => pure global

/--
Julia source: base/logging/logging.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const _min_enabled_level = Threads.Atomic{Int32}(Debug)
```
-/
def initialMinimumEnabledLevel : JInt .i32 := debugLevel.level

/--
Julia source: base/logging/logging.jl:498-519 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function logging_error(logger, level, _module, group, id,
                                 filepath, line, @nospecialize(err), real::Bool)
    @nospecialize
    if !_invoked_catch_exceptions(logger)
        real ? rethrow(err) : throw(err)
    end
    msg = try
              "Exception while generating log record in module $_module at $filepath:$line"
          catch ex
              LazyString("Exception handling log message: ", ex)
          end
    bt = Base.scrub_repl_backtrace(real ? catch_backtrace() : stacktrace())
    if !real
        # drop the frames of the logging machinery itself
        i = findfirst(fr -> fr.func === :logging_error, bt)
        i === nothing || deleteat!(bt, 1:i)
    end
    handle_message(
        logger, Error, msg, _module, :logevent_error, id, filepath, line;
        exception=(err,bt))
    nothing
end
```
-/
def loggingError
    {Logger Level Module Group Id Message File Backtrace Keywords Error World : Type}
    (ops : LoggingErrorOps Logger Level Module Group Id Message File Backtrace Keywords Error World)
    (logger : Logger) (module : Module) (group : Group) (id : Id) (filepath : File)
    (line : JInt .i64) (error : Error) (real : Bool) : LogM Error World Unit := do
  if !(← ops.catchExceptions logger) then
    if real then ops.rethrow error else throw error
  let message ←
    try ops.formatErrorMessage module filepath line
    catch exception => ops.fallbackErrorMessage exception
  let backtrace ←
    if real then ops.scrubReplBacktrace (← ops.catchBacktrace)
    else
      let stack := ← ops.stacktrace
      match ops.findLoggingError stack with
      | none => pure stack
      | some index => pure (ops.removeThroughLoggingError stack index)
  ops.handleMessage logger ops.errorLevel message module ops.errorGroup id filepath line
    (ops.exceptionKeywords error backtrace)

/-- The logger selection expression used before constructing a log record. -/
def logLevelAtLeast (level minimum : LogLevel) : Bool :=
  decide (minimum.level.val ≤ level.level.val)

/--
Julia source: base/logging/logging.jl:341-348 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline Base.@constprop :none function current_logger_for_env(std_level::LogLevel, group, _module)
    logstate = @inline current_logstate()
    if std_level >= logstate.min_enabled_level || env_override_minlevel(group, _module)
        return logstate.logger
    end
    return nothing
end

```
-/
def currentLoggerForEnv
    {Logger Key Level Module Group Id Message File Keywords Error World : Type}
    (stateOps : LogStateOps Logger Key Level Module Group Id Message File Keywords Error World)
    (global : LogState Logger) (debugOps : DebugEnvOps Group Module Error World)
    (cache : DebugCache) (stdLevel : LogLevel) (group : Group) (module : Module) :
    LogM Error World (Option Logger × DebugCache) := do
  let state ← currentLogstate stateOps global
  if logLevelAtLeast stdLevel state.minEnabledLevel then
    pure (some state.logger, cache)
  else
    let (enabled, cache) ← envOverrideMinlevel debugOps cache group module
    pure (if enabled then some state.logger else none, cache)

/--
Julia source: base/logging/logging.jl:431-441 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
@noinline function handle_message_nothrow(logger, level, msg, _module, group, id, file, line; kwargs...)
    @nospecialize
    try
        @invokelatest handle_message(
            logger, level, msg, _module, group, id, file, line;
            kwargs...)

    catch err
        @invokelatest logging_error(logger, level, _module, group, id, file, line, err, true)
    end
end
```
-/
def handleMessageNothrow
    {Logger Level Module Group Id Message File Backtrace Keywords Error World : Type}
    (ops : LoggingErrorOps Logger Level Module Group Id Message File Backtrace Keywords Error World)
    (logger : Logger) (level : Level) (message : Message) (module : Module) (group : Group)
    (id : Id) (filepath : File) (line : JInt .i64) (keywords : Keywords) :
    LogM Error World Unit :=
  tryCatch (ops.handleMessage logger level message module group id filepath line keywords)
    (fun error => loggingError ops logger module group id filepath line error true)

def pairFlatArguments {Any Error : Type} (boundsError : Error) :
    List Any → Except Error (List (Any × Any))
  | [] => .ok []
  | key :: value :: rest => do
      let pairs ← pairFlatArguments boundsError rest
      pure ((key, value) :: pairs)
  | _ :: [] => .error boundsError

/--
Julia source: base/logging/logging.jl:523-530 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function logmsg_shim(level, message, _module, group, id, file, line, kwargs)
    @nospecialize
    real_kws = Any[(kwargs[i], kwargs[i+1]) for i in 1:2:length(kwargs)]
    @logmsg(convert(LogLevel, level), message,
            _module=_module, _id=id, _group=group,
            _file=String(file), _line=line, real_kws...)
    nothing
end
```
-/
def logmsgShim
    {InputLevel Message Module Group Id File Any Error World : Type}
    (ops : LogmsgShimOps InputLevel Message Module Group Id File Any Error World)
    (level : InputLevel) (message : Message) (module : Module) (group : Group) (id : Id)
    (file : File) (line : JInt .i64) (kwargs : List Any) : LogM Error World Unit := do
  let pairs ← liftExcept (pairFlatArguments ops.boundsError kwargs)
  let level ← ops.convertLevel level
  ops.emit level message module group id (fun _ => ops.fileToString file) line pairs

/--
Julia source: base/logging/logging.jl:547-547 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
with_logstate(f::Function, logstate) = @with(CURRENT_LOGSTATE => logstate, f())
```
-/
def withLogstate
    {Logger Key Level Module Group Id Message File Keywords Error World A : Type}
    (ops : LogStateOps Logger Key Level Module Group Id Message File Keywords Error World)
    (f : LogM Error World A) (logstate : LogState Logger) : LogM Error World A :=
  ops.withScoped ops.currentKey logstate f

/--
Julia source: base/logging/logging.jl:565-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function disable_logging(level::LogLevel)
    @atomic _min_enabled_level[] = level + 1
end
```
-/
def disableLogging {Integer Error World : Type}
    (levelOps : LogLevelIntegerOps Integer Error) (atomic : GlobalThresholdOps Error World)
    (one : Integer) (level : LogLevel) : LogM Error World Unit := do
  let next ← liftExcept (addLogLevel levelOps level one)
  atomic.atomicStore next.level

/--
Julia source: base/logging/logging.jl:631-631 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
global_logger() = _global_logstate.logger
```
-/
def globalLoggerGet {Logger Error World : Type}
    (ops : GlobalLogStateOps Logger Error World) : LogM Error World Logger := do
  pure (← ops.get).logger

/--
Julia source: base/logging/logging.jl:633-637 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function global_logger(logger::AbstractLogger)
    prev = _global_logstate.logger
    global _global_logstate = LogState(logger)
    prev
end
```
-/
def globalLoggerSet
    {Logger Key Level Module Group Id Message File Keywords Error World : Type}
    (stateOps : LogStateOps Logger Key Level Module Group Id Message File Keywords Error World)
    (globalOps : GlobalLogStateOps Logger Error World) (logger : Logger) :
    LogM Error World Logger := do
  let previous ← globalOps.get
  let next ← makeLogState stateOps logger
  globalOps.set next
  pure previous.logger

/--
Julia source: base/logging/logging.jl:657-659 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function with_logger(@nospecialize(f::Function), logger::AbstractLogger)
    with_logstate(f, LogState(logger))
end
```
-/
def withLogger
    {Logger Key Level Module Group Id Message File Keywords Error World A : Type}
    (stateOps : LogStateOps Logger Key Level Module Group Id Message File Keywords Error World)
    (f : LogM Error World A) (logger : Logger) : LogM Error World A := do
  let logstate ← makeLogState stateOps logger
  withLogstate stateOps f logstate

/--
Julia source: base/logging/logging.jl:667-667 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
current_logger() = current_logstate().logger
```
-/
def currentLogger
    {Logger Key Level Module Group Id Message File Keywords Error World : Type}
    (ops : LogStateOps Logger Key Level Module Group Id Message File Keywords Error World)
    (global : LogState Logger) : LogM Error World Logger := do
  pure (← currentLogstate ops global).logger

/--
Julia source: base/logging/logging.jl:669-670 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const closed_stream = IOBuffer(UInt8[])
close(closed_stream)
```
-/
def makeClosedStream {Stream Error World : Type} (ops : ClosedStreamOps Stream Error World) :
    LogM Error World Stream := do
  let stream ← ops.newEmptyIOBuffer
  ops.close stream
  pure stream

/--
Julia source: base/logging/logging.jl:684-689 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct SimpleLogger <: AbstractLogger
    stream::IO
    lock::ReentrantLock
    min_level::LogLevel
    message_limits::Dict{Any,Int}
end
```
-/
structure SimpleLogger (Stream Lock Limits : Type) where
  stream : Stream
  lock : Lock
  minLevel : LogLevel
  messageLimits : Limits

/--
Julia source: base/logging/logging.jl:690-690 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SimpleLogger(stream::IO, level=Info) = SimpleLogger(stream, ReentrantLock(), level, Dict{Any,Int}())
```
-/
def simpleLogger
    {Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World : Type}
    (ops : SimpleLoggerOps Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World)
    (stream : Stream) (level : LogLevel := infoLevel) :
    LogM Error World (SimpleLogger Stream Lock Limits) := do
  let lock ← ops.newLock
  let messageLimits ← ops.newLimits
  pure ⟨stream, lock, level, messageLimits⟩

/--
Julia source: base/logging/logging.jl:691-691 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
SimpleLogger(level=Info) = SimpleLogger(closed_stream, level)
```
-/
def simpleLoggerDefaultStream
    {Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World : Type}
    (ops : SimpleLoggerOps Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World)
    (closedStream : Stream) (level : LogLevel := infoLevel) :
    LogM Error World (SimpleLogger Stream Lock Limits) :=
  simpleLogger ops closedStream level

/--
Julia source: base/logging/logging.jl:693-694 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
shouldlog(logger::SimpleLogger, level, _module, group, id) =
    @lock logger.lock get(logger.message_limits, id, 1) > 0
```
-/
def simpleLoggerShouldlog
    {Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World Level Group : Type}
    (ops : SimpleLoggerOps Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World)
    (logger : SimpleLogger Stream Lock Limits) (_level : Level) (_module : Module)
    (_group : Group) (id : Id) : LogM Error World Bool :=
  ops.withLock logger.lock do
    let limit ← ops.getLimit logger.messageLimits id
    pure (decide (0 < (limit.getD (JInt.wrap .i64 1)).val))

/--
Julia source: base/logging/logging.jl:696-696 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min_enabled_level(logger::SimpleLogger) = logger.min_level
```
-/
def simpleLoggerMinEnabledLevel {Stream Lock Limits : Type}
    (logger : SimpleLogger Stream Lock Limits) : LogLevel := logger.minLevel

/--
Julia source: base/logging/logging.jl:698-698 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
catch_exceptions(logger::SimpleLogger) = false
```
-/
def simpleLoggerCatchExceptions {Stream Lock Limits : Type}
    (_logger : SimpleLogger Stream Lock Limits) : Bool := false

def printSimpleLoggerLines
    {Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World : Type}
    (ops : SimpleLoggerOps Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World)
    (context : Context) : List String → LogM Error World Unit
  | [] => pure ()
  | line :: rest => do
      ops.println context [.text "│ ", .text line]
      printSimpleLoggerLines ops context rest

def printSimpleLoggerKeywords
    {Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World : Type}
    (ops : SimpleLoggerOps Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World)
    (context : Context) : List (Symbol × Any) → LogM Error World Unit
  | [] => pure ()
  | (key, value) :: rest => do
      if !ops.isMaxlogSymbol key then
        ops.println context [.text "│   ", .symbol key, .text " = ", .value value]
      printSimpleLoggerKeywords ops context rest

/--
Julia source: base/logging/logging.jl:700-734 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function handle_message(logger::SimpleLogger, level::LogLevel, message, _module, group, id,
                        filepath, line; kwargs...)
    @nospecialize
    maxlog = get(kwargs, :maxlog, nothing)
    if maxlog isa Core.BuiltinInts
        @lock logger.lock begin
            remaining = get!(logger.message_limits, id, Int(maxlog)::Int)
            remaining == 0 && return
            logger.message_limits[id] = remaining - 1
        end
    end
    buf = IOBuffer()
    stream::IO = logger.stream
    iob = IOContext(buf, stream)
    levelstr = level == Warn ? "Warning" : string(level)
    msglines = eachsplit(chomp(convert(String, string(message))::String), '\n')
    msg1, rest = Iterators.peel(msglines)
    println(iob, "┌ ", levelstr, ": ", msg1)
    for msg in rest
        println(iob, "│ ", msg)
    end
    for (key, val) in kwargs
        key === :maxlog && continue
        println(iob, "│   ", key, " = ", val)
    end
    println(iob, "└ @ ", _module, " ", filepath, ":", line)
    b = take!(buf)
    @lock logger.lock begin
        if !(isopen(stream)::Bool)
            stream = stderr
        end
        write(stream, b)
    end
    nothing
end
```
-/
def simpleLoggerHandleMessage
    {Stream Lock Limits Id Symbol Any Message Module Group File Buffer Context Bytes Error World : Type}
    (ops : SimpleLoggerOps Stream Lock Limits Id Symbol Any Message Module File Buffer Context Bytes Error World)
    (logger : SimpleLogger Stream Lock Limits) (level : LogLevel) (message : Message)
    (module : Module) (_group : Group) (id : Id) (filepath : File) (line : JInt .i64)
    (kwargs : List (Symbol × Any)) : LogM Error World Unit := do
  let shouldSkip ← match ops.getKeyword kwargs ops.maxlogSymbol with
    | some maxlog =>
        if ops.isBuiltinInt maxlog then
          ops.withLock logger.lock do
            let default ← ops.toInt64 maxlog
            let remaining ← ops.getOrInsertLimit logger.messageLimits id default
            if remaining.val = 0 then pure true
            else do
              ops.setLimit logger.messageLimits id (JInt.wrap .i64 (remaining.val - 1))
              pure false
        else pure false
    | none => pure false
  if shouldSkip then return ()
  let buffer ← ops.newBuffer
  let context ← ops.makeContext buffer logger.stream
  let levelString ← if logLevelEqual level warnLevel then pure "Warning"
    else ops.stringLogLevel level
  let rawMessage ← ops.stringMessage message
  let stringMessage ← ops.convertString rawMessage
  let lines ← ops.splitLines (ops.chomp stringMessage)
  let (firstLine, restLines) ← ops.peelLines lines
  ops.println context [.text "┌ ", .text levelString, .text ": ", .text firstLine]
  printSimpleLoggerLines ops context restLines
  printSimpleLoggerKeywords ops context kwargs
  ops.println context [
    .text "└ @ ", .moduleValue module, .text " ", .fileValue filepath,
    .text ":", .int64 line
  ]
  let bytes ← ops.takeBuffer buffer
  let stream ← if ← ops.isopen logger.stream then pure logger.stream else ops.stderr
  ops.write stream bytes

/--
Julia source: base/logging/logging.jl:736-736 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_global_logstate = LogState(SimpleLogger())
```
-/
def initializeGlobalLogState {Logger Error World : Type}
    (newSimpleLogger : LogM Error World Logger)
    (makeLogState : Logger → LogM Error World (LogState Logger)) :
    LogM Error World (LogState Logger) := do
  makeLogState (← newSimpleLogger)

structure LogRun (A : Type) where
  result : Option (Except JuliaLean.base.expr.ExprError A)

instance : Monad LogRun where
  pure value := ⟨some (.ok value)⟩
  bind run next := ⟨match run.result with
    | none => none
    | some (.error error) => some (.error error)
    | some (.ok value) => (next value).result⟩

def logRunFromExcept {A : Type}
    (result : Except JuliaLean.base.expr.ExprError A) : LogRun A :=
  ⟨some result⟩

structure LogRecordIdOps (L : Type) where
  isNothingModule : JuliaLean.base.expr.Value L → Bool
  fullName : JuliaLean.base.expr.Value L → JuliaLean.base.expr.ExprResult (List String)
  identifierText : String → JuliaLean.base.expr.Value L → JuliaLean.base.expr.Value L →
    List (JuliaLean.base.expr.Value L) → JuliaLean.base.expr.ExprResult String
  hashUInt32 : String → JInt .u32
  formatHash : JInt .u32 → String

/--
Julia source: base/logging/logging.jl:300-311 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    while true
        id = Symbol(modname, '_', string(h, base = 16, pad = 8))
        # _log_record_ids is a registry of log record ids for use during
        # compilation, to ensure uniqueness of ids.  Note that this state will
        # only persist during module compilation so it will be empty when a
        # precompiled module is loaded.
        if !(id in _log_record_ids)
            push!(_log_record_ids, id)
            return id
        end
        h +%= 1
    end
```
-/
def logRecordIdStep {L : Type} (ops : LogRecordIdOps L) (modname : String)
    (state : JInt .u32 × List String) :
    Except JuliaLean.base.expr.ExprError (Sum (String × List String) (JInt .u32 × List String)) :=
  let (hash, identifiers) := state
  let id := modname ++ "_" ++ ops.formatHash hash
  if identifiers.contains id then
    .ok (.inr (JInt.wrap .u32 (hash.val + 1), identifiers))
  else
    .ok (.inl (id, id :: identifiers))
/--
Julia source: base/logging/logging.jl:294-312 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function log_record_id(_module, level, message, log_kws)
    @nospecialize
    modname = _module === nothing ?  "" : join(fullname(_module), "_")
    # Use an arbitrarily chosen eight hex digits here. TODO: Figure out how to
    # make the id exactly the same on 32 and 64 bit systems.
    h = UInt32(hash(string(modname, level, message, log_kws)::String) & 0xFFFFFFFF)
    while true
        id = Symbol(modname, '_', string(h, base = 16, pad = 8))
        # _log_record_ids is a registry of log record ids for use during
        # compilation, to ensure uniqueness of ids.  Note that this state will
        # only persist during module compilation so it will be empty when a
        # precompiled module is loaded.
        if !(id in _log_record_ids)
            push!(_log_record_ids, id)
            return id
        end
        h +%= 1
    end
end
```
-/
def logRecordId {L : Type} (ops : LogRecordIdOps L) (identifiers : List String)
    (module level message : JuliaLean.base.expr.Value L)
    (logKeywords : List (JuliaLean.base.expr.Value L)) : LogRun (String × List String) :=
  let modnameResult :=
    if ops.isNothingModule module then .ok ""
    else (ops.fullName module).map (String.intercalate "_")
  match modnameResult with
  | .error error => logRunFromExcept (.error error)
  | .ok modname =>
      match ops.identifierText modname level message logKeywords with
      | .error error => logRunFromExcept (.error error)
      | .ok text =>
          ⟨JuliaLean.base.reduce.whileLoop (logRecordIdStep ops modname)
            (ops.hashUInt32 text, identifiers)⟩

structure LogDefaultGroupOps (L File : Type) where
  base : L
  hasBaseBasename : Bool
  isString : JuliaLean.base.expr.Value L → Bool
  asFile : JuliaLean.base.expr.Value L → JuliaLean.base.expr.ExprResult File
  groupOps : DefaultGroupOps File String
  newSymbolRef : Unit → JuliaLean.base.expr.Value L
  emptyString : L

/--
Julia source: base/logging/logging.jl:486-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function default_group_code(file)
    @nospecialize
    if file isa String && isdefined(Base, :basename)
        QuoteNode(default_group(file))  # precompute if we can
    else
        ref = Ref{Symbol}()  # memoized run-time execution
        :(isassigned($ref) ? $ref[] : $ref[] = default_group(something($file, ""))::Symbol)
    end
end
```
-/
def defaultGroupCode {L File : Type} (ops : LogDefaultGroupOps L File)
    (file : JuliaLean.base.expr.Value L) : JuliaLean.base.expr.ExprResult (JuliaLean.base.expr.Value L) :=
  if ops.isString file && ops.hasBaseBasename then do
    let file ← ops.asFile file
    pure (.quoteNode (.symbol (defaultGroup ops.groupOps file)))
  else
    let ref := ops.newSymbolRef ()
    let refValue := JuliaLean.base.expr.Value.expr "ref" [ref]
    let assigned := JuliaLean.base.expr.Value.expr "call"
      [.globalRef ops.base "isassigned", ref]
    let path := JuliaLean.base.expr.Value.expr "call"
      [.globalRef ops.base "something", file, .leaf ops.emptyString]
    let group := JuliaLean.base.expr.Value.expr "call"
      [.globalRef ops.base "default_group", path]
    let typedGroup := JuliaLean.base.expr.Value.expr "::"
      [group, .globalRef ops.base "Symbol"]
    pure (.expr "if" [assigned, refValue, .expr "=" [refValue, typedGroup]])

structure LogData (L : Type) where
  originModule : JuliaLean.base.expr.Value L
  group : JuliaLean.base.expr.Value L
  id : JuliaLean.base.expr.Value L
  file : JuliaLean.base.expr.Value L
  line : JuliaLean.base.expr.Value L
  kwargs : List (JuliaLean.base.expr.Value L)

structure LogMsgState (L : Type) where
  originModule : JuliaLean.base.expr.Value L
  group : Option (JuliaLean.base.expr.Value L)
  id : Option (JuliaLean.base.expr.Value L)
  file : JuliaLean.base.expr.Value L
  line : JuliaLean.base.expr.Value L
  kwargs : List (JuliaLean.base.expr.Value L)

/--
Julia source: base/logging/logging.jl:443-484 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function process_logmsg_exs(_orig_module, _file, _line, level, message, exs...)
    @nospecialize
    local _group, _id
    _module = _orig_module
    kwargs = Any[]
    for ex in exs
        if ex isa Expr && ex.head === :(=)
            k, v = ex.args
            if !(k isa Symbol)
                k = Symbol(k)
            end

            # Recognize several special keyword arguments
            if k === :_group
                _group = esc(v)
            elseif k === :_id
                _id = esc(v)
            elseif k === :_module
                _module = esc(v)
            elseif k === :_file
                _file = esc(v)
            elseif k === :_line
                _line = esc(v)
            else
                # Copy across key value pairs for structured log records
                push!(kwargs, Expr(:kw, k, esc(v)))
            end
        elseif ex isa Expr && ex.head === :... # Keyword splatting
            push!(kwargs, esc(ex))
        else # Positional arguments - will be converted to key value pairs automatically.
            push!(kwargs, Expr(:kw, Symbol(ex), esc(ex)))
        end
    end

    if !@isdefined(_group)
        _group = default_group_code(_file)
    end
    if !@isdefined(_id)
        _id = Expr(:quote, log_record_id(_orig_module, level, message, exs))
    end
    return (;_module, _group, _id, _file, _line, kwargs)
end
```
-/
def processLogmsgExs {L : Type}
    (symbolFrom : JuliaLean.base.expr.Value L → JuliaLean.base.expr.ExprResult String)
    (assignmentArgs : List (JuliaLean.base.expr.Value L) →
      JuliaLean.base.expr.ExprResult (JuliaLean.base.expr.Value L × JuliaLean.base.expr.Value L))
    (defaultGroup : JuliaLean.base.expr.Value L → JuliaLean.base.expr.ExprResult (JuliaLean.base.expr.Value L))
    (makeId : List String → JuliaLean.base.expr.Value L → JuliaLean.base.expr.Value L →
      JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
      LogRun (String × List String))
    (identifiers : List String) (originalModule file line level message : JuliaLean.base.expr.Value L)
    (exs : List (JuliaLean.base.expr.Value L)) : LogRun (LogData L × List String) := do
  let initial : LogMsgState L :=
    ⟨originalModule, none, none, file, line, []⟩
  let state ← exs.foldlM (fun state ex => do
    match ex with
    | .expr "=" args =>
        let (key, value) ← logRunFromExcept (assignmentArgs args)
        let keyName ← match key with
          | .symbol name => pure name
          | _ => logRunFromExcept (symbolFrom key)
        let escaped := JuliaLean.base.expr.esc value
        match keyName with
        | "_group" => pure { state with group := some escaped }
        | "_id" => pure { state with id := some escaped }
        | "_module" => pure { state with originModule := escaped }
        | "_file" => pure { state with file := escaped }
        | "_line" => pure { state with line := escaped }
        | _ => pure { state with kwargs := state.kwargs ++ [.expr "kw" [.symbol keyName, escaped]] }
    | .expr "..." _ =>
        pure { state with kwargs := state.kwargs ++ [JuliaLean.base.expr.esc ex] }
    | _ => do
        let key ← logRunFromExcept (symbolFrom ex)
        pure { state with kwargs := state.kwargs ++
          [.expr "kw" [.symbol key, JuliaLean.base.expr.esc ex]] }
    ) initial
  let group ← match state.group with
    | some group => pure group
    | none => logRunFromExcept (defaultGroup state.file)
  let (id, identifiers) ← match state.id with
    | some id => pure (id, identifiers)
    | none => do
        let (id, identifiers) ← makeId identifiers originalModule level message exs
        pure (.expr "quote" [.symbol id], identifiers)
  pure (⟨state.originModule, group, id, state.file, state.line, state.kwargs⟩, identifiers)
abbrev ProcessLogmsgExsFn (L : Type) :=
  List String → JuliaLean.base.expr.Value L → JuliaLean.base.expr.Value L →
  JuliaLean.base.expr.Value L → JuliaLean.base.expr.Value L →
  JuliaLean.base.expr.Value L → List (JuliaLean.base.expr.Value L) →
  LogRun (LogData L × List String)

structure LogmsgCodeOps (L : Type) where
  leaves : JuliaLean.base.expr.LeafOps L
  core : L
  isSimple : JuliaLean.base.expr.Value L → Bool
  isSimpleKeyword : JuliaLean.base.expr.Value L → Bool
  assertDefined : String → JuliaLean.base.expr.Value L → JuliaLean.base.expr.Value L

private def logAst {L : Type} (head : String) (args : List (JuliaLean.base.expr.Value L)) :
    JuliaLean.base.expr.Value L :=
  .expr head args

private def logAstCall {L : Type} (fn : JuliaLean.base.expr.Value L)
    (args : List (JuliaLean.base.expr.Value L)) : JuliaLean.base.expr.Value L :=
  logAst "call" (fn :: args)

private def logAstCallName {L : Type} (name : String)
    (args : List (JuliaLean.base.expr.Value L)) : JuliaLean.base.expr.Value L :=
  logAstCall (.symbol name) args

private def logAstAssign {L : Type} (name : String) (value : JuliaLean.base.expr.Value L) :
    JuliaLean.base.expr.Value L :=
  logAst "=" [.symbol name, value]

private def logAstBlock {L : Type} (body : List (JuliaLean.base.expr.Value L)) :
    JuliaLean.base.expr.Value L :=
  logAst "block" body

private def logUndefVarError {L : Type} (name : JuliaLean.base.expr.Value L) :
    JuliaLean.base.expr.Value L :=
  logAstCall (logAst "core" [.symbol "UndefVarError"])
    [.quoteNode name, .quoteNode (.symbol "local")]

private def logKeywordMissingCheck {L : Type}
    (kwarg check : JuliaLean.base.expr.Value L) : LogRun (JuliaLean.base.expr.Value L) := do
  let (_, kwargArgs) ← logRunFromExcept (JuliaLean.base.expr.asExpr kwarg)
  let value ← logRunFromExcept (JuliaLean.base.expr.argAt kwargArgs 2)
  let (_, valueArgs) ← logRunFromExcept (JuliaLean.base.expr.asExpr value)
  let varName ← logRunFromExcept (JuliaLean.base.expr.argAt valueArgs 1)
  match varName with
  | .symbol _ =>
      pure (logAst "if" [
        logAst "isdefined" [value],
        check,
        logUndefVarError varName
      ])
  | _ => pure check

/--
Julia source: base/logging/logging.jl:350-429 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function logmsg_code(_module, file, line, level, message, exs...)
    @nospecialize
    log_data = process_logmsg_exs(_module, file, line, level, message, exs...)
    if !isa(message, Symbol) && issimple(message) && isempty(log_data.kwargs)
        logrecord = quote
            msg = $(message)
            kwargs = (;)
            true
        end
    elseif issimple(message) && all(issimplekw, log_data.kwargs)
        # if message and kwargs are just values and variables, we can avoid try/catch
        # complexity by adding the code for testing the UndefVarError by hand
        checkerrors = nothing
        for kwarg in reverse(log_data.kwargs)
            if isa(kwarg.args[2].args[1], Symbol)
                checkerrors = Expr(:if, Expr(:isdefined, kwarg.args[2]), checkerrors, Expr(:call, Expr(:core, :UndefVarError), QuoteNode(kwarg.args[2].args[1]), QuoteNode(:local)))
            end
        end
        if isa(message, Symbol)
            message = esc(message)
            checkerrors = Expr(:if, Expr(:isdefined, message), checkerrors, Expr(:call, Expr(:core, :UndefVarError), QuoteNode(message.args[1]), QuoteNode(:local)))
        end
        logrecord = quote
            let err = $checkerrors
                if err === nothing
                    msg = $(message)
                    kwargs = (;$(log_data.kwargs...))
                    true
                else
                    @invokelatest $(logging_error)(logger, level, _module, group, id, file, line, err, false)
                    false
                end
            end
        end
    else
        logrecord = quote
            try
                msg = $(esc(message))
                kwargs = (;$(log_data.kwargs...))
                true
            catch err
                @invokelatest $(logging_error)(logger, level, _module, group, id, file, line, err, true)
                false
            end
        end
    end
    return quote
        let
            level = $level
            # simplify std_level code emitted, if we know it is one of our global constants
            std_level = $(level isa Symbol ? :level : :(level isa $LogLevel ? level : convert($LogLevel, level)::$LogLevel))
            if std_level.level >= $(_min_enabled_level)[]
                group = $(log_data._group)
                _module = $(log_data._module)
                logger = $(current_logger_for_env)(std_level, group, _module)
                if !(logger === nothing)
                    id = $(log_data._id)
                    # Second chance at an early bail-out (before computing the message),
                    # based on arbitrary logger-specific logic.
                    if invokelatest($shouldlog, logger, level, _module, group, id)
                        file = $(log_data._file)
                        if file isa String
                            file = Base.fixup_stdlib_path(file)
                        end
                        line = $(log_data._line)
                        local msg, kwargs
                        if $(logrecord)
                            @assert @isdefined(msg) "Assertion to tell the compiler about the definedness of this variable"
                            @assert @isdefined(kwargs) "Assertion to tell the compiler about the definedness of this variable"
                            $handle_message_nothrow(
                                logger, level, msg, _module, group, id, file, line;
                                kwargs...)
                        end
                    end
                end
            end
            nothing
        end
    end
end
```
-/
def logmsgCode {L : Type} (ops : LogmsgCodeOps L)
    (process : ProcessLogmsgExsFn L) (identifiers : List String)
    (originModule file line level message : JuliaLean.base.expr.Value L)
    (exs : List (JuliaLean.base.expr.Value L)) : LogRun (JuliaLean.base.expr.Value L × List String) := do
  let (data, identifiers) ← process identifiers originModule file line level message exs
  let nothing := JuliaLean.base.expr.Value.leaf ops.leaves.nothing
  let trueValue := JuliaLean.base.expr.Value.leaf (ops.leaves.ofBool true)
  let falseValue := JuliaLean.base.expr.Value.leaf (ops.leaves.ofBool false)
  let emptyNamedTuple := logAst "tuple" [logAst "parameters" []]
  let logrecord ←
    if !(match message with | .symbol _ => true | _ => false) &&
        ops.isSimple message && data.kwargs.isEmpty then
      pure (logAstBlock [
        logAstAssign "msg" message,
        logAstAssign "kwargs" emptyNamedTuple,
        trueValue
      ])
    else if ops.isSimple message && data.kwargs.all ops.isSimpleKeyword then do
      let checkerrors ← data.kwargs.reverse.foldlM
        (fun check kwarg => logKeywordMissingCheck kwarg check) nothing
      let (checkedMessage, checkerrors) ← match message with
        | .symbol _ =>
            let escaped := JuliaLean.base.expr.esc message
            let (_, escapedArgs) ← logRunFromExcept (JuliaLean.base.expr.asExpr escaped)
            let name ← logRunFromExcept (JuliaLean.base.expr.argAt escapedArgs 1)
            pure (escaped, logAst "if" [
              logAst "isdefined" [escaped],
              checkerrors,
              logUndefVarError name
            ])
        | _ => pure (message, checkerrors)
      let kwargsTuple := logAst "tuple" [logAst "parameters" data.kwargs]
      let errorCall := logAstCallName "invokelatest" [
        .globalRef ops.leaves.base "logging_error",
        .symbol "logger", .symbol "level", .symbol "_module", .symbol "group",
        .symbol "id", .symbol "file", .symbol "line", .symbol "err", falseValue
      ]
      pure (logAst "let" [
        logAstAssign "err" checkerrors,
        logAst "if" [
          logAstCallName "===" [.symbol "err", nothing],
          logAstBlock [
            logAstAssign "msg" checkedMessage,
            logAstAssign "kwargs" kwargsTuple,
            trueValue
          ],
          logAstBlock [errorCall, falseValue]
        ]
      ])
    else
      let escapedMessage := JuliaLean.base.expr.esc message
      let kwargsTuple := logAst "tuple" [logAst "parameters" data.kwargs]
      let errorCall := logAstCallName "invokelatest" [
        .globalRef ops.leaves.base "logging_error",
        .symbol "logger", .symbol "level", .symbol "_module", .symbol "group",
        .symbol "id", .symbol "file", .symbol "line", .symbol "err", trueValue
      ]
      pure (logAst "try" [
        logAstBlock [
          logAstAssign "msg" escapedMessage,
          logAstAssign "kwargs" kwargsTuple,
          trueValue
        ],
        .symbol "err",
        logAstBlock [errorCall, falseValue]
      ])
  let logLevelType := .globalRef ops.leaves.base "LogLevel"
  let standardLevel := match level with
    | .symbol _ => .symbol "level"
    | _ => logAst "if" [
        logAstCallName "isa" [level, logLevelType],
        level,
        logAst "::" [
          logAstCallName "convert" [logLevelType, level],
          logLevelType
        ]
      ]
  let minEnabled := logAst "ref" [.globalRef ops.leaves.base "_min_enabled_level"]
  let loggerCall := logAstCall (.globalRef ops.leaves.base "current_logger_for_env")
    [.symbol "std_level", .symbol "group", .symbol "_module"]
  let shouldlogCall := logAstCallName "invokelatest" [
    .globalRef ops.leaves.base "shouldlog",
    .symbol "logger", .symbol "level", .symbol "_module", .symbol "group", .symbol "id"
  ]
  let fileIsString := logAstCallName "isa" [.symbol "file", .globalRef ops.leaves.base "String"]
  let fixupFile := logAstCall (.globalRef ops.leaves.base "fixup_stdlib_path") [.symbol "file"]
  let messageDefined := ops.assertDefined "msg"
    (logAstCall (.globalRef ops.core "isdefined") [.symbol "msg"])
  let keywordsDefined := ops.assertDefined "kwargs"
    (logAstCall (.globalRef ops.core "isdefined") [.symbol "kwargs"])
  let handleMessage := logAstCall (.globalRef ops.leaves.base "handle_message_nothrow") [
    logAst "parameters" [logAst "..." [.symbol "kwargs"]],
    .symbol "logger", .symbol "level", .symbol "msg", .symbol "_module",
    .symbol "group", .symbol "id", .symbol "file", .symbol "line"
  ]
  let outerBody := logAstBlock [
    logAstAssign "std_level" standardLevel,
    logAst "if" [
      logAstCallName ">=" [
        logAst "." [.symbol "std_level", .quoteNode (.symbol "level")],
        minEnabled
      ],
      logAstBlock [
        logAstAssign "group" data.group,
        logAstAssign "_module" data.originModule,
        logAstAssign "logger" loggerCall,
        logAst "if" [
          logAstCallName "!" [
            logAstCallName "===" [.symbol "logger", nothing]
          ],
          logAstBlock [
            logAstAssign "id" data.id,
            logAst "if" [
              shouldlogCall,
              logAstBlock [
                logAstAssign "file" data.file,
                logAst "if" [
                  fileIsString,
                  logAstAssign "file" fixupFile,
                  nothing
                ],
                logAstAssign "line" data.line,
                logAst "local" [.symbol "msg", .symbol "kwargs"],
                logAst "if" [
                  logrecord,
                  logAstBlock [messageDefined, keywordsDefined, handleMessage],
                  nothing
                ]
              ],
              nothing
            ]
          ],
          nothing
        ]
      ],
      nothing
    ],
    nothing
  ]
  pure (logAst "let" [
    logAstBlock [logAstAssign "level" level],
    outerBody
  ], identifiers)
end JuliaLean.base.logging.logging

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

end JuliaLean.ConcurrencyCov.LoggingCov

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
  JInt.convert (IntTy.i32.name) .i32 (level.val + inc)

/-- `-(::LogLevel, ::Int)` on a 64-bit Julia process, lines 135 and 125-127. -/
def subInt (level : LogLevel) (inc : Int) : Jl LogLevel :=
  JInt.convert (IntTy.i32.name) .i32 (level.val - inc)

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

end JuliaLean.Logging
namespace JuliaLean.ConcurrencyCov.FaithfulLogging

open JuliaLean.ConcurrencyCov

def catchExceptionsM (_logger : Nat) := true

def invokedShouldlog (invoke : Nat → Int → Nat → Nat → Nat → Bool) logger level mod group id :=
  invoke logger level mod group id

def invokedMinLevel (invoke : Nat → Int) logger := invoke logger

def invokedCatch (invoke : Nat → Bool) logger := invoke logger

def nullMinLevel := LoggingCov.aboveMax

def nullShouldlog (_args : List Nat) := false

def nullHandleMessage (_args : List Nat) : R Unit :=
  .error (.errorException "Null logger handle_message() should not be called")

def logLevelCopy (level : Int) := level

def lessLevelLevel (a b : Int) : Bool := decide (a < b)

def lessLevelInteger := lessLevelLevel

def lessIntegerLevel := lessLevelLevel

def addLevel := JuliaLean.Logging.addInt

def subLevel := JuliaLean.Logging.subInt

def convertLevelM := LoggingCov.convertLevel

def convertInt32M := LoggingCov.levelToInt32

def showLevelM := LoggingCov.showLevel

def sourceInfoM := LoggingCov.sourceInfo

def logmsgMacro (level : Int) := LoggingCov.macroLevel .logmsg level

def debugMacro (level : Int) := LoggingCov.macroLevel .debug level

def infoMacro (level : Int) := LoggingCov.macroLevel .info level

def warnMacro (level : Int) := LoggingCov.macroLevel .warn level

def errorMacro (level : Int) := LoggingCov.macroLevel .error level

def logRecordIdM := LoggingCov.nextRecordId

def defaultGroupM := LoggingCov.defaultGroup

def isSimpleM := LoggingCov.isSimple

def isSimpleKwM := LoggingCov.isSimpleKw

def currentLoggerForEnv (minimum std : Int) (override : Bool) (logger : Nat) : Option Nat :=
  if minimum ≤ std || override then some logger else none

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

def handleMessageNothrowM := LoggingCov.handleMessageNothrow

def processLogmsgExsM := JuliaLean.Logging.processArgs

def defaultGroupCodeM := LoggingCov.defaultGroupCode

structure LoggingErrorTrace where
  action : LoggingCov.LoggingErrorAction
  scrubbedBacktrace : Bool
  droppedLoggingFrames : Bool
  emitted : Bool
  deriving DecidableEq, Repr

def loggingErrorM (catches real : Bool) : LoggingErrorTrace :=
  if !catches then ⟨.rethrow, false, false, false⟩
  else ⟨.emitError, true, !real, true⟩

structure ShimTrace (α : Type) where
  pairs : List (α × α)
  convertedLevel : Bool
  convertedFile : Bool
  emitted : Bool
  deriving Repr

def logmsgShimM {α : Type} (kwargs : List α) : ShimTrace α :=
  ⟨LoggingCov.pairKeywords kwargs, true, true, true⟩

def logStateCtor := LoggingCov.makeLogState

def currentLogstateM := LoggingCov.currentLogState

def withLogstate (f : Nat → Nat) (state : Nat) := f state

def disableLoggingM := JuliaLean.Logging.disableLogging

def envOverrideM := JuliaLean.Logging.envOverride

def globalLoggerM := LoggingCov.globalLogger

def setGlobalLoggerM := LoggingCov.setGlobalLogger

def withLoggerM := JuliaLean.Logging.withLogger

def currentLoggerM (state : LoggingCov.LogState) := state.logger

def simpleLoggerStream := LoggingCov.simpleLogger

def simpleLoggerDefault (minimum : Int) := LoggingCov.simpleLogger false minimum

def simpleShouldlogM := LoggingCov.simpleShouldlog

def simpleMinLevelM := LoggingCov.simpleMinEnabledLevel

def simpleCatchM := LoggingCov.simpleCatchExceptions

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

end JuliaLean.ConcurrencyCov.FaithfulLogging


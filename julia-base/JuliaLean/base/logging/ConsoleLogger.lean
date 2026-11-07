import JuliaLean.base.logging.logging
import JuliaLean.base.show
import JuliaLean.base.io

/-!
# Model of `base/logging/ConsoleLogger.jl`

Typed model at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.
Log levels reuse `logging.logging.LogLevel`; stream contexts, printing and property
lookup use `base.show`. Mutable buffers, locks and message-limit dictionaries are
typed references in a caller-supplied monad. `Text` remains generic so annotated
strings retain their regions through chomp, split and printing. User-defined show,
showerror, string conversion, metadata formatters and display-size queries are typed
callees, with their original call order. No method is left untranslated.
-/

namespace JuliaLean.base.logging.ConsoleLogger
open JuliaLean
open JuliaLean.base.logging.logging (LogLevel infoLevel warnLevel errorLevel)
open JuliaLean.base.show (JIO IOPrims AnyOps ShowError)

abbrev I := JInt64
def i (z : Int) : I := JInt.wrap .i64 z

inductive Color where
  | symbol (name : String)
  | integer (value : I)

inductive LineValue (Other : Type) where
  | range (first last : I)
  | other (value : Other)

structure TextOps (m : Type → Type) (Text Annotation Message : Type) where
  string : Message → m Text
  isannotated : Text → Bool
  annotations : Text → List Annotation
  plain : Text → m String
  annotated : String → List Annotation → m Text
  fromString : String → Text
  chomp : Text → Text
  splitLines : Text → List Text
  chars : Text → List Char

structure LockOps (m : Type → Type) (Lock : Type) where
  newLock : m Lock
  lock : Lock → m Unit
  unlock : Lock → m Unit

structure LimitOps (m : Type → Type) (Limits Id : Type) where
  newDict : m Limits
  get : Limits → Id → I → m I
  getInsert : Limits → Id → I → m I
  set : Limits → Id → I → m Unit

abbrev MetaFormatter (m : Type → Type) (Module Group Id File Line : Type) :=
  LogLevel → Option Module → Group → Id → Option File → Option Line → m (Color × String × String)

structure FormatOps (m : Type → Type) (Module File Line : Type) where
  debugColor : m Color
  infoColor : m Color
  warnColor : m Color
  errorColor : m Color
  levelString : LogLevel → m String
  moduleString : Module → m String
  fileString : File → m String
  contractuser : String → m String
  lineString : Line → m String
  intString : I → m String

structure OutputOps (m : Type → Type) (Io V Text Value : Type) where
  newBuffer : m Io
  closedStream : Io
  stderr : m Io
  isopen : Io → m Bool
  displaysize_ : Io → m (I × I)
  takeString : Io → m String
  takeBytes : Io → m JuliaLean.base.show.Bytes
  printText : JIO Io V → Text → m Unit
  printstyled : JIO Io V → String → Bool → Color → m Unit
  textwidth : String → m I
  ofDims : I × I → V
  nothingValue : Value
  builtinInteger : Value → Option (Jl I)
  showvalue : JIO Io V → Value → m Unit

section
variable {m : Type → Type} [Monad m] [MonadExceptOf ShowError m]

def withLock {Lock A : Type} (ops : LockOps m Lock) (lock : Lock) (body : m A) : m A := do
  ops.lock lock
  let result ← tryCatchThe ShowError (do pure (Except.ok (← body)))
    (fun error => pure (Except.error error))
  ops.unlock lock
  match result with
  | .ok value => pure value
  | .error error => throwThe ShowError error

/--
Julia source: base/logging/ConsoleLogger.jl:28-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct ConsoleLogger <: AbstractLogger
    stream::IO
    lock::ReentrantLock # do not log within this lock
    min_level::LogLevel
    meta_formatter
    show_limited::Bool
    right_justify::Int
    message_limits::Dict{Any,Int}
end
```
-/
structure ConsoleLogger (Io Lock Limits Formatter : Type) where
  stream : Io
  lock : Lock
  min_level : LogLevel
  meta_formatter : Formatter
  show_limited : Bool
  right_justify : I
  message_limits : Limits

/--
Julia source: base/logging/ConsoleLogger.jl:37-42 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ConsoleLogger(stream::IO, min_level=Info;
                       meta_formatter=default_metafmt, show_limited=true,
                       right_justify=0)
    ConsoleLogger(stream, ReentrantLock(), min_level, meta_formatter,
                  show_limited, right_justify, Dict{Any,Int}())
end
```
-/
def newLogger {Io Lock Limits Formatter Id : Type} (locks : LockOps m Lock)
    (limits : LimitOps m Limits Id) (stream : Io) (default_metafmt : Formatter)
    (meta_formatter : Formatter := default_metafmt)
    (min_level : LogLevel := infoLevel) (show_limited : Bool := true)
    (right_justify : I := i 0) : m (ConsoleLogger Io Lock Limits Formatter) := do
  let lock ← locks.newLock
  let messageLimits ← limits.newDict
  pure ⟨stream, lock, min_level, meta_formatter, show_limited, right_justify, messageLimits⟩

/--
Julia source: base/logging/ConsoleLogger.jl:43-48 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function ConsoleLogger(min_level=Info;
                       meta_formatter=default_metafmt, show_limited=true,
                       right_justify=0)
    ConsoleLogger(closed_stream, ReentrantLock(), min_level, meta_formatter,
                  show_limited, right_justify, Dict{Any,Int}())
end
```
-/
def newLoggerDefault {Io Lock Limits Formatter Id : Type} (locks : LockOps m Lock)
    (limits : LimitOps m Limits Id) (closed_stream : Io) (default_metafmt : Formatter)
    (meta_formatter : Formatter := default_metafmt)
    (min_level : LogLevel := infoLevel) (show_limited : Bool := true)
    (right_justify : I := i 0) : m (ConsoleLogger Io Lock Limits Formatter) := do
  let lock ← locks.newLock
  let messageLimits ← limits.newDict
  pure ⟨closed_stream, lock, min_level, meta_formatter, show_limited, right_justify, messageLimits⟩

/--
Julia source: base/logging/ConsoleLogger.jl:51-52 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
shouldlog(logger::ConsoleLogger, level, _module, group, id) =
    @lock logger.lock get(logger.message_limits, id, 1) > 0
```
-/
def shouldlog {Io Lock Limits Formatter Id Level Module Group : Type}
    (locks : LockOps m Lock) (limits : LimitOps m Limits Id)
    (logger : ConsoleLogger Io Lock Limits Formatter) (_level : Level) (_module : Module)
    (_group : Group) (id : Id) : m Bool :=
  withLock locks logger.lock (do pure ((← limits.get logger.message_limits id (i 1)).val > 0))

/--
Julia source: base/logging/ConsoleLogger.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
min_enabled_level(logger::ConsoleLogger) = logger.min_level
```
-/
def minEnabledLevel {Io Lock Limits Formatter : Type}
    (logger : ConsoleLogger Io Lock Limits Formatter) : LogLevel := logger.min_level

/--
Julia source: base/logging/ConsoleLogger.jl:57-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showvalue(io, msg) = show(io, MIME"text/plain"(), msg)
```
-/
def showvalue {Io V Message : Type} (showPlain : JIO Io V → Message → m Unit)
    (io : JIO Io V) (msg : Message) : m Unit := showPlain io msg

/--
Julia source: base/logging/ConsoleLogger.jl:58-62 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showvalue(io, e::Tuple{Exception,Any})
    ex,bt = e
    bt = Base.scrub_repl_backtrace(bt)
    showerror(io, ex, bt; backtrace = bt!==nothing)
end
```
-/
def showvalueExceptionBacktrace {Io V Exception Backtrace : Type}
    (scrub : Option Backtrace → m (Option Backtrace))
    (showerror : JIO Io V → Exception → Option Backtrace → Bool → m Unit)
    (io : JIO Io V) (e : Exception × Option Backtrace) : m Unit := do
  let (ex, bt) := e
  let bt ← scrub bt
  showerror io ex bt bt.isSome

/--
Julia source: base/logging/ConsoleLogger.jl:63-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showvalue(io, ex::Exception) = showerror(io, ex)
```
-/
def showvalueException {Io V Exception : Type}
    (showerror : JIO Io V → Exception → m Unit) (io : JIO Io V) (ex : Exception) : m Unit :=
  showerror io ex

/--
Julia source: base/logging/ConsoleLogger.jl:65-70 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function default_logcolor(level::LogLevel)
    level < Info  ? Base.debug_color() :
    level < Warn  ? Base.info_color()  :
    level < Error ? Base.warn_color()  :
                    Base.error_color()
end
```
-/
def defaultLogcolor {Module File Line : Type} (ops : FormatOps m Module File Line)
    (level : LogLevel) : m Color :=
  if level.level < infoLevel.level then ops.debugColor
  else if level.level < warnLevel.level then ops.infoColor
  else if level.level < errorLevel.level then ops.warnColor
  else ops.errorColor

/--
Julia source: base/logging/ConsoleLogger.jl:72-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function default_metafmt(level::LogLevel, _module, group, id, file, line)
    @nospecialize
    color = default_logcolor(level)
    prefix = string(level == Warn ? "Warning" : string(level), ':')
    suffix::String = ""
    Info <= level < Warn && return color, prefix, suffix
    _module !== nothing && (suffix *= string(_module)::String)
    if file !== nothing
        _module !== nothing && (suffix *= " ")
        suffix *= contractuser(string(file)::String)::String
        if line !== nothing
            suffix *= ":$(isa(line, UnitRange) ? "$(first(line))-$(last(line))" : line)"
        end
    end
    !isempty(suffix) && (suffix = "@ " * suffix)
    return color, prefix, suffix
end
```
-/
def defaultMetafmt {Module Group Id File Line : Type} (ops : FormatOps m Module File Line)
    (level : LogLevel) (module : Option Module) (_group : Group) (_id : Id)
    (file : Option File) (line : Option (LineValue Line)) : m (Color × String × String) := do
  let color ← defaultLogcolor ops level
  let label ← if level == warnLevel then pure "Warning" else ops.levelString level
  let messagePrefix := label ++ ":"
  let mut suffix := ""
  if infoLevel.level ≤ level.level && level.level < warnLevel.level then
    return (color, messagePrefix, suffix)
  if let some module := module then suffix := suffix ++ (← ops.moduleString module)
  if let some file := file then
    if module.isSome then suffix := suffix ++ " "
    suffix := suffix ++ (← ops.contractuser (← ops.fileString file))
    if let some line := line then
      let value ← match line with
        | .range first last => do pure ((← ops.intString first) ++ "-" ++ (← ops.intString last))
        | .other value => ops.lineString value
      suffix := suffix ++ ":" ++ value
  if !suffix.isEmpty then suffix := "@ " ++ suffix
  pure (color, messagePrefix, suffix)

/--
Julia source: base/logging/ConsoleLogger.jl:92-109 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function termlength(str)
    N = 0
    in_esc = false
    for c in str
        if in_esc
            if c == 'm'
                in_esc = false
            end
        else
            if c == '\e'
                in_esc = true
            else
                N += 1
            end
        end
    end
    return N
end
```
-/
def termlength {Text : Type} (chars : Text → List Char) (str : Text) : I := Id.run do
  let mut n := i 0
  let mut inEsc := false
  for c in chars str do
    if inEsc then
      if c == 'm' then inEsc := false
    else
      if c == '\x1b' then inEsc := true
      else n := n + i 1
  pure n

/--
Julia source: base/logging/ConsoleLogger.jl:111-199 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function handle_message(logger::ConsoleLogger, level::LogLevel, message, _module, group, id,
                        filepath, line; kwargs...)
    @nospecialize
    hasmaxlog = haskey(kwargs, :maxlog) ? 1 : 0
    maxlog = get(kwargs, :maxlog, nothing)
    if maxlog isa Core.BuiltinInts
        @lock logger.lock begin
            remaining = get!(logger.message_limits, id, Int(maxlog)::Int)
            remaining == 0 && return
            logger.message_limits[id] = remaining - 1
        end
    end

    # Generate a text representation of the message and all key value pairs,
    # split into lines.  This is specialised to improve type inference,
    # and reduce the risk of resulting method invalidations.
    message = string(message)
    msglines = if Base._isannotated(message) && !isempty(Base.annotations(message)::Vector{Base.RegionAnnotation})
        message = Base.AnnotatedString(String(message)::String, Base.annotations(message)::Vector{Base.RegionAnnotation})
        @NamedTuple{indent::Int, msg::Union{SubString{Base.AnnotatedString{String}}, SubString{String}}}[
            (indent=0, msg=l) for l in split(chomp(message), '\n')]
    else
        [(indent=0, msg=l) for l in split(
             chomp(String(message)::String), '\n')]
    end
    stream::IO = logger.stream
    if !(isopen(stream)::Bool)
        stream = stderr
    end
    dsize = Base.displaysize_(stream)::Tuple{Int,Int}
    nkwargs = length(kwargs)::Int
    if nkwargs > hasmaxlog
        valbuf = IOBuffer()
        rows_per_value = max(1, dsize[1] ÷ (nkwargs + 1 - hasmaxlog))
        valio = IOContext(IOContext(valbuf, stream),
                          :limit => logger.show_limited)
        for (key, val) in kwargs
            key === :maxlog && continue
            keyio = IOContext(valio,
                              :displaysize => (rows_per_value,
                                               dsize[2] - 7 - textwidth(string(key))))
            showvalue(keyio, val)
            vallines = split(takestring!(valbuf), '\n')
            if length(vallines) == 1
                push!(msglines, (indent=2, msg=SubString("$key = $(vallines[1])")))
            else
                push!(msglines, (indent=2, msg=SubString("$key =")))
                append!(msglines, ((indent=3, msg=line) for line in vallines))
            end
        end
    end

    # Format lines as text with appropriate indentation and with a box
    # decoration on the left.
    color, prefix, suffix = logger.meta_formatter(level, _module, group, id, filepath, line)::Tuple{Union{Symbol,Int},String,String}
    minsuffixpad = 2
    buf = IOBuffer()
    iob = IOContext(buf, stream)
    nonpadwidth = 2 + (isempty(prefix) || length(msglines) > 1 ? 0 : length(prefix)+1) +
                  msglines[end].indent + termlength(msglines[end].msg) +
                  (isempty(suffix) ? 0 : length(suffix)+minsuffixpad)
    justify_width = min(logger.right_justify, dsize[2])
    if nonpadwidth > justify_width && !isempty(suffix)
        push!(msglines, (indent=0, msg=SubString("")))
        minsuffixpad = 0
        nonpadwidth = 2 + length(suffix)
    end
    for (i, (indent, msg)) in enumerate(msglines)
        boxstr = length(msglines) == 1 ? "[ " :
                 i == 1                ? "┌ " :
                 i < length(msglines)  ? "│ " :
                                         "└ "
        printstyled(iob, boxstr, bold=true, color=color)
        if i == 1 && !isempty(prefix)
            printstyled(iob, prefix, " ", bold=true, color=color)
        end
        print(iob, " "^indent, msg)
        if i == length(msglines) && !isempty(suffix)
            npad = max(0, justify_width - nonpadwidth) + minsuffixpad
            print(iob, " "^npad)
            printstyled(iob, suffix, color=:light_black)
        end
        println(iob)
    end

    b = take!(buf)
    @lock logger.lock write(stream, b)
    nothing
end
```
-/
def handleMessage {Io V Ty Text Annotation Message Value Lock Limits Module Group Id File Line : Type}
    (p : IOPrims m Io V) (anyOps : AnyOps V Ty)
    (locks : LockOps m Lock) (limits : LimitOps m Limits Id)
    (text : TextOps m Text Annotation Message) (output : OutputOps m Io V Text Value)
    (logger : ConsoleLogger Io Lock Limits (MetaFormatter m Module Group Id File Line))
    (level : LogLevel) (message : Message) (module : Option Module) (group : Group)
    (id : Id) (filepath : Option File) (line : Option Line) (kwargs : List (String × Value)) : m Unit := do
  let maxlogEntry := kwargs.find? (fun entry => entry.1 == "maxlog")
  let hasmaxlog := if maxlogEntry.isSome then i 1 else i 0
  let maxlog := (maxlogEntry.map Prod.snd).getD output.nothingValue
  if let some conversion := output.builtinInteger maxlog then
    let stop ← withLock locks logger.lock do
      let default ← JuliaLean.base.show.ofJl conversion
      let remaining ← limits.getInsert logger.message_limits id default
      if remaining.val == 0 then pure true
      else
        limits.set logger.message_limits id (remaining - i 1)
        pure false
    if stop then return
  let mut message ← text.string message
  let mut msglines ← if text.isannotated message && !(text.annotations message).isEmpty then do
      message := ← text.annotated (← text.plain message) (text.annotations message)
      pure ((text.splitLines (text.chomp message)).map (fun l => (i 0, l)))
    else do
      let plain ← text.plain message
      pure ((text.splitLines (text.chomp (text.fromString plain))).map (fun l => (i 0, l)))
  let mut stream := logger.stream
  if !(← output.isopen stream) then stream := ← output.stderr
  let dsize ← output.displaysize_ stream
  let nkwargs := i kwargs.length
  if nkwargs > hasmaxlog then
    let valbuf ← output.newBuffer
    let rowsPerValue := max (i 1) (← JuliaLean.base.show.ofJl
      (JInt.div dsize.1 (nkwargs + i 1 - hasmaxlog)))
    let inherited ← JuliaLean.base.show.IOContext_IO_IO p anyOps (.plain valbuf) (.plain stream)
    let valio ← JuliaLean.base.show.withBool p anyOps (.context inherited) "limit" logger.show_limited
    for (key, val) in kwargs do
      if key == "maxlog" then continue
      let dims := (rowsPerValue, dsize.2 - i 7 - (← output.textwidth key))
      let keyio ← JuliaLean.base.show.IOContext_pair p anyOps
        (JuliaLean.base.dict.fieldConv String) (JuliaLean.base.dict.fieldConv V)
        valio ("displaysize", output.ofDims dims)
      output.showvalue (.context keyio) val
      let vallines := (← output.takeString valbuf).splitOn "\n"
      if vallines.length == 1 then
        match vallines with
        | [value] => msglines := msglines ++ [(i 2, text.fromString (key ++ " = " ++ value))]
        | _ => throwThe ShowError (.jl .boundsError)
      else
        msglines := msglines ++ [(i 2, text.fromString (key ++ " ="))]
        msglines := msglines ++ vallines.map (fun l => (i 3, text.fromString l))
  let (color, messagePrefix, suffix) ← logger.meta_formatter level module group id filepath line
  let mut minsuffixpad := i 2
  let buf ← output.newBuffer
  let iob := JIO.context (← JuliaLean.base.show.IOContext_IO_IO p anyOps (.plain buf) (.plain stream))
  let last ← match msglines.getLast? with
    | some last => pure last
    | none => throwThe ShowError (.jl .boundsError)
  let mut nonpadwidth := i 2 +
    (if messagePrefix.isEmpty || msglines.length > 1 then i 0 else i messagePrefix.length + i 1) +
    last.1 + termlength text.chars last.2 +
    (if suffix.isEmpty then i 0 else i suffix.length + minsuffixpad)
  let justifyWidth := min logger.right_justify dsize.2
  if nonpadwidth > justifyWidth && !suffix.isEmpty then
    msglines := msglines ++ [(i 0, text.fromString "")]
    minsuffixpad := i 0
    nonpadwidth := i 2 + i suffix.length
  for ((indent, msg), index) in msglines.zipIdx do
    let boxstr := if msglines.length == 1 then "[ "
      else if index == 0 then "┌ "
      else if index + 1 < msglines.length then "│ " else "└ "
    output.printstyled iob boxstr true color
    if index == 0 && !messagePrefix.isEmpty then
      output.printstyled iob (messagePrefix ++ " ") true color
    if indent.val < 0 then throwThe ShowError (.jl (.argumentError "negative repetition"))
    JuliaLean.base.show.printAll p iob [
      JuliaLean.base.show.printStr p iob (String.ofList (List.replicate indent.val.toNat ' ')),
      output.printText iob msg]
    if index + 1 == msglines.length && !suffix.isEmpty then
      let npad := max (i 0) (justifyWidth - nonpadwidth) + minsuffixpad
      if npad.val < 0 then throwThe ShowError (.jl (.argumentError "negative repetition"))
      JuliaLean.base.show.printStr p iob (String.ofList (List.replicate npad.val.toNat ' '))
      output.printstyled iob suffix false (.symbol "light_black")
    JuliaLean.base.show.println p iob []
  let b ← output.takeBytes buf
  withLock locks logger.lock (JuliaLean.base.show.write p (.plain stream) b)
  pure ()


end

/-! ## Source context (documentation, imports and declarations) -/
-- Source: base/logging/ConsoleLogger.jl:1-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
--     ConsoleLogger([stream,] min_level=Info; meta_formatter=default_metafmt,
--                   show_limited=true, right_justify=0)
-- 
-- Logger with formatting optimized for readability in a text console, for example
-- interactive work with the Julia REPL.
-- 
-- Log levels less than `min_level` are filtered out.
-- 
-- This Logger is thread-safe, with locks for both orchestration of message
-- limits i.e. `maxlog`, and writes to the stream.
-- 
-- Message formatting can be controlled by setting keyword arguments:
-- 
-- * `meta_formatter` is a function which takes the log event metadata
--   `(level, _module, group, id, file, line)` and returns a color (as would be
--   passed to printstyled), prefix and suffix for the log message.  The
--   default is to prefix with the log level and a suffix containing the module,
--   file and line location.
-- * `show_limited` limits the printing of large data structures to something
--   which can fit on the screen by setting the `:limit` `IOContext` key during
--   formatting.
-- * `right_justify` is the integer column which log metadata is right justified
--   at. The default is zero (metadata goes on its own line).
-- """
-- /Source

-- Source: base/logging/ConsoleLogger.jl:49-50 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- /Source

-- Source: base/logging/ConsoleLogger.jl:53-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/logging/ConsoleLogger.jl:55-56 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Formatting of values in key value pairs
-- /Source

-- Source: base/logging/ConsoleLogger.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/logging/ConsoleLogger.jl:71-71 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source: base/logging/ConsoleLogger.jl:89-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # Length of a string as it will appear in the terminal (after ANSI color codes
-- # are removed)
-- /Source

-- Source: base/logging/ConsoleLogger.jl:110-110 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source


end JuliaLean.base.logging.ConsoleLogger

namespace JuliaLean.ConcurrencyCov.LoggingCov

open JuliaLean.ConcurrencyCov

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

end JuliaLean.ConcurrencyCov.LoggingCov

namespace JuliaLean.Logging

open JuliaLean

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
namespace JuliaLean.ConcurrencyCov.FaithfulLogging

open JuliaLean.ConcurrencyCov

def consoleLoggerStream := LoggingCov.consoleLogger

def consoleLoggerDefault (minimum : Int) limited justify := LoggingCov.consoleLogger false minimum limited justify

def consoleShouldlogM := LoggingCov.consoleShouldlog

def consoleMinLevelM := LoggingCov.consoleMinEnabledLevel

def showValuePlain := LoggingCov.showValue false false

def showValueTuple (hasBacktrace : Bool) := LoggingCov.showValue true hasBacktrace

def showValueException := LoggingCov.showValue true false

def defaultLogcolorM := LoggingCov.defaultLogcolor

def defaultMetafmtM := LoggingCov.defaultMetafmt

def termlengthM := JuliaLean.Logging.terminalLength

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

end JuliaLean.ConcurrencyCov.FaithfulLogging


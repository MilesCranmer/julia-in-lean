import JuliaLean.base.runtime_internals
import JuliaLean.Core
import JuliaLean.base.options
import JuliaLean.base.locks_mt
import JuliaLean.base.path
import JuliaLean.base.meta
import JuliaLean.base.util
import JuliaLean.base.initdefs

/-!
# Model of `base/client.jl`

Typed models of command-line option processing, startup-file selection, input parsing, evaluation,
and REPL error handling. `JLOptions`, color selection, and command suppression use their existing
Base models. Process globals, environment access, files, logging, module loading, terminal REPL
loops, and the `@main` macro remain explicit operations or visible untranslated source.
-/

namespace JuliaLean.base.client

open JuliaLean

abbrev Bytes := JuliaLean.base.options.Bytes
abbrev I64 := JInt .i64
abbrev M (E W A : Type) := JuliaLean.base.locks_mt.M E W A
abbrev Color := JuliaLean.base.util.Color

structure ColorOps (E W : Type) where
  getEnv : String → String → M E W String
  tryParseInt : String → M E W (Option I64)
  colorKeyError : Color → E

inductive ReplColorResult (Default : Type) where
  | color : Color → ReplColorResult Default
  | default : Default → ReplColorResult Default

structure DisplayOps (E W IO Context Error Backtrace Stack : Type) where
  stderr : IO
  limitContext : IO → Context
  printStyled : IO → String → Color → Bool → M E W Unit
  showExceptionStack : Context → Stack → M E W Unit
  showError : Context → Error → Option Backtrace → Bool → M E W Unit
  println : IO → M E W Unit

structure ReplFrameOps (E W IP Frame Module : Type) where
  /-- `StackTraces.lookup(ip)` using the installed stack-trace model. -/
  lookup : IP → M E W (List Frame)
  isUnknown : Frame → Bool
  fromC : Frame → Bool
  functionName : Frame → String
  parentModule : Frame → Option Module
  baseModule : Module
  coreModule : Module
  sameModule : Module → Module → Bool

structure ReplBacktraceOps (E W Backtrace Frame : Type) where
  isNothing : Backtrace → Bool
  isAnyVector : Backtrace → Bool
  isFrameVector : Backtrace → Bool
  frameVector : Backtrace → List Frame
  stacktrace : Backtrace → M E W (List Frame)
  fromFrames : List Frame → Backtrace

structure ExceptionStackOps (E W Stack Entry Exception Backtrace : Type) where
  entries : Stack → List Entry
  fromEntries : List Entry → Stack
  exception : Entry → Exception
  backtrace : Entry → Backtrace
  entry : Exception → Backtrace → Entry
  isMethodError : Exception → Bool
  backtraceLength : Backtrace → M E W I64


def ipMatchesFrames {E W IP Frame Module : Type}
    (ops : ReplFrameOps E W IP Frame Module) (func : String) : List Frame → Bool
  | [] => false
  | frame :: rest =>
      if ops.isUnknown frame || ops.fromC frame then false
      else if ops.functionName frame == func then true
      else ipMatchesFrames ops func rest

/--
Julia source: base/client.jl:93-102 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# deprecated function--preserved for DocTests.jl
function ip_matches_func(ip, func::Symbol)
    for fr in StackTraces.lookup(ip)
        if fr === StackTraces.UNKNOWN || fr.from_c
            return false
        end
        fr.func === func && return true
    end
    return false
end
```
-/
def ipMatchesFunc {E W IP Frame Module : Type}
    (ops : ReplFrameOps E W IP Frame Module) (ip : IP) (func : String) :
    M E W Bool := do
  let frames ← ops.lookup ip
  pure (ipMatchesFrames ops func frames)

/--
Julia source: base/client.jl:109-112 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
is_driver_entry(frame) = !frame.from_c &&
    (startswith(String(frame.func), "__repl_entry") ||
     startswith(String(frame.func), "__script_entry"))

```
-/
def isDriverEntry {E W IP Frame Module : Type}
    (ops : ReplFrameOps E W IP Frame Module) (frame : Frame) : Bool :=
  !ops.fromC frame &&
    ((ops.functionName frame).startsWith "__repl_entry" ||
      (ops.functionName frame).startsWith "__script_entry")

/--
Julia source: base/client.jl:113-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# `eval`/`include` machinery a driver entry runs user code through; directly
# above the cut these frames cannot belong to user code
function is_driver_machinery(frame)
    frame.from_c && return false
    mod = parentmodule(frame)
    (mod === Base || mod === Core || mod === nothing) || return false
    return frame.func in (:eval, :include_string, :_include, :include, :fl_toplevel_eval)
end
```
-/
def isDriverMachinery {E W IP Frame Module : Type}
    (ops : ReplFrameOps E W IP Frame Module) (frame : Frame) : Bool :=
  !ops.fromC frame &&
    (match ops.parentModule frame with
    | none => true
    | some mod => ops.sameModule mod ops.baseModule || ops.sameModule mod ops.coreModule) &&
    ["eval", "include_string", "_include", "include", "fl_toplevel_eval"].contains
      (ops.functionName frame)

def trimDriverFrames {E W IP Frame Module : Type}
    (ops : ReplFrameOps E W IP Frame Module) (frames : List Frame) : List Frame :=
  let frames := match frames.reverse.findIdx? (isDriverEntry ops) with
    | some index => frames.take (frames.length - index - 1)
    | none => frames
  (frames.reverse.dropWhile (isDriverMachinery ops)).reverse

/--
Julia source: base/client.jl:122-135 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function scrub_repl_backtrace(bt)
    if bt !== nothing && !(bt isa Vector{Any}) # ignore our sentinel value types
        bt = bt isa Vector{StackFrame} ? copy(bt) : stacktrace(bt)
        # remove REPL/driver frames from interactive printing
        eval_ind = findlast(is_driver_entry, bt)
        if eval_ind !== nothing
            deleteat!(bt, eval_ind:length(bt))
            while !isempty(bt) && is_driver_machinery(bt[end])
                pop!(bt)
            end
        end
    end
    return bt
end
```
-/
def scrubReplBacktrace {E W Backtrace Frame IP Module : Type}
    (frames : ReplFrameOps E W IP Frame Module)
    (ops : ReplBacktraceOps E W Backtrace Frame) (backtrace : Backtrace) :
    M E W Backtrace := do
  if ops.isNothing backtrace || ops.isAnyVector backtrace then
    pure backtrace
  else
    let stack ← if ops.isFrameVector backtrace then
        pure (ops.frameVector backtrace)
      else ops.stacktrace backtrace
    pure (ops.fromFrames (trimDriverFrames frames stack))

/--
Julia source: base/client.jl:136-137 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
scrub_repl_backtrace(stack::ExceptionStack) =
    ExceptionStack(NamedTuple[(;x.exception, backtrace = scrub_repl_backtrace(x.backtrace)) for x in stack])
```
-/
def scrubReplBacktraceStack {E W Stack Entry Exception Backtrace Frame IP Module : Type}
    (frames : ReplFrameOps E W IP Frame Module)
    (backtraces : ReplBacktraceOps E W Backtrace Frame)
    (ops : ExceptionStackOps E W Stack Entry Exception Backtrace) (stack : Stack) :
    M E W Stack := do
  let mut result := []
  for item in ops.entries stack do
    let backtrace ← scrubReplBacktrace frames backtraces (ops.backtrace item)
    result := result ++ [ops.entry (ops.exception item) backtrace]
  pure (ops.fromEntries result)

/--
Julia source: base/client.jl:139-142 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
istrivialerror(stack::ExceptionStack) =
    length(stack) == 1 && length(stack[1].backtrace) ≤ 1 && !isa(stack[1].exception, MethodError)
    # frame 1 = top level; assumes already went through scrub_repl_backtrace; MethodError see #50803

```
-/
def isTrivialError {E W Stack Entry Exception Backtrace : Type}
    (ops : ExceptionStackOps E W Stack Entry Exception Backtrace) (stack : Stack) :
    M E W Bool := do
  let entries := ops.entries stack
  if entries.length != 1 then
    pure false
  else
    match entries with
    | [item] =>
        let backtrace ← ops.backtraceLength (ops.backtrace item)
        if backtrace.val > 1 then pure false else pure (!ops.isMethodError (ops.exception item))
    | _ => pure false

structure ParseInputOps (m : Type → Type) (L Mod P S Ty : Type) where
  parser : JuliaLean.base.meta.ParseOps m L Mod P S Ty
  exprType : Ty
  syntaxChildCount : L → I64
  syntaxChild : L → I64 → m (JuliaLean.base.expr.Value L)
  withNullLogger : {A : Type} → m A → m A

def isParseFailureNode {m : Type → Type} [Monad m]
    {L Mod P S Ty : Type} (ops : ParseInputOps m L Mod P S Ty)
    (node : JuliaLean.base.expr.Value L) : m Bool := do
  match node with
  | .expr head _ => pure (head == "error" || head == "incomplete")
  | .leaf value =>
      if ops.parser.isSyntax value then
        let head := ops.parser.syntaxHead value
        pure (head == "error" || head == "incomplete")
      else
        pure false
  | _ => pure false

/--
Julia source: base/client.jl:215-231 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _parse_input_line_core(s::String, filename::String, mod::Union{Module, Nothing}, type)
    ex = Meta.parseall(s; filename, mod, type)
    if ex isa Syntax && head(ex) === :toplevel && numchildren(ex) > 0
        last = ex[end]
        if (head(last) === :error || head(last) === :incomplete)
            # if a parse error happens in the middle of a multi-line input
            # return only the error, so that none of the input is evaluated.
            return last
        end
    elseif ex isa Expr && ex.head === :toplevel && length(ex.args) > 0
        last = ex.args[end]
        if last isa Expr && (last.head === :error || last.head === :incomplete)
            return last
        end
    end
    return ex
end
```
-/
def parseInputLineCore {m : Type → Type} [Monad m]
    {L Mod P S Ty : Type} [MonadExceptOf (JuliaLean.base.meta.MetaError L) m]
    (ops : ParseInputOps m L Mod P S Ty) (text : S) (filename : String)
    (mod : Option Mod) (type : Ty) : m (JuliaLean.base.expr.Value L) := do
  let parsed ← JuliaLean.base.meta.parseall ops.parser text filename (JInt.lit .i64 1) mod type none
  match parsed with
  | .leaf value =>
      if ops.parser.isSyntax value && ops.parser.syntaxHead value == "toplevel" then
        let count := ops.syntaxChildCount value
        if count.val > 0 then
          let last ← ops.syntaxChild value count
          if ← isParseFailureNode ops last then return last
      return parsed
  | .expr head args =>
      if head == "toplevel" then
        match args.getLast? with
        | some last => if ← isParseFailureNode ops last then return last
        | none => pure ()
      return parsed
  | _ => return parsed

/--
Julia source: base/client.jl:233-243 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function parse_input_line(s::String; filename::String="none", depwarn=true, mod::Union{Module, Nothing}=nothing, type=Expr)
    # For now, assume all parser warnings are depwarns
    ex = if depwarn
        _parse_input_line_core(s, filename, mod, type)
    else
        with_logger(NullLogger()) do
            _parse_input_line_core(s, filename, mod, type)
        end
    end
    return ex
end
```
-/
def parseInputLine {m : Type → Type} [Monad m]
    {L Mod P S Ty : Type} [MonadExceptOf (JuliaLean.base.meta.MetaError L) m]
    (ops : ParseInputOps m L Mod P S Ty) (text : S) (filename : String := "none")
    (depwarn : Bool := true) (mod : Option Mod := none) (type : Ty := ops.exprType) :
    m (JuliaLean.base.expr.Value L) := do
  if depwarn then
    parseInputLineCore ops text filename mod type
  else
    ops.withNullLogger (parseInputLineCore ops text filename mod type)

/--
Julia source: base/client.jl:244-244 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
parse_input_line(s::AbstractString; kwargs...) = parse_input_line(String(s); kwargs...)
```
-/
def parseInputLineAbstract {m : Type → Type} [Monad m]
    {L Mod P S Ty AbstractString : Type}
    [MonadExceptOf (JuliaLean.base.meta.MetaError L) m]
    (ops : ParseInputOps m L Mod P S Ty) (toString : AbstractString → S)
    (text : AbstractString) (filename : String := "none") (depwarn : Bool := true)
    (mod : Option Mod := none) (type : Ty := ops.exprType) :
    m (JuliaLean.base.expr.Value L) :=
  parseInputLine ops (toString text) filename depwarn mod type
inductive Banner where
  | no
  | yes
  | short
  deriving DecidableEq, Repr

/--
Julia source: base/client.jl:8-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const default_color_warn = :yellow
```
-/
def defaultColorWarn : Color := .symbol "yellow"
/--
Julia source: base/client.jl:9-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const default_color_error = :light_red
```
-/
def defaultColorError : Color := .symbol "light_red"
 
/--
Julia source: base/client.jl:10-10 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const default_color_info = :cyan
```
-/
def defaultColorInfo : Color := .symbol "cyan"

/--
Julia source: base/client.jl:11-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const default_color_debug = :blue
```
-/
def defaultColorDebug : Color := .symbol "blue"

/--
Julia source: base/client.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const default_color_input = :normal
```
-/
def defaultColorInput : Color := .symbol "normal"

/--
Julia source: base/client.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const default_color_answer = :normal
```
-/
def defaultColorAnswer : Color := .symbol "normal"

/--
Julia source: base/client.jl:14-14 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const color_normal = text_colors[:normal]
```
-/
def colorNormal : String := "\x1b[0m"

/--
Julia source: base/client.jl:16-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repl_color(key, default)
    env_str = get(ENV, key, "")
    c = tryparse(Int, env_str)
    c_conv = something(c, Symbol(env_str))
    haskey(text_colors, c_conv) ? c_conv : default
end
```
-/
def replColor {E W Default : Type} (ops : ColorOps E W) (key : String)
    (default : Default) : M E W (ReplColorResult Default) := do
  let envString ← ops.getEnv key ""
  let parsed ← ops.tryParseInt envString
  let symbolColor : Color := .symbol envString
  let color := match parsed with
    | some integer => JuliaLean.base.util.Color.integer integer
    | none => symbolColor
  if (JuliaLean.base.util.textColorEntry color).isSome then
    pure (.color color)
  else
    pure (.default default)

def replColorValue {E W : Type} (ops : ColorOps E W) (key : String) (default : Color) :
    M E W Color := do
  match ← replColor ops key default with
  | .color color => pure color
  | .default color => pure color

def replColorText {E W : Type} (ops : ColorOps E W) (key : String) (default : Color) :
    M E W String := do
  let color ← replColorValue ops key default
  match JuliaLean.base.util.textColorEntry color with
  | some text => pure text
  | none => throw (ops.colorKeyError color)

/--
Julia source: base/client.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
error_color() = repl_color("JULIA_ERROR_COLOR", default_color_error)
```
-/
def errorColor {E W : Type} (ops : ColorOps E W) : M E W Color :=
  replColorValue ops "JULIA_ERROR_COLOR" defaultColorError
 
 


/--
Julia source: base/client.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
warn_color()  = repl_color("JULIA_WARN_COLOR" , default_color_warn)
```
-/
def warnColor {E W : Type} (ops : ColorOps E W) : M E W Color :=
  replColorValue ops "JULIA_WARN_COLOR" defaultColorWarn

/--
Julia source: base/client.jl:25-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
info_color()  = repl_color("JULIA_INFO_COLOR" , default_color_info)
```
-/
def infoColor {E W : Type} (ops : ColorOps E W) : M E W Color :=
  replColorValue ops "JULIA_INFO_COLOR" defaultColorInfo

/--
Julia source: base/client.jl:26-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
debug_color()  = repl_color("JULIA_DEBUG_COLOR" , default_color_debug)
```
-/
def debugColor {E W : Type} (ops : ColorOps E W) : M E W Color :=
  replColorValue ops "JULIA_DEBUG_COLOR" defaultColorDebug

/--
Julia source: base/client.jl:28-28 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
input_color()  = text_colors[repl_color("JULIA_INPUT_COLOR", default_color_input)]
```
-/
def inputColor {E W : Type} (ops : ColorOps E W) : M E W String :=
  replColorText ops "JULIA_INPUT_COLOR" defaultColorInput

/--
Julia source: base/client.jl:29-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
answer_color() = text_colors[repl_color("JULIA_ANSWER_COLOR", default_color_answer)]
```
-/
def answerColor {E W : Type} (ops : ColorOps E W) : M E W String :=
  replColorText ops "JULIA_ANSWER_COLOR" defaultColorAnswer

/--
Julia source: base/client.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stackframe_lineinfo_color() = repl_color("JULIA_STACKFRAME_LINEINFO_COLOR", :bold)
```
-/
def stackframeLineinfoColor {E W : Type} (ops : ColorOps E W) : M E W Color :=
  replColorValue ops "JULIA_STACKFRAME_LINEINFO_COLOR" (.symbol "bold")

/--
Julia source: base/client.jl:32-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stackframe_function_color() = repl_color("JULIA_STACKFRAME_FUNCTION_COLOR", :bold)
```
-/
def stackframeFunctionColor {E W : Type} (ops : ColorOps E W) : M E W Color :=
  replColorValue ops "JULIA_STACKFRAME_FUNCTION_COLOR" (.symbol "bold")
/--
Julia source: base/client.jl:143-147 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function display_error(io::IO, stack::ExceptionStack)
    printstyled(io, "ERROR: "; bold=true, color=Base.error_color())
    show_exception_stack(IOContext(io, :limit => true), stack)
    println(io)
end
```
-/
def displayErrorStack {E W IO Context Error Backtrace Stack : Type}
    (colors : ColorOps E W) (ops : DisplayOps E W IO Context Error Backtrace Stack)
    (io : IO) (stack : Stack) : M E W Unit := do
  let color ← errorColor colors
  ops.printStyled io "ERROR: " color true
  ops.showExceptionStack (ops.limitContext io) stack
  ops.println io

/--
Julia source: base/client.jl:148-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
display_error(stack::ExceptionStack) = display_error(stderr, stack)
```
-/
def displayErrorStackDefault {E W IO Context Error Backtrace Stack : Type}
    (colors : ColorOps E W) (ops : DisplayOps E W IO Context Error Backtrace Stack)
    (stack : Stack) : M E W Unit :=
  displayErrorStack colors ops ops.stderr stack

/--
Julia source: base/client.jl:150-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# these forms are depended on by packages outside Julia
function display_error(io::IO, er, bt)
    printstyled(io, "ERROR: "; bold=true, color=Base.error_color())
    showerror(IOContext(io, :limit => true), er, bt, backtrace = bt!==nothing)
    println(io)
end
```
-/
def displayErrorValue {E W IO Context Error Backtrace Stack : Type}
    (colors : ColorOps E W) (ops : DisplayOps E W IO Context Error Backtrace Stack)
    (io : IO) (error : Error) (backtrace : Option Backtrace) : M E W Unit := do
  let color ← errorColor colors
  ops.printStyled io "ERROR: " color true
  ops.showError (ops.limitContext io) error backtrace backtrace.isSome
  ops.println io

/--
Julia source: base/client.jl:156-156 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
display_error(er, bt=nothing) = display_error(stderr, er, bt)
```
-/
def displayErrorValueDefault {E W IO Context Error Backtrace Stack : Type}
    (colors : ColorOps E W) (ops : DisplayOps E W IO Context Error Backtrace Stack)
    (error : Error) (backtrace : Option Backtrace := none) : M E W Unit :=
  displayErrorValue colors ops ops.stderr error backtrace

def i64 (n : Int) : I64 := JInt.wrap .i64 n

structure ScriptOps (E W Module Expr Value : Type) where
  includeFile : Module → Bytes → M E W Value
  includeString : Module → Bytes → Bytes → M E W Value
  eval : Module → Expr → M E W Value

/--
Julia source: base/client.jl:158-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# N.B.: Any functions starting with __repl_entry cut off backtraces when printing in the REPL.
__repl_entry_client_eval(mod::Module, @nospecialize(ast)) = Core.eval(mod, ast)
```
-/
def replEntryClientEval {E W Module Expr Value : Type}
    (ops : ScriptOps E W Module Expr Value) (mod : Module) (ast : Expr) :
    M E W Value :=
  ops.eval mod ast

structure EvalUserInputOps
    (E W Module Value ErrorIO Stack Source CancelToken : Type) where
  stdoutHasColor : M E W Bool
  printStdout : String → M E W Unit
  answerColor : M E W String
  setGlobal : {A : Type} → Module → String → A → M E W Unit
  isNothing : Value → Bool
  display : Value → M E W Unit
  displayError : ErrorIO → Stack → M E W Unit
  scrubBacktrace : Stack → M E W Stack
  isTrivialError : Stack → M E W Bool
  currentExceptions : M E W Stack
  newEvaluationSource : M E W Source
  newEpisode : Source → M E W CancelToken
  withCancelToken : CancelToken → M E W Unit → M E W Unit
  closeEpisode : M E W Unit
  logDisplayFailure : Value → M E W Unit
  logDisplayErrorFailure : M E W Unit
  logTooManyErrors : Nat → M E W Unit
  stdinIsTTY : M E W Bool
  println : M E W Unit
structure EvalUserInputState (Stack : Type) where
  errorCount : Nat
  lastError : Option Stack

def evalUserInputStep
    {E W Module Expr Value ErrorIO Stack Source CancelToken : Type}
    (ops : EvalUserInputOps E W Module Value ErrorIO Stack Source CancelToken)
    (script : ScriptOps E W Module Expr Value) (mod : Module) (errio : ErrorIO)
    (ast : Expr) (showValue : Bool) (haveColor : Bool)
    (state : EvalUserInputState Stack) : M E W (Sum Unit (EvalUserInputState Stack)) := do
  let completed ← tryCatch (do
    if haveColor then ops.printStdout colorNormal
    match state.lastError with
    | some lastError =>
        let lastError ← ops.scrubBacktrace lastError
        if !(← ops.isTrivialError lastError) then
          ops.setGlobal mod "err" lastError
        let source ← ops.newEvaluationSource
        let token ← ops.newEpisode source
        JuliaLean.base.locks_mt.finallyDo
          (ops.withCancelToken token (ops.displayError errio lastError))
          ops.closeEpisode
    | none =>
        let value ← replEntryClientEval script mod ast
        ops.setGlobal mod "ans" value
        if !ops.isNothing value && showValue then
          if haveColor then ops.printStdout (← ops.answerColor)
          tryCatch (ops.display value) (fun error => do
            ops.logDisplayFailure value
            throw error)
    pure true) (fun _ => pure false)
  if completed then
    pure (.inl ())
  else do
    if state.errorCount > 0 then ops.logDisplayErrorFailure
    let errorCount := state.errorCount + 1
    let errors ← ops.scrubBacktrace (← ops.currentExceptions)
    ops.setGlobal mod "err" errors
    if errorCount > 2 then
      ops.logTooManyErrors errorCount
      pure (.inl ())
    else
      pure (.inr ⟨errorCount, some errors⟩)

/--
Julia source: base/client.jl:161-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function eval_user_input(errio, @nospecialize(ast), show_value::Bool)
    errcount = 0
    lasterr = nothing
    have_color = get(stdout, :color, false)::Bool
    while true
        try
            if have_color
                print(color_normal)
            end
            if lasterr !== nothing
                lasterr = scrub_repl_backtrace(lasterr)
                istrivialerror(lasterr) || setglobal!(Base.MainInclude, :err, lasterr)
                # error display (user-extensible show methods) runs in a
                # fresh ^C epoch: the failed evaluation's cancelled epoch
                # must not poison it, and a stuck printout is cancellable
                try
                    ScopedValues.@with(CANCEL_TOKEN => sigint_new_episode!(new_evaluation_cancel_source!()),
                                       invokelatest(display_error, errio, lasterr))
                finally
                    sigint_close_episode!()
                end
            else
                value = __repl_entry_client_eval(Main, ast)
                setglobal!(Base.MainInclude, :ans, value)
                if !(value === nothing) && show_value
                    if have_color
                        print(answer_color())
                    end
                    try
                        invokelatest(display, value)
                    catch
                        @error "Evaluation succeeded, but an error occurred while displaying the value" typeof(value)
                        rethrow()
                    end
                end
            end
            break
        catch
            if errcount > 0
                @error "SYSTEM: display_error(errio, lasterr) caused an error"
            end
            errcount += 1
            lasterr = scrub_repl_backtrace(current_exceptions())
            setglobal!(Base.MainInclude, :err, lasterr)
            if errcount > 2
                @error "It is likely that something important is broken, and Julia will not be able to continue normally" errcount
                break
            end
        end
    end
    isa(stdin, TTY) && println()
    nothing
end
```
-/
def evalUserInput
    {E W Module Expr Value ErrorIO Stack Source CancelToken : Type}
    (ops : EvalUserInputOps E W Module Value ErrorIO Stack Source CancelToken)
    (script : ScriptOps E W Module Expr Value) (mod : Module) (errio : ErrorIO)
    (ast : Expr) (showValue : Bool) : M E W Unit := do
  let haveColor ← ops.stdoutHasColor
  let _ ← JuliaLean.base.locks_mt.loop
    (evalUserInputStep ops script mod errio ast showValue haveColor)
    ⟨0, none⟩
  if ← ops.stdinIsTTY then ops.println
  pure ()

structure StartupOps (E W : Type) where
  kernel : String
  pathStrings : JuliaLean.base.path.StringOps
  pathFiles : JuliaLean.base.path.FileBindings W
  bindir : JuliaLean.base.path.Path
  sysconfdir : JuliaLean.base.path.Path
  depotPath : M E W (List JuliaLean.base.path.Path)
  isfile : JuliaLean.base.path.Path → M E W Bool
  pathError : JuliaLean.base.path.PathError → E

structure ClientOps
    (E W P PP Module Expr Value Distributed TraceMode ExceptionStack : Type) where
  options : JuliaLean.base.options.JLOptions P PP
  pointer : JuliaLean.base.options.PtrOps (M E W) P PP
  unsafeLoadCommands : PP → M E W (List (Char × Bytes))
  getEnvBytes : Bytes → M E W Bytes
  getBoolEnv : String → Bool → M E W (Option Bool)
  boolCondition : Option Bool → M E W Bool
  setEnvBytes : Bytes → Bytes → M E W Unit
  getTraceEval : M E W TraceMode
  setTraceEval : TraceMode → M E W Unit
  traceEvalIsFull : TraceMode → Bool
  traceEvalLoc : TraceMode
  setHaveColor : Option Bool → M E W Unit
  setInteractive : Bool → M E W Unit
  argsEmpty : M E W Bool
  popFirstArg : M E W Bytes
  setProgramFile : Bytes → M E W Unit
  stdinIsTTY : M E W Bool
  loadInteractiveUtils : M E W Value
  reportBug : Value → Bytes → M E W Unit
  requireDistributed : M E W Distributed
  setMainIncludeDistributed : Distributed → M E W Unit
  usingMainIncludeDistributed : M E W Unit
  processDistributedOptions : Distributed → JuliaLean.base.options.JLOptions P PP → M E W Unit
  startup : StartupOps E W
  script : ScriptOps E W Module Expr Value
  main : Module
  parseInputLine : Bytes → Module → M E W Expr
  showLatest : Value → M E W Unit
  println : M E W Unit
  entrypointImport : Bytes → M E W Expr
  runMainRepl : Bool → Bool → Banner → Bool → M E W Unit
  includeAllProcessors : Bytes → M E W Unit
  setExitOnSigint : Bool → M E W Unit
  readStdin : M E W Bytes
  currentExceptions : M E W ExceptionStack
  clearExceptionBacktraces : ExceptionStack → ExceptionStack
  scrubReplBacktrace : ExceptionStack → M E W ExceptionStack
  warnUnexpectedCommand : Char → Bytes → M E W Unit
  bytesToString : Bytes → M E W String
  raiseError : String → M E W Empty
  exit : I64 → M E W Empty

structure EntrypointOps (E W Module : Type) where
  isDefined : Module → Bytes → M E W Bool
  bindingModule : Module → Bytes → M E W Module
  getBool : Module → Bytes → M E W Bool

/--
Julia source: base/client.jl:580-585 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function should_use_main_entrypoint()
    isdefined(Main, :main) || return false
    M_binding_owner = Base.binding_module(Main, :main)
    (isdefined(M_binding_owner, Symbol("#__main_is_entrypoint__#")) && M_binding_owner.var"#__main_is_entrypoint__#") || return false
    return true
end
```
-/
def shouldUseMainEntrypoint {E W Module : Type}
    (ops : EntrypointOps E W Module) (main : Module) : M E W Bool := do
  let mainName := JuliaLean.base.options.lit "main"
  if !(← ops.isDefined main mainName) then return false
  let owner ← ops.bindingModule main mainName
  let marker := JuliaLean.base.options.lit "#__main_is_entrypoint__#"
  if !(← ops.isDefined owner marker) then return false
  ops.getBool owner marker

/--
Julia source: base/client.jl:104-104 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
__script_entry_include(mod::Module, path::String) = _include(identity, mod, path)
```
-/
def scriptEntryInclude {E W Module Expr Value : Type}
    (ops : ScriptOps E W Module Expr Value) (mod : Module) (path : Bytes) : M E W Value :=
  ops.includeFile mod path

/--
Julia source: base/client.jl:105-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
__script_entry_include_string(mod::Module, code::String, filename::String) =
    include_string(mod, code, filename)
```
-/
def scriptEntryIncludeString {E W Module Expr Value : Type}
    (ops : ScriptOps E W Module Expr Value) (mod : Module) (code filename : Bytes) : M E W Value :=
  ops.includeString mod code filename

/--
Julia source: base/client.jl:107-107 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
__script_entry_eval(mod::Module, @nospecialize(ex)) = Core.eval(mod, ex)
```
-/
def scriptEntryEval {E W Module Expr Value : Type}
    (ops : ScriptOps E W Module Expr Value) (mod : Module) (expr : Expr) : M E W Value :=
  ops.eval mod expr

def literalPath {E W : Type} (ops : StartupOps E W) (value : String) : JuliaLean.base.path.Path :=
  ops.pathStrings.fromBytes value.toUTF8.toList

def absolutePath {E W : Type} (ops : StartupOps E W)
    (parts : List JuliaLean.base.path.Path) : M E W JuliaLean.base.path.Path := do
  let os ← match JuliaLean.base.path.platformForKernel ops.kernel with
    | .ok os => pure os
    | .error error => throw (ops.pathError error)
  let joined ← match JuliaLean.base.path.joinpathStrings os ops.pathStrings parts with
    | .ok path => pure path
    | .error error => throw (ops.pathError error)
  fun world => do
    let (result, world) ← JuliaLean.base.path.abspath ops.pathFiles.ops os ops.pathStrings joined world
    match result with
    | .ok path => some (.ok (path, world))
    | .error error => some (.error (ops.pathError error, world))

/--
Julia source: base/client.jl:363-377 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _global_julia_startup_file()
    # If the user built us with a specific Base.SYSCONFDIR, check that location first for a startup.jl file
    # If it is not found, then continue on to the relative path based on Sys.BINDIR
    BINDIR = Sys.BINDIR
    SYSCONFDIR = Base.SYSCONFDIR
    p1 = nothing
    if !isempty(SYSCONFDIR)
        p1 = abspath(BINDIR, SYSCONFDIR, "julia", "startup.jl")
        isfile(p1) && return p1
    end
    p2 = abspath(BINDIR, "..", "etc", "julia", "startup.jl")
    p1 == p2 && return nothing # don't check the same path twice
    isfile(p2) && return p2
    return nothing
end
```
-/
def globalStartupFile {E W : Type} (ops : StartupOps E W) : M E W (Option JuliaLean.base.path.Path) := do
  let startupName := literalPath ops "startup.jl"
  let p1 ← if ops.sysconfdir.bytes.isEmpty then
      pure none
    else do
      let path ← absolutePath ops
        [ops.bindir, ops.sysconfdir, literalPath ops "julia", startupName]
      pure (some path)
  if let some path := p1 then
    if ← ops.isfile path then return some path
  let p2 ← absolutePath ops
    [ops.bindir, literalPath ops "..", literalPath ops "etc", literalPath ops "julia", startupName]
  if p1 == some p2 then return none
  if ← ops.isfile p2 then return some p2
  pure none

/--
Julia source: base/client.jl:379-385 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _local_julia_startup_file()
    if !isempty(DEPOT_PATH)
        path = abspath(DEPOT_PATH[1], "config", "startup.jl")
        isfile(path) && return path
    end
    return nothing
end
```
-/
def localStartupFile {E W : Type} (ops : StartupOps E W) : M E W (Option JuliaLean.base.path.Path) := do
  match ← ops.depotPath with
  | [] => pure none
  | depot :: _ => do
      let path ← absolutePath ops [depot, literalPath ops "config", literalPath ops "startup.jl"]
      if ← ops.isfile path then pure (some path) else pure none

/--
Julia source: base/client.jl:387-393 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function load_julia_startup()
    global_file = _global_julia_startup_file()
    (global_file !== nothing) && __script_entry_include(Main, global_file)
    local_file = _local_julia_startup_file()
    (local_file !== nothing) && __script_entry_include(Main, local_file)
    return nothing
end
```
-/
def loadJuliaStartup {E W Module Expr Value : Type}
    (startup : StartupOps E W) (script : ScriptOps E W Module Expr Value) (main : Module) :
    M E W Unit := do
  let globalFile ← globalStartupFile startup
  if let some path := globalFile then
    let _ ← scriptEntryInclude script main path.bytes
  let localFile ← localStartupFile startup
  if let some path := localFile then
    let _ ← scriptEntryInclude script main path.bytes
  pure ()


structure ReplHookOps (E W Repl Hook ErrorIO : Type) where
  hooks : M E W (List Hook)
  pushFirst : Hook → M E W Unit
  call : Hook → Repl → M E W Unit
  stderr : ErrorIO
  showError : ErrorIO → E → M E W Unit
  println : ErrorIO → M E W Unit
  invokeLatest : M E W Unit → M E W Unit

/--
Julia source: base/client.jl:405-405 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
atreplinit(f::Function) = (pushfirst!(repl_hooks, f); nothing)
```
-/
def atreplinit {E W Repl Hook ErrorIO : Type}
    (ops : ReplHookOps E W Repl Hook ErrorIO) (hook : Hook) : M E W Unit := do
  ops.pushFirst hook
  pure ()

/--
Julia source: base/client.jl:407-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function __atreplinit(repl)
    for f in repl_hooks
        try
            f(repl)
        catch err
            showerror(stderr, err)
            println(stderr)
        end
    end
end
```
-/
def runReplHooks {E W Repl Hook ErrorIO : Type}
    (ops : ReplHookOps E W Repl Hook ErrorIO) (repl : Repl) : M E W Unit := do
  for hook in ← ops.hooks do
    tryCatch (ops.call hook repl) (fun error => do
      ops.showError ops.stderr error
      ops.println ops.stderr)

/--
Julia source: base/client.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_atreplinit(repl) = invokelatest(__atreplinit, repl)
```
-/
def runReplHooksLatest {E W Repl Hook ErrorIO : Type}
    (ops : ReplHookOps E W Repl Hook ErrorIO) (repl : Repl) : M E W Unit :=
  ops.invokeLatest (runReplHooks ops repl)

structure ReplLoaderOps (E W Module Package Backtrace : Type) where
  main : Module
  mainInclude : Module
  interactiveUtilsPackage : Package
  replPackage : Package
  interactiveUtilsName : String
  isDefined : Module → String → M E W Bool
  requireStdlib : Package → M E W Module
  setModule : Module → String → Module → M E W Unit
  evalInteractiveUtilsImport : Module → M E W Module
  captureBacktrace : M E W Backtrace
  warnInteractiveUtilsFailure : Module → E → Backtrace → M E W Unit
  warnReplFailure : E → Backtrace → M E W Unit

/--
Julia source: base/client.jl:419-433 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function load_InteractiveUtils(mod::Module=Main)
    # load interactive-only libraries
    if !isdefined(MainInclude, :InteractiveUtils)
        try
            # TODO: we have to use require_stdlib here because it is a dependency of REPL, but we would sort of prefer not to
            let InteractiveUtils = require_stdlib(PkgId(UUID(0xb77e0a4c_d291_57a0_90e8_8db25a27a240), "InteractiveUtils"))
                MainInclude.InteractiveUtils = InteractiveUtils
            end
        catch ex
            @warn "Failed to import InteractiveUtils into module $mod" exception=(ex, catch_backtrace())
            return nothing
        end
    end
    return Core.eval(mod, :(using Base.MainInclude.InteractiveUtils; Base.MainInclude.InteractiveUtils))
end
```
-/
def loadInteractiveUtils {E W Module Package Backtrace : Type}
    (ops : ReplLoaderOps E W Module Package Backtrace)
    (mod : Module := ops.main) : M E W (Option Module) := do
  if !(← ops.isDefined ops.mainInclude ops.interactiveUtilsName) then
    let loaded ← tryCatch (do
      let moduleValue ← ops.requireStdlib ops.interactiveUtilsPackage
      ops.setModule ops.mainInclude ops.interactiveUtilsName moduleValue
      pure true) (fun error => do
        let backtrace ← ops.captureBacktrace
        ops.warnInteractiveUtilsFailure mod error backtrace
        pure false)
    if !loaded then return none
  pure (some (← ops.evalInteractiveUtilsImport mod))

/--
Julia source: base/client.jl:435-443 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function load_REPL()
    # load interactive-only libraries
    try
        return Base.require_stdlib(PkgId(UUID(0x3fa0cd96_eef1_5676_8a61_b3b8758bbffb), "REPL"))
    catch ex
        @warn "Failed to import REPL" exception=(ex, catch_backtrace())
    end
    return nothing
end
```
-/
def loadRepl {E W Module Package Backtrace : Type}
    (ops : ReplLoaderOps E W Module Package Backtrace) : M E W (Option Module) :=
  tryCatch (do
    pure (some (← ops.requireStdlib ops.replPackage))) (fun error => do
    let backtrace ← ops.captureBacktrace
    ops.warnReplFailure error backtrace
    pure none)

structure MainParserOps (E W Args Parsed : Type) where
  parse : Args → M E W Parsed

/--
Julia source: base/client.jl:568-570 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function var"#_internal_julia_parse"(args...)
    main_parser[](args...)
end
```
-/
def internalJuliaParse {E W Args Parsed : Type}
    (ops : MainParserOps E W Args Parsed) (args : Args) : M E W Parsed :=
  ops.parse args
structure FallbackReplOps
    (E W Input Text Module Value ErrorIO Source CancelToken : Type) where
  stdin : Input
  stderr : ErrorIO
  nothing : Value
  isFile : Input → Bool
  isIOStream : Input → Bool
  readString : Input → M E W Text
  parseMainSyntax : Text → M E W Value
  head : Value → String
  isSyntax : Value → Bool
  children : Value → List Value
  eof : Input → M E W Bool
  printPrompt : M E W Unit
  flushStdout : M E W Unit
  readline : Input → Bool → M E W Text
  emptyText : Text
  appendText : Text → Text → Text
  evalUserInput : ErrorIO → Value → Bool → M E W Unit
  newEvaluationCancelSource : M E W Source
  newEpisode : Source → M E W CancelToken
  withCancelToken : CancelToken → M E W Unit → M E W Unit
  closeEpisode : M E W Unit
  isInterrupt : E → Bool
  printInterruptNewlines : M E W Unit

structure FallbackInputState (Text Value : Type) where
  line : Text
  expression : Option Value

def readFallbackInputStep
    {E W Input Text Module Value ErrorIO Source CancelToken : Type}
    (ops : FallbackReplOps E W Input Text Module Value ErrorIO Source CancelToken)
    (input : Input) (state : FallbackInputState Text Value) :
    M E W (Sum Value (FallbackInputState Text Value)) := do
  if ← ops.eof input then
    pure (.inl (state.expression.getD ops.nothing))
  else
    let line := ops.appendText state.line (← ops.readline input true)
    let expression ← ops.parseMainSyntax line
    if ops.isSyntax expression && ops.head expression == "incomplete" then
      pure (.inr ⟨line, some expression⟩)
    else
      pure (.inl expression)

/--
Julia source: base/client.jl:448-494 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function run_fallback_repl(interactive::Bool)
    let input = stdin
        if isa(input, File) || isa(input, IOStream)
            # for files, we can slurp in the whole thing at once
            ex = parse_input_line(read(input, String); mod=Main, type=Syntax)
            if head(ex) === :toplevel
                # if we get back a list of statements, eval them sequentially
                # as if we had parsed them sequentially
                for stmt in children(ex)
                    eval_user_input(stderr, stmt, true)
                end
            else
                eval_user_input(stderr, ex, true)
            end
        else
            while true
                if interactive
                    print("julia> ")
                    flush(stdout)
                end
                eof(input) && break
                try
                    line = ""
                    ex = nothing
                    while !eof(input)
                        line *= readline(input, keep=true)
                        ex = parse_input_line(line; mod=Main, type=Syntax)
                        if !(isa(ex, Syntax) && head(ex) === :incomplete)
                            break
                        end
                    end
                    # each interactive input is a fresh ^C epoch (an
                    # evaluation source, so leftovers stay session-sweepable)
                    try
                        ScopedValues.@with(CANCEL_TOKEN => sigint_new_episode!(new_evaluation_cancel_source!()),
                                           eval_user_input(stderr, ex, true))
                    finally
                        sigint_close_episode!()
                    end
                catch err
                    isa(err, InterruptException) ? print("\n\n") : rethrow()
                end
            end
        end
    end
    nothing
end
```
-/
def runFallbackRepl
    {E W Input Text Module Value ErrorIO Source CancelToken : Type}
    (ops : FallbackReplOps E W Input Text Module Value ErrorIO Source CancelToken)
    (interactive : Bool) : M E W Unit := do
  let input := ops.stdin
  if ops.isFile input || ops.isIOStream input then
    let expression ← ops.parseMainSyntax (← ops.readString input)
    if ops.head expression == "toplevel" then
      for statement in ops.children expression do
        ops.evalUserInput ops.stderr statement true
    else
      ops.evalUserInput ops.stderr expression true
  else
    let _ ← JuliaLean.base.locks_mt.loop (fun (_ : Unit) => do
      if interactive then
        ops.printPrompt
        ops.flushStdout
      if ← ops.eof input then
        pure (.inl ())
      else
        tryCatch (do
          let expression ← JuliaLean.base.locks_mt.loop
            (readFallbackInputStep ops input) ⟨ops.emptyText, none⟩
          let source ← ops.newEvaluationCancelSource
          let token ← ops.newEpisode source
          JuliaLean.base.locks_mt.finallyDo
            (ops.withCancelToken token (ops.evalUserInput ops.stderr expression true))
            ops.closeEpisode
          pure (.inr ())) (fun error =>
            if ops.isInterrupt error then do
              ops.printInterruptNewlines
              pure (.inr ())
            else
              throw error)) ()
  pure ()
def debugEnvLoop
    {E W P PP Module Expr Value Distributed TraceMode ExceptionStack : Type}
    (ops : ClientOps E W P PP Module Expr Value Distributed TraceMode ExceptionStack) :
    List String → M E W Unit
  | [] => pure ()
  | name :: rest => do
      let parsed ← ops.getBoolEnv name false
      if ← ops.boolCondition parsed then do
        let current ← ops.getTraceEval
        ops.setTraceEval (if ops.traceEvalIsFull current then current else ops.traceEvalLoc)
        ops.setEnvBytes (JuliaLean.base.options.lit "JULIA_TEST_VERBOSE")
          (JuliaLean.base.options.lit "true")
      else
        debugEnvLoop ops rest

def processSetupCommands
    {E W P PP Module Expr Value Distributed TraceMode ExceptionStack : Type}
    (ops : ClientOps E W P PP Module Expr Value Distributed TraceMode ExceptionStack)
    (argIsProgram repl : Bool) : List (Char × Bytes) → M E W (Option (Bool × Bool))
  | [] => pure (some (argIsProgram, repl))
  | (command, arg) :: rest => do
      if JuliaLean.base.initdefs.cmdSuppressesProgram 'e' 'E' command then
        processSetupCommands ops false false rest
      else if command == 'L' || command == 'm' then
        processSetupCommands ops argIsProgram repl rest
      else if command == 'B' then do
        let interactiveUtils ← ops.loadInteractiveUtils
        ops.reportBug interactiveUtils arg
        pure none
      else do
        ops.warnUnexpectedCommand command arg
        processSetupCommands ops argIsProgram repl rest

def processMainCommands
    {E W P PP Module Expr Value Distributed TraceMode ExceptionStack : Type}
    (ops : ClientOps E W P PP Module Expr Value Distributed TraceMode ExceptionStack)
    (entrypoint : EntrypointOps E W Module) (distributedMode : Bool) :
    List (Char × Bytes) → M E W Bool
  | [] => pure true
  | (command, arg) :: rest => do
      if command == 'e' then do
        let expr ← ops.parseInputLine arg ops.main
        let _ ← scriptEntryEval ops.script ops.main expr
        processMainCommands ops entrypoint distributedMode rest
      else if command == 'E' then do
        let expr ← ops.parseInputLine arg ops.main
        let value ← scriptEntryEval ops.script ops.main expr
        ops.showLatest value
        ops.println
        processMainCommands ops entrypoint distributedMode rest
      else if command == 'm' then do
        let expr ← ops.entrypointImport arg
        let _ ← scriptEntryEval ops.script ops.main expr
        if ← shouldUseMainEntrypoint entrypoint ops.main then pure false
        else do
          let moduleName ← ops.bytesToString arg
          let never ← ops.raiseError
            ("`main` in `" ++ moduleName ++ "` not declared as entry point (use `@main` to do so)")
          nomatch never
      else if command == 'L' then do
        if distributedMode then ops.includeAllProcessors arg
        else let _ ← scriptEntryInclude ops.script ops.main arg
        processMainCommands ops entrypoint distributedMode rest
      else
        processMainCommands ops entrypoint distributedMode rest

structure ReplCommandOps (E W Command Fields IO : Type) where
  isCmd : Command → Bool
  exec : Command → List String
  fields : Command → Fields
  commandWithExec : List String → Fields → Command
  ignoreStatus : Command → Command
  run : Command → M E W Unit
  isWindows : Bool
  getEnv : String → String → M E W String
  shellSplit : String → List String
  shellEscapePosixly : Command → String
  homeDir : M E W String
  hasEnv : String → M E W Bool
  getEnvValue : String → M E W String
  setEnv : String → String → M E W Unit
  deleteEnv : String → M E W Unit
  pwd : M E W String
  cd : String → M E W Unit
  isIOError : E → Bool
  argumentError : String → E
  error : String → E
  typeName : Command → String
  println : IO → String → M E W Unit

/--
Julia source: base/client.jl:34-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repl_cmd(cmd::AbstractCmd, out)
    if !(cmd isa Cmd)
        # Pipelines and redirects: run directly without shell wrapping.
        try
            run(ignorestatus(cmd))
        catch
            lasterr = current_exceptions()
            lasterr = ExceptionStack(NamedTuple[(exception = e[1], backtrace = [] ) for e in lasterr])
            invokelatest(display_error, lasterr)
        end
        return nothing
    end
    if isempty(cmd.exec)
        throw(ArgumentError("no cmd to execute"))
    elseif cmd.exec[1] == "cd"
        if length(cmd.exec) > 2
            throw(ArgumentError("cd method only takes one argument"))
        elseif length(cmd.exec) == 2
            dir = cmd.exec[2]
            if dir == "-"
                if !haskey(ENV, "OLDPWD")
                    error("cd: OLDPWD not set")
                end
                dir = ENV["OLDPWD"]
            end
        else
            dir = homedir()
        end
        try
            ENV["OLDPWD"] = pwd()
        catch ex
            ex isa IOError || rethrow()
            # if current dir has been deleted, then pwd() will throw an IOError: pwd(): no such file or directory (ENOENT)
            delete!(ENV, "OLDPWD")
        end
        cd(dir)
        println(out, pwd())
    else
        if !Sys.iswindows()
            shell = shell_split(get(ENV, "JULIA_SHELL", get(ENV, "SHELL", "/bin/sh")))
            shell_escape_cmd = shell_escape_posixly(cmd)
            original_cmd = cmd
            cmd = Cmd(`$shell -c $shell_escape_cmd`, original_cmd.ignorestatus, original_cmd.flags, original_cmd.env, original_cmd.dir, original_cmd.cpus, original_cmd.uid, original_cmd.gid)
        end
        try
            run(ignorestatus(cmd))
        catch
            # Julia throws an exception if it can't find the cmd (which may be the shell itself), but the stack trace isn't useful
            lasterr = current_exceptions()
            lasterr = ExceptionStack(NamedTuple[(exception = e[1], backtrace = [] ) for e in lasterr])
            invokelatest(display_error, lasterr)
        end
    end
    nothing
end
```
-/
def replCmd
    {E W P PP Module Expr Value Distributed TraceMode ExceptionStack Command Fields IO Context Error Backtrace : Type}
    (client : ClientOps E W P PP Module Expr Value Distributed TraceMode ExceptionStack)
    (commandOps : ReplCommandOps E W Command Fields IO)
    (colors : ColorOps E W)
    (display : DisplayOps E W IO Context Error Backtrace ExceptionStack)
    (cmd : Command) (out : IO) : M E W Unit := do
  if !commandOps.isCmd cmd then
    tryCatch (commandOps.run (commandOps.ignoreStatus cmd)) (fun _ => do
      let stack ← client.currentExceptions
      let stack := client.clearExceptionBacktraces stack
      let _ ← displayErrorStack colors display display.stderr stack
      pure ())
    pure ()
  else
    match commandOps.exec cmd with
    | [] => throw (commandOps.argumentError "no cmd to execute")
    | executable :: arguments =>
      if executable == "cd" then do
        let directory ← match arguments with
          | _ :: _ :: _ => throw (commandOps.argumentError "cd method only takes one argument")
          | [directory] =>
            if directory == "-" then do
              if !(← commandOps.hasEnv "OLDPWD") then
                throw (commandOps.error "cd: OLDPWD not set")
              commandOps.getEnvValue "OLDPWD"
            else pure directory
          | [] => commandOps.homeDir
        tryCatch (do
          let currentDirectory ← commandOps.pwd
          commandOps.setEnv "OLDPWD" currentDirectory)
          (fun error =>
            if commandOps.isIOError error then commandOps.deleteEnv "OLDPWD"
            else throw error)
        commandOps.cd directory
        commandOps.println out (← commandOps.pwd)
      else do
        let command ← if commandOps.isWindows then
            pure cmd
          else do
            let defaultShell ← commandOps.getEnv "SHELL" "/bin/sh"
            let shell ← commandOps.getEnv "JULIA_SHELL" defaultShell
            let shellPrefix := commandOps.shellSplit shell
            let escapedCommand := commandOps.shellEscapePosixly cmd
            pure (commandOps.commandWithExec
              (shellPrefix ++ ["-c", escapedCommand]) (commandOps.fields cmd))
        tryCatch (commandOps.run (commandOps.ignoreStatus command)) (fun _ => do
          let stack ← client.currentExceptions
          let stack := client.clearExceptionBacktraces stack
          let _ ← displayErrorStack colors display display.stderr stack
          pure ())

/--
Julia source: base/client.jl:90-91 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repl_cmd(@nospecialize(cmd), out) =
    throw(ArgumentError("repl_cmd: expected an `AbstractCmd`, got $(typeof(cmd))"))
```
-/
def replCmdFallback
    {E W Command Fields IO : Type}
    (commandOps : ReplCommandOps E W Command Fields IO) (cmd : Command) (_out : IO) :
    M E W Empty :=
  throw (commandOps.argumentError
    ("repl_cmd: expected an `AbstractCmd`, got " ++ commandOps.typeName cmd))

structure FrontendOps (E W : Type) where
  enableInCore : Bool → Bool → M E W Unit
  getBoolEnv : String → Bool → M E W (Option Bool)
  activateJuliaLowering : Bool → Bool → M E W Unit

/--
Julia source: base/client.jl:644-651 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function init_frontend()
    JuliaSyntax.enable_in_core!(true; freeze_world_age=true)
    if get_bool_env("JULIA_USE_FLISP_LOWERING", true) === true
        JuliaLowering.activate!(false)
    else
        JuliaLowering.activate!(true; freeze_world_age=true)
    end
end
```
-/
def initFrontend {E W : Type} (ops : FrontendOps E W) : M E W Unit := do
  ops.enableInCore true true
  let useFlisp ← ops.getBoolEnv "JULIA_USE_FLISP_LOWERING" true
  if useFlisp == some true then
    ops.activateJuliaLowering false false
  else
    ops.activateJuliaLowering true true

structure MainReplOps (E W Module : Type) where
  fallbackRepl : M E W Bool
  loadInteractiveUtils : M E W (Option Module)
  replModule : M E W Module
  isBase : Module → Bool
  loadRepl : M E W (Option Module)
  runStdRepl : Module → Bool → Banner → Bool → M E W Unit
  warnFallback : M E W Unit
  runFallbackRepl : Bool → M E W Unit

/--
Julia source: base/client.jl:526-546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# run the requested sort of evaluation loop on stdio
function run_main_repl(interactive::Bool, quiet::Bool, banner::Symbol, history_file::Bool)
    fallback_repl = parse(Bool, get(ENV, "JULIA_FALLBACK_REPL", "false"))
    if !fallback_repl && interactive
        load_InteractiveUtils()
        REPL = REPL_MODULE_REF[]
        if REPL === Base
            load_REPL()
        end
    end
    REPL = REPL_MODULE_REF[]
    if !fallback_repl && interactive && REPL !== Base
        invokelatest(run_std_repl, REPL, quiet, banner, history_file)
    else
        if !fallback_repl && interactive && !quiet
            @warn "REPL provider not available: using basic fallback" LOAD_PATH=join(Base.LOAD_PATH, Sys.iswindows() ? ';' : ':')
        end
        run_fallback_repl(interactive)
    end
    nothing
end
```
-/
def runMainRepl {E W Module : Type} (ops : MainReplOps E W Module)
    (interactive quiet : Bool) (banner : Banner) (historyFile : Bool) : M E W Unit := do
  let fallback ← ops.fallbackRepl
  if !fallback && interactive then
    let _ ← ops.loadInteractiveUtils
    if ops.isBase (← ops.replModule) then
      let _ ← ops.loadRepl
  let repl ← ops.replModule
  if !fallback && interactive && !ops.isBase repl then
    ops.runStdRepl repl quiet banner historyFile
  else
    if !fallback && interactive && !quiet then ops.warnFallback
    ops.runFallbackRepl interactive
  pure ()

/--
Julia source: base/client.jl:721-733 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function repl_main(_)
    opts = Base.JLOptions()
    interactiveinput = isa(stdin, Base.TTY)
    b = opts.banner
    auto = b == -1
    banner = b == 0 || (auto && !interactiveinput) ? :no  :
             b == 1 || (auto && interactiveinput)  ? :yes :
             :short # b == 2

    quiet                 = (opts.quiet != 0)
    history_file          = (opts.historyfile != 0)
    return run_main_repl(interactiveinput, quiet, banner, history_file)
end
```
-/
def replMain
    {E W P PP Module Expr Value Distributed TraceMode ExceptionStack Ignored : Type}
    (ops : ClientOps E W P PP Module Expr Value Distributed TraceMode ExceptionStack)
    (_arg : Ignored) : M E W Unit := do
  let interactiveInput ← ops.stdinIsTTY
  let bannerOption := ops.options.banner.val
  let automatic := bannerOption == -1
  let banner :=
    if bannerOption == 0 || (automatic && !interactiveInput) then Banner.no
    else if bannerOption == 1 || (automatic && interactiveInput) then Banner.yes
    else Banner.short
  let quiet := ops.options.quiet.val != 0
  let historyFile := ops.options.historyfile.val != 0
  ops.runMainRepl interactiveInput quiet banner historyFile

structure SessionCancelOps (E W Source Lock : Type) where
  sessionLock : Lock
  lockNoCancel : Lock → M E W Unit
  unlock : Lock → M E W Unit
  getSource : M E W (Option Source)
  setSource : Option Source → M E W Unit
  newSessionSource : M E W Source
  newEvaluationSource : Source → M E W Source
  cancelSource : Source → M E W Unit

/--
Julia source: base/client.jl:603-615 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function session_cancel_source!()
    lock(_session_cancel_lock; cancel=nothing)
    try
        ses = _session_cancel_source[]
        if ses === nothing
            ses = CancellationTokenSource()
            _session_cancel_source[] = ses
        end
        return ses
    finally
        unlock(_session_cancel_lock)
    end
end
```
-/
def sessionCancelSource {E W Source Lock : Type} (ops : SessionCancelOps E W Source Lock) :
    M E W Source := do
  ops.lockNoCancel ops.sessionLock
  JuliaLean.base.locks_mt.finallyDo (do
    match ← ops.getSource with
    | some source => pure source
    | none => do
      let source ← ops.newSessionSource
      ops.setSource (some source)
      pure source) (ops.unlock ops.sessionLock)

/--
Julia source: base/client.jl:617-620 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# A fresh source governing one interactive evaluation, linked under the
# session source.
new_evaluation_cancel_source!() =
    CancellationTokenSource(CancellationToken(session_cancel_source!()))
```
-/
def newEvaluationCancelSource {E W Source Lock : Type}
    (ops : SessionCancelOps E W Source Lock) : M E W Source := do
  ops.newEvaluationSource (← sessionCancelSource ops)

/--
Julia source: base/client.jl:622-642 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    Base.cancel_session_work!() -> Bool

Cancel every still-running piece of work started under the current
interactive session's evaluations (see the session-source tree above) and
start a fresh session epoch. Returns whether there was a session to sweep.
The REPL binds this to a repeated `^C` at an empty prompt.
"""
function cancel_session_work!()
    lock(_session_cancel_lock; cancel=nothing)
    ses = try
        s = _session_cancel_source[]
        _session_cancel_source[] = nothing
        s
    finally
        unlock(_session_cancel_lock)
    end
    ses === nothing && return false
    cancel!(ses)
    return true
end
```
-/
def cancelSessionWork {E W Source Lock : Type} (ops : SessionCancelOps E W Source Lock) :
    M E W Bool := do
  ops.lockNoCancel ops.sessionLock
  let source ← JuliaLean.base.locks_mt.finallyDo (do
    let source ← ops.getSource
    ops.setSource none
    pure source) (ops.unlock ops.sessionLock)
  match source with
  | none => pure false
  | some source =>
    ops.cancelSource source
    pure true

/--
Julia source: base/client.jl:246-361 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function exec_options(opts)
    startup               = (opts.startupfile != 2)
    global have_color     = colored_text(opts)
    global is_interactive = (opts.isinteractive != 0)

    # Enable verbose debugging options when requested by other frameworks
    debug_env_vars = (
        "RUNNER_DEBUG",   # github actions when UI "debug logging" is enabled
        "CI_DEBUG_TRACE", # gitlab CI when UI "debug" toggle is enabled
        "SYSTEM_DEBUG",   # azure pipelines when UI "System diagnostics" is enabled
    )
    for v in debug_env_vars
        if get_bool_env(v, false)
            Base.TRACE_EVAL = Base.TRACE_EVAL === :full ? :full : :loc # Enable --trace-eval (location only)
            ENV["JULIA_TEST_VERBOSE"] = "true" # Set JULIA_TEST_VERBOSE for this session
            break
        end
    end

    # pre-process command line argument list
    arg_is_program = !isempty(ARGS)
    repl = !arg_is_program
    cmds = unsafe_load_commands(opts.commands)
    for (cmd, arg) in cmds
        if cmd_suppresses_program(cmd)
            arg_is_program = false
            repl = false
        elseif cmd == 'L' || cmd == 'm'
            # nothing
        elseif cmd == 'B' # --bug-report
            # If we're doing a bug report, don't load anything else. We will
            # spawn a child in which to execute these options.
            let InteractiveUtils = load_InteractiveUtils()
                invokelatest(InteractiveUtils.report_bug, arg)
            end
            return false
        else
            @warn "Unexpected command -$cmd'$arg'"
        end
    end

    # remove filename from ARGS
    global PROGRAM_FILE = arg_is_program ? popfirst!(ARGS) : ""

    # Load Distributed module only if any of the Distributed options have been specified.
    distributed_mode = (opts.worker == 1) || (opts.nprocs > 0) || (opts.machine_file != C_NULL)
    if distributed_mode
        let Distributed = require(PkgId(UUID((0x8ba89e20_285c_5b6f, 0x9357_94700520ee1b)), "Distributed"))
            MainInclude.Distributed = Distributed
            Core.eval(Main, :(using Base.MainInclude.Distributed))
            invokelatest(Distributed.process_opts, opts)
        end
    end

    interactiveinput = (repl || is_interactive::Bool) && isa(stdin, TTY)
    is_interactive::Bool |= interactiveinput

    # load ~/.julia/config/startup.jl file
    if startup
        try
            load_julia_startup()
        catch
            invokelatest(display_error, scrub_repl_backtrace(current_exceptions()))
            !(repl || is_interactive::Bool) && exit(1)
        end
    end

    # process cmds list
    for (cmd, arg) in cmds
        if cmd == 'e'
            __script_entry_eval(Main, parse_input_line(arg; mod=Main))
        elseif cmd == 'E'
            invokelatest(show, __script_entry_eval(Main, parse_input_line(arg; mod=Main)))
            println()
        elseif cmd == 'm'
            entrypoint = push!(split(arg, "."), "main")
            __script_entry_eval(Main, Expr(:import, Expr(:., Symbol.(entrypoint)...)))
            if !invokelatest(should_use_main_entrypoint)
                error("`main` in `$arg` not declared as entry point (use `@main` to do so)")
            end
            return false
        elseif cmd == 'L'
            # load file immediately on all processors
            if !distributed_mode
                __script_entry_include(Main, arg)
            else
                # TODO: Move this logic to Distributed and use a callback
                @sync for p in invokelatest(Main.procs)
                    @async invokelatest(Main.remotecall_wait, include, p, Main, arg)
                end
            end
        end
    end

    # load file
    if arg_is_program
        # program
        if !is_interactive::Bool
            exit_on_sigint(true)
        end
        try
            if PROGRAM_FILE == "-"
                __script_entry_include_string(Main, read(stdin, String), "stdin")
            else
                __script_entry_include(Main, PROGRAM_FILE)
            end
        catch
            invokelatest(display_error, scrub_repl_backtrace(current_exceptions()))
            if !is_interactive::Bool
                exit(1)
            end
        end
    end

    return repl
end
```
-/
def execOptions
    {E W P PP Module Expr Value Distributed TraceMode ExceptionStack IO Context Error Backtrace : Type}
    (ops : ClientOps E W P PP Module Expr Value Distributed TraceMode ExceptionStack)
    (colors : ColorOps E W)
    (display : DisplayOps E W IO Context Error Backtrace ExceptionStack)
    (entrypoint : EntrypointOps E W Module) :
    M E W Bool := do
  let startup := ops.options.startupfile.val != 2
  let color ← JuliaLean.base.options.colored_text ops.getEnvBytes ops.options
  ops.setHaveColor color
  let initialInteractive := ops.options.isinteractive.val != 0
  ops.setInteractive initialInteractive
  debugEnvLoop ops ["RUNNER_DEBUG", "CI_DEBUG_TRACE", "SYSTEM_DEBUG"]
  let hasProgram ← ops.argsEmpty
  let argIsProgram := !hasProgram
  let repl := hasProgram
  let commands ← ops.unsafeLoadCommands ops.options.commands
  let setup ← processSetupCommands ops argIsProgram repl commands
  match setup with
  | none => pure false
  | some (argIsProgram, repl) => do
      let programFile ← if argIsProgram then ops.popFirstArg else pure (JuliaLean.base.options.lit "")
      ops.setProgramFile programFile
      let distributedMode := ops.options.worker.val == 1 || ops.options.nprocs.val > 0 ||
        !ops.pointer.isNullP ops.options.machine_file
      if distributedMode then do
        let distributed ← ops.requireDistributed
        ops.setMainIncludeDistributed distributed
        ops.usingMainIncludeDistributed
        ops.processDistributedOptions distributed ops.options
      let interactiveInput ← if repl || initialInteractive then ops.stdinIsTTY else pure false
      let interactive := initialInteractive || interactiveInput
      ops.setInteractive interactive
      if startup then
        tryCatch (loadJuliaStartup ops.startup ops.script ops.main) (fun _ => do
          let stack ← ops.currentExceptions
          let stack ← ops.scrubReplBacktrace stack
          let _ ← displayErrorStack colors display display.stderr stack
          if !(repl || interactive) then
            let never ← ops.exit (i64 1)
            nomatch never
          pure ())
      let shouldContinue ← processMainCommands ops entrypoint distributedMode commands
      if !shouldContinue then return false
      if argIsProgram then do
        if !interactive then ops.setExitOnSigint true
        tryCatch (do
          if programFile == JuliaLean.base.options.lit "-" then do
            let code ← ops.readStdin
            let _ ← scriptEntryIncludeString ops.script ops.main code (JuliaLean.base.options.lit "stdin")
          else
            let _ ← scriptEntryInclude ops.script ops.main programFile) (fun _ => do
          let stack ← ops.currentExceptions
          let stack ← ops.scrubReplBacktrace stack
          let _ ← displayErrorStack colors display display.stderr stack
          if !interactive then
            let never ← ops.exit (i64 1)
            nomatch never
          pure ())
      pure repl

structure StartOps (E W Module Args Parser CancelToken Value : Type) where
  prepareArgs : M E W Unit
  clearPostOutputHooks : M E W Unit
  newCancellationEpisode : M E W CancelToken
  parserForActiveProject : M E W Parser
  withStartupScope : Parser → CancelToken → M E W (JInt .i32) → M E W (JInt .i32)
  getArgs : M E W Args
  getGlobalMain : Module → M E W Value
  callMain : Value → Args → M E W Value
  precompileMain : Value → M E W Unit
  generatingOutput : M E W Bool
  setGeneratingOutput : Bool → M E W Bool
  getInteractive : M E W Bool
  isNothing : Value → Bool
  zeroValue : Value
  nothingValue : Value
  toCint : Value → M E W (JInt .i32)
  logInvalidMainReturn : M E W Unit
  runFreshCancellation : M E W Unit → M E W Unit
  closeCancellationEpisode : M E W Unit
  printSystemFailure : M E W Unit
  stdoutHasColor : M E W Bool
  printStdout : String → M E W Unit
  isIOError : E → Bool

/--
Julia source: base/client.jl:653-719 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _start()
    empty!(ARGS)
    append!(ARGS, Core.ARGS)
    # clear any postoutput hooks that were saved in the sysimage
    empty!(Base.postoutput_hooks)
    local ret = 0
    # `--project` has been processed at this point - latch the active project's syntax
    # version and use it for `-L`, `argfile`, etc. If launched, the REPL will re-evaluate
    # at each prompt.
    # The whole foreground execution runs as a ^C episode: a SIGINT (with
    # exit-on-sigint disabled) cancels the episode token's scope. An
    # interactive session installs its own per-evaluation episodes later
    # (see REPL.repl_backend_loop), superseding this one. Deliberately a
    # standalone root, not a session child - see the `sigint_new_episode!`
    # docstring.
    sigint_tok = sigint_new_episode!()
    @Base.ScopedValues.with MainInclude.main_parser=>parser_for_active_project() CANCEL_TOKEN=>sigint_tok try
        repl_was_requested = exec_options(JLOptions())
        if invokelatest(should_use_main_entrypoint) && !is_interactive
            main = invokelatest(getglobal, Main, :main)
            if Base.generating_output()
                precompile(main, (typeof(ARGS),))
            else
                ret = invokelatest(main, ARGS)
            end
        elseif (repl_was_requested || is_interactive)
            # Run the Base `main`, which will either load the REPL stdlib
            # or run the fallback REPL
            ret = repl_main(ARGS)
        end
        ret === nothing && (ret = 0)
        ret = try
            Cint(ret)
        catch
            @error "The return value of `main` should be `nothing` or convertible to `Cint`"
            Cint(1)
        end
    catch
        ret = Cint(1)
        # report the error in a fresh ^C epoch (the script's epoch may be
        # the very cancellation being reported; level-triggered checks in
        # the printing path would re-throw it mid-report)
        local errs = scrub_repl_backtrace(current_exceptions())
        try
            ScopedValues.@with(CANCEL_TOKEN => sigint_new_episode!(),
                               invokelatest(display_error, errs))
        catch
            # The report itself failed - e.g. a further ^C cancelled the
            # display epoch, or a user-defined `show` method errored. The
            # exit code already reflects the original failure; leave a bare
            # note rather than dying with an unhandled exception.
            Core.print(Core.stderr, "\nSYSTEM: displaying the error report failed\n")
        finally
            sigint_close_episode!()
        end
    end
    if is_interactive && get(stdout, :color, false)
        try
            print(color_normal)
        catch e
            # the terminal may be gone by now (that may be why the session ended)
            e isa IOError || rethrow()
        end
    end
    generating_output(false) && init_frontend()
    return ret
end
```
-/
def startClient
    {E W P PP Module Expr Value Distributed TraceMode Stack IO Context Error Backtrace
      Args Parser CancelToken : Type}
    (client : ClientOps E W P PP Module Expr Value Distributed TraceMode Stack)
    (colors : ColorOps E W)
    (display : DisplayOps E W IO Context Error Backtrace Stack)
    (entrypoint : EntrypointOps E W Module)
    (frontend : FrontendOps E W)
    (ops : StartOps E W Module Args Parser CancelToken Value) : M E W (JInt .i32) := do
  ops.prepareArgs
  ops.clearPostOutputHooks
  let cancelToken ← ops.newCancellationEpisode
  let parser ← ops.parserForActiveProject
  let returnCode ← ops.withStartupScope parser cancelToken (tryCatch (do
    let replRequested ← execOptions client colors display entrypoint
    let interactive ← ops.getInteractive
    let value ← if (← shouldUseMainEntrypoint entrypoint client.main) && !interactive then do
        let main ← ops.getGlobalMain client.main
        if ← ops.generatingOutput then
          ops.precompileMain main
          pure ops.zeroValue
        else
          ops.callMain main (← ops.getArgs)
      else if replRequested || interactive then do
        let _ ← replMain client (← ops.getArgs)
        pure ops.nothingValue
      else
        pure ops.zeroValue
    let value := if ops.isNothing value then ops.zeroValue else value
    tryCatch (ops.toCint value) (fun _ => do
      ops.logInvalidMainReturn
      pure (JInt.wrap .i32 1)))
    (fun _ => do
      let stack ← client.currentExceptions
      let stack ← client.scrubReplBacktrace stack
      let _ ← JuliaLean.base.locks_mt.finallyDo
        (tryCatch (ops.runFreshCancellation (displayErrorStack colors display display.stderr stack))
          (fun _ => ops.printSystemFailure))
        ops.closeCancellationEpisode
      pure (JInt.wrap .i32 1)))
  if ← ops.getInteractive then
    if ← ops.stdoutHasColor then
      tryCatch (ops.printStdout colorNormal) (fun error =>
        if ops.isIOError error then pure () else throw error)
  if !(← ops.setGeneratingOutput false) then
    initFrontend frontend
  pure returnCode

-- Reason: Mutable terminal capability flags are owned by the REPL runtime.
-- UNTRANSLATED
-- Source: base/client.jl:1-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- ## client.jl - frontend handling command line options, environment setup,
-- ##             and REPL
-- 
-- have_color = nothing
-- have_truecolor = nothing
-- /Source
--
--
--
-- Reason: The REPL hook registry and its user-facing documentation are runtime state.
-- UNTRANSLATED
-- Source: base/client.jl:395-404 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- const repl_hooks = []
-- 
-- """
--     atreplinit(f)
-- 
-- Register a one-argument function to be called before the REPL interface is initialized in
-- interactive sessions; this is useful to customize the interface. The argument of `f` is the
-- REPL object. This function should be called from within the `.julia/config/startup.jl`
-- initialization file.
-- """
-- /Source

-- Reason: The active REPL values are runtime-managed globals.
-- UNTRANSLATED
-- Source: base/client.jl:445-446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- global active_repl::Any
-- global active_repl_backend = nothing
-- /Source

structure StdReplOps
    (E W Module IO Terminal Repl Display Backend Hook ErrorIO : Type) where
  isWindows : Bool
  getEnv : String → String → M E W String
  stdin : IO
  stdout : IO
  stderr : IO
  ttyTerminal : Module → String → IO → IO → IO → M E W Terminal
  displayBanner : Module → Terminal → Bool → M E W Unit
  terminalType : Terminal → String
  basicRepl : Module → Terminal → M E W Repl
  stdoutColor : M E W Bool
  lineEditRepl : Module → Terminal → Bool → Bool → M E W Repl
  setHistoryFile : Repl → Bool → M E W Unit
  warnTerminal : M E W Unit
  replDisplay : Module → Repl → M E W Display
  activeRepl : M E W (Option Repl)
  setActiveRepl : Option Repl → M E W Unit
  activeBackend : M E W (Option Backend)
  setActiveBackend : Option Backend → M E W Unit
  pushDisplay : Display → M E W Unit
  popDisplay : Display → M E W Unit
  hooks : ReplHookOps E W Repl Hook ErrorIO
  runRepl : Module → Repl → (Backend → M E W Unit) → M E W Unit

/-!
Julia source: base/client.jl:496-524 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function run_std_repl(REPL::Module, quiet::Bool, banner::Symbol, history_file::Bool)
    term_env = get(ENV, "TERM", @static Sys.iswindows() ? "" : "dumb")
    term = REPL.Terminals.TTYTerminal(term_env, stdin, stdout, stderr)
    banner == :no || REPL.banner(term, short=banner==:short)
    if term.term_type == "dumb"
        repl = REPL.BasicREPL(term)
        quiet || @warn "Terminal not fully functional"
    else
        repl = REPL.LineEditREPL(term, get(stdout, :color, false), true)
        repl.history_file = history_file
    end
    # Make sure any displays pushed in .julia/config/startup.jl end up above the
    # REPLDisplay
    d = REPL.REPLDisplay(repl)
    last_active_repl = @isdefined(active_repl) ? active_repl : nothing
    last_active_repl_backend = active_repl_backend
    global active_repl = repl
    pushdisplay(d)
    try
        global active_repl = repl
        _atreplinit(repl)
        REPL.run_repl(repl, backend->(global active_repl_backend = backend))
    finally
        popdisplay(d)
        active_repl = last_active_repl
        global active_repl_backend = last_active_repl_backend
    end
    nothing
end
```
-/
def runStdRepl
    {E W Module IO Terminal Repl Display Backend Hook ErrorIO : Type}
    (ops : StdReplOps E W Module IO Terminal Repl Display Backend Hook ErrorIO)
    (replModule : Module) (quiet : Bool) (banner : Banner)
    (historyFile : Bool) : M E W Unit := do
  let termEnv ← ops.getEnv "TERM" (if ops.isWindows then "" else "dumb")
  let terminal ← ops.ttyTerminal replModule termEnv ops.stdin ops.stdout ops.stderr
  if banner != .no then ops.displayBanner replModule terminal (banner == .short)
  let repl ← if ops.terminalType terminal == "dumb" then do
    let repl ← ops.basicRepl replModule terminal
    if !quiet then ops.warnTerminal
    pure repl
  else do
    let color ← ops.stdoutColor
    let repl ← ops.lineEditRepl replModule terminal color true
    ops.setHistoryFile repl historyFile
    pure repl
  let display ← ops.replDisplay replModule repl
  let previousRepl ← ops.activeRepl
  let previousBackend ← ops.activeBackend
  ops.setActiveRepl (some repl)
  ops.pushDisplay display
  let _ ← JuliaLean.base.locks_mt.finallyDo (do
    ops.setActiveRepl (some repl)
    runReplHooksLatest ops.hooks repl
    ops.runRepl replModule repl (fun backend => ops.setActiveBackend (some backend)))
    (do
      ops.popDisplay display
      ops.setActiveRepl previousRepl
      ops.setActiveBackend previousBackend)
  pure ()

-- Reason: MainInclude's mutable globals and scoped parser belong to module runtime state.
-- UNTRANSLATED
-- Source: base/client.jl:548-567 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # MainInclude exists to weakly add certain identifiers to Main
-- baremodule MainInclude
-- using ..Base
-- 
-- """
--     ans
-- 
-- A variable referring to the last computed value, automatically imported to the interactive prompt.
-- """
-- global ans = nothing
-- 
-- """
--     err
-- 
-- A variable referring to the last thrown errors, automatically imported to the interactive prompt.
-- The thrown errors are collected in a stack of exceptions.
-- """
-- global err = nothing
-- 
-- const main_parser = Base.ScopedValues.ScopedValue{Any}(Base.VersionedParse(Base.VERSION_EDITION))
-- /Source

-- Reason: MainInclude's weak stdlib bindings and exports are module-level runtime state.
-- UNTRANSLATED
-- Source: base/client.jl:572-579 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # Used for memoizing require_stdlib of these modules
-- global InteractiveUtils::Module
-- global Distributed::Module
-- 
-- # weakly exposes ans and err variables to Main
-- export ans, err, var"#_internal_julia_parse"
-- end
-- 
-- /Source
-- Reason: Session cancellation state is supplied through explicit operations.
-- UNTRANSLATED
-- Source: base/client.jl:586-602 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- 
-- ## The interactive session's two-level cancellation-source tree
-- #
-- # An interactive driver (the REPL backend) runs every evaluation under its
-- # own cancellation source, each a child of one long-lived *session* source:
-- # cancelling an evaluation's source stops exactly that evaluation (and
-- # everything it spawned), while cancelling the session source sweeps every
-- # still-running piece of work any evaluation has started - the runaway
-- # `@async` from three prompts ago included. Cancellation is monotonic, so a
-- # swept session source is retired and the next evaluation starts a fresh
-- # session epoch: "everything so far" always means "since the last sweep".
-- 
-- const _session_cancel_source = Ref{Union{Nothing, CancellationTokenSource}}(nothing)
-- const _session_cancel_lock = ReentrantLock()
-- 
-- # The current session source, created on first use (and after each sweep).
-- /Source
-- 
-- 
--
-- Reason: Julia's `@main` macro expands calls and adds a binding in the user's module.
-- UNTRANSLATED
-- Source: base/client.jl:735-802 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     @main
-- 
-- This macro is used to mark that the binding `main` in the current module is considered an
-- entrypoint. The precise semantics of the entrypoint depend on the CLI driver.
-- 
-- In the `julia` driver, if `Main.main` is marked as an entrypoint, it will be automatically called upon
-- the completion of script execution.
-- 
-- The `@main` macro may be used standalone or as part of the function definition.
-- The following are equivalent:
-- 
-- ```
-- function @main(args)
--     println("Hello World")
-- end
-- ```
-- 
-- ```
-- function main(args)
-- end
-- @main
-- ```
-- 
-- ## Detailed semantics
-- 
-- The entrypoint semantics attach to the owner of the binding owner. In particular, if a marked entrypoint is
-- imported into `Main`, it will be treated as an entrypoint in `Main`:
-- 
-- ```
-- module MyApp
--     export main
--     @main(args) = println("Hello World")
-- end
-- using .MyApp
-- # `julia` Will execute MyApp.main at the conclusion of script execution
-- ```
-- 
-- Note that in particular, the semantics do not attach to the method
-- or the name:
-- ```
-- module MyApp
--     @main(args) = println("Hello World")
-- end
-- const main = MyApp.main
-- # `julia` Will *NOT* execute MyApp.main unless there is a separate `@main` annotation in `Main`
-- ```
-- 
-- !!! compat "Julia 1.11"
--     This macro is new in Julia 1.11. At present, the precise semantics of `@main` are still subject to change.
-- """
-- macro main(args...)
--     if isdefined(__module__, :main)
--         if Base.binding_module(__module__, :main) !== __module__
--             error("Symbol `main` is already a resolved import in module $(__module__). `@main` must be used in the defining module.")
--         end
--     end
--     Core.eval(__module__, quote
--         # Force the binding to resolve to this module
--         global main
--         global var"#__main_is_entrypoint__#"::Bool = true
--     end)
--     if !isempty(args)
--         Expr(:call, esc(:main), map(esc, args)...)
--     else
--         esc(:main)
--     end
-- end
-- /Source

end JuliaLean.base.client

section
namespace JuliaLean.RuntimeCov.Client

open JuliaLean.RuntimeCov

/-! ## Colors -/

/-- A key of `Base.text_colors`: an integer or a symbol. -/
inductive ColorKey where
  | int (n : Int)
  | sym (s : Sym)
  deriving DecidableEq, Repr

/-- `repl_color(key, default)`, base/client.jl:16-21: `env` is
`get(ENV, key, "")`, `tryparse` is `tryparse(Int, _)`, `haskey` tests
`text_colors`. -/
def parseColor (env : String) (tryparse : String → Option Int) : ColorKey :=
  match tryparse env with | some n => ColorKey.int n | none => ColorKey.sym env

def replColor (env : String) (tryparse : String → Option Int) (haskey : ColorKey → Bool)
    (default : ColorKey) : ColorKey :=
  let c := parseColor env tryparse
  if haskey c then c else default

/-- The named color queries, base/client.jl:23-32: environment variable and default. -/
def colorSettings : List (String × ColorKey) :=
  [("JULIA_ERROR_COLOR", .sym "light_red"), ("JULIA_WARN_COLOR", .sym "yellow"),
   ("JULIA_INFO_COLOR", .sym "cyan"), ("JULIA_DEBUG_COLOR", .sym "blue"),
   ("JULIA_INPUT_COLOR", .sym "normal"), ("JULIA_ANSWER_COLOR", .sym "normal"),
   ("JULIA_STACKFRAME_LINEINFO_COLOR", .sym "bold"), ("JULIA_STACKFRAME_FUNCTION_COLOR", .sym "bold")]

/-- `error_color()` … `stackframe_function_color()`: `repl_color` of the
setting's variable and default; `input_color`/`answer_color` index
`text_colors` with the result. -/
def namedColor (env : String → String) (tryparse : String → Option Int) (haskey : ColorKey → Bool)
    (setting : String × ColorKey) : ColorKey :=
  replColor (env setting.1) tryparse haskey setting.2
def colorCode (textColors : ColorKey → String) (env : String → String) (tryparse : String → Option Int)
    (haskey : ColorKey → Bool) (setting : String × ColorKey) : String :=
  textColors (namedColor env tryparse haskey setting)

/-! ## Shell mode -/

/-- What `repl_cmd` does. -/
inductive ShellAction where
  | runDirect
  | cd (dir : String) (oldpwd : Option String)
  | runShell (argv : List String)
  deriving DecidableEq, Repr

/-- The command handed to `repl_cmd`. -/
inductive CmdArg where
  | cmd (exec : List String)
  | pipeline
  | notACmd

/-- `repl_cmd(cmd, out)`, base/client.jl:34-91: `oldpwdEnv` is `ENV["OLDPWD"]`,
`pwd` the current directory (`none` if `pwd()` throws `IOError`), `shell` the
split `JULIA_SHELL`/`SHELL` command, `escape` `shell_escape_posixly`. -/
def replCmd (c : CmdArg) (iswindows : Bool) (oldpwdEnv : Option String) (home : String)
    (pwd : Option String) (shell : List String) (escape : List String → String) : Rt ShellAction :=
  match c with
  | .notACmd => .error (.argumentError "repl_cmd: expected an `AbstractCmd`")
  | .pipeline => .ok .runDirect
  | .cmd [] => .error (.argumentError "no cmd to execute")
  | .cmd (x :: rest) =>
    if x = "cd" then
      if rest.length > 1 then .error (.argumentError "cd method only takes one argument")
      else
        let dir : Rt String := match rest with
          | [d] => if d = "-" then (match oldpwdEnv with
              | none => .error (.errorException "cd: OLDPWD not set")
              | some o => .ok o) else .ok d
          | _ => .ok home
        match dir with
        | .error e => .error e
        | .ok d => .ok (.cd d pwd)
    else if iswindows then .ok .runDirect
    else .ok (.runShell (shell ++ ["-c", escape (x :: rest)]))

/-! ## Backtraces -/

/-- A stack frame as the scrubbing code sees it. -/
structure Frame where
  func : String
  fromC : Bool
  unknown : Bool
  modBaseOrCore : Bool
  deriving DecidableEq, Repr

/-- `ip_matches_func(ip, func)`, base/client.jl:94-102, over the frames of `ip`. -/
def ipMatchesFunc (frames : List Frame) (func : String) : Bool :=
  match frames with
  | [] => false
  | fr :: rest => if fr.unknown || fr.fromC then false else if fr.func = func then true
                  else ipMatchesFunc rest func

/-- `is_driver_entry(frame)`, base/client.jl:109-111. -/
def isDriverEntry (f : Frame) : Bool :=
  !f.fromC && ("__repl_entry".isPrefixOf f.func || "__script_entry".isPrefixOf f.func)

/-- `is_driver_machinery(frame)`, base/client.jl:115-120. -/
def isDriverMachinery (f : Frame) : Bool :=
  !f.fromC && f.modBaseOrCore &&
    f.func ∈ ["eval", "include_string", "_include", "include", "fl_toplevel_eval"]

/-- Pop machinery frames from the end (`while ... pop!`). -/
def popMachinery (bt : List Frame) : List Frame :=
  (bt.reverse.dropWhile isDriverMachinery).reverse

/-- Index of the last driver-entry frame (`findlast`). -/
def findLastEntry (bt : List Frame) : Option Nat :=
  ((List.range bt.length).filter (fun i => isDriverEntry (bt.getD i ⟨"", false, false, false⟩))).getLast?

/-- `scrub_repl_backtrace(bt)`, base/client.jl:122-135. -/
def scrubBacktrace (bt : List Frame) : List Frame :=
  match findLastEntry bt with
  | none => bt
  | some i => popMachinery (bt.take i)

/-- `scrub_repl_backtrace(stack::ExceptionStack)`, base/client.jl:136-137. -/
def scrubStack {ε : Type} (stack : List (ε × List Frame)) : List (ε × List Frame) :=
  stack.map fun p => (p.1, scrubBacktrace p.2)

/-- `istrivialerror(stack)`, base/client.jl:139-140. -/
def istrivialerror (stack : List (Bool × List Frame)) : Bool :=
  match stack with
  | [(isMethodError, bt)] => bt.length ≤ 1 && !isMethodError
  | _ => false

/-- `display_error(io, stack)` and the other `display_error` methods,
base/client.jl:143-156: `"ERROR: "` then the shown exceptions, then a newline. -/
def displayError (shown : String) : String := "ERROR: " ++ shown ++ "\n"

/-- `__script_entry_include`, `__script_entry_include_string`,
`__script_entry_eval`, `__repl_entry_client_eval`, base/client.jl:104-107,159:
delegate to `_include`/`include_string`/`Core.eval` unchanged. -/
def entryDelegate {α β : Type} (f : α → β) (x : α) : β := f x

/-! ## Parsing and evaluation -/

/-- A parse result: a top-level block of statements, or a single node. -/
inductive Parsed where
  | toplevel (children : List Parsed)
  | error
  | incomplete
  | node (n : Nat)
  deriving Repr

def Parsed.isIncomplete : Parsed → Bool
  | .incomplete => true
  | _ => false

def Parsed.isBad : Parsed → Bool
  | .error | .incomplete => true
  | _ => false

/-- `_parse_input_line_core`, base/client.jl:215-231. -/
def parseInputLineCore (ex : Parsed) : Parsed :=
  match ex with
  | .toplevel cs => match cs.getLast? with
    | some last => if last.isBad then last else ex
    | none => ex
  | _ => ex

/-- `parse_input_line(s; depwarn)`, base/client.jl:233-244: the logger choice
does not change the result. -/
def parseInputLine (parse : String → Parsed) (_depwarn : Bool) (s : String) : Parsed :=
  parseInputLineCore (parse s)

/-- Outcome of evaluating or displaying in `eval_user_input`. -/
inductive Outcome where
  | ok
  | throws
  deriving DecidableEq, Repr

/-- `eval_user_input(errio, ast, show_value)`, base/client.jl:161-213: returns
the number of error-display attempts made. The first try evaluates; every
later try displays the last error; it gives up after three failures. -/
def evalUserInput (evalOutcome : Outcome) (displayOutcomes : List Outcome) : Nat :=
  match evalOutcome with
  | .ok => 0
  | .throws =>
    let rec go : Nat → List Outcome → Nat
      | errcount, [] => errcount
      | errcount, o :: os => if errcount > 2 then errcount
        else match o with | .ok => errcount | .throws => go (errcount + 1) os
    min 3 (go 1 displayOutcomes)

/-! ## Command-line processing -/

/-- The decisions of `exec_options(opts)`, base/client.jl:246-361. -/
structure ExecPlan where
  programFile : String
  argsLeft : List String
  repl : Bool
  bugReport : Bool
  deriving DecidableEq, Repr

/-- The pre-processing loop of `exec_options`: `cmds` are the `-e`, `-E`,
`-L`, `-m`, `-B` options. -/
def execOptions (args : List String) (cmds : List (Char × String)) : ExecPlan :=
  let isProgram0 := !args.isEmpty
  let rec scan : List (Char × String) → Bool → Bool → Option (Bool × Bool)
    | [], p, r => some (p, r)
    | (c, _) :: cs, p, r =>
      if c = 'e' || c = 'E' then scan cs false false
      else if c = 'B' then none
      else scan cs p r
  match scan cmds isProgram0 (!isProgram0) with
  | none => ⟨"", args, false, true⟩
  | some (isProgram, repl) =>
    match isProgram, args with
    | true, a :: rest => ⟨a, rest, repl, false⟩
    | _, _ => ⟨"", args, repl, false⟩

/-- `_global_julia_startup_file()`, base/client.jl:363-377. -/
def globalStartupFile (sysconfdirEmpty : Bool) (p1 p2 : String) (isfile : String → Bool) : Option String :=
  if !sysconfdirEmpty && isfile p1 then some p1
  else if !sysconfdirEmpty && p1 = p2 then none
  else if isfile p2 then some p2 else none

/-- `_local_julia_startup_file()`, base/client.jl:379-385: `config/startup.jl`
in `DEPOT_PATH[1]`. -/
def localStartupFile (depots : List String) (startupIn : String → String) (isfile : String → Bool) :
    Option String :=
  match depots with
  | [] => none
  | d :: _ => if isfile (startupIn d) then some (startupIn d) else none

/-- `load_julia_startup()`, base/client.jl:387-393: the files included, global first. -/
def loadJuliaStartup (g l : Option String) : List String := g.toList ++ l.toList

/-! ## REPL hooks and drivers -/

/-- `atreplinit(f)`, base/client.jl:405. -/
def atreplinit (hooks : List Nat) (f : Nat) : List Nat := f :: hooks
/-- `__atreplinit(repl)` and `_atreplinit`, base/client.jl:407-417: calls in list order. -/
def runReplHooks (hooks : List Nat) : List Nat := hooks

/-- `load_InteractiveUtils(mod)`, base/client.jl:419-433: `none` when the
stdlib cannot be required (a warning is logged). -/
def loadInteractiveUtils (already : Bool) (requireOk : Bool) : Option Unit :=
  if already || requireOk then some () else none
/-- `load_REPL()`, base/client.jl:435-443. -/
def loadREPL (requireOk : Bool) : Option Unit := if requireOk then some () else none

/-- Which driver `run_main_repl` uses, base/client.jl:527-546, and whether it warns. -/
inductive Driver where
  | std
  | fallback (warned : Bool)
  deriving DecidableEq, Repr

def runMainRepl (fallbackEnv interactive quiet replAvailable : Bool) : Driver :=
  if !fallbackEnv && interactive && replAvailable then .std
  else .fallback (!fallbackEnv && interactive && !quiet)

/-- `run_fallback_repl(interactive)`, base/client.jl:448-494: a file input is
parsed whole and each top-level statement evaluated in order; otherwise lines
are accumulated until the parse is complete. -/
def fallbackStatements (whole : Parsed) : List Parsed :=
  match whole with
  | .toplevel cs => cs
  | ex => [ex]

def accumulateLines (parse : String → Parsed) : String → List String → String × List String
  | acc, [] => (acc, [])
  | acc, l :: ls =>
    let acc := acc ++ l
    if (parse acc).isIncomplete then accumulateLines parse acc ls else (acc, ls)

/-- `run_std_repl(REPL, quiet, banner, history_file)`, base/client.jl:496-524:
the basic REPL for a dumb terminal, the line editor otherwise; the previously
active REPL is restored afterwards. -/
def runStdRepl (term : String) (prev : Option Nat) (this : Nat) : Bool × Option Nat × Option Nat :=
  (term = "dumb", some this, prev)

/-- `var"#_internal_julia_parse"(args...)`, base/client.jl:568-570: calls the
parser held by `main_parser`. -/
def internalParse {α β : Type} (parser : α → β) (args : α) : β := parser args

/-- `should_use_main_entrypoint()`, base/client.jl:580-585. -/
def shouldUseMainEntrypoint (mainDefined : Bool) (ownerFlag : Option Bool) : Bool :=
  mainDefined && ownerFlag = some true

/-! ## Session cancellation -/

/-- `session_cancel_source!()`, base/client.jl:603-615: reuse or create. -/
def sessionCancelSource (cur : Option Nat) (fresh : Nat) : Nat × Option Nat :=
  match cur with
  | some s => (s, some s)
  | none => (fresh, some fresh)

/-- `new_evaluation_cancel_source!()`, base/client.jl:619-620: a child of the session source. -/
def newEvaluationCancelSource (cur : Option Nat) (fresh child : Nat) : (Nat × Nat) × Option Nat :=
  let (ses, st) := sessionCancelSource cur fresh
  ((child, ses), st)

/-- `cancel_session_work!()`, base/client.jl:630-642: the source cancelled and
the new state. -/
def cancelSessionWork (cur : Option Nat) : Bool × Option Nat × Option Nat :=
  match cur with
  | none => (false, none, none)
  | some s => (true, some s, none)

/-- `init_frontend()`, base/client.jl:644-651: the lowering choice. -/
def initFrontend (useFlisp : Bool) : Bool := !useFlisp

/-! ## `_start`, `repl_main`, `@main` -/

/-- `_start()`, base/client.jl:653-719: the exit code. `mainRet` is the
result of `main(ARGS)` or the REPL (`none` = `nothing`), `conv` the
conversion to `Cint`; a thrown error gives 1. -/
def start (threw : Bool) (mainRet : Option Int) (conv : Int → Option Int) : Int :=
  if threw then 1 else
  let r := mainRet.getD 0
  (conv r).getD 1

/-- `repl_main(_)`, base/client.jl:721-733: the banner choice. -/
inductive Banner where
  | no
  | yes
  | short
  deriving DecidableEq, Repr

def replBanner (b : Int) (interactiveInput : Bool) : Banner :=
  let auto := b == -1
  if b == 0 || (auto && !interactiveInput) then .no
  else if b == 1 || (auto && interactiveInput) then .yes
  else .short

/-- `@main(args...)`, base/client.jl:786-802: errors when `main` is an
imported binding; otherwise marks the entrypoint and returns `main` or the call. -/
def mainMacro (mainDefined importedMain : Bool) (args : List Nat) : Rt (Bool × Option (List Nat)) :=
  if mainDefined && importedMain then
    .error (.errorException "Symbol `main` is already a resolved import in module. `@main` must be used in the defining module.")
  else .ok (true, if args.isEmpty then none else some args)
end JuliaLean.RuntimeCov.Client
end

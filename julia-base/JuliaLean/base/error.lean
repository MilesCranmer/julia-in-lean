import JuliaLean.Core
import JuliaLean.Float.Basic

/-!
# Typed model of `base/error.jl` at Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`.

Runtime calls and Julia's dynamic dispatch are typed interfaces. Backtrace words, managed stack
values, exception results, and the random `Float64` stream remain typed in the model.
-/

namespace JuliaLean.base.error

open JuliaLean JuliaLean.Float

inductive JuliaException where
  | errorException (message : String)
  | argumentError (message : String)
  | assertionError (message : String)
  | boundsError
  | typeError
  | methodError (method : String) (arguments : List String) (worldAge : Nat)
  | systemError (functionName : String) (errno : Int) (extraInfo : String)
  | windowsSystemError (functionName : String) (code : BitVec 32) (extraInfo : String)
  deriving Repr, DecidableEq

inductive ErrorArgument where
  | abstractString (text : String)
  | other (stringValue : String)
  deriving Repr, DecidableEq

namespace ErrorArgument

def stringValue : ErrorArgument → String
  | .abstractString text => text
  | .other text => text

end ErrorArgument

-- UNTRANSLATED
-- Source: base/error.jl:30-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # NOTE It is important to always be able to infer the return type of `error` as `Union{}`,
-- # see issue (JuliaLang/julia#54029). Ensure that method counts are small enough with
-- # respect to the `max_methods` value of the function.
-- function error end
-- /Source
-- Reason: this generic function declaration has no method body in this file.
-- UNTRANSLATED
-- Source: base/error.jl:35-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     error(message::AbstractString)
-- 
-- Raise an `ErrorException` with the given message.
-- """
-- error(::AbstractString)
-- /Source
-- Reason: Julia provides the `AbstractString` overload at runtime.
/--
Julia source: base/error.jl:42-57 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    error(msg...)

Raise an `ErrorException` with a message constructed by `string(msg...)`.
"""
function error(s::Vararg{Any,N}) where {N}
    @noinline
    exc = if s === ()
        ErrorException("")
    elseif s isa Tuple{AbstractString}
        ErrorException(s...)
    else
        ErrorException(Main.Base.string(s...))
    end
    throw(exc)
end
```
-/
def errorVararg {α : Type} (arguments : List ErrorArgument) : Except JuliaException α :=
  let exception :=
    match arguments with
    | [] => .errorException ""
    | [.abstractString message] => .errorException message
    | arguments => .errorException (String.intercalate "" (arguments.map ErrorArgument.stringValue))
  .error exception

/-- A runtime primitive called by the source's body-less `throw` declaration. -/
def throwException {Exception α : Type} (exception : Exception) : Except Exception α :=
  .error exception
structure ExceptionContext (Exception Trace : Type) where
  exception : Exception
  backtrace : Trace

-- UNTRANSLATED
-- Source: base/error.jl:19-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- """
--     throw(e)
-- 
-- Throw an object as an exception.
-- 
-- See also [`rethrow`](@ref), [`error`](@ref).
-- """
-- throw
-- /Source
-- Reason: `throw` is a runtime-provided builtin declaration.

/--
Julia source: base/error.jl:59-73 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    rethrow()

Rethrow the current exception from within a `catch` block. The rethrown
exception will continue propagation as if it had not been caught.

!!! note
    The alternative form `rethrow(e)` allows you to associate an alternative
    exception object `e` with the current backtrace. However this misrepresents
    the program state at the time of the error so you're encouraged to instead
    throw a new exception using `throw(e)`. In Julia 1.1 and above, using
    `throw(e)` will preserve the root cause exception on the stack, as
    described in [`current_exceptions`](@ref).
"""
rethrow() = ccall(:jl_rethrow, Bottom, ())
```
-/
def rethrowCurrent {Exception Trace α : Type} (current : ExceptionContext Exception Trace) :
    Except (ExceptionContext Exception Trace) α := .error current

/--
Julia source: base/error.jl:74-74 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
rethrow(@nospecialize(e)) = ccall(:jl_rethrow_other, Bottom, (Any,), e)
```
-/
def rethrowOther {Exception Trace α : Type} (current : ExceptionContext Exception Trace)
    (replacement : Exception) : Except (ExceptionContext Exception Trace) α :=
  .error { current with exception := replacement }

abbrev BacktraceWord := BitVec 64

inductive InterpreterCode where
  | codeInfo (identity : Nat)
  | methodInstance (identity : Nat)
  | codeInstance (identity : Nat)
  | nothing
  deriving Repr, DecidableEq

inductive BacktraceManaged where
  | code (value : InterpreterCode)
  | module (name : String)
  | nothing
  | other
  deriving Repr, DecidableEq

structure InterpreterIP where
  code : InterpreterCode
  statement : Nat
  module : Option String
  deriving Repr, DecidableEq

inductive BacktraceLocation where
  | native (address : BacktraceWord)
  | interpreter (ip : InterpreterIP)
  deriving Repr, DecidableEq

/-- Julia array indexing used by the source's one-based runtime buffers. -/
def arrayGet1 {α : Type} (values : Array α) (index : Nat) : Except JuliaException α :=
  match values[index - 1]? with
  | some value => .ok value
  | none => .error .boundsError

def managedCode : BacktraceManaged → Except JuliaException InterpreterCode
  | .code value => .ok value
  | .nothing => .ok .nothing
  | .module _ | .other => .error .typeError

def managedModule : BacktraceManaged → Except JuliaException (Option String)
  | .module name => .ok (some name)
  | .nothing => .ok none
  | .code _ | .other => .error .typeError

def reformatBacktraceLoop (bt : Array BacktraceWord) (bt2 : Array BacktraceManaged)
    (i j : Nat) (ret : Array BacktraceLocation) :
    Except JuliaException (Array BacktraceLocation) := do
  if i <= bt.size then
    let ip ← arrayGet1 bt i
    if ip != BitVec.ofNat 64 (2 ^ 64 - 1) then
      reformatBacktraceLoop bt bt2 (i + 1) j (ret.push (.native ip))
    else
      let entryMetadata ← arrayGet1 bt (i + 1)
      let njlvalues := (entryMetadata &&& BitVec.ofNat 64 7).toNat
      let nuintvals := ((entryMetadata >>> 3) &&& BitVec.ofNat 64 7).toNat
      let tag := ((entryMetadata >>> 6) &&& BitVec.ofNat 64 15).toNat
      let header := (entryMetadata >>> 10).toNat
      if tag == 1 then
        let codeValue ← arrayGet1 bt2 j
        let code ← managedCode codeValue
        let moduleValue ← if njlvalues == 2 then do
          let value ← arrayGet1 bt2 (j + 1)
          managedModule value
        else pure none
        reformatBacktraceLoop bt bt2 (i + 2 + njlvalues + nuintvals)
          (j + njlvalues) (ret.push (.interpreter ⟨code, header, moduleValue⟩))
      else
        throw (.argumentError s!"Unexpected extended backtrace entry tag {tag} at bt[{i}]")
  else pure ret
termination_by bt.size + 1 - i
decreasing_by all_goals omega

/--
Julia source: base/error.jl:84-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _reformat_bt(bt::Array{Ptr{Cvoid},1}, bt2::Array{Any,1})
    ret = Vector{Union{InterpreterIP,Ptr{Cvoid}}}()
    i, j = 1, 1
    while i <= length(bt)
        ip = bt[i]::Ptr{Cvoid}
        if UInt(ip) != (-1 % UInt) # See also jl_bt_is_native
            # native frame
            push!(ret, ip)
            i += 1
            continue
        end
        # Extended backtrace entry
        entry_metadata = reinterpret(UInt, bt[i+1])::UInt
        njlvalues =  entry_metadata & 0x7
        nuintvals = (entry_metadata >> 3) & 0x7
        tag       = (entry_metadata >> 6) & 0xf
        header    =  entry_metadata >> 10
        if tag == 1 # JL_BT_INTERP_FRAME_TAG
            code = bt2[j]::Union{CodeInfo,Core.MethodInstance,Core.CodeInstance,Nothing}
            mod = njlvalues == 2 ? bt2[j+1]::Union{Module,Nothing} : nothing
            push!(ret, InterpreterIP(code, header, mod))
        else
            # Tags we don't know about are an error
            throw(ArgumentError("Unexpected extended backtrace entry tag $tag at bt[$i]"))
        end
        # See jl_bt_entry_size
        j += Int(njlvalues)
        i += 2 + Int(njlvalues + nuintvals)
    end
    ret
end
```
-/
def reformatBacktrace (bt : Array BacktraceWord) (bt2 : Array BacktraceManaged) :
    Except JuliaException (Array BacktraceLocation) :=
  reformatBacktraceLoop bt bt2 1 1 #[]

/--
Julia source: base/error.jl:116-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    backtrace()

Get a backtrace object for the current program point.
"""
function backtrace()
    @noinline
    # skip frame for backtrace(). Note that for this to work properly,
    # backtrace() itself must not be interpreted nor inlined.
    skip = 1
    bt1, bt2 = ccall(:jl_backtrace_from_here, Ref{SimpleVector}, (Cint, Cint), false, skip)
    return _reformat_bt(bt1::Vector{Ptr{Cvoid}}, bt2::Vector{Any})
end
```
-/
def backtrace (jlBacktraceFromHere : Bool → Nat → Array BacktraceWord × Array BacktraceManaged) :
    Except JuliaException (Array BacktraceLocation) := do
  let skip := 1
  let (bt1, bt2) := jlBacktraceFromHere false skip
  reformatBacktrace bt1 bt2

/--
Julia source: base/error.jl:130-155 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    catch_backtrace()

Get the backtrace of the current exception, for use within `catch` blocks.

The result is a raw backtrace in the same format as [`backtrace`](@ref), but for the point
where the exception was thrown. Pass it to [`stacktrace`](@ref) to get a vector of
[`StackFrame`](@ref Base.StackTraces.StackFrame)s, or to [`showerror`](@ref) to print the
exception together with its stack trace.

See also [`current_exceptions`](@ref) to get all exceptions currently being handled, along
with their backtraces.

# Examples
```julia
try
    error("oops")
catch e
    showerror(stderr, e, catch_backtrace())
end
```
"""
function catch_backtrace()
    bt, bt2 = ccall(:jl_get_backtrace, Ref{SimpleVector}, ())
    return _reformat_bt(bt::Vector{Ptr{Cvoid}}, bt2::Vector{Any})
end
````
-/
def catchBacktrace (jlGetBacktrace : Unit → Array BacktraceWord × Array BacktraceManaged) :
    Except JuliaException (Array BacktraceLocation) := do
  let (bt, bt2) := jlGetBacktrace ()
  reformatBacktrace bt bt2

structure ExceptionStackEntry (E : Type) where
  exception : E
  backtrace : Option (Array BacktraceLocation)
  deriving Repr, DecidableEq

structure ExceptionStack (E : Type) where
  stack : Array (ExceptionStackEntry E)
  deriving Repr, DecidableEq

inductive ExceptionStackValue (E : Type) where
  | exception (value : E)
  | backtracePointers (value : Array BacktraceWord)
  | backtraceValues (value : Array BacktraceManaged)
  | other
  deriving Repr, DecidableEq

def stackException {E : Type} : ExceptionStackValue E → Except JuliaException E
  | .exception value => .ok value
  | .backtracePointers _ | .backtraceValues _ | .other => .error .typeError

def stackBacktracePointers {E : Type} : ExceptionStackValue E → Except JuliaException (Array BacktraceWord)
  | .backtracePointers value => .ok value
  | .exception _ | .backtraceValues _ | .other => .error .typeError

def stackBacktraceValues {E : Type} : ExceptionStackValue E → Except JuliaException (Array BacktraceManaged)
  | .backtraceValues value => .ok value
  | .exception _ | .backtracePointers _ | .other => .error .typeError

def currentExceptionEntry {E : Type} (raw : Array (ExceptionStackValue E))
    (backtrace : Bool) (i : Nat) : Except JuliaException (ExceptionStackEntry E) := do
  let excValue ← arrayGet1 raw i
  let exc ← stackException excValue
  let bt ← if backtrace then do
    let pointerValue ← arrayGet1 raw (i + 1)
    let managedValue ← arrayGet1 raw (i + 2)
    let bt1 ← stackBacktracePointers pointerValue
    let bt2 ← stackBacktraceValues managedValue
    let formattedBacktrace ← reformatBacktrace bt1 bt2
    pure (some formattedBacktrace)
  else pure none
  pure ⟨exc, bt⟩

def currentExceptionsLoop {E : Type} (raw : Array (ExceptionStackValue E))
    (backtrace : Bool) (stride : Nat) :
    List Nat → Array (ExceptionStackEntry E) → Except JuliaException (Array (ExceptionStackEntry E))
  | [], formatted => .ok formatted
  | k :: rest, formatted => do
      let entry ← currentExceptionEntry raw backtrace (1 + k * stride)
      currentExceptionsLoop raw backtrace stride rest (formatted.push entry)

/--
Julia source: base/error.jl:161-189 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    current_exceptions(task::Task=current_task(); [backtrace::Bool=true])

Get the stack of exceptions currently being handled. For nested catch blocks
there may be more than one current exception in which case the most recently
thrown exception is last in the stack. The stack is returned as an
`ExceptionStack` which is an AbstractVector of named tuples
`(exception,backtrace)`. If `backtrace` is false, the backtrace in each pair
will be set to `nothing`.

Explicitly passing `task` will return the current exception stack on an
arbitrary task. This is useful for inspecting tasks which have failed due to
uncaught exceptions.

!!! compat "Julia 1.7"
    This function went by the experimental name `catch_stack()` in Julia
    1.1–1.6, and had a plain Vector-of-tuples as a return type.
"""
function current_exceptions(task::Task=current_task(); backtrace::Bool=true)
    raw = ccall(:jl_get_excstack, Any, (Any,Cint,Cint), task, backtrace, typemax(Cint))::Vector{Any}
    formatted = NamedTuple{(:exception, :backtrace)}[]
    stride = backtrace ? 3 : 1
    for i = reverse(1:stride:length(raw))
        exc = raw[i]
        bt = backtrace ? Base._reformat_bt(raw[i+1],raw[i+2]) : nothing
        push!(formatted, (exception=exc,backtrace=bt))
    end
    ExceptionStack(formatted)
end
```
-/
def currentExceptions {Task E : Type} (currentTask : Task)
    (jlGetExcStack : Task → Bool → Int → Array (ExceptionStackValue E))
    (task : Task := currentTask) (backtrace : Bool := true) :
    Except JuliaException (ExceptionStack E) := do
  let raw := jlGetExcStack task backtrace 2147483647
  let stride := if backtrace then 3 else 1
  let count := (raw.size + stride - 1) / stride
  let formatted ← currentExceptionsLoop raw backtrace stride (List.range count).reverse #[]
  return ⟨formatted⟩

/--
Julia source: base/error.jl:191-195 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
## keyword arg lowering generates calls to this ##
function kwerr(kw, args::Vararg{Any,N}) where {N}
    @noinline
    throw(MethodError(Core.kwcall, (kw, args...), tls_world_age()))
end
```
-/
def kwerr {α : Type} (keyword : String) (arguments : List String) (worldAge : Unit → Nat) :
    Except JuliaException α :=
  throwException (.methodError "Core.kwcall" (keyword :: arguments) (worldAge ()))

/--
Julia source: base/error.jl:205-205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
systemerror(p, errno::Cint=Libc.errno(); extrainfo=nothing) = throw(Main.Base.SystemError(string(p), errno, extrainfo))
```
-/
def systemerrorErrno {P α : Type} (string : P → String) (p : P) (errno : Int)
    (extraInfo : String) : Except JuliaException α :=
  throwException (.systemError (string p) errno extraInfo)

/--
Julia source: base/error.jl:198-204 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    systemerror(sysfunc[, errno::Cint=Libc.errno()])
    systemerror(sysfunc, iftrue::Bool)

Raises a `SystemError` for `errno` with the descriptive string `sysfunc` if `iftrue` is `true`
"""
systemerror(p, b::Bool; extrainfo=nothing) = b ? systemerror(p, extrainfo=extrainfo) : nothing
```
-/
def systemerrorBool {P : Type} (string : P → String) (errnoNow : Unit → Int) (p : P)
    (iftrue : Bool) (extraInfo : String) : Except JuliaException Unit :=
  if iftrue then systemerrorErrno string p (errnoNow ()) extraInfo else .ok ()

structure WindowsErrorInfo where
  errnum : BitVec 32
  extrainfo : String
  deriving Repr, DecidableEq

/--
Julia source: base/error.jl:220-220 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
windowserror(p, code::UInt32=Libc.GetLastError(); extrainfo=nothing) = throw(Main.Base.SystemError(string(p), 0, WindowsErrorInfo(code, extrainfo)))
```
-/
def windowserrorCode {P α : Type} (string : P → String) (p : P) (code : BitVec 32)
    (extraInfo : String) : Except JuliaException α :=
  throwException (.windowsSystemError (string p) code extraInfo)

/--
Julia source: base/error.jl:212-219 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    windowserror(sysfunc[, code::UInt32=Libc.GetLastError()])
    windowserror(sysfunc, iftrue::Bool)

Like [`systemerror`](@ref), but for Windows API functions that use [`GetLastError`](@ref Base.Libc.GetLastError) to
return an error code instead of setting [`errno`](@ref Base.Libc.errno).
"""
windowserror(p, b::Bool; extrainfo=nothing) = b ? windowserror(p, extrainfo=extrainfo) : nothing
```
-/
def windowserrorBool {P : Type} (string : P → String) (getLastError : Unit → BitVec 32)
    (p : P) (iftrue : Bool) (extraInfo : String) : Except JuliaException Unit :=
  if iftrue then windowserrorCode string p (getLastError ()) extraInfo else .ok ()

inductive AssertExpression where
  | string (text : String)
  | expression (text : String)
  | symbol (name : String)
  | other (text : String)
  | quoted (expression : AssertExpression)
  | escaped (expression : AssertExpression)
  deriving Repr, DecidableEq

inductive AssertMessage where
  | literal (text : String)
  | runtimeStringify (expression : AssertExpression)
  | quotedStringify (expression : AssertExpression)
  deriving Repr, DecidableEq

structure AssertExpansion where
  condition : AssertExpression
  message : AssertMessage
  deriving Repr, DecidableEq

/--
Julia source: base/error.jl:226-263 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    @assert cond [text]

Throw an [`AssertionError`](@ref) if `cond` is `false`. This is the preferred syntax for
writing assertions, which are conditions that are assumed to be true, but that the user
might decide to check anyways, as an aid to debugging if they fail.
The optional message `text` is displayed upon assertion failure.

!!! warning
    An assert might be disabled at some optimization levels.
    Assert should therefore only be used as a debugging tool
    and not used for authentication verification (e.g., verifying passwords or checking array bounds).
    The code must not rely on the side effects of running `cond` for the correct behavior
    of a function.

# Examples
```jldoctest
julia> @assert iseven(3) "3 is an odd number!"
ERROR: AssertionError: 3 is an odd number!

julia> @assert isodd(3) "What even are numbers?"
```
"""
macro assert(ex, msgs...)
    msg = isempty(msgs) ? ex : msgs[1]
    if isa(msg, AbstractString)
        msg = msg # pass-through
    elseif !isempty(msgs) && (isa(msg, Expr) || isa(msg, Symbol))
        # message is an expression needing evaluating
        msg = :($_assert_tostring($(esc(msg))))
    elseif isdefined(Main, :Base) && isdefined(Main.Base, :string) && applicable(Main.Base.string, msg)
        msg = Main.Base.string(msg)
    else
        # string() might not be defined during bootstrap
        msg = :($_assert_tostring($(Expr(:quote,msg))))
    end
    return :($(esc(ex)) ? $(nothing) : throw(AssertionError($msg)))
end
````
-/
def assertMacro (condition : AssertExpression) (messages : List AssertExpression)
    (baseStringAvailable : Bool) (baseStringApplicable : AssertExpression → Bool)
    (baseString : AssertExpression → String) : AssertExpansion :=
  let message := if messages.isEmpty then condition else messages.headD condition
  let selectedMessage :=
    match message with
    | .string text => .literal text
    | .expression _ | .symbol _ =>
        if !messages.isEmpty then .runtimeStringify message
        else if baseStringAvailable && baseStringApplicable message then .literal (baseString message)
        else .quotedStringify message
    | .quoted _ | .escaped _ | .other _ =>
        if baseStringAvailable && baseStringApplicable message then .literal (baseString message)
        else .quotedStringify message
  ⟨.escaped condition, selectedMessage⟩

/--
Julia source: base/error.jl:267-268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
__assert_tostring(msg) = isdefined(Main, :Base) ? Main.Base.string(msg) :
    (Core.println(msg); "Error during bootstrap. See stdout.")
```
-/
def bootstrapAssertToString {α : Type} (baseDefined : Bool) (baseString : α → String)
    (println : α → Unit) (message : α) : String :=
  if baseDefined then baseString message
  else
    let _ := println message
    "Error during bootstrap. See stdout."

/--
Julia source: base/error.jl:266-266 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
_assert_tostring(@nospecialize(msg)) = Core.compilerbarrier(:type, __assert_tostring)(msg)
```
-/
def assertToString {α : Type} (compilerBarrier : (α → String) → α → String)
    (baseDefined : Bool) (baseString : α → String) (println : α → Unit) (message : α) : String :=
  compilerBarrier (bootstrapAssertToString baseDefined baseString println) message

def assertionMessageText (compilerBarrier : (AssertExpression → String) → AssertExpression → String)
    (baseDefined : Bool) (baseString : AssertExpression → String)
    (println : AssertExpression → Unit) : AssertMessage → String
  | .literal text => text
  | .runtimeStringify expression => assertToString compilerBarrier baseDefined baseString println expression
  | .quotedStringify expression => assertToString compilerBarrier baseDefined baseString println (.quoted expression)

def evaluateAssertExpansion (expansion : AssertExpansion) (condition : Bool)
    (compilerBarrier : (AssertExpression → String) → AssertExpression → String)
    (baseDefined : Bool) (baseString : AssertExpression → String)
    (println : AssertExpression → Unit) : Except JuliaException Unit :=
  if condition then .ok ()
  else .error (.assertionError (assertionMessageText compilerBarrier baseDefined baseString println expansion.message))

structure ExponentialBackOff where
  n : Int
  first_delay : F64
  max_delay : F64
  factor : F64
  jitter : F64
  deriving Repr, DecidableEq

/- Comparison and field-conversion interfaces used by Julia's generic inner constructor. -/
/--
Julia source: base/error.jl:277-280 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function ExponentialBackOff(n, first_delay, max_delay, factor, jitter)
        all(x->x>=0, (n, first_delay, max_delay, factor, jitter)) || error("all inputs must be non-negative")
        new(n, first_delay, max_delay, factor, jitter)
    end
```
-/
def makeExponentialBackOff {N A M F J : Type}
    (nonnegativeN : N → Bool) (nonnegativeA : A → Bool) (nonnegativeM : M → Bool)
    (nonnegativeF : F → Bool) (nonnegativeJ : J → Bool)
    (toInt : N → Except JuliaException Int)
    (toFirst : A → Except JuliaException F64) (toMax : M → Except JuliaException F64)
    (toFactor : F → Except JuliaException F64) (toJitter : J → Except JuliaException F64)
    (n : N) (first_delay : A) (max_delay : M) (factor : F) (jitter : J) :
    Except JuliaException ExponentialBackOff := do
  if nonnegativeN n && nonnegativeA first_delay && nonnegativeM max_delay &&
      nonnegativeF factor && nonnegativeJ jitter then
    let n ← toInt n
    let first_delay ← toFirst first_delay
    let max_delay ← toMax max_delay
    let factor ← toFactor factor
    let jitter ← toJitter jitter
    pure ⟨n, first_delay, max_delay, factor, jitter⟩
  else
    errorVararg [.abstractString "all inputs must be non-negative"]

def nonnegativeInt (value : Int) : Bool := decide (0 ≤ value)
def nonnegativeFloat (value : F64) : Bool := F64.le F64.zero value
def identityInt (value : Int) : Except JuliaException Int := .ok value
def identityFloat (value : F64) : Except JuliaException F64 := .ok value
def backoffKeywordDefaults : Int × F64 × F64 × F64 × F64 :=
  (1, F64.ofBits 0x3fa999999999999a, F64.ofBits 0x4024000000000000,
    F64.ofBits 0x4014000000000000, F64.ofBits 0x3fb999999999999a)

/--
Julia source: base/error.jl:283-291 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    ExponentialBackOff(; n=1, first_delay=0.05, max_delay=10.0, factor=5.0, jitter=0.1)

A [`Float64`](@ref) iterator of length `n` whose elements exponentially increase at a
rate in the interval `factor` * (1 ± `jitter`).  The first element is
`first_delay` and all elements are clamped to `max_delay`.
"""
ExponentialBackOff(; n=1, first_delay=0.05, max_delay=10.0, factor=5.0, jitter=0.1) =
    ExponentialBackOff(n, first_delay, max_delay, factor, jitter)
```
-/
def defaultExponentialBackOff {N A M F J : Type}
    (nonnegativeN : N → Bool) (nonnegativeA : A → Bool) (nonnegativeM : M → Bool)
    (nonnegativeF : F → Bool) (nonnegativeJ : J → Bool)
    (toInt : N → Except JuliaException Int)
    (toFirst : A → Except JuliaException F64) (toMax : M → Except JuliaException F64)
    (toFactor : F → Except JuliaException F64) (toJitter : J → Except JuliaException F64)
    (n : N) (first_delay : A) (max_delay : M) (factor : F) (jitter : J) :
    Except JuliaException ExponentialBackOff :=
  makeExponentialBackOff nonnegativeN nonnegativeA nonnegativeM nonnegativeF nonnegativeJ
    toInt toFirst toMax toFactor toJitter n first_delay max_delay factor jitter

structure Float64RNG where
  cursor : Nat
  sample : Nat → F64

def oneFloat64 : F64 := F64.one
def twoFloat64 : F64 := F64.ofBits 0x4000000000000000

def backoffRateFactor (jitter sample : F64) : F64 :=
  F64.add (F64.sub F64.one jitter) (F64.mul (F64.mul sample twoFloat64) jitter)

inductive JuliaType where
  | float64
  deriving Repr, DecidableEq


/--
Julia source: base/error.jl:292-298 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function iterate(ebo::ExponentialBackOff, state= (ebo.n, min(ebo.first_delay, ebo.max_delay)))
    state[1] < 1 && return nothing
    next_n = state[1]-1
    curr_delay = state[2]
    next_delay = min(ebo.max_delay, state[2] * ebo.factor * (1.0 - ebo.jitter + (Libc.rand(Float64) * 2.0 * ebo.jitter)))
    (curr_delay, (next_n, next_delay))
end
```
-/
def iterateExponentialBackOff (min : F64 → F64 → F64) (backoff : ExponentialBackOff)
    (rng : Float64RNG) (state : Option (Int × F64)) :
    Option (F64 × (Int × F64)) × Float64RNG :=
  let state := state.getD (backoff.n, min backoff.first_delay backoff.max_delay)
  if state.1 < 1 then
    (none, rng)
  else
    let next_n := state.1 - 1
    let curr_delay := state.2
    let nextFactor := backoffRateFactor backoff.jitter (rng.sample rng.cursor)
    let next_delay := min backoff.max_delay (F64.mul (F64.mul state.2 backoff.factor) nextFactor)
    (some (curr_delay, (next_n, next_delay)), { rng with cursor := rng.cursor + 1 })

/--
Julia source: base/error.jl:299-299 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
length(ebo::ExponentialBackOff) = ebo.n
```
-/
def lengthExponentialBackOff (backoff : ExponentialBackOff) : Int := backoff.n

/--
Julia source: base/error.jl:300-300 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eltype(::Type{ExponentialBackOff}) = Float64
```
-/
def eltypeExponentialBackOff (_type : Unit) : JuliaType := .float64

inductive RetryCheckResult (State : Type) where
  | decision (retry : Bool)
  | stateAndDecision (state : State) (retry : Bool)
  deriving Repr, DecidableEq
inductive RetryEvent (State Exception Trace Result : Type) where
  | success (value : Result)
  | retry (state nextState : State) (context : ExceptionContext Exception Trace) (delay : F64)
  | rejected (state : State) (context : ExceptionContext Exception Trace)
  | final (result : Except (ExceptionContext Exception Trace) Result)


structure RetryTrace (Exception Trace State Result : Type) where
  result : Except (ExceptionContext Exception Trace) Result
  calls : Nat
  sleptDelays : List F64
  rng : Float64RNG
  events : List (RetryEvent State Exception Trace Result)

def retryCheck {State Exception : Type}
    (check : Option (State → Exception → RetryCheckResult State))
    (state : State) (exception : Exception) : State × Bool :=
  match check with
  | none => (state, true)
  | some checkFunction =>
    match checkFunction state exception with
    | .decision decision => (state, decision)
    | .stateAndDecision nextState decision => (nextState, decision)

def retryLoop {Args Delays State Exception Trace Result : Type}
    (f : Nat → Args → Except (ExceptionContext Exception Trace) Result)
    (args : Args) (delays : Delays)
    (iterate : Delays → Float64RNG → Option State → Option (F64 × State) × Float64RNG)
    (check : Option (State → Exception → RetryCheckResult State))
    (sleep : F64 → Unit) (calls : Nat)
    (next : Option (F64 × State) × Float64RNG) :
    Option (RetryTrace Exception Trace State Result) :=
  match next.1 with
  | none =>
    let result := f (calls + 1) args
    some ⟨result, calls + 1, [], next.2, [.final result]⟩
  | some (delay, state) =>
    match f (calls + 1) args with
    | .ok value => some ⟨.ok value, calls + 1, [], next.2, [.success value]⟩
    | .error context =>
      let decision := retryCheck check state context.exception
      if decision.2 then
        let _ := sleep delay
        do
          let rest ← retryLoop f args delays iterate check sleep (calls + 1)
            (iterate delays next.2 (some decision.1))
          pure { rest with sleptDelays := delay :: rest.sleptDelays
                           events := .retry state decision.1 context delay :: rest.events }
      else
        some ⟨rethrowCurrent context, calls + 1, [], next.2, [.rejected state context]⟩
partial_fixpoint

/--
Julia source: base/error.jl:302-342 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    retry(f;  delays=ExponentialBackOff(), check=nothing) -> Function

Return an anonymous function that calls function `f`.  If an exception arises,
`f` is repeatedly called again, each time `check` returns `true`, after waiting the
number of seconds specified in `delays`.  `check` should input `delays`'s
current state and the `Exception`.

!!! compat "Julia 1.2"
    Before Julia 1.2 this signature was restricted to `f::Function`.

# Examples
```julia
retry(f, delays=fill(5.0, 3))
retry(f, delays=rand(5:10, 2))
retry(f, delays=Base.ExponentialBackOff(n=3, first_delay=5, max_delay=1000))
retry(http_get, check=(s,e)->e.status == "503")(url)
retry(read, check=(s,e)->isa(e, IOError))(io, 128; all=false)
```
"""
function retry(f;  delays=ExponentialBackOff(), check=nothing)
    (args...; kwargs...) -> begin
        y = iterate(delays)
        while y !== nothing
            (delay, state) = y
            try
                return f(args...; kwargs...)
            catch e
                if check !== nothing
                    result = check(state, e)
                    state, retry_or_not = length(result) == 2 ? result : (state, result)
                    retry_or_not || rethrow()
                end
            end
            sleep(delay)
            y = iterate(delays, state)
        end
        # When delays is out, just run the function without try/catch
        return f(args...; kwargs...)
    end
end
````
-/
def retry {Args Delays State Exception Trace Result : Type}
    (f : Nat → Args → Except (ExceptionContext Exception Trace) Result)
    (delays : Delays)
    (iterate : Delays → Float64RNG → Option State → Option (F64 × State) × Float64RNG)
    (check : Option (State → Exception → RetryCheckResult State))
    (sleep : F64 → Unit) (rng : Float64RNG) :
    Args → Option (RetryTrace Exception Trace State Result) :=
  fun args => retryLoop f args delays iterate check sleep 0 (iterate delays rng none)

end JuliaLean.base.error

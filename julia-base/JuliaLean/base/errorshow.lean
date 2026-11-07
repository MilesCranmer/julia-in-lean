import JuliaLean.base.error
import JuliaLean.base.methodshow
import JuliaLean.base.pointer
import JuliaLean.base.abstractarray
import JuliaLean.base.runtime_internals
import JuliaLean.Core
import JuliaLean.base.show
import JuliaLean.base.stacktraces
import JuliaLean.base.path
import JuliaLean.base.env
/-!
# Model of `base/errorshow.jl`

Typed source-mirrored exception printers at Julia
f755f49a9e41380d7da126b3c1db9fe7f83dd027. The model reuses show.jl's
IOPrims, JIO, IOContext, printAll and ShowError. User-defined show/print/summary
methods and error-hint handlers are typed callees. Missing exception fields are
Options, preserving isdefined checks. Runtime stack-frame lookup and reflection
that have no typed model stay visible as untranslated source.
-/
namespace JuliaLean.base.errorshow
open JuliaLean
open JuliaLean.base.show

abbrev Clong := JInt .i64
abbrev Culong := JInt .u64

inductive Scope (Mod : Type) where
  | moduleScope (module : Mod)
  | staticParameter
  | localScope
  | other (name : Bytes)
  deriving Repr, DecidableEq

inductive ErrorContext where
  | empty
  | globalBinding (moduleName name : Bytes)
  | other (text : Bytes)
  deriving Repr, DecidableEq

inductive BoundsIndices (R S X : Type) where
  | range (value : R)
  | string (value : S)
  | sequence (values : List X)

structure BoundsError (A I : Type) where
  array : Option A
  indices : Option I

structure TypeError (A Ty : Type) where
  func : Bytes
  expected : Ty
  got : A
  context : ErrorContext

structure UndefVarError (Mod : Type) where
  var : String
  scope : Option (Scope Mod)
  world : Culong

structure InexactError (A : Type) where
  func : Bytes
  arguments : List A

section
variable {m : Type → Type} [Monad m] [MonadExceptOf ShowError m] {Io V Ty : Type}


/--
Julia source: base/errorshow.jl:30-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ex) = show(io, ex)

show_index(io::IO, x::Any) = show(io, x)
show_index(io::IO, x::Slice) = show_index(io, x.indices)
show_index(io::IO, x::LogicalIndex) = summary(io, x.mask)
show_index(io::IO, x::OneTo) = print(io, "1:", x.stop)
show_index(io::IO, x::Colon) = print(io, ':')
```
-/
-- Source: base/errorshow.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showerrorAny {E R : Type} (showValue : JIO Io V → E → m R)
    (io : JIO Io V) (ex : E) : m R := showValue io ex

-- Source: base/errorshow.jl:32-32 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showIndexAny {X R : Type} (showValue : JIO Io V → X → m R)
    (io : JIO Io V) (x : X) : m R := showValue io x
-- Source: base/errorshow.jl:33-33 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showIndexSlice {X I R : Type} (indices : X → I)
    (showIndex : JIO Io V → I → m R) (io : JIO Io V) (x : X) : m R :=
  showIndex io (indices x)
-- Source: base/errorshow.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showIndexLogical {X A R : Type} (mask : X → A)
    (summary : JIO Io V → A → m R) (io : JIO Io V) (x : X) : m R :=
  summary io (mask x)
-- Source: base/errorshow.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showIndexOneTo {I : Type} (p : IOPrims m Io V)
    (printInt : JIO Io V → I → m Unit) (io : JIO Io V) (stop : I) : m Unit :=
  printAll p io [printStr p io "1:", printInt io stop]
-- Source: base/errorshow.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showIndexColon (p : IOPrims m Io V) (io : JIO Io V) : m Unit := printStr p io ":"

/--
Julia source: base/errorshow.jl:38-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::Meta.ParseError)
    if isnothing(ex.detail)
        print(io, "ParseError(", repr(ex.msg), ")")
    else
        showerror(io, ex.detail)
    end
end
```
-/
def showParseError {D : Type} (p : IOPrims m Io V) (repr : Bytes → m Bytes)
    (showError : JIO Io V → D → m Unit) (io : JIO Io V) (message : Bytes) (detail : Option D) : m Unit :=
  match detail with
  | none => do
    let text ← repr message
    printAll p io [printStr p io "ParseError(",printBytes p io text,printStr p io ")"]
  | some detail => showError io detail

/--
Julia source: base/errorshow.jl:46-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::Core.TypeNameError)
    print(io, "TypeNameError: ")
    if isa(ex.a, Union)
        print(io, "typename does not apply to unions whose components have different typenames")
    else
        print(io, "typename does not apply to this type")
    end
end
```
-/
-- Source: base/errorshow.jl:46-53 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showTypeNameError {A : Type} (p : IOPrims m Io V) (isUnion : A → Bool)
    (io : JIO Io V) (a : A) : m Unit := do
  printStr p io "TypeNameError: "
  if isUnion a then printStr p io "typename does not apply to unions whose components have different typenames"
  else printStr p io "typename does not apply to this type"

/--
Julia source: base/errorshow.jl:55-76 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::BoundsError)
    print(io, "BoundsError")
    if isdefined(ex, :a)
        print(io, ": attempt to access ")
        summary(io, ex.a)
        if isdefined(ex, :i)
            print(io, " at index [")
            if ex.i isa AbstractRange
                print(io, ex.i)
            elseif ex.i isa AbstractString
                show(io, inferencebarrier(ex.i))
            else
                for (i, x) in enumerate(ex.i)
                    i > 1 && print(io, ", ")
                    show_index(io, x)
                end
            end
            print(io, ']')
        end
    end
    Experimental.show_error_hints(io, ex)
end
```
-/
def showBoundsError {A R S X : Type} (p : IOPrims m Io V)
    (summary : JIO Io V → A → m Unit) (printRange : JIO Io V → R → m Unit)
    (showString : JIO Io V → S → m Unit) (showIndex : JIO Io V → X → m Unit)
    (hints : JIO Io V → BoundsError A (BoundsIndices R S X) → m Unit)
    (io : JIO Io V) (ex : BoundsError A (BoundsIndices R S X)) : m Unit := do
  printStr p io "BoundsError"
  match ex.array with
  | none => pure ()
  | some array =>
    printStr p io ": attempt to access "
    summary io array
    match ex.indices with
    | none => pure ()
    | some indices =>
      printStr p io " at index ["
      match indices with
      | .range r => printRange io r
      | .string s => showString io s
      | .sequence values =>
        for (x,i) in values.zipIdx do
          if i > 0 then printStr p io ", "
          showIndex io x
      printStr p io "]"
  hints io ex

/--
Julia source: base/errorshow.jl:78-105 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::TypeError)
    print(io, "TypeError: ")
    if ex.expected === Bool
        print(io, "non-boolean (", typeof(ex.got), ") used in boolean context")
    elseif ex.func === :var"dict key"
        print(io, "$(limitrepr(ex.got)) is not a valid key for type $(ex.expected)")
    else
        if isvarargtype(ex.got)
            targs = (ex.got,)
        elseif isa(ex.got, Type)
            targs = ("Type{", ex.got, "}")
        else
            targs = ("a value of type $(typeof(ex.got))",)
        end
        if ex.context == ""
            ctx = "in $(ex.func)"
        elseif isa(ex.context, GlobalRef)
            gr = ex.context
            ctx = "in $(ex.func) of global binding `$(gr.mod).$(gr.name)`"
        elseif ex.func === :var"keyword argument"
            ctx = "in keyword argument $(ex.context)"
        else
            ctx = "in $(ex.func), in $(ex.context)"
        end
        print(io, ctx, ", expected ", ex.expected, ", got ", targs...)
    end
    Experimental.show_error_hints(io, ex)
end
```
-/
def showTypeError {A : Type} (p : IOPrims m Io V) (t : TypeOps m Ty)
    (isVararg : A → Bool) (asType : A → Option Ty) (typeof : A → Ty)
    (printType : JIO Io V → Ty → m Unit) (printValue : JIO Io V → A → m Unit)
    (stringValue : A → m Bytes) (stringType : Ty → m Bytes) (limitrepr : A → m Bytes)
    (hints : JIO Io V → TypeError A Ty → m Unit)
    (io : JIO Io V) (ex : TypeError A Ty) : m Unit := do
  printStr p io "TypeError: "
  if t.egal ex.expected t.bool then
    printAll p io [printStr p io "non-boolean (",printType io (typeof ex.got),
      printStr p io ") used in boolean context"]
  else if ex.func = lit "dict key" then
    let value ← limitrepr ex.got
    let expected ← stringType ex.expected
    printBytes p io (value ++ lit " is not a valid key for type " ++ expected)
  else
    let targetParts ← if isVararg ex.got then pure [printValue io ex.got]
      else match asType ex.got with
      | some type => pure [printStr p io "Type{",printType io type,printStr p io "}"]
      | none => do
        let type ← stringType (typeof ex.got)
        pure [printBytes p io (lit "a value of type " ++ type)]
    let context := match ex.context with
      | .empty => lit "in " ++ ex.func
      | .globalBinding mod name => lit "in " ++ ex.func ++ lit " of global binding `" ++ mod ++ lit "." ++ name ++ lit "`"
      | .other text => if ex.func = lit "keyword argument" then lit "in keyword argument " ++ text
        else lit "in " ++ ex.func ++ lit ", in " ++ text
    printAll p io ([printBytes p io context,printStr p io ", expected ",printType io ex.expected,
      printStr p io ", got "] ++ targetParts)
  hints io ex

/--
Julia source: base/errorshow.jl:107-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex, bt; backtrace=true)
    try
        showerror(io, ex)
    finally
        backtrace && show_backtrace(io, bt)
    end
end
```
-/
-- Source: base/errorshow.jl:107-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showErrorBacktraceWith {E BT Ex R : Type} [MonadExceptOf Ex m]
    (showError : JIO Io V → E → m R) (showBacktrace : JIO Io V → BT → m Unit)
    (io : JIO Io V) (ex : E) (bt : BT) (backtrace : Bool := true) : m R := do
  let value ← tryCatchThe Ex (showError io ex) (fun error => do
    if backtrace then showBacktrace io bt
    throwThe Ex error)
  if backtrace then showBacktrace io bt
  pure value

-- Source: base/errorshow.jl:107-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showErrorBacktrace {E BT Ex : Type} [MonadExceptOf Ex m]
    (showError : JIO Io V → E → m Unit) (showBacktrace : JIO Io V → BT → m Unit)
    (io : JIO Io V) (ex : E) (bt : BT) (backtrace : Bool := true) : m Unit :=
  showErrorBacktraceWith (Ex := Ex) showError showBacktrace io ex bt backtrace

/--
Julia source: base/errorshow.jl:115-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::LoadError, bt; backtrace=true)
    !isa(ex.error, LoadError) && print(io, "LoadError: ")
    showerror(io, ex.error, bt, backtrace=backtrace)
    print(io, "\nin expression starting at $(ex.file):$(ex.line)")
end
showerror(io::IO, ex::LoadError) = showerror(io, ex, [])

function showerror(io::IO, ex::InitError, bt; backtrace=true)
    print(io, "InitError: ")
    showerror(io, ex.error, bt, backtrace=backtrace)
    print(io, "\nduring initialization of module ", ex.mod)
end
showerror(io::IO, ex::InitError) = showerror(io, ex, [])
```
-/
def showLoadError {E BT : Type} (p : IOPrims m Io V) (isLoadError : E → Bool)
    (showError : JIO Io V → E → BT → Bool → m Unit)
    (stringLine : Clong → m Bytes) (io : JIO Io V) (error : E) (file : Bytes)
    (line : Clong) (bt : BT) (backtrace : Bool := true) : m Unit := do
  if !isLoadError error then printStr p io "LoadError: "
  showError io error bt backtrace
  let line ← stringLine line
  printBytes p io (lit "
in expression starting at " ++ file ++ lit ":" ++ line)

def showLoadErrorDefault {E BT : Type} (callee : JIO Io V → E → BT → m Unit)
    (emptyTrace : BT) (io : JIO Io V) (ex : E) := callee io ex emptyTrace

-- Source: base/errorshow.jl:122-126 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showInitError {E BT : Type} (p : IOPrims m Io V)
    (showError : JIO Io V → E → BT → Bool → m Unit)
    (io : JIO Io V) (error : E) (moduleName : Bytes) (bt : BT) (backtrace : Bool := true) : m Unit := do
  printStr p io "InitError: "
  showError io error bt backtrace
  printAll p io [printStr p io "
during initialization of module ",printBytes p io moduleName]

-- Source: base/errorshow.jl:127-127 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showInitErrorDefaultNative {E Frame : Type} (p : IOPrims m Io V)
    (showError : JIO Io V → E → List Frame → Bool → m Unit)
    (io : JIO Io V) (error : E) (moduleName : Bytes) : m Unit :=
  showInitError p showError io error moduleName [] true

def showInitErrorDefault {E BT : Type} (callee : JIO Io V → E → BT → m Unit)
    (emptyTrace : BT) (io : JIO Io V) (ex : E) := callee io ex emptyTrace

/--
Julia source: base/errorshow.jl:129-143 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::DomainError)
    if isa(ex.val, AbstractArray)
        compact = get(io, :compact, true)::Bool
        limit = get(io, :limit, true)::Bool
        print(IOContext(io, :compact => compact, :limit => limit),
              "DomainError with ", ex.val)
    else
        print(io, "DomainError with ", ex.val)
    end
    if isdefined(ex, :msg)
        print(io, ":\n", ex.msg)
    end
    Experimental.show_error_hints(io, ex)
    nothing
end
```
-/
def showDomainError {A : Type} (p : IOPrims m Io V) (a : AnyOps V Ty)
    (isArray : A → m Bool) (printValue : JIO Io V → A → m Unit)
    (hints : JIO Io V → A → Option Bytes → m Unit)
    (io : JIO Io V) (value : A) (message : Option Bytes) : m Unit := do
  if ← isArray value then
    let compact ← assertBool a (getIO p io "compact" true)
    let limit ← assertBool a (getIO p io "limit" true)
    let context ← IOContext_pairs p a (JuliaLean.base.dict.fieldConv String) (boolConv a)
      io ("compact",compact) [("limit",limit)]
    printAll p (.context context) [printStr p (.context context) "DomainError with ", printValue (.context context) value]
  else printAll p io [printStr p io "DomainError with ",printValue io value]
  match message with
  | none => pure ()
  | some message => printAll p io [printStr p io ":
",printBytes p io message]
  hints io value message
  pure ()

/--
Julia source: base/errorshow.jl:145-158 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::SystemError)
    if @static(Sys.iswindows() ? ex.extrainfo isa WindowsErrorInfo : false)
        errstring = Libc.FormatMessage(ex.extrainfo.errnum)
        extrainfo = ex.extrainfo.extrainfo
    else
        errstring = Libc.strerror(ex.errnum)
        extrainfo = ex.extrainfo
    end
    if extrainfo === nothing
        print(io, "SystemError: $(ex.prefix): ", errstring)
    else
        print(io, "SystemError (with $extrainfo): $(ex.prefix): ", errstring)
    end
end
```
-/
def showSystemError {A : Type} (p : IOPrims m Io V) (windows : Bool)
    (windowsError : A → Option (Clong × Option A)) (formatMessage strerror : Clong → m Bytes)
    (stringExtra : A → m Bytes) (io : JIO Io V) (errorPrefix : Bytes) (errno : Clong)
    (extrainfo : Option A) : m Unit := do
  let (errstring,extra) ← (if windows then
    match extrainfo.bind windowsError with
    | some (code,extra) => do return (← formatMessage code,extra)
    | none => do return (← strerror errno,extrainfo)
  else do return (← strerror errno,extrainfo))
  match extra with
  | none => printAll p io [printBytes p io (lit "SystemError: " ++ errorPrefix ++ lit ": "),printBytes p io errstring]
  | some extra =>
    let extra ← stringExtra extra
    printAll p io [printBytes p io (lit "SystemError (with " ++ extra ++ lit "): " ++ errorPrefix ++ lit ": "),printBytes p io errstring]

/--
Julia source: base/errorshow.jl:160-160 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ::DivideError) = print(io, "DivideError: integer division error")
```
-/
def showDivideError (p : IOPrims m Io V) (io : JIO Io V) : m Unit := printStr p io "DivideError: integer division error"

/--
Julia source: base/errorshow.jl:161-161 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ::StackOverflowError) = print(io, "StackOverflowError:")
```
-/
def showStackOverflowError (p : IOPrims m Io V) (io : JIO Io V) : m Unit := printStr p io "StackOverflowError:"

/--
Julia source: base/errorshow.jl:162-162 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ::UndefRefError) = print(io, "UndefRefError: access to undefined reference")
```
-/
def showUndefRefError (p : IOPrims m Io V) (io : JIO Io V) : m Unit := printStr p io "UndefRefError: access to undefined reference"

/--
Julia source: base/errorshow.jl:163-163 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ::EOFError) = print(io, "EOFError: read end of file")
```
-/
def showEOFError (p : IOPrims m Io V) (io : JIO Io V) : m Unit := printStr p io "EOFError: read end of file"

/--
Julia source: base/errorshow.jl:168-168 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ex::InterruptException) = print(io, "InterruptException:")
```
-/
def showInterruptException (p : IOPrims m Io V) (io : JIO Io V) : m Unit := printStr p io "InterruptException:"

/--
Julia source: base/errorshow.jl:164-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ex::ErrorException) = print(io, ex.msg)
showerror(io::IO, ex::KeyError) = (print(io, "KeyError: key ");
                                   show(io, ex.key);
                                   print(io, " not found"))
```
-/
-- Source: base/errorshow.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- The message's AbstractString subtype selects its own print method.
def showErrorExceptionWith {A R : Type} (printMessage : JIO Io V → A → m R)
    (io : JIO Io V) (message : A) : m R := printMessage io message

-- Source: base/errorshow.jl:164-164 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showErrorException (p : IOPrims m Io V) (io : JIO Io V) (message : Bytes) : m Unit :=
  showErrorExceptionWith (printBytes p) io message

-- Source: base/errorshow.jl:165-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showKeyError {A : Type} (p : IOPrims m Io V) (showValue : JIO Io V → A → m Unit)
    (io : JIO Io V) (key : A) : m Unit := do
  printStr p io "KeyError: key "
  showValue io key
  printStr p io " not found"

/--
Julia source: base/errorshow.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ex::ArgumentError) = print(io, "ArgumentError: ", ex.msg)
```
-/
-- Source: base/errorshow.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showArgumentErrorWith {A : Type} (p : IOPrims m Io V)
    (printMessage : JIO Io V → A → m Unit) (io : JIO Io V) (message : A) : m Unit :=
  printAll p io [printStr p io "ArgumentError: ", printMessage io message]

-- Source: base/errorshow.jl:169-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showArgumentError (p : IOPrims m Io V) (io : JIO Io V) (message : Bytes) : m Unit :=
  showArgumentErrorWith p (printBytes p) io message

/--
Julia source: base/errorshow.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ex::DimensionMismatch) = print(io, "DimensionMismatch: ", ex.msg)
```
-/
-- Source: base/errorshow.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showDimensionMismatchWith {A : Type} (p : IOPrims m Io V)
    (printMessage : JIO Io V → A → m Unit) (io : JIO Io V) (message : A) : m Unit :=
  printAll p io [printStr p io "DimensionMismatch: ", printMessage io message]

-- Source: base/errorshow.jl:170-170 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showDimensionMismatch (p : IOPrims m Io V) (io : JIO Io V) (message : Bytes) : m Unit :=
  showDimensionMismatchWith p (printBytes p) io message

/--
Julia source: base/errorshow.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ex::AssertionError) = print(io, "AssertionError: ", ex.msg)
```
-/
-- Source: base/errorshow.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showAssertionErrorWith {A : Type} (p : IOPrims m Io V)
    (printMessage : JIO Io V → A → m Unit) (io : JIO Io V) (message : A) : m Unit :=
  printAll p io [printStr p io "AssertionError: ", printMessage io message]

-- Source: base/errorshow.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showAssertionError (p : IOPrims m Io V) (io : JIO Io V) (message : Bytes) : m Unit :=
  showAssertionErrorWith p (printBytes p) io message

/--
Julia source: base/errorshow.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ex::OverflowError) = print(io, "OverflowError: ", ex.msg)
```
-/
-- Source: base/errorshow.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showOverflowErrorWith {A : Type} (p : IOPrims m Io V)
    (printMessage : JIO Io V → A → m Unit) (io : JIO Io V) (message : A) : m Unit :=
  printAll p io [printStr p io "OverflowError: ", printMessage io message]

-- Source: base/errorshow.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showOverflowError (p : IOPrims m Io V) (io : JIO Io V) (message : Bytes) : m Unit :=
  showOverflowErrorWith p (printBytes p) io message

/--
Julia source: base/errorshow.jl:174-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showerror(io::IO, ex::UndefKeywordError) =
    print(io, "UndefKeywordError: keyword argument `$(ex.var)` not assigned")
```
-/
def showUndefKeywordError (p : IOPrims m Io V) (io : JIO Io V) (var : Bytes) : m Unit :=
  printBytes p io (lit "UndefKeywordError: keyword argument `" ++ var ++ lit "` not assigned")

/--
Julia source: base/errorshow.jl:177-190 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::UndefVarError)
    print(io, "UndefVarError: `$(ex.var)` not defined")
    if isdefined(ex, :scope)
        scope = ex.scope
        if scope isa Module
            print(io, " in `$scope`")
        elseif scope === :static_parameter
            print(io, " in static parameter matching")
        else
            print(io, " in $scope scope")
        end
    end
    Experimental.show_error_hints(io, ex)
end
```
-/
def showUndefVarError {Mod : Type} (p : IOPrims m Io V) (stringModule : Mod → m Bytes)
    (hints : JIO Io V → UndefVarError Mod → m Unit)
    (io : JIO Io V) (ex : UndefVarError Mod) : m Unit := do
  printBytes p io (lit "UndefVarError: `" ++ lit ex.var ++ lit "` not defined")
  match ex.scope with
  | none => pure ()
  | some (.moduleScope module) => printBytes p io (lit " in `" ++ (← stringModule module) ++ lit "`")
  | some .staticParameter => printStr p io " in static parameter matching"
  | some .localScope => printStr p io " in local scope"
  | some (.other name) => printBytes p io (lit " in " ++ name ++ lit " scope")
  hints io ex

/--
Julia source: base/errorshow.jl:192-205 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::InexactError)
    print(io, "InexactError: ", ex.func, '(')
    T = first(ex.args)
    nameof(T) === ex.func || print(io, T, ", ")
    # `join` calls `string` on its arguments, which shadows the size of e.g. Inf16
    # as `string(Inf16) == "Inf"` instead of "Inf16". Thus we cannot use `join` here.
    for arg in ex.args[2:end-1]
        show(io, arg)
        print(io, ", ")
    end
    show(io, ex.args[end])
    print(io, ")")
    Experimental.show_error_hints(io, ex)
end
```
-/
def showInexactError {A : Type} (p : IOPrims m Io V) (nameof : A → m Bytes)
    (printValue showValue : JIO Io V → A → m Unit)
    (hints : JIO Io V → InexactError A → m Unit)
    (io : JIO Io V) (ex : InexactError A) : m Unit := do
  printAll p io [printStr p io "InexactError: ",printBytes p io ex.func,printStr p io "("]
  let first ← match ex.arguments.head? with
    | none => throwShow (.jl .boundsError)
    | some value => pure value
  if (← nameof first) ≠ ex.func then printAll p io [printValue io first,printStr p io ", "]
  for arg in (ex.arguments.drop 1).dropLast do
    showValue io arg
    printStr p io ", "
  let last ← match ex.arguments.getLast? with
    | none => throwShow (.jl .boundsError)
    | some value => pure value
  showValue io last
  printStr p io ")"
  hints io ex

/--
Julia source: base/errorshow.jl:207-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::CanonicalIndexError)
    print(io, "CanonicalIndexError: ", ex.func, " not defined for ", ex.type)
end
```
-/
-- Source: base/errorshow.jl:207-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def showCanonicalIndexError (p : IOPrims m Io V) (printType : JIO Io V → Ty → m Unit)
    (io : JIO Io V) (func : Bytes) (type : Ty) : m Unit :=
  printAll p io [printStr p io "CanonicalIndexError: ",printBytes p io func,
    printStr p io " not defined for ",printType io type]

structure MethodError (A Ty : Type) where
  function : A
  /-- Left: ordinary argument tuple. Right: the tuple type passed to invoke. -/
  arguments : List A ⊕ Ty
  world : Culong

/-- Typed callees of the earlier-loaded reflection and runtime type modules.
No laws about method availability, subtype, or world age are assumed. -/
structure MethodReflection (A Ty Mod Method : Type) where
  types : TypeOps m Ty
  typeof : A → Ty
  coreTypeof : A → Ty
  parameters : Ty → List Ty
  tupleType : List Ty → Ty
  rewrap : Ty → Ty → Ty
  methodsIncludingAmbiguous : A → Ty → m (Option (List Method))
  methods : A → m (List Method)
  hasmethod : A → Ty → Option Culong → m Bool
  kwcall : A
  convert : A
  add : A
  sub : A
  equal : A → A → Bool
  namedTuple : Ty
  number : Ty
  numberArray : Ty
  array : Ty
  functionType : Ty
  isFunction : A → m Bool
  isType : A → Bool
  isDataType : A → Bool
  isAbstractType : A → Bool
  isBuiltin : A → Bool
  isSelf : Ty → Bool
  keywordKeys : Ty → List String
  fieldtype : Ty → Nat → m Ty
  singletonName : Ty → String
  parentModule : Ty → Mod
  baseModule : Mod
  typeModules : Ty → m (List Mod)
  moduleName : Mod → String
  moduleEqual : Mod → Mod → Bool
  globalBinding : Mod → String → m (Option A)
  worldCounter : m Culong
  functionName : A → String
  isgensym : String → Bool
  isArray : A → Bool
  ndims : A → m Clong
  size : A → Clong → m Clong
  vec : A → m A
  applicable : A → List A → m Bool

structure MethodPrinters (A Ty Mod Method : Type) where
  printValue : JIO Io V → A → m Unit
  printType : JIO Io V → Ty → m Unit
  stringValue : A → m String
  stringType : Ty → m String
  stringUInt : Culong → m String
  showAmbiguous : JIO Io V → List Method → A → Ty → m Unit
  showConvertError : JIO Io V → MethodError A Ty → List Ty → m Unit
  newBuffer : m Io
  takeString : Io → m String
  showSignatureFunction : JIO Io V → Ty → m Unit
  showTupleAsCall : JIO Io V → String → Ty → Bool → Option (List (String × Ty)) → m Unit
  typeLimitedStringFromContext : JIO Io V → String → m String
  showGlobal : JIO Io V → Mod → String → m Unit
  showModule : JIO Io V → Mod → m Unit
  shadowedTypeHint : JIO Io V → A → List Ty → m Unit
  errorHints : JIO Io V → MethodError A Ty → List Ty → List (String × Ty) → m Unit
  methodCandidates : JIO Io V → MethodError A Ty → List (String × Ty) → m Unit
  logCandidateError : ShowError → m Unit


/--
Julia source: base/errorshow.jl:211-213 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Must match `jl_inst_arg_tuple_type`: reflection through `typesof` should agree
# with actual dispatch, including egality keys for closed type-valued arguments.
typesof(@nospecialize args...) = Tuple{Any[Core.Typeof(arg) for arg in args]...}
```
-/
def typesof {A : Type} (coreTypeof : A → Ty) (tupleType : List Ty → Ty) (args : List A) : Ty :=
  tupleType (args.map coreTypeof)

/--
Julia source: base/errorshow.jl:260-409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, ex::MethodError)
    @nospecialize io
    # ex.args is a tuple type if it was thrown from `invoke` and is
    # a tuple of the arguments otherwise.
    is_arg_types = !isa(ex.args, Tuple)
    arg_types = is_arg_types ? ex.args : typesof(ex.args...)
    arg_types_param::SimpleVector = (unwrap_unionall(arg_types)::DataType).parameters
    san_arg_types_param = Any[rewrap_unionall(arg_types_param[i], arg_types) for i in 1:length(arg_types_param)]
    f = ex.f
    meth = methods_including_ambiguous(f, arg_types)
    if isa(meth, MethodList) && length(meth) > 1
        return showerror_ambiguous(io, meth, f, arg_types)
    end
    print(io, "MethodError: ")
    ft = typeof(f)
    f_is_function = false
    kwargs = []
    if f === Core.kwcall && length(arg_types_param) >= 2 && arg_types_param[1] <: NamedTuple && !is_arg_types
        # if this is a kwcall, reformat it as a call with kwargs
        # TODO: handle !is_arg_types here (aka invoke with kwargs), which needs a value for `f`
        local kwt
        let args = ex.args::Tuple
            f = args[2]
            ft = typeof(f)
            kwt = typeof(args[1])
            ex = MethodError(f, args[3:end], ex.world)
        end
        arg_types_param = arg_types_param[3:end]
        san_arg_types_param = san_arg_types_param[3:end]
        keys = kwt.parameters[1]::Tuple
        kwargs = Any[(keys[i], fieldtype(kwt, i)) for i in eachindex(keys)]
        arg_types = rewrap_unionall(Tuple{arg_types_param...}, arg_types)
    end
    if f === Base.convert && length(arg_types_param) == 2 && !is_arg_types
        f_is_function = true
        show_convert_error(io, ex, arg_types_param)
    elseif isempty(methods(f)) && isa(f, DataType) && isabstracttype(f)
        print(io, "no constructors have been defined for ", f)
    elseif isempty(methods(f)) && !isa(f, Function) && !isa(f, Type)
        println(io, "objects of type ", ft, " are not callable.")
        print(io, "In case you did not try calling it explicitly, check if a ", ft,
            " has been passed as an argument to a method that expects a callable instead.")
    else
        if ft <: Function && isempty(ft.parameters) && _isself(ft)
            f_is_function = true
        end
        if is_arg_types
            print(io, "no method matching invoke ")
        else
            print(io, "no method matching ")
        end
        buf = IOBuffer()
        iob = IOContext(buf, io)     # for type abbreviation as in #49795; some, like `convert(T, x)`, should not abbreviate
        show_signature_function(iob, Core.Typeof(f))
        show_tuple_as_call(iob, :function, arg_types; hasfirst=false, kwargs = isempty(kwargs) ? nothing : kwargs)
        str = takestring!(buf)
        str = type_limited_string_from_context(io, str)
        print(io, str)
    end
    # catch the two common cases of element-wise addition and subtraction
    if (f === Base.:+ || f === Base.:-) && length(san_arg_types_param) == 2
        # we need one array of numbers and one number, in any order
        if any(x -> x <: AbstractArray{<:Number}, san_arg_types_param) &&
            any(x -> x <: Number, san_arg_types_param)

            nounf = f === Base.:+ ? "addition" : "subtraction"
            varnames = ("scalar", "array")
            first, second = san_arg_types_param[1] <: Number ? varnames : reverse(varnames)
            fstring = f === Base.:+ ? "+" : "-"  # avoid depending on show_default for functions (invalidation)
            print(io, "\nFor element-wise $nounf, use broadcasting with dot syntax: $first .$fstring $second")
        end
    end
    if ft <: AbstractArray
        print(io, "\nIn case you're trying to index into the array, use square brackets [] instead of parentheses ().")
    end
    # Check for functions with the same name in other modules
    if f_is_function && ex.world != typemax(UInt)
        let name = ft.name.singletonname
            modules_to_check = Set{Module}()
            push!(modules_to_check, Base)
            for T in san_arg_types_param
                modulesof!(modules_to_check, T)
            end

            # Check all modules (sorted for consistency)
            sorted_modules = sort!(collect(modules_to_check), by=nameof)
            for mod in sorted_modules
                if isdefinedglobal(mod, name)
                    candidate = getglobal(mod, name)
                    if candidate !== f && hasmethod(candidate, arg_types; world=ex.world)
                        if mod === Base
                            print(io, "\nYou may have intended to import ")
                            show_unquoted(io, Expr(:., :Base, QuoteNode(name)))
                        else
                            print(io, "\nThe definition in ")
                            show_unquoted(io, mod)
                            print(io, " may have intended to extend ")
                            f_module = parentmodule(ft)
                            show_unquoted(io, Expr(:., f_module, QuoteNode(name)))
                        end
                    end
                end
            end
        end
    end
    if ex.world == typemax(UInt) || hasmethod(f, arg_types, world=ex.world)
        if !isempty(kwargs)
            print(io, "\nThis method does not support all of the given keyword arguments (and may not support any).")
        end
        if ex.world == typemax(UInt) || isempty(kwargs)
            print(io, "\nThis error has been manually thrown, explicitly, so the method may exist but be intentionally marked as unimplemented.")
        end
    elseif hasmethod(f, arg_types) && !hasmethod(f, arg_types, world=ex.world)
        curworld = get_world_counter()
        print(io, "\nThe applicable method may be too new: running in world age $(ex.world), while current world is $(curworld).")
    elseif f isa Function
        print(io, "\nThe ")
        isgensym(nameof(f)) && print(io, "anonymous ")
        print(io, "function `$f` exists, but no method is defined for this combination of argument types.")
    elseif f isa Type
        print(io, "\nThe type `$f` exists, but no method is defined for this combination of argument types when trying to construct it.")
    else
        print(io, "\nThe object of type `$(typeof(f))` exists, but no method is defined for this combination of argument types when trying to treat it as a callable object.")
    end
    if !is_arg_types
        # Check for row vectors used where a column vector is intended.
        vec_args = []
        hasrows = false
        for arg in ex.args
            isrow = isa(arg,Array) && ndims(arg)::Int==2 && size(arg,1)::Int==1
            hasrows |= isrow
            push!(vec_args, isrow ? vec(arg) : arg)
        end
        if hasrows && applicable(f, vec_args...) && isempty(kwargs)
            print(io, "\n\nYou might have used a 2d row vector where a 1d column vector was required.",
                      "\nNote the difference between 1d column vector [1,2,3] and 2d row vector [1 2 3].",
                      "\nYou can convert to a column vector with the vec() function.")
        end
    end
    if !is_arg_types && !(f isa Core.Builtin)
        show_shadowed_type_hint(io, f, san_arg_types_param)
    end
    Experimental.show_error_hints(io, ex, san_arg_types_param, kwargs)
    try
        show_method_candidates(io, ex, kwargs)
    catch ex
        @error "Error showing method candidates, aborted" exception=ex,catch_backtrace()
    end
    nothing
end
```
-/
def showMethodError {A Mod Method : Type} (p : IOPrims m Io V) (a : AnyOps V Ty)
    (r : MethodReflection (m := m) A Ty Mod Method)
    (s : MethodPrinters (m := m) (Io := Io) (V := V) A Ty Mod Method)
    (io : JIO Io V) (original : MethodError A Ty) : m Unit := do
  let isArgTypes := original.arguments.isRight
  let mut argTypes := match original.arguments with
    | .inl args => typesof r.coreTypeof r.tupleType args
    | .inr type => type
  let mut parameters := r.parameters argTypes
  let mut sanitized := parameters.map (fun t => r.rewrap t argTypes)
  let mut ex := original
  let mut f := ex.function
  let methods ← r.methodsIncludingAmbiguous f argTypes
  match methods with
  | some methods => if methods.length > 1 then return ← s.showAmbiguous io methods f argTypes
  | none => pure ()
  printStr p io "MethodError: "
  let mut ft := r.typeof f
  let mut fIsFunction := false
  let mut kwargs : List (String × Ty) := []
  if ← (if r.equal f r.kwcall && parameters.length ≥ 2 then
      (do if ← (match parameters.head? with | some t => r.types.subtype t r.namedTuple | none => pure false)
          then return !isArgTypes else return false) else pure false) then
    let args ← match ex.arguments with
      | .inl args => pure args
      | .inr _ => throwShow .typeError
    let kw ← match args[0]? with
      | some arg => pure arg
      | none => throwShow (.jl .boundsError)
    f ← match args[1]? with
      | some arg => pure arg
      | none => throwShow (.jl .boundsError)
    ft := r.typeof f
    let kwt := r.typeof kw
    ex := { ex with function := f, arguments := .inl (args.drop 2) }
    parameters := parameters.drop 2
    sanitized := sanitized.drop 2
    for (key,i) in (r.keywordKeys kwt).zipIdx do
      kwargs := kwargs ++ [(key, ← r.fieldtype kwt (i+1))]
    argTypes := r.rewrap (r.tupleType parameters) argTypes
  if r.equal f r.convert && parameters.length = 2 && !isArgTypes then
    fIsFunction := true
    s.showConvertError io ex parameters
  else if (← r.methods f).isEmpty && r.isDataType f && r.isAbstractType f then
    printAll p io [printStr p io "no constructors have been defined for ",s.printValue io f]
  else if ← (do
      if !(← r.methods f).isEmpty then return false
      if ← r.isFunction f then return false
      return !r.isType f) then
    printAll p io [printStr p io "objects of type ",s.printType io ft,printStr p io " are not callable.
"]
    printAll p io [printStr p io "In case you did not try calling it explicitly, check if a ",
      s.printType io ft,printStr p io " has been passed as an argument to a method that expects a callable instead."]
  else
    if ← (do if ← r.types.subtype ft r.functionType then return (r.parameters ft).isEmpty && r.isSelf ft else return false) then
      fIsFunction := true
    printStr p io (if isArgTypes then "no method matching invoke " else "no method matching ")
    let buffer ← s.newBuffer
    let context ← IOContext_IO_IO p a (.plain buffer) io
    s.showSignatureFunction (.context context) (r.coreTypeof f)
    s.showTupleAsCall (.context context) "function" argTypes false (if kwargs.isEmpty then none else some kwargs)
    let text ← s.takeString buffer
    let text ← s.typeLimitedStringFromContext io text
    printStr p io text
  if (r.equal f r.add || r.equal f r.sub) && sanitized.length = 2 then
    if ← (do if ← sanitized.anyM (fun t => r.types.subtype t r.numberArray)
        then sanitized.anyM (fun t => r.types.subtype t r.number) else pure false) then
      let addition := r.equal f r.add
      let noun := if addition then "addition" else "subtraction"
      let firstIsScalar ← match sanitized.head? with
        | some t => r.types.subtype t r.number
        | none => pure false
      let (first,second) := if firstIsScalar then ("scalar","array") else ("array","scalar")
      let op := if addition then "+" else "-"
      printStr p io ("
For element-wise " ++ noun ++ ", use broadcasting with dot syntax: " ++ first ++ " ." ++ op ++ " " ++ second)
  if ← r.types.subtype ft r.array then
    printStr p io "
In case you're trying to index into the array, use square brackets [] instead of parentheses ()."
  let maxWorld := JInt.wrap .u64 (2^64-1)
  if fIsFunction && ex.world.val ≠ maxWorld.val then
    let name := r.singletonName ft
    let mut modules := [r.baseModule]
    for type in sanitized do
      for mod in (← r.typeModules type) do
        if !(modules.any (r.moduleEqual mod)) then modules := modules ++ [mod]
    let sortedModules := modules.mergeSort (fun a b => r.moduleName a ≤ r.moduleName b)
    for mod in sortedModules do
      match ← r.globalBinding mod name with
      | none => pure ()
      | some candidate =>
        if !r.equal candidate f && (← r.hasmethod candidate argTypes (some ex.world)) then
          if r.moduleEqual mod r.baseModule then
            printStr p io "
You may have intended to import "
            s.showGlobal io r.baseModule name
          else
            printStr p io "
The definition in "
            s.showModule io mod
            printStr p io " may have intended to extend "
            s.showGlobal io (r.parentModule ft) name
  if ex.world.val = maxWorld.val || (← r.hasmethod f argTypes (some ex.world)) then
    if !kwargs.isEmpty then
      printStr p io "
This method does not support all of the given keyword arguments (and may not support any)."
    if ex.world.val = maxWorld.val || kwargs.isEmpty then
      printStr p io "
This error has been manually thrown, explicitly, so the method may exist but be intentionally marked as unimplemented."
  else if (← r.hasmethod f argTypes none) && !(← r.hasmethod f argTypes (some ex.world)) then
    let current ← r.worldCounter
    let old ← s.stringUInt ex.world
    let current ← s.stringUInt current
    printStr p io ("
The applicable method may be too new: running in world age " ++ old ++ ", while current world is " ++ current ++ ".")
  else if ← r.isFunction f then
    printStr p io "
The "
    if r.isgensym (r.functionName f) then printStr p io "anonymous "
    let text ← s.stringValue f
    printStr p io ("function `" ++ text ++ "` exists, but no method is defined for this combination of argument types.")
  else if r.isType f then
    let text ← s.stringValue f
    printStr p io ("
The type `" ++ text ++ "` exists, but no method is defined for this combination of argument types when trying to construct it.")
  else
    let text ← s.stringType (r.typeof f)
    printStr p io ("
The object of type `" ++ text ++ "` exists, but no method is defined for this combination of argument types when trying to treat it as a callable object.")
  if !isArgTypes then
    let args ← match ex.arguments with
      | .inl args => pure args
      | .inr _ => throwShow .typeError
    let mut vecArgs := []
    let mut hasRows := false
    for arg in args do
      let isRow := r.isArray arg && (← r.ndims arg).val = 2 && (← r.size arg (JInt.wrap .i64 1)).val = 1
      hasRows := hasRows || isRow
      vecArgs := vecArgs ++ [← if isRow then r.vec arg else pure arg]
    if hasRows && (← r.applicable f vecArgs) && kwargs.isEmpty then
      printAll p io [printStr p io "

You might have used a 2d row vector where a 1d column vector was required.",
        printStr p io "
Note the difference between 1d column vector [1,2,3] and 2d row vector [1 2 3].",
        printStr p io "
You can convert to a column vector with the vec() function."]
  if !isArgTypes && !r.isBuiltin f then s.shadowedTypeHint io f sanitized
  s.errorHints io ex sanitized kwargs
  tryCatchThe ShowError (s.methodCandidates io ex kwargs) s.logCandidateError
  pure ()

/--
Julia source: base/errorshow.jl:411-415 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror(io::IO, exc::FieldError)
    @nospecialize
    print(io, "FieldError: type $(exc.type.name.wrapper) has no field `$(exc.field)`")
    Base.Experimental.show_error_hints(io, exc)
end
```
-/
def showFieldError (p : IOPrims m Io V) (hints : JIO Io V → Ty → Bytes → m Unit)
    (stringWrapper : Ty → m Bytes) (io : JIO Io V) (type : Ty) (field : Bytes) : m Unit := do
  let wrapper ← stringWrapper type
  printBytes p io (lit "FieldError: type " ++ wrapper ++ lit " has no field `" ++ field ++ lit "`")
  hints io type field

/--
Julia source: base/errorshow.jl:417-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
striptype(::Type{T}) where {T} = T
striptype(::Any) = nothing
```
-/
def striptype {A : Type} (asType : A → Option Ty) (value : A) : Option Ty := asType value

/--
Julia source: base/errorshow.jl:243-258 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_convert_error(io::IO, ex::MethodError, arg_types_param)
    # See #13033
    T = striptype(ex.args[1])
    if T === nothing
        print(io, "First argument to `convert` must be a Type, got ", ex.args[1])
    else
        p2 = arg_types_param[2]
        print_one_line = isa(T, DataType) && isa(p2, DataType) && T.name != p2.name
        printstyled(io, "Cannot `convert` an object of type ")
        print_one_line || printstyled(io, "\n  ")
        print_with_compare(io, p2, T, :light_green)
        printstyled(io, " to an object of type ")
        print_one_line || printstyled(io, "\n  ")
        print_with_compare(io, T, p2, :light_red)
    end
end
```
-/
def showConvertError {A Name : Type} (p : IOPrims m Io V) (styled : PrintStyled m Io V)
    (asType : A → Option Ty) (typeName : Ty → Option Name) (nameEqual : Name → Name → Bool)
    (printValue : JIO Io V → A → m Unit) (compare : JIO Io V → Ty → Ty → String → m Unit)
    (io : JIO Io V) (ex : MethodError A Ty) (parameters : List Ty) : m Unit := do
  let first ← match ex.arguments with
    | .inr _ => throwShow .typeError
    | .inl args => match args.head? with
      | none => throwShow (.jl .boundsError)
      | some value => pure value
  match asType first with
  | none => printAll p io [printStr p io "First argument to `convert` must be a Type, got ",printValue io first]
  | some target =>
    let actual ← match parameters[1]? with
      | none => throwShow (.jl .boundsError)
      | some type => pure type
    let oneLine := match typeName target,typeName actual with
      | some a,some b => !nameEqual a b
      | _,_ => false
    styled io [fun stream => printStr p stream "Cannot `convert` an object of type "] "normal" false
    if !oneLine then styled io [fun stream => printStr p stream "\n  "] "normal" false
    compare io actual target "light_green"
    styled io [fun stream => printStr p stream " to an object of type "] "normal" false
    if !oneLine then styled io [fun stream => printStr p stream "\n  "] "normal" false
    compare io target actual "light_red"

/--
Julia source: base/errorshow.jl:420-446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror_ambiguous(io::IO, meths, f, args::Type)
    @nospecialize f args
    print(io, "MethodError: ")
    show_signature_function(io, isa(f, Type) ? Type{f} : typeof(f))
    show_tuple_as_call(io, :var"", args, hasfirst=false)
    println(io, " is ambiguous.\n\nCandidates:")
    sigfix = Any
    for m in meths
        print(io, "  ")
        show_method(io, m; digit_align_width=0)
        println(io)
        sigfix = typeintersect(m.sig, sigfix)
    end
    if isa(unwrap_unionall(sigfix), DataType) && sigfix <: Tuple
        let sigfix=Core.Box(sigfix)
            if all(m->morespecific(sigfix.contents, m.sig), meths)
                print(io, "\nPossible fix, define\n  ")
                show_tuple_as_call(io, :function,  sigfix.contents)
            else
                print(io, "To resolve the ambiguity, try making one of the methods more specific, or ")
                print(io, "adding a new method more specific than any of the existing applicable methods.")
            end
        end
        println(io)
    end
    nothing
end
```
-/
def showAmbiguous {A Method : Type} (p : IOPrims m Io V) (t : TypeOps m Ty)
    (isType : A → Bool) (typeOfValue typeof : A → Ty)
    (showSignature : JIO Io V → Ty → m Unit)
    (showTuple : JIO Io V → String → Ty → Bool → m Unit)
    (showMethod : JIO Io V → Method → Clong → m Unit)
    (signature : Method → Ty) (intersect : Ty → Ty → Ty) (isDataType : Ty → Bool)
    (moreSpecific : Ty → Ty → Bool)
    (io : JIO Io V) (methods : List Method) (f : A) (args : Ty) : m Unit := do
  printStr p io "MethodError: "
  showSignature io (if isType f then typeOfValue f else typeof f)
  showTuple io "" args false
  printAll p io [printStr p io " is ambiguous.\n\nCandidates:",printStr p io "\n"]
  let mut fix := t.any
  for method in methods do
    printStr p io "  "
    showMethod io method (JInt.wrap .i64 0)
    printStr p io "\n"
    fix := intersect (signature method) fix
  if ← (if isDataType fix then t.subtype fix t.tuple else pure false) then
    if methods.all (fun method => moreSpecific fix (signature method)) then
      printStr p io "\nPossible fix, define\n  "
      showTuple io "function" fix true
    else
      printStr p io "To resolve the ambiguity, try making one of the methods more specific, or "
      printStr p io "adding a new method more specific than any of the existing applicable methods."
    printStr p io "\n"
  pure ()

/--
Julia source: base/errorshow.jl:450-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function showerror_nostdio(@nospecialize(err), msg::AbstractString)
    stderr_stream = ccall(:jl_stderr_stream, Ptr{Cvoid}, ())
    ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, msg)
    ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, ":\n")
    ccall(:jl_static_show, Csize_t, (Ptr{Cvoid},Any), stderr_stream, err)
    ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, "\n")
end
```
-/
def showErrorNoStdio {A Ptr : Type} (stderrStream : m Ptr)
    (printf : Ptr → String → m (JInt .i32)) (staticShow : Ptr → A → m Culong)
    (err : A) (message : String) : m (JInt .i32) := do
  let stream ← stderrStream
  let _ ← printf stream message
  let _ ← printf stream ":\n"
  let _ ← staticShow stream err
  printf stream "\n"

/--
Julia source: base/errorshow.jl:458-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stacktrace_expand_basepaths()::Bool = Base.get_bool_env("JULIA_STACKTRACE_EXPAND_BASEPATHS", false) === true
stacktrace_contract_userdir()::Bool = Base.get_bool_env("JULIA_STACKTRACE_CONTRACT_HOMEDIR", true) === true
stacktrace_linebreaks()::Bool = Base.get_bool_env("JULIA_STACKTRACE_LINEBREAKS", false) === true
stacktrace_full_loading()::Bool = Base.get_bool_env("JULIA_STACKTRACE_FULL_LOADING", false) === true
```
-/
def stacktraceExpandBasepaths (getBoolEnv : String → Bool → m (Option Bool)) : m Bool :=
  return (← getBoolEnv "JULIA_STACKTRACE_EXPAND_BASEPATHS" false) == some true
def stacktraceContractUserdir (getBoolEnv : String → Bool → m (Option Bool)) : m Bool :=
  return (← getBoolEnv "JULIA_STACKTRACE_CONTRACT_HOMEDIR" true) == some true
def stacktraceLinebreaks (getBoolEnv : String → Bool → m (Option Bool)) : m Bool :=
  return (← getBoolEnv "JULIA_STACKTRACE_LINEBREAKS" false) == some true
def stacktraceFullLoading (getBoolEnv : String → Bool → m (Option Bool)) : m Bool :=
  return (← getBoolEnv "JULIA_STACKTRACE_FULL_LOADING" false) == some true

/-- Bind the fixed Base parser and the String emptiness check used by it.
The remaining operations access the mutable process environment. -/
def stacktraceBoolEnv {World : Type} (ops : JuliaLean.base.env.BoolEnvOps World)
    (name : String) (fallback : Bool) : JuliaLean.base.env.EnvAction World (Option Bool) :=
  JuliaLean.base.env.getBoolEnvDefault { ops with isEmpty := String.isEmpty } name fallback

-- Source: base/errorshow.jl:458-458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def stacktraceExpandBasepathsNative {World : Type} (ops : JuliaLean.base.env.BoolEnvOps World) :
    JuliaLean.base.env.EnvAction World Bool :=
  stacktraceExpandBasepaths (stacktraceBoolEnv ops)

-- Source: base/errorshow.jl:459-459 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def stacktraceContractUserdirNative {World : Type} (ops : JuliaLean.base.env.BoolEnvOps World) :
    JuliaLean.base.env.EnvAction World Bool :=
  stacktraceContractUserdir (stacktraceBoolEnv ops)

-- Source: base/errorshow.jl:460-460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def stacktraceLinebreaksNative {World : Type} (ops : JuliaLean.base.env.BoolEnvOps World) :
    JuliaLean.base.env.EnvAction World Bool :=
  stacktraceLinebreaks (stacktraceBoolEnv ops)

-- Source: base/errorshow.jl:461-461 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def stacktraceFullLoadingNative {World : Type} (ops : JuliaLean.base.env.BoolEnvOps World) :
    JuliaLean.base.env.EnvAction World Bool :=
  stacktraceFullLoading (stacktraceBoolEnv ops)

/--
Julia source: base/errorshow.jl:1423-1436 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_exception_stack(io::IO, stack)
    # Display exception stack with the top of the stack first.  This ordering
    # means that the user doesn't have to scroll up in the REPL to discover the
    # root cause.
    nexc = length(stack)
    for i = nexc:-1:1
        if nexc != i
            printstyled(io, "\ncaused by: ", color=error_color())
        end
        exc, bt = stack[i]
        showerror(io, exc, bt, backtrace = bt!==nothing)
        i == 1 || println(io)
    end
end
```
-/
def showExceptionStack {E BT : Type} (p : IOPrims m Io V) (styled : PrintStyled m Io V)
    (errorColor : String) (showError : JIO Io V → E → Option BT → Bool → m Unit)
    (io : JIO Io V) (stack : List (E × Option BT)) : m Unit := do
  for (entry,index) in stack.reverse.zipIdx do
    if index ≠ 0 then styled io [fun stream => printStr p stream "\ncaused by: "] errorColor false
    showError io entry.1 entry.2 entry.2.isSome
    if index + 1 ≠ stack.length then printStr p io "\n"

/--
Julia source: base/errorshow.jl:1701-1709 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
size(s::ExceptionStack) = size(s.stack)
getindex(s::ExceptionStack, i::Int) = s.stack[i]

function show(io::IO, ::MIME"text/plain", stack::ExceptionStack)
    nexc = length(stack)
    printstyled(io, nexc, "-element ExceptionStack", nexc == 0 ? "" : ":\n")
    show_exception_stack(io, stack)
end
show(io::IO, stack::ExceptionStack) = show(io, MIME"text/plain"(), stack)
```
-/
def exceptionStackSize {E BT : Type} (stack : List (E × BT)) : Clong :=
  JInt.wrap .i64 stack.length

def exceptionStackGetindex {E BT : Type} (stack : List (E × BT)) (index : Clong) : Jl (E × BT) :=
  if index.val ≤ 0 then .error .boundsError
  else match stack[(index.val-1).toNat]? with
    | none => .error .boundsError
    | some entry => .ok entry

def showExceptionStackPlain {S : Type} (p : IOPrims m Io V) (styled : PrintStyled m Io V)
    (printInt : JIO Io V → Clong → m Unit) (showStack : JIO Io V → List S → m Unit)
    (io : JIO Io V) (stack : List S) : m Unit := do
  let count := JInt.wrap .i64 stack.length
  styled io [fun stream => printInt stream count,
    fun stream => printStr p stream "-element ExceptionStack",
    fun stream => printStr p stream (if count.val = 0 then "" else ":\n")] "normal" false
  showStack io stack

def showExceptionStackDefault {S : Type} (showPlain : JIO Io V → List S → m Unit)
    (io : JIO Io V) (stack : List S) : m Unit := showPlain io stack

inductive IncompleteInput where
  | other
  | string (text : String)
  | expression (head : String) (arguments : List IncompleteInput)


/--
Julia source: base/errorshow.jl:1714-1734 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
incomplete_tag(ex) = :none
function incomplete_tag(ex::Expr)
    if ex.head !== :incomplete
        return :none
    elseif isempty(ex.args)
        return :other
    else
        a = ex.args[1]
        if a isa String
            occursin("string", a) && return :string
            occursin("comment", a) && return :comment
            occursin("requires end", a) && return :block
            occursin("\"`\"", a) && return :cmd
            occursin("character", a) && return :char
            return :other
        else
            return incomplete_tag(a)::Symbol
        end
    end
end
incomplete_tag(exc::Meta.ParseError) = incomplete_tag(exc.detail)
```
-/
-- Source: base/errorshow.jl:1714-1714 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def incompleteTagAny {A : Type} (_value : A) : String := "none"

-- Source: base/errorshow.jl:1715-1733 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def incompleteTag : IncompleteInput → String
  | .expression head args =>
    if head ≠ "incomplete" then "none"
    else match args with
      | [] => "other"
      | .string message :: _ =>
        if (message.splitOn "string").length > 1 then "string"
        else if (message.splitOn "comment").length > 1 then "comment"
        else if (message.splitOn "requires end").length > 1 then "block"
        else if (message.splitOn "\"`\"").length > 1 then "cmd"
        else if (message.splitOn "character").length > 1 then "char"
        else "other"
      | arg :: _ => incompleteTag arg
  | _ => incompleteTagAny ()

-- Source: base/errorshow.jl:1734-1734 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def incompleteTagParseErrorWith {D R : Type} (tag : D → m R) (detail : D) : m R :=
  tag detail

-- Source: base/errorshow.jl:1734-1734 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
def incompleteTagParseError (detail : IncompleteInput) : String :=
  incompleteTagParseErrorWith (m := Id) incompleteTag detail

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:1-29 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
--     showerror(io, e)
-- 
-- Show a descriptive representation of an exception object `e`.
-- This method is used to display the exception after a call to [`throw`](@ref).
-- 
-- # Examples
-- ```jldoctest
-- julia> struct MyException <: Exception
--            msg::String
--        end
-- 
-- julia> function Base.showerror(io::IO, err::MyException)
--            print(io, "MyException: ")
--            print(io, err.msg)
--        end
-- 
-- julia> err = MyException("test exception")
-- MyException("test exception")
-- 
-- julia> sprint(showerror, err)
-- "MyException: test exception"
-- 
-- julia> throw(MyException("test exception"))
-- ERROR: MyException: test exception
-- ```
-- """
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:54-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:77-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:106-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:114-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:128-128 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:144-144 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:159-159 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:176-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:191-191 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:206-206 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:210-210 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source


-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:259-259 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:410-410 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:416-416 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:419-419 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:447-449 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- #Show an error by directly calling jl_printf and jl_static_show.
-- #Useful in Base submodule __init__ functions where stderr isn't defined yet.
-- /Source

-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:457-457 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- /Source


/-! ## Stack traces (`base/errorshow.jl:870-1421`), over the `base/stacktraces.jl` model -/

open JuliaLean.base.stacktraces (StackFrame Reflect Linfo MIDef IP frame_location frame_mi
  frame_method_or_module parentmodule_StackFrame is_top_level_frame show_spec_linfo stacktrace_trace
  eq_StackFrame)

variable {MI CI Meth CInfo DI Mod RF P : Type}
variable [MonadExceptOf JuliaLean.base.stacktraces.StError m] [MonadExceptOf JuliaLean.base.path.PathError m]

/-- An element `(frame, count)::Tuple{StackFrame,Int}` of a processed backtrace. -/
abbrev Entry (MI CI Meth CInfo DI : Type) := StackFrame MI CI Meth CInfo DI × JInt64

/-- Wrapping `Int` arithmetic. -/
def addI (a b : JInt64) : JInt64 := JInt.wrap .i64 (a.val + b.val)
def subI (a b : JInt64) : JInt64 := JInt.wrap .i64 (a.val - b.val)
def mulI (a b : JInt64) : JInt64 := JInt.wrap .i64 (a.val * b.val)
def negI (a : JInt64) : JInt64 := JInt.wrap .i64 (-a.val)

/-- `s ^ n` of a `String` and an `Int`: `ArgumentError` for a negative `n`. -/
def repeatStr [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (s : String) (n : JInt64) : m String :=
  if n.val < 0 then throwShow (.jl (.argumentError "can't repeat a string a negative number of times"))
  else pure (String.join (List.replicate n.val.toNat s))

/-- `kept[a:b] .= v` (1-based, inclusive). -/
def setRange (kept : List Bool) (a b : Nat) (v : Bool) : List Bool :=
  kept.mapIdx fun j x => if a ≤ j + 1 ∧ j + 1 ≤ b then v else x

/-- `keepat!(trace, kept)` with `length(kept) == length(trace)`. -/
def keepat {α : Type} (trace : List α) (kept : List Bool) : List α :=
  (trace.zip kept).filterMap fun (e, k) => if k then some e else none

/-- `xs[i] = v` on a `Vector`. -/
def setIdx {α : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (xs : List α) (i : JInt64) (v : α) : m (List α) :=
  if 1 ≤ i.val ∧ i.val ≤ xs.length then pure (xs.set (i.val - 1).toNat v)
  else throwShow (.jl .boundsError)

def natI (n : Nat) : JInt64 := i64 n

/-- A `String` as a `base/path.jl` path. -/
def toPath (s : String) : JuliaLean.base.path.Path := ⟨lit s⟩

/-- The arguments `show_backtrace(io, t::Vector)` distinguishes: a processed `Vector{Any}` of
`(StackFrame, Int)` tuples, a raw trace of instruction pointers, or a `Vector{StackFrame}`. -/
inductive BacktraceArg (MI CI Meth CInfo DI : Type) where
  | processed (entries : List (Entry MI CI Meth CInfo DI))
  | raw (ips : List (IP MI CI CInfo))
  | frames (frames : List (StackFrame MI CI Meth CInfo DI))

/-- Callees of the stack-trace printers over a monad `n`. -/
structure BacktraceOps (n : Type → Type) (Io V Ty MI CI Meth CInfo DI Mod RF P : Type) where
  /-- Reflection and printing callees of the `base/stacktraces.jl` model. -/
  r : Reflect n MI CI Meth CInfo DI Mod Ty RF
  sc : JuliaLean.base.stacktraces.Callees n (JIO Io V) MI CI Meth CInfo DI Mod Ty
  p : IOPrims n Io V
  a : AnyOps V Ty
  /-- `printstyled(io, xs...; color, italic, underline)` (`base/util.jl`, loaded later). -/
  styled : JIO Io V → List (JIO Io V → n Unit) → Sym → Bool → Bool → n Unit
  /-- `print(io, n::Int)`, `print(io, m::Module)`, `print(io, prefix)` of a non-`nothing` prefix. -/
  printInt : JIO Io V → JInt64 → n Unit
  printModule : JIO Io V → Mod → n Unit
  printPrefix : JIO Io V → P → n Unit
  /-- `string(n::Int)`, `lpad(s, n)` (`base/strings/util.jl`), `ndigits(n::Int)` (`base/intfuncs.jl`). -/
  stringInt : JInt64 → String
  lpad : String → JInt64 → String
  ndigits : JInt64 → JInt64
  /-- `m === Base`, `m === Core`, `m === Main`, `parentmodule(m::Module)`. -/
  isBase : Mod → Bool
  isCore : Mod → Bool
  isMain : Mod → Bool
  parentmodule : Mod → Mod
  /-- `===` on a frame's `linfo` field. -/
  egalLinfo : Linfo MI CI Meth CInfo → Linfo MI CI Meth CInfo → Bool
  /-- `hash(entry::Tuple{StackFrame,Int})` (`base/tuple.jl` over `stacktraces.hash_StackFrame`). -/
  hashEntry : Entry MI CI Meth CInfo DI → JInt .u64
  /-- `sig <: Tuple{typeof(Core.kwcall),NamedTuple,Any,Vararg}`, and `==` on types. -/
  isKwcallSig : Ty → n Bool
  tyEq : Ty → Ty → n Bool
  /-- `push!(io[:last_shown_line_infos], x)` and `empty!(io[:last_shown_line_infos])` of the value
  stored in the `IOContext`. -/
  pushLineInfo : V → String × JInt64 → n Unit
  emptyLineInfos : V → n Unit
  /-- `fixup_stdlib_path` (the `base/methodshow.jl` model instantiated with its callees) and
  `find_source_file` (`base/loading.jl`, loaded later), on the bytes of a `String`. -/
  fixup_stdlib_path : List UInt8 → n (List UInt8)
  find_source_file : List UInt8 → n (Option (List UInt8))
  /-- `Base.get_bool_env(name, default)`: `none` when the variable is not a boolean. -/
  getBoolEnv : String → Bool → n (Option Bool)
  /-- The platform and the string/filesystem primitives of the `base/path.jl` model. -/
  os : JuliaLean.base.path.Platform
  pathOps : JuliaLean.base.path.StringOps
  fs : JuliaLean.base.path.FileSystemOps
  /-- `sprint(show, frame)` (the bytes of the `String`), whose `show` method is
  `stacktraces.show_StackFrame`. -/
  sprintShowFrame : StackFrame MI CI Meth CInfo DI → n (List UInt8)
  /-- `invokelatest(update_stackframes_callback[], filtered)`: the vector after the call, which
  mutates it in place, whether or not the callback threw (`try ... catch end` discards it). -/
  updateStackframes : List (Entry MI CI Meth CInfo DI) → n (List (Entry MI CI Meth CInfo DI))

/-- The `BacktraceOps` fields `print_module_path_file` reads. -/
structure PathPrinter (n : Type → Type) (Io V Mod : Type) where
  p : IOPrims n Io V
  styled : JIO Io V → List (JIO Io V → n Unit) → Sym → Bool → Bool → n Unit
  printInt : JIO Io V → JInt64 → n Unit
  printModule : JIO Io V → Mod → n Unit
  fixup_stdlib_path : List UInt8 → n (List UInt8)
  find_source_file : List UInt8 → n (Option (List UInt8))
  getBoolEnv : String → Bool → n (Option Bool)
  os : JuliaLean.base.path.Platform
  pathOps : JuliaLean.base.path.StringOps
  fs : JuliaLean.base.path.FileSystemOps

def BacktraceOps.pathPrinter {n : Type → Type} {Io V Ty MI CI Meth CInfo DI Mod RF P : Type}
    (o : BacktraceOps n Io V Ty MI CI Meth CInfo DI Mod RF P) : PathPrinter n Io V Mod :=
  ⟨o.p, o.styled, o.printInt, o.printModule, o.fixup_stdlib_path, o.find_source_file, o.getBoolEnv, o.os,
    o.pathOps, o.fs⟩

/-- `printstyled(io, strs...; color, italic, underline)` of string arguments. -/
def sty [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P) (io : JIO Io V) (strs : List String)
    (color : Sym) (italic : Bool := false) (underline : Bool := false) : m Unit :=
  o.styled io (strs.map fun s st => printStr o.p st s) color italic underline

/-- `prefix === nothing || print(io, prefix)`. -/
def printPrefixOpt [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P) (io : JIO Io V) :
    Option P → m Unit
  | none => pure ()
  | some x => o.printPrefix io x

/--
Julia source: base/errorshow.jl:870-886 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# In case the line numbers in the source code have changed since the code was compiled,
# allow packages to set a callback function that corrects them.
# (Used by Revise and perhaps other packages.)
#
# Set this with
#     Base.update_stackframes_callback[] = my_updater!
# where my_updater! takes a single argument and works in-place. The argument will be a
# Vector{Any} storing tuples (sf::StackFrame, nrepetitions::Int), and the updater should
# replace `sf` as needed.
const update_stackframes_callback = Ref{Function}(identity)

const STACKTRACE_MODULECOLORS = Iterators.Stateful(Iterators.cycle([:magenta, :cyan, :green, :yellow]))
const STACKTRACE_FIXEDCOLORS = IdDict(Base => :light_black, Core => :light_black)
# Profile's package colors share the same color cycler.
const STACKTRACE_COLORS_LOCK = ReentrantLock()

```
-/
/- `STACKTRACE_MODULECOLORS`: `Iterators.Stateful` over the cycled colors; `popfirst!` takes
the next one. -/
def cycleColor (taken : Nat) : Sym :=
  match taken % 4 with
  | 0 => "magenta"
  | 1 => "cyan"
  | 2 => "green"
  | _ => "yellow"

/-- The color dictionary (`STACKTRACE_FIXEDCOLORS`, an `IdDict`) and the number of colors taken
from the cycler (`STACKTRACE_MODULECOLORS`). -/
structure ColorState (Mod : Type) where
  dict : List (Mod × Sym)
  taken : Nat

/-- The initial global state: `IdDict(Base => :light_black, Core => :light_black)`, no color taken. -/
def STACKTRACE_FIXEDCOLORS_init (base core : Mod) : ColorState Mod :=
  ⟨[(base, "light_black"), (core, "light_black")], 0⟩

/-- A color dictionary and cycler (the globals above, or a package's own), with the
`STACKTRACE_COLORS_LOCK` that guards them. `update_stackframes_callback` is
`BacktraceOps.updateStackframes`. -/
structure ColorStore (n : Type → Type) (Mod : Type) where
  get : n (ColorState Mod)
  set : ColorState Mod → n Unit
  lock : n Unit
  unlock : n Unit

/--
Julia source: base/errorshow.jl:887-890 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function get_stacktrace_color(key, colordict=STACKTRACE_FIXEDCOLORS, colorcycler=STACKTRACE_MODULECOLORS)
    return @lock STACKTRACE_COLORS_LOCK get!(() -> popfirst!(colorcycler), colordict, key)
end

```
-/
def get_stacktrace_color [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (colors : ColorStore m Mod) (egalMod : Mod → Mod → Bool) (key : Mod) : m Sym := do
  colors.lock
  let body : m Sym := do
    let s ← colors.get
    match s.dict.find? (fun e => egalMod e.1 key) with
    | some e => pure e.2
    | none =>
      let c := cycleColor s.taken
      colors.set ⟨s.dict ++ [(key, c)], s.taken + 1⟩
      pure c
  let c ← tryCatchThe ShowError body (fun e => do colors.unlock; throwThe ShowError e)
  colors.unlock
  pure c

/--
Julia source: base/errorshow.jl:891-892 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const BIG_STACKTRACE_SIZE = 50 # Arbitrary constant chosen here

```
-/
def BIG_STACKTRACE_SIZE : JInt64 := i64 50

/--
Julia source: base/errorshow.jl:893-957 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _backtrace_find_and_remove_cycles(t)
    recorded_positions = IdDict{UInt, Vector{Int}}()
    #= For each frame of hash h, recorded_positions[h] is the list of indices i
    such that hash(t[i-1]) == h, ie the list of positions in which the
    frame appears just before. =#

    max_nested_cycles = 0
    displayed_stackframes = []
    repeated_cycles = Tuple{Int,Int,Int}[]
    # First:  index into `displayed_stackframes` to introduce the cycle bracket on
    # Second: length of the cycle as a count in the trace
    # Third:  number of cycle repetitions

    #= For each entry of the trace, where it ended up in `displayed_stackframes`, or 0 if it
    was collapsed away, so that a cycle can be bracketed from where its turn began. =#
    displayed_at = zeros(Int, length(t))

    t_curr = 1

    while t_curr ≤ length(t)
        t_this = t_curr
        entry = t[t_curr]::Tuple{StackFrame,Int}
        (last_frame, n) = entry
        current_hash = hash(entry)
        positions = get(recorded_positions, current_hash,  Int[])

        t_curr += 1
        recorded_positions[current_hash] = push!(positions, t_curr)

        # Check previous positions for cycles
        ncycles = 0
        nnested_cycles = n > 0
        for k ∈ reverse(eachindex(positions))[2:end] # More recent is more likely
            t_prev = positions[k]
            t_cycle_length = t_curr - t_prev

            # walk trace at current and previous matching positions until matching stops
            t_curr_end = t_curr
            t_prev_end = t_prev
            while t_curr_end < length(t) && t[t_curr_end]::Tuple{StackFrame,Int} == t[t_prev_end]::Tuple{StackFrame,Int}
                t_curr_end += 1
                t_prev_end += 1
            end

            if t_prev_end ≥ t_curr - 1
                #= At least one cycle repeated =#
                ncycles = div(t_curr_end - t_prev + 1, t_cycle_length)
                push!(repeated_cycles, (displayed_at[t_prev - 1], t_cycle_length, ncycles))
                t_curr += t_cycle_length * (ncycles - 1) - 1
                nnested_cycles += 1
            end
        end

        # ensure an outer cycle comes before a contained inner cycle
        sort!(repeated_cycles, by = x -> (x[1], -x[2]))
        max_nested_cycles = max(max_nested_cycles, nnested_cycles)

        if ncycles == 0
            push!(displayed_stackframes, (last_frame, n))
            displayed_at[t_this] = length(displayed_stackframes)
        end
    end
    return displayed_stackframes, repeated_cycles, max_nested_cycles
end

```
-/
/- `t[i] == t[j]` on `Tuple{StackFrame,Int}` entries. -/
def entryEq (a b : Entry MI CI Meth CInfo DI) : Bool := eq_StackFrame a.1 b.1 && a.2 == b.2

/-- The `while t_curr_end < length(t) && t[t_curr_end] == t[t_prev_end]` walk. -/
def cycles_walk [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (t : List (Entry MI CI Meth CInfo DI)) (ce pe : JInt64) : m (JInt64 × JInt64) := do
  if ce.val < t.length then
    if entryEq (← atIdx t ce) (← atIdx t pe) then
      cycles_walk t (addI ce (i64 1)) (addI pe (i64 1))
    else pure (ce, pe)
  else pure (ce, pe)
partial_fixpoint

/-- `isless` on the sort keys `(x[1], -x[2])`. -/
def cycleKeyLe (x y : JInt64 × JInt64 × JInt64) : Bool :=
  x.1.val < y.1.val || (x.1.val == y.1.val && (negI x.2.1).val ≤ (negI y.2.1).val)

/-- The mutable locals of `_backtrace_find_and_remove_cycles`. -/
structure CycleState (MI CI Meth CInfo DI : Type) where
  recorded : List (JInt .u64 × List JInt64)
  max_nested_cycles : JInt64
  displayed : List (Entry MI CI Meth CInfo DI)
  repeated_cycles : List (JInt64 × JInt64 × JInt64)
  displayed_at : List JInt64
  t_curr : JInt64

/-- The `while t_curr ≤ length(t)` loop. -/
def cycles_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P) (t : List (Entry MI CI Meth CInfo DI))
    (st : CycleState MI CI Meth CInfo DI) : m (CycleState MI CI Meth CInfo DI) := do
  if st.t_curr.val ≤ t.length then
    let t_this := st.t_curr
    let entry ← atIdx t st.t_curr
    let (last_frame, n) := entry
    let current_hash := o.hashEntry entry
    let positions := ((st.recorded.find? (fun e => e.1 == current_hash)).map (·.2)).getD []
    let mut t_curr := addI st.t_curr (i64 1)
    -- `recorded_positions[current_hash] = push!(positions, t_curr)`
    let positions := positions ++ [t_curr]
    let recorded := if st.recorded.any (fun e => e.1 == current_hash) then
        st.recorded.map fun e => if e.1 == current_hash then (e.1, positions) else e
      else st.recorded ++ [(current_hash, positions)]
    -- Check previous positions for cycles
    let mut ncycles : JInt64 := i64 0
    let mut nnested_cycles : JInt64 := if n.val > 0 then i64 1 else i64 0
    let mut repeated_cycles := st.repeated_cycles
    -- `for k ∈ reverse(eachindex(positions))[2:end]` (more recent is more likely)
    for k in (List.range (positions.length - 1)).reverse do
      let t_prev ← atIdx positions (natI (k + 1))
      let t_cycle_length := subI t_curr t_prev
      -- walk trace at current and previous matching positions until matching stops
      let (t_curr_end, t_prev_end) ← cycles_walk t t_curr t_prev
      if t_prev_end.val ≥ (subI t_curr (i64 1)).val then
        -- At least one cycle repeated
        ncycles ← ofJl (JuliaLean.base.int.div_BitSigned64
          (addI (subI t_curr_end t_prev) (i64 1)) t_cycle_length)
        let at_ ← atIdx st.displayed_at (subI t_prev (i64 1))
        repeated_cycles := repeated_cycles ++ [(at_, t_cycle_length, ncycles)]
        t_curr := subI (addI t_curr (mulI t_cycle_length (subI ncycles (i64 1)))) (i64 1)
        nnested_cycles := addI nnested_cycles (i64 1)
    -- ensure an outer cycle comes before a contained inner cycle (Julia's default sort is stable)
    repeated_cycles := repeated_cycles.mergeSort cycleKeyLe
    let max_nested_cycles := if st.max_nested_cycles.val ≥ nnested_cycles.val then st.max_nested_cycles
      else nnested_cycles
    let mut displayed := st.displayed
    let mut displayed_at := st.displayed_at
    if ncycles.val == 0 then
      displayed := displayed ++ [(last_frame, n)]
      displayed_at ← setIdx displayed_at t_this (natI displayed.length)
    cycles_loop o t ⟨recorded, max_nested_cycles, displayed, repeated_cycles, displayed_at, t_curr⟩
  else pure st
partial_fixpoint

def _backtrace_find_and_remove_cycles [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (t : List (Entry MI CI Meth CInfo DI)) :
    m (List (Entry MI CI Meth CInfo DI) × List (JInt64 × JInt64 × JInt64) × JInt64) := do
  let st ← cycles_loop o t ⟨[], i64 0, [], [], List.replicate t.length (i64 0), i64 1⟩
  return (st.displayed, st.repeated_cycles, st.max_nested_cycles)

/--
Julia source: base/errorshow.jl:958-993 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _backtrace_print_repetition_closings!(io::IO, i, current_cycles, frame_counter, max_nested_cycles, nactive_cycles, ndigits_max; prefix = nothing)
    while !isempty(current_cycles)
        start_line = current_cycles[end][1]
        cycle_length = current_cycles[end][2]
        end_line = start_line + cycle_length - 1
        repetitions = current_cycles[end][3]
        frame_counter_advance = current_cycles[end][4]

        i != end_line && break

        println(io)
        prefix === nothing || print(io, prefix)
        line_length = (max_nested_cycles - nactive_cycles) + ndigits_max + 2
        nactive_cycles -= 1
        printstyled(io, " ", "│" ^ nactive_cycles, "╰", "─" ^ (line_length); color = :light_black)
        printstyled(io, " repeated $repetitions times"; color = :light_black, italic = true)

        pop!(current_cycles)

        if cycle_length > 1
            # adjust cycle_length in outer cycles to reflect displayed frames consumed by this inner cycle
            for j ∈ eachindex(current_cycles)
                current_cycles[j] = (current_cycles[j][1], current_cycles[j][2] - cycle_length * (repetitions - 1), current_cycles[j][3:4]...)
            end
        else
            # adjust frame_counter_advance in outer cycles to reflect frames consumed by a single repeated frame
            for j ∈ eachindex(current_cycles)
                current_cycles[j] = (current_cycles[j][1:3]..., current_cycles[j][4] + (frame_counter_advance * (current_cycles[j][3] - 1)))
            end
        end

        frame_counter += frame_counter_advance
    end
    return frame_counter, nactive_cycles
end

```
-/
/- `_backtrace_print_repetition_closings!`: returns the mutated `current_cycles` with
`(frame_counter, nactive_cycles)`. -/
def _backtrace_print_repetition_closings [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (io : JIO Io V) (i : JInt64) (current_cycles : List (JInt64 × JInt64 × JInt64 × JInt64))
    (frame_counter max_nested_cycles nactive_cycles ndigits_max : JInt64) (pfx : Option P) :
    m (List (JInt64 × JInt64 × JInt64 × JInt64) × JInt64 × JInt64) := do
  match current_cycles.getLast? with
  | none => pure (current_cycles, frame_counter, nactive_cycles)
  | some (start_line, cycle_length, repetitions, frame_counter_advance) =>
    let end_line := subI (addI start_line cycle_length) (i64 1)
    if i != end_line then return (current_cycles, frame_counter, nactive_cycles)
    printStr o.p io "\n"
    printPrefixOpt o io pfx
    let line_length := addI (addI (subI max_nested_cycles nactive_cycles) ndigits_max) (i64 2)
    let nactive_cycles := subI nactive_cycles (i64 1)
    let bars ← repeatStr "│" nactive_cycles
    let dashes ← repeatStr "─" line_length
    sty o io [" ", bars, "╰", dashes] "light_black"
    sty o io [" repeated " ++ o.stringInt repetitions ++ " times"] "light_black" (italic := true)
    let current_cycles := current_cycles.dropLast
    let current_cycles :=
      if cycle_length.val > 1 then
        -- adjust cycle_length in outer cycles to reflect displayed frames consumed by this inner cycle
        current_cycles.map fun c =>
          (c.1, subI c.2.1 (mulI cycle_length (subI repetitions (i64 1))), c.2.2)
      else
        -- adjust frame_counter_advance in outer cycles to reflect frames consumed by a single repeated frame
        current_cycles.map fun c =>
          (c.1, c.2.1, c.2.2.1, addI c.2.2.2 (mulI frame_counter_advance (subI c.2.2.1 (i64 1))))
    _backtrace_print_repetition_closings o io i current_cycles (addI frame_counter frame_counter_advance)
      max_nested_cycles nactive_cycles ndigits_max pfx
partial_fixpoint

/--
Julia source: base/errorshow.jl:1047-1057 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Gets the topmost parent module that isn't Main
function parentmodule_before_main(m::Module)
    while parentmodule(m) !== m
        pm = parentmodule(m)
        pm == Main && break
        m = pm
    end
    m
end
parentmodule_before_main(x) = parentmodule_before_main(parentmodule(x))

```
-/
def parentmodule_before_main [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (egalMod : Mod → Mod → Bool)
    (parentmodule : Mod → Mod) (isMain : Mod → Bool) (md : Mod) : m Mod := do
  if !(egalMod (parentmodule md) md) then
    let pm := parentmodule md
    if isMain pm then return md
    parentmodule_before_main egalMod parentmodule isMain pm
  else return md
partial_fixpoint

def parentmodule_before_main_Any {X : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (parentmoduleOf : X → Mod) (x : X) : m Mod :=
  parentmodule_before_main o.r.egalMod o.parentmodule o.isMain (parentmoduleOf x)

/--
Julia source: base/errorshow.jl:1102-1125 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_module_path_file(io, modul, file, line, col = 0;
                                modulecolor = :light_black, digit_align_width = 0)
    printstyled(io, " " ^ digit_align_width * "@", color = :light_black)

    # module
    if modul !== nothing && modulecolor !== nothing
        print(io, " ")
        printstyled(io, modul, color = modulecolor)
    end

    # filepath
    file = fixup_stdlib_path(file)
    stacktrace_expand_basepaths() && (file = something(find_source_file(file), file))
    stacktrace_contract_userdir() && (file = contractuser(file))
    print(io, " ")
    dir = dirname(file)
    !isempty(dir) && printstyled(io, dir, Filesystem.path_separator, color = :light_black)

    # filename, separator, line (`?` if unknown), column if available
    printstyled(io, basename(file), ":", line >= 0 ? line : "?"; color = :light_black, underline = true)
    col != 0 && printstyled(io, ":", col; color = :light_black, underline = true)
    nothing
end

```
-/
def print_module_path_file [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : PathPrinter m Io V Mod) (io : JIO Io V)
    (modul : Option Mod) (file : Bytes) (line : JInt64) (col : JInt64 := i64 0)
    (modulecolor : Option Sym := some "light_black") (digit_align_width : JInt64 := i64 0) : m Unit := do
  let pad ← repeatStr " " digit_align_width
  o.styled io [fun st => printStr o.p st (pad ++ "@")] "light_black" false false
  -- module
  match modul, modulecolor with
  | some md, some mc =>
    printStr o.p io " "
    o.styled io [fun st => o.printModule st md] mc false false
  | _, _ => pure ()
  -- filepath
  let file ← o.fixup_stdlib_path file
  let file ← if ← stacktraceExpandBasepaths o.getBoolEnv then
      pure ((← o.find_source_file file).getD file)
    else pure file
  let path ← if ← stacktraceContractUserdir o.getBoolEnv then
      match JuliaLean.base.path.contractuser o.os o.pathOps o.fs ⟨file⟩ with
      | .ok path => pure path
      | .error e => throwThe JuliaLean.base.path.PathError e
    else pure ⟨file⟩
  printStr o.p io " "
  let dir := JuliaLean.base.path.dirname o.os o.pathOps path
  if !dir.bytes.isEmpty then
    o.styled io [fun st => printBytes o.p st dir.bytes,
      fun st => printBytes o.p st [JuliaLean.base.path.separator o.os]] "light_black" false false
  -- filename, separator, line (`?` if unknown), column if available
  let base := JuliaLean.base.path.basename o.os o.pathOps path
  o.styled io [fun st => printBytes o.p st base.bytes, fun st => printStr o.p st ":",
    fun st => if line.val ≥ 0 then o.printInt st line else printStr o.p st "?"] "light_black" false true
  if col.val != 0 then
    o.styled io [fun st => printStr o.p st ":", fun st => o.printInt st col] "light_black" false true

/--
Julia source: base/errorshow.jl:1058-1101 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Print a stack frame where the module color is set manually with `modulecolor`.
function print_stackframe(io, i, frame::StackFrame, ndigits_max::Int, max_nested_cycles::Int, nactive_cycles::Int, ncycle_starts::Int, modulecolor; prefix = nothing)
    file = string(frame.file)
    fl = StackTraces.frame_location(frame)

    # Used by the REPL to make it possible to open
    # the location of a stackframe/method in the editor.
    if haskey(io, :last_shown_line_infos)
        push!(io[:last_shown_line_infos], (string(frame.file), fl.line))
    end

    inlined = getfield(frame, :inlined)
    modul = parentmodule(frame)

    digit_align_width = ndigits_max + 2 + max_nested_cycles - nactive_cycles

    # repeated section bracket line 1
    prefix === nothing || print(io, prefix)
    print(io, " ")
    printstyled(io, "├" ^ (nactive_cycles - ncycle_starts); color = :light_black)
    printstyled(io, "┌" ^ ncycle_starts; color = :light_black)

    # frame number
    print(io, lpad("[" * string(i) * "]", digit_align_width))
    print(io, " ")

    # func name and arguments
    StackTraces.show_spec_linfo(IOContext(io, :backtrace=>true), frame)
    println(io)

    # repeated section bracket line 2
    prefix === nothing || print(io, prefix)
    print(io, " ")
    printstyled(io, "│" ^ nactive_cycles; color = :light_black)

    # @ Module path / file : line
    print_module_path_file(
        io, modul, file, fl.line, fl.col;
        modulecolor, digit_align_width = digit_align_width - 1)

    # inlined
    printstyled(io, inlined ? " [inlined]" : "", color = :light_black)
end

```
-/
def print_stackframe [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P) (io : JIO Io V) (i : JInt64)
    (frame : StackFrame MI CI Meth CInfo DI) (ndigits_max max_nested_cycles nactive_cycles ncycle_starts : JInt64)
    (modulecolor : Sym) (pfx : Option P) : m Unit := do
  let file := frame.file
  let fl ← frame_location o.r frame
  -- Used by the REPL to make it possible to open
  -- the location of a stackframe/method in the editor.
  if haskey io "last_shown_line_infos" then
    o.pushLineInfo (← getindex io "last_shown_line_infos") (frame.file, fl.line)
  let inlined := frame.inlined
  let modul := parentmodule_StackFrame o.r frame
  let digit_align_width := subI (addI (addI ndigits_max (i64 2)) max_nested_cycles) nactive_cycles
  -- repeated section bracket line 1
  printPrefixOpt o io pfx
  printStr o.p io " "
  sty o io [← repeatStr "├" (subI nactive_cycles ncycle_starts)] "light_black"
  sty o io [← repeatStr "┌" ncycle_starts] "light_black"
  -- frame number
  printStr o.p io (o.lpad ("[" ++ o.stringInt i ++ "]") digit_align_width)
  printStr o.p io " "
  -- func name and arguments
  show_spec_linfo o.r o.sc (← withBool o.p o.a io "backtrace" true) frame
  printStr o.p io "\n"
  -- repeated section bracket line 2
  printPrefixOpt o io pfx
  printStr o.p io " "
  sty o io [← repeatStr "│" nactive_cycles] "light_black"
  -- @ Module path / file : line
  print_module_path_file o.pathPrinter io modul (lit file) fl.line fl.col (some modulecolor) (subI digit_align_width (i64 1))
  -- inlined
  sty o io [if inlined then " [inlined]" else ""] "light_black"

/--
Julia source: base/errorshow.jl:1033-1046 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Print a stack frame where the module color is determined by looking up the parent module in
# `modulecolordict`. If the module does not have a color, yet, a new one can be drawn
# from `modulecolorcycler`.
function print_stackframe(io, i, frame::StackFrame, ndigits_max::Int, max_nested_cycles::Int, nactive_cycles::Int, ncycle_starts::Int, modulecolordict, modulecolorcycler; prefix = nothing)
    m = Base.parentmodule(frame)
    modulecolor = if m !== nothing
        m = parentmodule_before_main(m)
        get_stacktrace_color(m, modulecolordict, modulecolorcycler)
    else
        :default
    end
    print_stackframe(io, i, frame, ndigits_max, max_nested_cycles, nactive_cycles, ncycle_starts, modulecolor; prefix)
end

```
-/
def print_stackframe_colors [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P) (io : JIO Io V)
    (i : JInt64) (frame : StackFrame MI CI Meth CInfo DI)
    (ndigits_max max_nested_cycles nactive_cycles ncycle_starts : JInt64) (colors : ColorStore m Mod)
    (pfx : Option P) : m Unit := do
  let modulecolor ← match parentmodule_StackFrame o.r frame with
    | some md => do
      let md ← parentmodule_before_main o.r.egalMod o.parentmodule o.isMain md
      get_stacktrace_color colors o.r.egalMod md
    | none => pure "default"
  print_stackframe o io i frame ndigits_max max_nested_cycles nactive_cycles ncycle_starts modulecolor pfx

/--
Julia source: base/errorshow.jl:994-1032 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_processed_backtrace(io::IO, trace::Vector, num_frames::Int, repeated_cycles::Vector{NTuple{3, Int}}, max_nested_cycles::Int; print_linebreaks::Bool, prefix = nothing)
    println(io)
    prefix === nothing || print(io, prefix)
    println(io, "Stacktrace:")

    ndigits_max = ndigits(num_frames)

    push!(repeated_cycles, (0,0,0)) # repeated_cycles is never empty

    frame_counter = 1
    current_cycles = NTuple{4, Int}[] # adding a value to track amount to advance frame_counter when cycle is closed

    for i in eachindex(trace)
        (frame, n) = trace[i]::Tuple{StackFrame,Int}

        ncycle_starts = 0
        while repeated_cycles[1][1] == i
            cycle = popfirst!(repeated_cycles)
            push!(current_cycles, (cycle..., cycle[2] * (cycle[3] - 1)))
            ncycle_starts += 1
        end
        if n > 1
            push!(current_cycles, (i, 1, n, n - 1))
            ncycle_starts += 1
        end
        nactive_cycles = length(current_cycles)

        print_stackframe(io, frame_counter, frame, ndigits_max, max_nested_cycles, nactive_cycles, ncycle_starts, STACKTRACE_FIXEDCOLORS, STACKTRACE_MODULECOLORS; prefix)

        frame_counter, _nactive_cycles = _backtrace_print_repetition_closings!(io, i, current_cycles, frame_counter, max_nested_cycles, nactive_cycles, ndigits_max; prefix)
        frame_counter += 1

        if i < length(trace)
            println(io)
            print_linebreaks && println(io)
        end
    end
end

```
-/
/- `while repeated_cycles[1][1] == i`: move the cycles starting at `i` to `current_cycles`. -/
def cycle_starts_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (i : JInt64) (repeated_cycles : List (JInt64 × JInt64 × JInt64))
    (current_cycles : List (JInt64 × JInt64 × JInt64 × JInt64)) (ncycle_starts : JInt64) :
    m (List (JInt64 × JInt64 × JInt64) × List (JInt64 × JInt64 × JInt64 × JInt64) × JInt64) := do
  let first ← atIdx repeated_cycles (i64 1)
  if first.1 == i then
    let cycle := first
    cycle_starts_loop i repeated_cycles.tail
      (current_cycles ++ [(cycle.1, cycle.2.1, cycle.2.2, mulI cycle.2.1 (subI cycle.2.2 (i64 1)))])
      (addI ncycle_starts (i64 1))
  else pure (repeated_cycles, current_cycles, ncycle_starts)
partial_fixpoint

def show_processed_backtrace [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P) (colors : ColorStore m Mod)
    (io : JIO Io V) (trace : List (Entry MI CI Meth CInfo DI)) (num_frames : JInt64)
    (repeated_cycles : List (JInt64 × JInt64 × JInt64)) (max_nested_cycles : JInt64)
    (print_linebreaks : Bool) (pfx : Option P := none) : m Unit := do
  printStr o.p io "\n"
  printPrefixOpt o io pfx
  printAll o.p io [printStr o.p io "Stacktrace:", printStr o.p io "\n"]
  let ndigits_max := o.ndigits num_frames
  let mut repeated_cycles := repeated_cycles ++ [(i64 0, i64 0, i64 0)] -- repeated_cycles is never empty
  let mut frame_counter := i64 1
  -- adding a value to track amount to advance frame_counter when cycle is closed
  let mut current_cycles : List (JInt64 × JInt64 × JInt64 × JInt64) := []
  for (entry, idx) in trace.zipIdx do
    let i := natI (idx + 1)
    let (frame, n) := entry
    let (rc, cc, ncs) ← cycle_starts_loop i repeated_cycles current_cycles (i64 0)
    repeated_cycles := rc
    current_cycles := cc
    let mut ncycle_starts := ncs
    if n.val > 1 then
      current_cycles := current_cycles ++ [(i, i64 1, n, subI n (i64 1))]
      ncycle_starts := addI ncycle_starts (i64 1)
    let nactive_cycles := natI current_cycles.length
    print_stackframe_colors o io frame_counter frame ndigits_max max_nested_cycles nactive_cycles ncycle_starts
      colors pfx
    let (cc, fc, _) ← _backtrace_print_repetition_closings o io i current_cycles frame_counter
      max_nested_cycles nactive_cycles ndigits_max pfx
    current_cycles := cc
    frame_counter := addI fc (i64 1)
    if i.val < trace.length then
      printStr o.p io "\n"
      if print_linebreaks then printStr o.p io "\n"

/--
Julia source: base/errorshow.jl:1189-1211 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

function _backtrace_collapse_and_count_repeated_frames(frames::Vector{StackFrame})
    n = 0
    last_frame = StackTraces.UNKNOWN
    tracecount = Any[]
    for frame in frames
        if frame.file != last_frame.file || frame.line != last_frame.line || frame.func != last_frame.func || frame.linfo !== last_frame.linfo ||
                StackTraces.frame_location(frame).col != StackTraces.frame_location(last_frame).col
            if n > 0
                push!(tracecount, (last_frame, n))
            end
            n = 1
            last_frame = frame
        else
            n += 1
        end
    end
    if n > 0
        push!(tracecount, (last_frame, n))
    end
    return tracecount
end

```
-/
def _backtrace_collapse_and_count_repeated_frames [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (frames : List (StackFrame MI CI Meth CInfo DI)) : m (List (Entry MI CI Meth CInfo DI)) := do
  let mut n : JInt64 := i64 0
  let mut last_frame : StackFrame MI CI Meth CInfo DI := JuliaLean.base.stacktraces.UNKNOWN
  let mut tracecount : List (Entry MI CI Meth CInfo DI) := []
  for frame in frames do
    let differ ← if frame.file != last_frame.file || frame.line != last_frame.line ||
        frame.func != last_frame.func || !o.egalLinfo frame.linfo last_frame.linfo then pure true
      else do
        let c1 := (← frame_location o.r frame).col
        let c2 := (← frame_location o.r last_frame).col
        pure (c1 != c2)
    if differ then
      if n.val > 0 then
        tracecount := tracecount ++ [(last_frame, n)]
      n := i64 1
      last_frame := frame
    else
      n := addI n (i64 1)
  if n.val > 0 then
    tracecount := tracecount ++ [(last_frame, n)]
  return tracecount

/--
Julia source: base/errorshow.jl:1212-1230 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _backtrace_remove_kwcall_frames!(trace)
    todelete = findall(trace) do (frame, _)
        code = StackTraces.frame_mi(frame)
        if code isa MethodInstance
            def = code.def
            if def isa Method && def.name !== :kwcall && def.sig <: Tuple{typeof(Core.kwcall),NamedTuple,Any,Vararg}
                # hide kwcall() methods, which are probably internal keyword sorter methods
                # (we print the internal method instead, after demangling
                # the argument list, since it has the right line number info)
                return true
            end
        else # this branch may not be needed, from before current keyword argument handling
            frame.func === :kwcall && return true
        end
        return false
    end
    deleteat!(trace, todelete)
end

```
-/
/- The `findall` predicate of `_backtrace_remove_kwcall_frames!`. -/
def isKwcallFrame [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (frame : StackFrame MI CI Meth CInfo DI) : m Bool :=
  match frame_mi o.r frame with
  | some code => match o.r.miDef code with
    -- hide kwcall() methods, which are probably internal keyword sorter methods
    | .method dfn => if o.r.methName dfn != "kwcall" then o.isKwcallSig (o.r.methSig dfn) else pure false
    | .module _ => pure false
  -- this branch may not be needed, from before current keyword argument handling
  | none => pure (frame.func == "kwcall")

def _backtrace_remove_kwcall_frames [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (trace : List (Entry MI CI Meth CInfo DI)) : m (List (Entry MI CI Meth CInfo DI)) :=
  trace.filterM fun e => do return !(← isKwcallFrame o e.1)

/--
Julia source: base/errorshow.jl:1231-1268 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# For improved user experience, filter out frames for include() implementation
# - see #33065. See also #35371 for extended discussion of internal frames.
function _backtrace_simplify_include_frames!(trace)
    kept_frames = trues(length(trace))
    first_ignored = nothing
    for i in length(trace):-1:1
        frame::StackFrame, _ = trace[i]
        mod = parentmodule(frame)
        if mod === Base && frame.func === :IncludeInto ||
           mod === Core && frame.func === :EvalInto ||
           mod === Base && frame.func === :fl_toplevel_eval
            kept_frames[i] = false
        elseif first_ignored === nothing
            if mod === Base && frame.func === :_include
                # Hide include() machinery by default
                first_ignored = i
            end
        else
            first_ignored = first_ignored::Int
            # Hack: allow `mod==nothing` as a workaround for inlined functions.
            # TODO: Fix this by improving debug info.
            if mod in (Base,Core,nothing) && 1+first_ignored-i <= 5
                if frame.func === :eval
                    kept_frames[i:first_ignored] .= false
                    first_ignored = nothing
                end
            else
                # Bail out to avoid hiding frames in unexpected circumstances
                first_ignored = nothing
            end
        end
    end
    if first_ignored !== nothing
        kept_frames[1:first_ignored] .= false
    end
    keepat!(trace, kept_frames)
end

```
-/
def _backtrace_simplify_include_frames [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (trace : List (Entry MI CI Meth CInfo DI)) : m (List (Entry MI CI Meth CInfo DI)) := do
  let mut kept_frames := List.replicate trace.length true
  let mut first_ignored : Option Nat := none
  for k in List.range trace.length do
    let i := trace.length - k
    let (frame, _) ← atIdx trace (natI i)
    let md := parentmodule_StackFrame o.r frame
    let isBase := md.any o.isBase
    let isCore := md.any o.isCore
    if isBase && frame.func == "IncludeInto" || isCore && frame.func == "EvalInto" ||
        isBase && frame.func == "fl_toplevel_eval" then
      kept_frames := kept_frames.set (i - 1) false
    else
      match first_ignored with
      | none =>
        if isBase && frame.func == "_include" then
          -- Hide include() machinery by default
          first_ignored := some i
      | some fi =>
        -- Hack: allow `mod==nothing` as a workaround for inlined functions.
        if (isBase || isCore || md.isNone) && (1 + (fi : Int) - i) ≤ 5 then
          if frame.func == "eval" then
            kept_frames := setRange kept_frames i fi false
            first_ignored := none
        else
          -- Bail out to avoid hiding frames in unexpected circumstances
          first_ignored := none
  if let some fi := first_ignored then
    kept_frames := setRange kept_frames 1 fi false
  return keepat trace kept_frames

/--
Julia source: base/errorshow.jl:1269-1304 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Functions making up the code loading machinery. Their frames are an implementation
# detail of `using`/`import` and are collapsed away by
# `_backtrace_simplify_loading_frames!` - see #52988.
const _LOADING_INTERNAL_FUNCS = (
    :__require, :_require_prelocked, :__require_prelocked, :_require_from_serialized,
    :_tryrequire_from_serialized, :run_package_callbacks, :run_extension_callbacks,
    :retry_load_extensions, :eval_import_path, :eval_import_path_all, :_eval_import,
    :_eval_using)

# The frames a collapsed run is allowed to be represented by. A run without one of
# these is left alone, so that frames which are only incidentally part of loading
# (e.g. `invoke_in_world`) are never hidden on their own.
const _LOADING_ANCHOR_FUNCS = (:require, :require_stdlib, :include_package_for_output)

function _is_loading_frame(frame::StackFrame)
    mod = parentmodule(frame)
    # Hack: allow `mod === nothing` as a workaround for inlined functions, as in
    # `_backtrace_simplify_include_frames!`
    (mod === Base || mod === nothing) || return false
    file = basename(string(frame.file))
    func = frame.func
    if func === Symbol("macro expansion")
        # the `@lock require_lock` and `@zone` blocks in `require`/`__require`
        return file == "loading.jl" || file == "lock.jl"
    elseif func === :invoke_in_world || func === :invokelatest
        return file == "essentials.jl"
    elseif func === :include || func === :_include
        # `include`ing the package's own source, not a user-level `include`
        return file == "Base.jl" || file == "loading.jl"
    end
    return (file == "loading.jl" || file == "module.jl") &&
           (func in _LOADING_INTERNAL_FUNCS || func in _LOADING_ANCHOR_FUNCS)
end

_is_loading_anchor(frame::StackFrame) = frame.func in _LOADING_ANCHOR_FUNCS

```
-/
def _LOADING_INTERNAL_FUNCS : List Sym :=
  ["__require", "_require_prelocked", "__require_prelocked", "_require_from_serialized",
   "_tryrequire_from_serialized", "run_package_callbacks", "run_extension_callbacks",
   "retry_load_extensions", "eval_import_path", "eval_import_path_all", "_eval_import",
   "_eval_using"]

def _LOADING_ANCHOR_FUNCS : List Sym := ["require", "require_stdlib", "include_package_for_output"]

def _is_loading_frame [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (frame : StackFrame MI CI Meth CInfo DI) : Bool :=
  let md := parentmodule_StackFrame o.r frame
  if !(md.any o.isBase || md.isNone) then false
  else
    let file := (JuliaLean.base.path.basename o.os o.pathOps (toPath frame.file)).bytes
    let func := frame.func
    if func == "macro expansion" then
      -- the `@lock require_lock` and `@zone` blocks in `require`/`__require`
      file == lit "loading.jl" || file == lit "lock.jl"
    else if func == "invoke_in_world" || func == "invokelatest" then
      file == lit "essentials.jl"
    else if func == "include" || func == "_include" then
      -- `include`ing the package's own source, not a user-level `include`
      file == lit "Base.jl" || file == lit "loading.jl"
    else
      (file == lit "loading.jl" || file == lit "module.jl") &&
        (_LOADING_INTERNAL_FUNCS.contains func || _LOADING_ANCHOR_FUNCS.contains func)

def _is_loading_anchor (frame : StackFrame MI CI Meth CInfo DI) : Bool :=
  _LOADING_ANCHOR_FUNCS.contains frame.func

/--
Julia source: base/errorshow.jl:1305-1345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# For improved user experience, collapse runs of frames belonging to the code loading
# machinery down to the single frame that entered it - see #52988. Unlike hiding
# everything thrown through `require`, this keeps frames for user code that runs
# during loading (e.g. a package erroring while its source is being run).
function _backtrace_simplify_loading_frames!(trace)
    stacktrace_full_loading() && return trace
    kept_frames = trues(length(trace))
    i = firstindex(trace)
    while i <= lastindex(trace)
        if !_is_loading_frame(trace[i][1]::StackFrame)
            i += 1
            continue
        end
        # find the extent of this run of loading frames
        j = i
        while j < lastindex(trace) && _is_loading_frame(trace[j+1][1]::StackFrame)
            j += 1
        end
        anchor = nothing
        for k in i:j
            frame = trace[k][1]::StackFrame
            if frame.func === :require || frame.func === :require_stdlib
                anchor = k
                break
            elseif frame.func === :include_package_for_output
                # precompilation runs the package in a worker process, where the whole
                # run is machinery. Represent it by its innermost frame, which at least
                # reports the file being run, rather than by the long `input`/`depot_path`
                # signature of `include_package_for_output` itself.
                anchor = i
            end
        end
        if anchor !== nothing
            kept_frames[i:j] .= false
            kept_frames[anchor] = true
        end
        i = j + 1
    end
    keepat!(trace, kept_frames)
end

```
-/
/- `while j < lastindex(trace) && _is_loading_frame(trace[j+1][1])`. -/
def loading_run_end [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (trace : List (Entry MI CI Meth CInfo DI)) (j : Nat) : m Nat := do
  if j < trace.length then
    let (frame, _) ← atIdx trace (natI (j + 1))
    if _is_loading_frame o frame then loading_run_end o trace (j + 1) else pure j
  else pure j
partial_fixpoint

/-- The anchor of the run `i:j`: the first `require`/`require_stdlib` frame, otherwise `i` when
the run contains `include_package_for_output`. -/
def loading_anchor [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (trace : List (Entry MI CI Meth CInfo DI)) (i j : Nat) : m (Option Nat) := do
  let mut anchor : Option Nat := none
  for k in (List.range (j + 1 - i)).map (· + i) do
    let (frame, _) ← atIdx trace (natI k)
    if frame.func == "require" || frame.func == "require_stdlib" then
      anchor := some k
      break
    else if frame.func == "include_package_for_output" then
      -- precompilation runs the package in a worker process: represent the run by its innermost frame
      anchor := some i
  return anchor

/-- The `while i <= lastindex(trace)` loop. -/
def simplify_loading_loop [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (trace : List (Entry MI CI Meth CInfo DI)) (i : Nat) (kept_frames : List Bool) : m (List Bool) := do
  if i ≤ trace.length then
    let (frame, _) ← atIdx trace (natI i)
    if !_is_loading_frame o frame then
      simplify_loading_loop o trace (i + 1) kept_frames
    else
      -- find the extent of this run of loading frames
      let j ← loading_run_end o trace i
      let anchor ← loading_anchor trace i j
      let kept_frames := match anchor with
        | some a => (setRange kept_frames i j false).set (a - 1) true
        | none => kept_frames
      simplify_loading_loop o trace (j + 1) kept_frames
  else pure kept_frames
partial_fixpoint

def _backtrace_simplify_loading_frames [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (trace : List (Entry MI CI Meth CInfo DI)) : m (List (Entry MI CI Meth CInfo DI)) := do
  if ← stacktraceFullLoading o.getBoolEnv then return trace
  let kept_frames ← simplify_loading_loop o trace 1 (List.replicate trace.length true)
  return keepat trace kept_frames

/--
Julia source: base/errorshow.jl:1346-1409 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Collapse frames that have the same location (in some cases)
function _backtrace_collapse_repeated_locations!(trace)
    kept_frames = trues(length(trace))
    last_frame = nothing
    for i in eachindex(trace)
        frame::StackFrame, _ = trace[i]
        if last_frame !== nothing && frame.file == last_frame.file && frame.line == last_frame.line
            #=
            Handles this case:

            f(g, a; kw...) = error();
            @inline f(a; kw...) = f(identity, a; kw...);
            f(1)

            which otherwise ends up as:

            [4] #f#4 <-- useless
            @ ./REPL[2]:1 [inlined]
            [5] f(a::Int64)
            @ Main ./REPL[2]:1
            =#
            if startswith(sprint(show, last_frame), "#")
                kept_frames[i-1] = false
            end

            #= Handles this case
            g(x, y=1, z=2) = error();
            g(1)

            which otherwise ends up as:

            [2] g(x::Int64, y::Int64, z::Int64)
            @ Main ./REPL[1]:1
            [3] g(x::Int64) <-- useless
            @ Main ./REPL[1]:1
            =#
            m, last_m = StackTraces.frame_method_or_module(frame),
                        StackTraces.frame_method_or_module(last_frame)
            if m isa Method && last_m isa Method
                params, last_params = Base.unwrap_unionall(m.sig).parameters::SimpleVector, Base.unwrap_unionall(last_m.sig).parameters::SimpleVector
                if last_m.nkw != 0
                    pos_sig_params = last_params[(last_m.nkw+2):end]
                    if pos_sig_params == params
                        kept_frames[i] = false
                    end
                end
                if length(last_params) > length(params)
                    issame = true
                    for i = eachindex(params)
                        issame &= params[i] == last_params[i]
                    end
                    if issame
                        kept_frames[i] = false
                    end
                end
            end

            # TODO: Detect more cases that can be collapsed
        end
        last_frame = frame
    end
    keepat!(trace, kept_frames)
end

```
-/
/- `v[a:end]` of a `SimpleVector`: an empty range is in bounds for any `a`. -/
def svecFrom {α : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (v : List α) (a : JInt64) : m (List α) :=
  if a.val > v.length then pure []
  else if a.val < 1 then throwShow (.jl .boundsError)
  else pure (v.drop (a.val - 1).toNat)

/-- `==(v1::SimpleVector, v2::SimpleVector)` (`base/essentials.jl`) over `==` on types. -/
def svecEq {α : Type} (eq : α → α → m Bool) (v1 v2 : List α) : m Bool :=
  if v1.length == v2.length then (v1.zip v2).allM fun (a, b) => eq a b else pure false

def _backtrace_collapse_repeated_locations [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (trace : List (Entry MI CI Meth CInfo DI)) : m (List (Entry MI CI Meth CInfo DI)) := do
  let mut kept_frames := List.replicate trace.length true
  let mut last_frame : Option (StackFrame MI CI Meth CInfo DI) := none
  for idx in List.range trace.length do
    let i := idx + 1
    let (frame, _) ← atIdx trace (natI i)
    if let some lf := last_frame then
      if frame.file == lf.file && frame.line == lf.line then
        -- `#f#4` keyword-sorter frames at the same location
        if (← o.sprintShowFrame lf).head? == some 35 then -- `startswith(…, "#")`
          kept_frames := kept_frames.set (i - 2) false
        -- default-argument methods at the same location
        match frame_method_or_module o.r frame, frame_method_or_module o.r lf with
        | some (.method mth), some (.method last_m) =>
          let params ← o.r.parameters (o.r.unwrap_unionall (o.r.methSig mth))
          let last_params ← o.r.parameters (o.r.unwrap_unionall (o.r.methSig last_m))
          if (o.r.nkw last_m).val != 0 then
            let pos_sig_params ← svecFrom last_params (addI (o.r.nkw last_m) (i64 2))
            if ← svecEq o.tyEq pos_sig_params params then
              kept_frames := kept_frames.set (i - 1) false
          if last_params.length > params.length then
            -- `issame &= params[i] == last_params[i]` for `i = eachindex(params)`
            let mut issame := true
            for (x, y) in params.zip last_params do
              issame := issame && (← o.tyEq x y)
            if issame then
              kept_frames := kept_frames.set (i - 1) false
        | _, _ => pure ()
    last_frame := some frame
  return keepat trace kept_frames

/--
Julia source: base/errorshow.jl:1410-1422 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function process_backtrace(t::Vector{StackFrame})
    tracecount = _backtrace_collapse_and_count_repeated_frames(t)
    process_backtrace(tracecount)
end

function process_backtrace(tracecount::Vector{Any})
    _backtrace_remove_kwcall_frames!(tracecount)
    _backtrace_simplify_include_frames!(tracecount)
    _backtrace_simplify_loading_frames!(tracecount)
    _backtrace_collapse_repeated_locations!(tracecount)
    return tracecount
end

```
-/
def process_backtrace_Any [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (tracecount : List (Entry MI CI Meth CInfo DI)) : m (List (Entry MI CI Meth CInfo DI)) := do
  let tracecount ← _backtrace_remove_kwcall_frames o tracecount
  let tracecount ← _backtrace_simplify_include_frames o tracecount
  let tracecount ← _backtrace_simplify_loading_frames o tracecount
  _backtrace_collapse_repeated_locations o tracecount

def process_backtrace_StackFrame [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P)
    (t : List (StackFrame MI CI Meth CInfo DI)) : m (List (Entry MI CI Meth CInfo DI)) := do
  let tracecount ← _backtrace_collapse_and_count_repeated_frames o t
  process_backtrace_Any o tracecount

/--
Julia source: base/errorshow.jl:1126-1188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
#=

Stacktrace processing pipeline:
1. Raw traces extracted with `backtrace` or `catch_backtrace` as vector of instruction pointers.
2. IP traces converted to frames with `stacktrace`, which may or may not include C frames.
3. Originator trims frames related to itself (e.g. REPL removes REPL-specific frames)
   - CapturedException only keeps a limit of 100 frames by processing before display
4. `process_backtrace` filters a trace for internal implementation or redundant frames and summarizes repeated single frames:
    - `kwcall` frames removed
    - `include`-related stack frames removed
    - code loading (`using`/`import`) stack frames collapsed to the frame that entered loading
    - Some frames that have the same location info are merged
    - Repeated frames are removed and summarized with a count
    - Output is an Any[] containing (StackFrame, count) tuple elements and this form is exposed to e.g. Revise
5. If a trace is too long, cycles are identified and summarized
6. `update_stackframes_callback[]` provides e.g. Revise an opportunity to edit line info

=#

function show_backtrace(io::IO, t::Vector; prefix = nothing)
    if haskey(io, :last_shown_line_infos)
        empty!(io[:last_shown_line_infos])
    end

    # Process backtrace if it has not yet been. A processed backtrace is a Vector{Any}
    # with elements of type Tuple{StackFrame, Int}. (ref #12856)
    if t isa Vector{Any} && (length(t) == 0 || t[1] isa Tuple{StackFrame,Int})
        filtered = t
    else
        # t is a raw trace requiring lookup
        if t isa Vector{<:Union{Base.InterpreterIP,Ptr{Cvoid}}}
            frametrace = stacktrace(t)
        else
            frametrace = t
        end
        filtered = process_backtrace(frametrace)
    end
    isempty(filtered) && return

    nframes = sum(last(x::Tuple{StackFrame,Int}) for x ∈ filtered)

    # don't show a single top-level frame with no location info
    if nframes == 1 && StackTraces.is_top_level_frame(filtered[1][1])
        f = filtered[1][1]::StackFrame
        if f.line == 0 && f.file === :var""
            return
        end
    end

    # Find repeated cycles if trace is too long
    if length(filtered) > BIG_STACKTRACE_SIZE
        filtered, repeated_cycles, max_nested_cycles = _backtrace_find_and_remove_cycles(filtered)
    else
        repeated_cycles = NTuple{3, Int}[]
        max_nested_cycles = any(x -> last(x::Tuple{StackFrame,Int}) > 1, filtered) ? 1 : 0
    end

    # Allow external code to edit information in the frames (e.g. line numbers with Revise)
    try invokelatest(update_stackframes_callback[], filtered) catch end

    show_processed_backtrace(IOContext(io, :backtrace => true), filtered, nframes, repeated_cycles, max_nested_cycles; print_linebreaks = stacktrace_linebreaks(), prefix)
    nothing
end
```
-/
def show_backtrace [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m] (o : BacktraceOps m Io V Ty MI CI Meth CInfo DI Mod RF P) (colors : ColorStore m Mod)
    (io : JIO Io V) (t : BacktraceArg MI CI Meth CInfo DI) (pfx : Option P := none) : m Unit := do
  if haskey io "last_shown_line_infos" then
    o.emptyLineInfos (← getindex io "last_shown_line_infos")
  -- Process backtrace if it has not yet been.
  let filtered ← match t with
    | .processed entries => pure entries
    -- t is a raw trace requiring lookup
    | .raw ips => do process_backtrace_StackFrame o (← stacktrace_trace o.r o.sc ips)
    | .frames frames => process_backtrace_StackFrame o frames
  if filtered.isEmpty then return
  -- `sum` of wrapping `Int` additions (associative, so the reduction order does not matter)
  let nframes := filtered.foldl (fun s x => addI s x.2) (i64 0)
  -- don't show a single top-level frame with no location info
  match filtered with
  | (f, _) :: _ =>
    if nframes.val == 1 && is_top_level_frame f then
      if f.line.val == 0 && f.file == "" then return
  | [] => pure ()
  -- Find repeated cycles if trace is too long
  let (filtered, repeated_cycles, max_nested_cycles) ←
    if filtered.length > BIG_STACKTRACE_SIZE.val then _backtrace_find_and_remove_cycles o filtered
    else pure (filtered, [], if filtered.any (fun x => x.2.val > 1) then i64 1 else i64 0)
  -- Allow external code to edit information in the frames (e.g. line numbers with Revise)
  let filtered ← o.updateStackframes filtered
  show_processed_backtrace o colors (← withBool o.p o.a io "backtrace" true) filtered nframes
    repeated_cycles max_nested_cycles (← stacktraceLinebreaks o.getBoolEnv) pfx



-- Source documentation or spacing; no method body.
-- UNTRANSLATED
-- Source: base/errorshow.jl:1710-1713 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- 
-- # detect the reason which caused an :incomplete expression
-- # from the error message
-- # NOTE: the error messages are defined in src/julia-parser.scm
-- /Source

structure TypeDiffOps (World D Name Mod Ptr Alias : Type) where
  runtime : JuliaLean.base.runtime_internals.TypeOps World Ty D Name Mod Ptr String
  liftRuntime : {A : Type} → JuliaLean.base.io.M World A → m A
  moduleDefined : Name → Bool
  parentModule : Mod → m Mod
  moduleName : Mod → m String
  moduleEqual : Mod → Mod → Bool
  moduleValue : Mod → Ty
  globalBinding : Mod → String → m (Option Ty)
  alias : Ty → JIO Io V → m (Option (Alias × List Ty))
  aliasEqual : Alias → Alias → Bool
  printAlias : JIO Io V → Alias → m Unit
  printName : JIO Io V → Name → m Unit
  printType : JIO Io V → Ty → m Unit
  printSymbol : JIO Io V → String → m Unit
  printModule : JIO Io V → Mod → m Unit
  textColor : String → m String
  errorColor : m String

def diagnosticDatatype {World D Name Mod Ptr Alias : Type}
    (o : TypeDiffOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias)
    (value : Ty) : m D :=
  match o.runtime.asDatatype value with
  | none => throwShow .typeError
  | some value => pure value

def diagnosticAt {A : Type} (values : List A) (index : Nat) : m A :=
  match values[index]? with
  | none => throwShow (.jl .boundsError)
  | some value => pure value

/--
Julia source: base/errorshow.jl:495-501 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_separator(io::IO, use_color::Bool)
    if use_color
        print(io, text_colors[:light_black], ", ", text_colors[:default])
    else
        print(io, ", ")
    end
end
```
-/
def showSeparator (p : IOPrims m Io V) (textColor : String → m String)
    (io : JIO Io V) (useColor : Bool) : m Unit := do
  if useColor then
    printStr p io (← textColor "light_black")
    printStr p io ", "
    printStr p io (← textColor "default")
  else printStr p io ", "

/--
Julia source: base/errorshow.jl:503-511 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_type_match(io::IO, @nospecialize(ty), use_color::Bool)
    if use_color
        print(io, text_colors[:light_black])
        show(io, ty)
        print(io, text_colors[:default])
    else
        show(io, ty)
    end
end
```
-/
def showTypeMatch (p : IOPrims m Io V) (textColor : String → m String)
    (printType : JIO Io V → Ty → m Unit) (io : JIO Io V) (type : Ty) (useColor : Bool) : m Unit := do
  if useColor then
    printStr p io (← textColor "light_black")
    printType io type
    printStr p io (← textColor "default")
  else printType io type

/--
Julia source: base/errorshow.jl:545-574 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Decide whether `sig` and `called` are pairwise-comparable at this level.
# Returns one of:
#   `(sig.parameters, called.parameters, nothing)` — same name, no alias to print
#   `(sa_env, ca_env, alias::GlobalRef)`           — both resolve to the same alias
#   `nothing`                                      — bail; caller falls back to whole-subtree highlighting
function descend_params(io::IO, @nospecialize(sig), @nospecialize(called))
    if sig isa TypeEq && (called isa TypeEq || called isa Core.TypeEgal)
        return Core.svec(type_parameter(sig)), Core.svec(type_parameter(called)), nothing
    end
    sig isa DataType && called isa DataType || return nothing
    sig.name === called.name || return nothing
    sp = (sig::DataType).parameters
    cp = (called::DataType).parameters
    n = length(sp)
    n > 0 && n == length(cp) || return nothing
    sig.name === typename(NamedTuple) && return nothing
    (any(isvarargtype, sp) || any(isvarargtype, cp)) && return nothing
    sa = make_typealias(sig, io)
    ca = make_typealias(called, io)
    if sa === nothing && ca === nothing
        return sp, cp, nothing
    elseif sa !== nothing && ca !== nothing && sa[1] === ca[1]
        se = sa[2]::SimpleVector
        ce = ca[2]::SimpleVector
        length(se) == length(ce) > 0 || return nothing
        return se, ce, sa[1]
    else
        return nothing
    end
end
```
-/
def descendParams {World D Name Mod Ptr Alias : Type}
    (o : TypeDiffOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias)
    (io : JIO Io V) (sig called : Ty) : m (Option (List Ty × List Ty × Option Alias)) := do
  let r := o.runtime
  if r.isTypeEq sig && (r.isTypeEq called || r.isTypeEgal called) then
    return some ([← o.liftRuntime (r.typeParameter sig)], [← o.liftRuntime (r.typeParameter called)], none)
  let some sd := r.asDatatype sig | return none
  let some cd := r.asDatatype called | return none
  if !r.egalName (r.nameOf sd) (r.nameOf cd) then return none
  let sp ← o.liftRuntime (r.parameters sd)
  let cp ← o.liftRuntime (r.parameters cd)
  if !(sp.length > 0 && sp.length == cp.length) then return none
  if r.egalName (r.nameOf sd) r.namedTupleName then return none
  if sp.any r.isVararg || cp.any r.isVararg then return none
  let sa ← o.alias sig io
  let ca ← o.alias called io
  match sa, ca with
  | none, none => return some (sp, cp, none)
  | some (sn, se), some (cn, ce) =>
    if o.aliasEqual sn cn then
      if !(se.length == ce.length && ce.length > 0) then return none
      return some (se, ce, some sn)
    else return none
  | _, _ => return none

/--
Julia source: base/errorshow.jl:576-590 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_type_mismatch(io::IO, @nospecialize(ty), use_color::Bool, top_level::Bool)
    if use_color
        print(io, text_colors[error_color()])
        top_level && print(io, "::")
        show(io, ty)
        print(io, text_colors[:default])
    elseif top_level
        print(io, "!Matched::")
        show(io, ty)
    else
        print(io, "!Matched{")
        show(io, ty)
        print(io, "}")
    end
end
```
-/
def showTypeMismatch {World D Name Mod Ptr Alias : Type}
    (p : IOPrims m Io V)
    (o : TypeDiffOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias)
    (io : JIO Io V) (type : Ty) (useColor topLevel : Bool) : m Unit := do
  if useColor then
    printStr p io (← o.textColor (← o.errorColor))
    if topLevel then printStr p io "::"
    o.printType io type
    printStr p io (← o.textColor "default")
  else if topLevel then
    printStr p io "!Matched::"
    o.printType io type
  else
    printStr p io "!Matched{"
    o.printType io type
    printStr p io "}"

mutual

/--
Julia source: base/errorshow.jl:462-493 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia

# Print `::<sig>` with structural framing (type names, braces) in the default
# color, matching parameters and their separating commas in gray, and the
# topmost differing subtree(s) in `error_color`.
function show_type_diff(io::IO, @nospecialize(sig), @nospecialize(called), use_color::Bool, top_level::Bool=true)
    show_namedtuple_diff(io, sig, called, use_color, top_level) && return nothing
    params = descend_params(io, sig, called)
    if params === nothing
        return show_type_mismatch(io, sig, use_color, top_level)
    end
    top_level && print(io, "::")
    sig_params, called_params, alias = params
    if alias !== nothing
        show_typealias_name(io, alias)
    elseif sig isa TypeEq
        print(io, "Type")
    else
        show_type_name(io, (sig::DataType).name)
    end
    print(io, "{")
    for k in 1:length(sig_params)
        k > 1 && show_separator(io, use_color)
        sp = sig_params[k]
        cp = called_params[k]
        if sp === cp
            show_type_match(io, sp, use_color)
        else
            show_type_diff(io, sp, cp, use_color, #=top_level=#false)
        end
    end
    print(io, "}")
end
```
-/
def showTypeDiff {World D Name Mod Ptr Alias : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : TypeDiffOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias)
    (io : JIO Io V) (sig called : Ty) (useColor : Bool) (topLevel : Bool := true) : m Unit := do
  if ← showNamedtupleDiff p o io sig called useColor topLevel then return ()
  let params ← descendParams o io sig called
  let some (sp, cp, alias) := params | return ← showTypeMismatch p o io sig useColor topLevel
  if topLevel then printStr p io "::"
  match alias with
  | some name => o.printAlias io name
  | none =>
    if o.runtime.isTypeEq sig then printStr p io "Type"
    else o.printName io (o.runtime.nameOf (← diagnosticDatatype o sig))
  printStr p io "{"
  for k in List.range sp.length do
    if k > 0 then showSeparator p o.textColor io useColor
    let s ← diagnosticAt sp k
    let c ← diagnosticAt cp k
    if o.runtime.egal s c then showTypeMatch p o.textColor o.printType io s useColor
    else showTypeDiff p o io s c useColor false
  printStr p io "}"
partial_fixpoint

/--
Julia source: base/errorshow.jl:513-543 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_namedtuple_diff(io::IO, @nospecialize(sig), @nospecialize(called),
                              use_color::Bool, top_level::Bool)
    sig isa DataType && called isa DataType || return false
    sig.name === typename(NamedTuple) && called.name === typename(NamedTuple) || return false
    length(sig.parameters) == 2 && length(called.parameters) == 2 || return false
    s_syms, s_types = sig.parameters
    c_syms, c_types = called.parameters
    s_syms isa Tuple && c_syms isa Tuple && s_syms === c_syms || return false
    s_types isa DataType && c_types isa DataType || return false
    n = length(s_syms)::Int
    length(s_types.parameters) == n == length(c_types.parameters) || return false
    (isvatuple(s_types) || isvatuple(c_types)) && return false
    top_level && print(io, "::")
    print(io, "@NamedTuple{")
    for i in 1:n
        i > 1 && show_separator(io, use_color)
        show_sym(io, s_syms[i])
        sp = s_types.parameters[i]
        cp = c_types.parameters[i]
        if sp === cp
            sp === Any && continue   # match `show_at_namedtuple` and don't print `::Any`
            print(io, "::")
            show_type_match(io, sp, use_color)
        else
            print(io, "::")
            show_type_diff(io, sp, cp, use_color, #=top_level=#false)
        end
    end
    print(io, "}")
    return true
end
```
-/
def showNamedtupleDiff {World D Name Mod Ptr Alias : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : TypeDiffOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias)
    (io : JIO Io V) (sig called : Ty) (useColor topLevel : Bool) : m Bool := do
  let r := o.runtime
  let some sd := r.asDatatype sig | return false
  let some cd := r.asDatatype called | return false
  if !(r.egalName (r.nameOf sd) r.namedTupleName && r.egalName (r.nameOf cd) r.namedTupleName) then return false
  let sp ← o.liftRuntime (r.parameters sd)
  let cp ← o.liftRuntime (r.parameters cd)
  if !(sp.length == 2 && cp.length == 2) then return false
  let ss ← diagnosticAt sp 0
  let st ← diagnosticAt sp 1
  let cs ← diagnosticAt cp 0
  let ct ← diagnosticAt cp 1
  if !(r.isTuple ss && r.isTuple cs && r.egal ss cs) then return false
  let some st := r.asDatatype st | return false
  let some ct := r.asDatatype ct | return false
  let some symbols := r.symbolTuple ss | throwShow .typeError
  let sp ← o.liftRuntime (r.parameters st)
  let cp ← o.liftRuntime (r.parameters ct)
  if !(sp.length == symbols.length && symbols.length == cp.length) then return false
  if r.isVaTuple st || r.isVaTuple ct then return false
  if topLevel then printStr p io "::"
  printStr p io "@NamedTuple{"
  for k in List.range symbols.length do
    if k > 0 then showSeparator p o.textColor io useColor
    o.printSymbol io (← diagnosticAt symbols k)
    let s ← diagnosticAt sp k
    let c ← diagnosticAt cp k
    if r.egal s c then
      if r.egal s r.any then continue
      printStr p io "::"
      showTypeMatch p o.textColor o.printType io s useColor
    else
      printStr p io "::"
      showTypeDiff p o io s c useColor false
  printStr p io "}"
  return true
partial_fixpoint

end

def resolvesToSelfModules {World D Name Mod Ptr Alias : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDiffOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias)
    (module : Mod) : m Bool := do
  let parent ← o.parentModule module
  if o.moduleEqual parent module then return true
  match ← o.globalBinding parent (← o.moduleName module) with
  | none => return false
  | some value =>
    if !o.runtime.egal value (o.moduleValue module) then return false
    resolvesToSelfModules o parent
partial_fixpoint

/--
Julia source: base/errorshow.jl:592-601 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _resolves_to_self(tn::Core.TypeName)
    isdefined(tn, :module) || return true
    m = tn.module
    (isdefined(m, tn.name) && getglobal(m, tn.name) === tn.wrapper) || return false
    while (p = parentmodule(m)) !== m
        (isdefined(p, nameof(m)) && getglobal(p, nameof(m)) === m) || return false
        m = p
    end
    return true
end
```
-/
def resolvesToSelf {World D Name Mod Ptr Alias : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (o : TypeDiffOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias)
    (name : Name) : m Bool := do
  if !o.moduleDefined name then return true
  let r := o.runtime
  let module := r.module name
  match ← o.globalBinding module (r.name name) with
  | none => return false
  | some value => if !r.egal value (r.wrapper name) then return false
  resolvesToSelfModules o module

structure CandidateOps (A World D Name Mod Ptr Alias Method : Type) where
  diff : TypeDiffOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias
  reflection : MethodReflection (m := m) A Ty Mod Method
  asUnionall : Ty → Option (Ty × Ty)
  hasFreeTypevars : Ty → Bool
  functionOfType : Ty → m A
  datatypeFunction : A → Option D
  isaFunction : A → Ty → Bool
  opaqueClosure : A → Bool
  signatureType : A → Ty → m Ty
  getindex : A
  setindex : A
  keywordDeclaration : Method → m (List String)
  showSignatureFunction : JIO Io V → Ty → m Unit
  showMethodParams : JIO Io V → List Ty → m Unit
  newBuffer : m Io
  takeString : Io → m String
  updatedLocation : Method → m (Option String × Clong)
  methodFile : Method → m String
  primaryWorld : Method → Clong
  withOutputColor : String → JIO Io V → (JIO Io V → m Unit) → m Unit

/--
Julia source: base/errorshow.jl:603-654 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_shadowed_type_hint(io::IO, @nospecialize(f), san_arg_types_param::Vector{Any})
    reported = IdSet{Core.TypeName}()
    ft = Core.Typeof(f)
    for method in methods(f)
        msig = unwrap_unionall(method.sig)::DataType
        mparams = msig.parameters

        # skip methods where the arity can't match the call
        nargs = length(san_arg_types_param)
        is_va = !isempty(mparams) && isa(mparams[end], Core.TypeofVararg)
        is_va || nargs == length(mparams) - 1 || continue

        # build a list of potential shadows, max one candidate per argument
        new_args = copy(san_arg_types_param)
        shadows = Tuple{Core.TypeName,Core.TypeName}[]
        for i in 1:nargs
            # everything past nargs+1 hits vararg parameter
            expected = mparams[min(i + 1, length(mparams))]
            isa(expected, Core.TypeofVararg) && (expected = unwrapva(expected))

            e_dt = unwrap_unionall(expected); isa(e_dt, DataType) || continue
            a_dt = unwrap_unionall(san_arg_types_param[i]); isa(a_dt, DataType) || continue
            e_tn, a_tn = e_dt.name, a_dt.name

            # actual shadowing heuristics
            e_tn === a_tn && continue
            e_tn.name === a_tn.name || continue
            isdefined(e_tn, :module) && isdefined(a_tn, :module) || continue
            new_args[i] = rewrap_unionall(expected, method.sig)
            push!(shadows, (a_tn, e_tn))
        end
        isempty(shadows) && continue
        # make sure our suggestion hits an actual method
        Tuple{ft, new_args...} <: method.sig || continue
        for (a_tn, e_tn) in shadows
            # don't print too many hints
            a_tn in reported && continue
            push!(reported, a_tn)
            if !_resolves_to_self(e_tn) || !_resolves_to_self(a_tn)
                print(io, "\nHint: `")
                show_unquoted(io, a_tn.module); print(io, ".", a_tn.name)
                print(io, "` appears to have been redefined, and methods refer to the older definition.")
            else
                print(io, "\nHint: You may have intended `")
                show_unquoted(io, e_tn.module); print(io, ".", e_tn.name)
                print(io, "` rather than `")
                show_unquoted(io, a_tn.module); print(io, ".", a_tn.name)
                print(io, "`.")
            end
        end
    end
end
```
-/
def showShadowedTypeHint {A World D Name Mod Ptr Alias Method : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : CandidateOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (signature : Method → Ty) (io : JIO Io V) (f : A) (args : List Ty) : m Unit := do
  let r := o.diff.runtime
  let mut reported : List Name := []
  let ft := o.reflection.coreTypeof f
  for method in ← o.reflection.methods f do
    let msig ← diagnosticDatatype o.diff (r.unwrap (signature method))
    let mparams ← o.diff.liftRuntime (r.parameters msig)
    let nargs := args.length
    let isVa := match mparams.getLast? with
      | none => false
      | some type => r.isVararg type
    if !(isVa || (nargs : Int) == (mparams.length : Int) - 1) then continue
    let mut newArgs := args
    let mut shadows : List (Name × Name) := []
    for i in List.range nargs do
      let mut expected ← diagnosticAt mparams (min (i + 2) mparams.length - 1)
      if r.isVararg expected then expected := r.unwrapVararg expected
      let some edt := r.asDatatype (r.unwrap expected) | continue
      let actual ← diagnosticAt args i
      let some adt := r.asDatatype (r.unwrap actual) | continue
      let en := r.nameOf edt
      let an := r.nameOf adt
      if r.egalName en an then continue
      if r.name en != r.name an then continue
      if !(o.diff.moduleDefined en && o.diff.moduleDefined an) then continue
      newArgs := newArgs.set i (o.reflection.rewrap expected (signature method))
      shadows := shadows ++ [(an, en)]
    if shadows.isEmpty then continue
    if !(← o.reflection.types.subtype (o.reflection.tupleType (ft :: newArgs)) (signature method)) then continue
    for (an, en) in shadows do
      if reported.any (r.egalName an) then continue
      reported := reported ++ [an]
      let redefined ← if !(← resolvesToSelf o.diff en) then pure true
        else pure (!(← resolvesToSelf o.diff an))
      if redefined then
        printStr p io "\nHint: `"
        o.diff.printModule io (r.module an)
        printStr p io "."
        printStr p io (r.name an)
        printStr p io "` appears to have been redefined, and methods refer to the older definition."
      else
        printStr p io "\nHint: You may have intended `"
        o.diff.printModule io (r.module en)
        printStr p io "."
        printStr p io (r.name en)
        printStr p io "` rather than `"
        o.diff.printModule io (r.module an)
        printStr p io "."
        printStr p io (r.name an)
        printStr p io "`."

def candidateUnionallEnv {A World D Name Mod Ptr Alias Method : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : CandidateOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (io : JIO Io V) (variables : List Ty) (sig : Ty) : m (JIO Io V × List Ty × Ty) := do
  match o.asUnionall sig with
  | none => pure (io, variables, sig)
  | some (var, body) =>
    let next ← IOContext_pair p a (JuliaLean.base.dict.fieldConv String) (typeConv a) io ("unionall_env", var)
    candidateUnionallEnv p a o (.context next) (variables ++ [var]) body
partial_fixpoint

def printCandidateArgument {World D Name Mod Ptr Alias : Type}
    (p : IOPrims m Io V)
    (o : TypeDiffOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias)
    (io : JIO Io V) (type : Ty) (vararg : Bool) : m Unit := do
  o.printType io type
  if vararg then printStr p io "..."

/--
Julia source: base/errorshow.jl:656-869 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show_method_candidates(io::IO, ex::MethodError, kwargs=[])
    @nospecialize io
    is_arg_types = !isa(ex.args, Tuple)
    arg_types = is_arg_types ? ex.args : typesof(ex.args...)
    arg_types_param = Any[(unwrap_unionall(arg_types)::DataType).parameters...]
    arg_types_param = Any[rewrap_unionall(a, arg_types) for a in arg_types_param]
    # Displays the closest candidates of the given function by looping over the
    # functions methods and counting the number of matching arguments.
    f = ex.f
    lines = String[]
    line_score = Int[]
    # These functions are special cased to only show if first argument is matched.
    special = f === convert || f === getindex || f === setindex!
    f isa Core.Builtin && return # `methods` isn't very useful for a builtin
    funcs = Tuple{Any,Vector{Any}}[(f, arg_types_param)]

    # An incorrect call method produces a MethodError for convert.
    # It also happens that users type convert when they mean call. So
    # pool MethodErrors for these two functions.
    if f === convert && !isempty(arg_types_param)
        at1 = arg_types_param[1]
        if isType(at1) && !has_free_typevars(at1)
            at1p = type_parameter(at1)
            if at1p isa Type
                push!(funcs, (at1p, arg_types_param[2:end]))
            end
        end
    end

    # helpful when a parameterized struct has an unparameterized inner constructor
    show_constructor_hint = isa(f, DataType) && (f !== f.name.wrapper) && isempty(methods(f))
    if show_constructor_hint
        push!(funcs, (f.name.wrapper, arg_types_param))
    end

    for (func, arg_types_param) in funcs
        for method in methods(func)
            buf = IOBuffer()
            iob0 = iob = IOContext(buf, io)
            tv = Any[]
            if func isa Core.OpaqueClosure
                sig0 = signature_type(func, typeof(func).parameters[1])
            else
                sig0 = method.sig
            end
            while isa(sig0, UnionAll)
                push!(tv, sig0.var)
                iob = IOContext(iob, :unionall_env => sig0.var)
                sig0 = sig0.body
            end
            sig0 = sig0::DataType
            s1 = sig0.parameters[1]
            if !isa(func, rewrap_unionall(s1, method.sig))
                # function itself doesn't match
                continue
            else
                print(iob, "  ")
                show_signature_function(iob, s1)
            end
            print(iob, "(")
            t_i = copy(arg_types_param)
            right_matches = 0
            sig = sig0.parameters[2:end]
            use_color = get(io, :color, false)::Bool
            for i = 1 : min(length(t_i), length(sig))
                i > 1 && show_separator(iob, use_color)
                # If isvarargtype then it checks whether the rest of the input arguments matches
                # the varargtype
                if Base.isvarargtype(sig[i])
                    sigstr = Core.svec(unwrapva(unwrap_unionall(sig[i])), "...")
                    j = length(t_i)
                else
                    sigstr = Core.svec(sig[i],)
                    j = i
                end
                # Checks if the type of arg 1:i of the input intersects with the current method
                t_in = typeintersect(rewrap_unionall(Tuple{sig[1:i]...}, method.sig),
                                     rewrap_unionall(Tuple{t_i[1:j]...}, method.sig))
                # If the function is one of the special cased then it should break the loop if
                # the type of the first argument is not matched.
                t_in === Union{} && special && i == 1 && break
                if t_in === Union{}
                    if Base.isvarargtype(sig[i])
                        if use_color
                            let sigstr=sigstr
                                Base.with_output_color(Base.error_color(), iob) do iob
                                    print(iob, "::", sigstr...)
                                end
                            end
                        else
                            print(iob, "!Matched::", sigstr...)
                        end
                    else
                        show_type_diff(iob, sig[i], t_i[i], use_color)
                    end
                    # If there is no typeintersect then the type signature from the method is
                    # inserted in t_i this ensures if the type at the next i matches the type
                    # signature then there will be a type intersect
                    t_i[i] = sig[i]
                else
                    right_matches += j==i ? 1 : 0
                    if use_color
                        print(iob, text_colors[:light_black], "::", sigstr..., text_colors[:default])
                    else
                        print(iob, "::", sigstr...)
                    end
                end
            end
            special && right_matches == 0 && continue

            if length(t_i) > length(sig) && !isempty(sig) && Base.isvarargtype(sig[end])
                # It ensures that methods like f(a::AbstractString...) gets the correct
                # number of right_matches
                for t in arg_types_param[length(sig):end]
                    if t <: rewrap_unionall(unwrapva(unwrap_unionall(sig[end])), method.sig)
                        right_matches += 1
                    end
                end
            end

            if length(t_i) < length(sig)
                # If the methods args is longer than input then the method
                # arguments is printed as not a match
                for (k, sigtype) in enumerate(sig[length(t_i)+1:end])
                    sigtype = isvarargtype(sigtype) ? unwrap_unionall(sigtype) : sigtype
                    if Base.isvarargtype(sigtype)
                        sigstr = Core.svec(unwrapva(sigtype::Core.TypeofVararg), "...")
                    else
                        sigstr = Core.svec(sigtype,)
                    end
                    if !((min(length(t_i), length(sig)) == 0) && k==1)
                        show_separator(iob, use_color)
                    end
                    if k == 1 && Base.isvarargtype(sigtype)
                        # There wasn't actually a mismatch - the method match failed for
                        # some other reason, e.g. world age. Just print the sigstr.
                        print(iob, sigstr...)
                    elseif get(io, :color, false)::Bool
                        let sigstr=sigstr
                            Base.with_output_color(Base.error_color(), iob) do iob
                                print(iob, "::", sigstr...)
                            end
                        end
                    else
                        print(iob, "!Matched::", sigstr...)
                    end
                end
            end
            kwords = kwarg_decl(method)
            if !isempty(kwords)
                print(iob, "; ")
                join(iob, kwords, ", ")
            end
            print(iob, ")")
            show_method_params(iob0, tv)
            file, line = updated_methodloc(method)
            if file === nothing
                file = string(method.file)
            end
            stacktrace_contract_userdir() && (file = contractuser(file))

            if !isempty(kwargs)::Bool
                unexpected = Symbol[]
                if isempty(kwords) || !(any(endswith(string(kword), "...") for kword in kwords))
                    for (k, _) in kwargs
                        if !(k::Symbol in kwords)
                            push!(unexpected, k::Symbol)
                        end
                    end
                end
                if !isempty(unexpected)
                    Base.with_output_color(Base.error_color(), iob) do iob
                        plur = length(unexpected) > 1 ? "s" : ""
                        print(iob, " got unsupported keyword argument$plur \"", join(unexpected, "\", \""), "\"")
                    end
                end
            end
            if ex.world < reinterpret(UInt, method.primary_world)
                print(iob, " (method too new to be called from this world context.)")
            end
            println(iob)

            m = parentmodule_before_main(method)
            modulecolor = get_stacktrace_color(m)
            print_module_path_file(iob, m, string(file), line; modulecolor, digit_align_width = 3)
            push!(lines, takestring!(buf))
            push!(line_score, -(right_matches * 2 + (length(arg_types_param) < 2 ? 1 : 0)))
        end
    end

    if !isempty(lines) # Display up to three closest candidates
        Base.with_output_color(:normal, io) do io
            if show_constructor_hint
                print(io, "\n\nHint: constructors are defined for `", f.name.wrapper,
                    "`, but not for `", f, "`:")
            else
                print(io, "\n\nClosest candidates are:")
            end
            permute!(lines, sortperm(line_score))
            i = 0
            for line in lines
                println(io)
                if i >= 3
                    print(io, "  ...")
                    break
                end
                i += 1
                print(io, line)
            end
            println(io) # extra newline for spacing to stacktrace
        end
    end
    nothing
end
```
-/
def showMethodCandidates {A K World D Name Mod Ptr Alias MI CI Method CInfo DI RF P : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    [MonadExceptOf JuliaLean.base.path.PathError m]
    (p : IOPrims m Io V) (a : AnyOps V Ty)
    (o : CandidateOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (b : BacktraceOps m Io V Ty MI CI Method CInfo DI Mod RF P)
    (colors : ColorStore m Mod) (symbol : K → m String)
    (io : JIO Io V) (ex : MethodError A Ty) (kwargs : List (K × A) := []) : m Unit := do
  let r := o.diff.runtime
  let mr := o.reflection
  let argTypes := match ex.arguments with
    | .inr type => type
    | .inl args => typesof mr.coreTypeof mr.tupleType args
  let dt ← diagnosticDatatype o.diff (r.unwrap argTypes)
  let argTypesParam ← o.diff.liftRuntime (r.parameters dt)
  let argTypesParam := argTypesParam.map (fun value => mr.rewrap value argTypes)
  let f := ex.function
  let mut lines : List (String × Clong) := []
  let special := mr.equal f mr.convert || mr.equal f o.getindex || mr.equal f o.setindex
  if mr.isBuiltin f then return ()
  let mut funcs := [(f, argTypesParam)]
  if mr.equal f mr.convert && !argTypesParam.isEmpty then
    let at1 ← diagnosticAt argTypesParam 0
    if JuliaLean.base.runtime_internals.isType r at1 && !o.hasFreeTypevars at1 then
      let at1p ← o.diff.liftRuntime (r.typeParameter at1)
      if r.isAType at1p then
        funcs := funcs ++ [(← o.functionOfType at1p, argTypesParam.drop 1)]
  let constructorHint ← match o.datatypeFunction f with
    | none => pure false
    | some dt => do
      let wrapper ← o.functionOfType (r.wrapper (r.nameOf dt))
      if mr.equal f wrapper then pure false else pure (← mr.methods f).isEmpty
  if constructorHint then
    let dt ← match o.datatypeFunction f with
      | none => throwShow .typeError
      | some dt => pure dt
    funcs := funcs ++ [(← o.functionOfType (r.wrapper (r.nameOf dt)), argTypesParam)]
  for (func, argTypesParam) in funcs do
    for method in ← mr.methods func do
      let buf ← o.newBuffer
      let iob0 := JIO.context (← IOContext_IO_IO p a (.plain buf) io)
      let sig0 ← if o.opaqueClosure func then do
          let dt ← diagnosticDatatype o.diff (mr.typeof func)
          let parameters ← o.diff.liftRuntime (r.parameters dt)
          o.signatureType func (← diagnosticAt parameters 0)
        else pure (b.r.methSig method)
      let (iob, variables, sig0) ← candidateUnionallEnv p a o iob0 [] sig0
      let sig0 ← diagnosticDatatype o.diff sig0
      let parameters ← o.diff.liftRuntime (r.parameters sig0)
      let s1 ← diagnosticAt parameters 0
      if !o.isaFunction func (mr.rewrap s1 (b.r.methSig method)) then continue
      printStr p iob "  "
      o.showSignatureFunction iob s1
      printStr p iob "("
      let mut ti := argTypesParam
      let mut rightMatches := i64 0
      let sig := parameters.drop 1
      let useColor ← assertBool a (getIO p io "color" false)
      for index in List.range (min ti.length sig.length) do
        if index > 0 then showSeparator p o.diff.textColor iob useColor
        let st ← diagnosticAt sig index
        let isVararg := r.isVararg st
        let printed := if isVararg then r.unwrapVararg (r.unwrap st) else st
        let j := if isVararg then ti.length else index + 1
        let tin ← o.diff.liftRuntime (r.typeintersect
          (mr.rewrap (mr.tupleType (sig.take (index + 1))) (b.r.methSig method))
          (mr.rewrap (mr.tupleType (ti.take j)) (b.r.methSig method)))
        if r.egal tin r.bottom && special && index == 0 then break
        if r.egal tin r.bottom then
          if isVararg then
            if useColor then
              o.withOutputColor (← o.diff.errorColor) iob (fun stream => do
                printStr p stream "::"
                printCandidateArgument p o.diff stream printed true)
            else
              printStr p iob "!Matched::"
              printCandidateArgument p o.diff iob printed true
          else
            showTypeDiff p o.diff iob st (← diagnosticAt ti index) useColor
          ti := ti.set index st
        else
          rightMatches := addI rightMatches (if j == index + 1 then i64 1 else i64 0)
          if useColor then printStr p iob (← o.diff.textColor "light_black")
          printStr p iob "::"
          printCandidateArgument p o.diff iob printed isVararg
          if useColor then printStr p iob (← o.diff.textColor "default")
      if special && rightMatches.val == 0 then continue
      if ti.length > sig.length && !sig.isEmpty then
        let last ← diagnosticAt sig (sig.length - 1)
        if r.isVararg last then
          for type in argTypesParam.drop (sig.length - 1) do
            if ← mr.types.subtype type (mr.rewrap (r.unwrapVararg (r.unwrap last)) (b.r.methSig method)) then
              rightMatches := addI rightMatches (i64 1)
      if ti.length < sig.length then
        for (k, original) in (sig.drop ti.length).zipIdx do
          let sigtype := if r.isVararg k then r.unwrap k else k
          let vararg := r.isVararg sigtype
          let printed := if vararg then r.unwrapVararg sigtype else sigtype
          if !(min ti.length sig.length == 0 && original == 0) then
            showSeparator p o.diff.textColor iob useColor
          if original == 0 && vararg then
            printCandidateArgument p o.diff iob printed vararg
          else if ← assertBool a (getIO p io "color" false) then
            o.withOutputColor (← o.diff.errorColor) iob (fun stream => do
              printStr p stream "::"
              printCandidateArgument p o.diff stream printed vararg)
          else
            printStr p iob "!Matched::"
            printCandidateArgument p o.diff iob printed vararg
      let kwords ← o.keywordDeclaration method
      if !kwords.isEmpty then
        printStr p iob "; "
        printStr p iob (String.intercalate ", " kwords)
      printStr p iob ")"
      o.showMethodParams iob0 variables
      let (file, line) ← o.updatedLocation method
      let file ← match file with
        | none => o.methodFile method
        | some file => pure file
      let file ← if ← stacktraceContractUserdir b.getBoolEnv then
          match JuliaLean.base.path.contractuser b.os b.pathOps b.fs (toPath file) with
          | .ok path => pure (String.fromUTF8! ⟨path.bytes.toArray⟩)
          | .error error => throwThe JuliaLean.base.path.PathError error
        else pure file
      if !kwargs.isEmpty then
        let mut unexpected : List String := []
        if kwords.isEmpty || !(kwords.any (fun word => word.endsWith "...")) then
          for (key, _) in kwargs do
            let key ← symbol key
            if !kwords.contains key then unexpected := unexpected ++ [key]
        if !unexpected.isEmpty then
          o.withOutputColor (← o.diff.errorColor) iob (fun stream => do
            let plural := if unexpected.length > 1 then "s" else ""
            printStr p stream (" got unsupported keyword argument" ++ plural ++ " \"")
            printStr p stream (String.intercalate "\", \"" unexpected)
            printStr p stream "\"")
      if ex.world.val < (JInt.wrap .u64 (o.primaryWorld method).val).val then
        printStr p iob " (method too new to be called from this world context.)"
      printStr p iob "\n"
      let module ← parentmodule_before_main_Any b b.r.methModule method
      let color ← get_stacktrace_color colors b.r.egalMod module
      print_module_path_file b.pathPrinter iob (some module) (lit file) line (modulecolor := some color) (digit_align_width := i64 3)
      let text ← o.takeString buf
      let score := negI (addI (mulI rightMatches (i64 2)) (if argTypesParam.length < 2 then i64 1 else i64 0))
      lines := lines ++ [(text, score)]
  if !lines.isEmpty then
    o.withOutputColor "normal" io (fun stream => do
      if constructorHint then
        let dt ← match o.datatypeFunction f with
          | none => throwShow .typeError
          | some dt => pure dt
        printStr p stream "\n\nHint: constructors are defined for `"
        o.diff.printType stream (r.wrapper (r.nameOf dt))
        printStr p stream "`, but not for `"
        let ft ← match o.datatypeFunction f with
          | none => throwShow .typeError
          | some dt => pure dt
        o.diff.printType stream (r.datatypeValue ft)
        printStr p stream "`:"
      else printStr p stream "\n\nClosest candidates are:"
      let ordered := lines.mergeSort (fun left right => decide (left.2.val ≤ right.2.val))
      for (line, index) in ordered.zipIdx do
        printStr p stream "\n"
        if index ≥ 3 then
          printStr p stream "  ..."
          break
        printStr p stream line.1
      printStr p stream "\n")


structure CompareOps (World D Name Mod Ptr Alias : Type) where
  diff : TypeDiffOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias
  printValue : JIO Io V → Ty → m Unit
  styled : PrintStyled m Io V

/--
Julia source: base/errorshow.jl:235-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_with_compare(io::IO, @nospecialize(a), @nospecialize(b), color::Symbol)
    if a === b
        print(io, a)
    else
        printstyled(io, a; color=color)
    end
end
```
-/
def printWithCompareAny {World D Name Mod Ptr Alias : Type}
    (o : CompareOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias)
    (io : JIO Io V) (a b : Ty) (color : String) : m Unit := do
  if o.diff.runtime.egal a b then o.printValue io a
  else o.styled io [fun stream => o.printValue stream a] color false

mutual

/--
Julia source: base/errorshow.jl:215-233 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_with_compare(io::IO, @nospecialize(a::DataType), @nospecialize(b::DataType), color::Symbol)
    if a.name === b.name
        Base.show_type_name(io, a.name)
        n = length(a.parameters)
        n > 0 || return
        print(io, '{')
        for i = 1:n
            if i > length(b.parameters)
                printstyled(io, a.parameters[i], color=color)
            else
                print_with_compare(io::IO, a.parameters[i], b.parameters[i], color)
            end
            i < n && print(io, ',')
        end
        print(io, '}')
    else
        printstyled(io, a; color=color)
    end
end
```
-/
def printWithCompareDatatype {World D Name Mod Ptr Alias : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : CompareOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias)
    (io : JIO Io V) (a b : D) (color : String) : m Unit := do
  let r := o.diff.runtime
  if r.egalName (r.nameOf a) (r.nameOf b) then
    o.diff.printName io (r.nameOf a)
    let ap ← o.diff.liftRuntime (r.parameters a)
    if ap.isEmpty then return ()
    printStr p io "{"
    for index in List.range ap.length do
      let bp ← o.diff.liftRuntime (r.parameters b)
      let av ← diagnosticAt ap index
      if index ≥ bp.length then
        o.styled io [fun stream => o.printValue stream av] color false
      else printWithCompare p o io av (← diagnosticAt bp index) color
      if index + 1 < ap.length then printStr p io ","
    printStr p io "}"
  else o.styled io [fun stream => o.printValue stream (r.datatypeValue a)] color false
partial_fixpoint

def printWithCompare {World D Name Mod Ptr Alias : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : CompareOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias)
    (io : JIO Io V) (a b : Ty) (color : String) : m Unit :=
  match o.diff.runtime.asDatatype a, o.diff.runtime.asDatatype b with
  | some a, some b => printWithCompareDatatype p o io a b color
  | _, _ => printWithCompareAny o io a b color
partial_fixpoint

end

/--
Julia source: base/errorshow.jl:1439-1446 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(io::IO, ip::InterpreterIP)
    print(io, typeof(ip))
    if ip.code isa Core.CodeInfo
        print(io, " in top-level CodeInfo for $(ip.mod) at statement $(Int(ip.stmt))")
    else
        print(io, " in $(ip.code) at statement $(Int(ip.stmt))")
    end
end
```
-/
def showInterpreterIP {IP Code Mod : Type} (p : IOPrims m Io V)
    (typeof : IP → Ty) (code : IP → Code) (module : IP → Mod) (statement : IP → Culong)
    (isCodeInfo : Code → Bool) (printType : JIO Io V → Ty → m Unit)
    (stringCode : Code → m String) (stringModule : Mod → m String) (stringInt : Clong → m String)
    (io : JIO Io V) (ip : IP) : m Unit := do
  printType io (typeof ip)
  if isCodeInfo (code ip) then
    let module ← stringModule (module ip)
    let stmt ← ofJl (JInt.convert "convert" .i64 (statement ip).val)
    printStr p io (" in top-level CodeInfo for " ++ module ++ " at statement " ++ (← stringInt stmt))
  else
    let code ← stringCode (code ip)
    let stmt ← ofJl (JInt.convert "convert" .i64 (statement ip).val)
    printStr p io (" in " ++ code ++ " at statement " ++ (← stringInt stmt))

structure ErrorHintOps (A World D Name Mod Ptr Alias Method : Type) where
  diff : TypeDiffOps (m := m) (Io := Io) (V := V) (Ty := Ty) World D Name Mod Ptr Alias
  types : TypeOps m Ty
  styled : PrintStyled m Io V
  equal : A → A → Bool
  isNumber : A → Bool
  number : Ty
  abstractString : Ty
  abstractDict : Ty
  valType : Ty
  unionallType : Ty
  setindex : A
  add : A
  replace : A
  min : A
  max : A
  length : A
  size : A
  iterate : A
  tupleType : List Ty → Ty
  isIterable : Ty → m Bool
  hasmethod : A → Ty → m Bool
  iteratorSize : Ty → m JuliaLean.base.iterators.IteratorSizeTag
  stringType : Ty → m String
  printValue : JIO Io V → A → m Unit
  fieldNames : Ty → m (List String)
  whichPropertynames : Ty → m Method
  methodEqual : Method → Method → Bool
  promoteValPropertynames : Ty → m Ty

/--
Julia source: base/errorshow.jl:1451-1458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function noncallable_number_hint_handler(io, ex, arg_types, kwargs)
    @nospecialize
    if ex.f isa Number
        print(io, "\nMaybe you forgot to use an operator such as ")
        printstyled(io, "*, ^, %, / etc. ", color=:cyan)
        print(io, "?")
    end
end
```
-/
def noncallableNumberHintHandler {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (io : JIO Io V) (ex : MethodError A Ty) (_argTypes : List Ty) (_kwargs : List (String × Ty)) : m Unit := do
  if o.isNumber ex.function then
    printStr p io "\nMaybe you forgot to use an operator such as "
    o.styled io [fun stream => printStr p stream "*, ^, %, / etc. "] "cyan" false
    printStr p io "?"

/--
Julia source: base/errorshow.jl:1468-1483 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function nonsetable_type_hint_handler(io, ex, arg_types, kwargs)
    @nospecialize
    if ex.f === setindex!
        T = arg_types[1]
        if T <: Number
            print(io, "\nAre you trying to index into an array? For multi-dimensional arrays, separate the indices with commas: ")
            printstyled(io, "a[1, 2]", color=:cyan)
            print(io, " rather than a[1][2]")
        elseif isType(T)
            Tx = type_parameter(T)
            print(io, "\nYou attempted to index the type $Tx, rather than an instance of the type. Make sure you create the type using its constructor: ")
            printstyled(io, "d = $Tx([...])", color=:cyan)
            print(io, " rather than d = $Tx")
        end
    end
end
```
-/
def nonsetableTypeHintHandler {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (io : JIO Io V) (ex : MethodError A Ty) (argTypes : List Ty) (_kwargs : List (String × Ty)) : m Unit := do
  if o.equal ex.function o.setindex then
    let type ← diagnosticAt argTypes 0
    if ← o.types.subtype type o.number then
      printStr p io "\nAre you trying to index into an array? For multi-dimensional arrays, separate the indices with commas: "
      o.styled io [fun stream => printStr p stream "a[1, 2]"] "cyan" false
      printStr p io " rather than a[1][2]"
    else if JuliaLean.base.runtime_internals.isType o.diff.runtime type then
      let tx ← o.diff.liftRuntime (o.diff.runtime.typeParameter type)
      printStr p io ("\nYou attempted to index the type " ++ (← o.stringType tx) ++
        ", rather than an instance of the type. Make sure you create the type using its constructor: ")
      o.styled io [fun stream => do printStr p stream ("d = " ++ (← o.stringType tx) ++ "([...])")] "cyan" false
      printStr p io (" rather than d = " ++ (← o.stringType tx))

/--
Julia source: base/errorshow.jl:1489-1495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function string_concatenation_hint_handler(@nospecialize(io::IO), ex::MethodError, arg_types::Vector{Any}, kwargs::Vector{Any})
    if (ex.f === +) && !isempty(arg_types) && all(@nospecialize(a) -> unwrapva(a) <: AbstractString, arg_types)
        print(io, "\nString concatenation is performed with ")
        printstyled(io, "*", color=:cyan)
        print(io, " (See also: https://docs.julialang.org/en/v1/manual/strings/#man-concatenation).")
    end
end
```
-/
def stringConcatenationHintHandler {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (io : JIO Io V) (ex : MethodError A Ty) (argTypes : List Ty) (_kwargs : List (String × Ty)) : m Unit := do
  if ← (if o.equal ex.function o.add && !argTypes.isEmpty then
      argTypes.allM (fun type => o.types.subtype (o.diff.runtime.unwrapVararg type) o.abstractString) else pure false) then
    printStr p io "\nString concatenation is performed with "
    o.styled io [fun stream => printStr p stream "*"] "cyan" false
    printStr p io " (See also: https://docs.julialang.org/en/v1/manual/strings/#man-concatenation)."

/--
Julia source: base/errorshow.jl:1501-1507 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function string_replace_hint_handler(@nospecialize(io::IO), ex::MethodError, arg_types::Vector{Any}, kwargs::Vector{Any})
    if ex.f === _replace! && any(@nospecialize(a) -> unwrapva(a) <: AbstractString, arg_types)
        print(io, "\n`String`s cannot be modified with `replace!`. Use ")
        printstyled(io, "replace", color=:cyan)
        print(io, " instead, which returns a new string.")
    end
end
```
-/
def stringReplaceHintHandler {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (io : JIO Io V) (ex : MethodError A Ty) (argTypes : List Ty) (_kwargs : List (String × Ty)) : m Unit := do
  if ← (if o.equal ex.function o.replace then
      argTypes.anyM (fun type => o.types.subtype (o.diff.runtime.unwrapVararg type) o.abstractString) else pure false) then
    printStr p io "\n`String`s cannot be modified with `replace!`. Use "
    o.styled io [fun stream => printStr p stream "replace"] "cyan" false
    printStr p io " instead, which returns a new string."

/--
Julia source: base/errorshow.jl:1513-1532 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function methods_on_iterable(io, ex, arg_types, kwargs)
    @nospecialize
    f = ex.f
    if (f === max || f === min) && length(arg_types) == 1 && Base.isiterable(only(arg_types))
        f_correct = f === max ? "maximum" : "minimum"
        print(io, "\nFinding the $f_correct of an iterable is performed with `$f_correct`.")
    end
    if (f === Base.length || f === Base.size) && length(arg_types) >= 1
        arg_type_tuple = Tuple{arg_types...}
        if hasmethod(iterate, arg_type_tuple)
            iterkind = IteratorSize(arg_types[1])
            if iterkind isa HasLength
                print(io, "\nYou may need to implement the `length` method or define `IteratorSize` for this type to be `SizeUnknown`.")
            elseif iterkind isa HasShape
                print(io, "\nYou may need to implement the `length` and `size` methods for `IteratorSize` `HasShape`.")
            end
        end
    end
    nothing
end
```
-/
def methodsOnIterable {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (io : JIO Io V) (ex : MethodError A Ty) (argTypes : List Ty) (_kwargs : List (String × Ty)) : m Unit := do
  let f := ex.function
  if (o.equal f o.max || o.equal f o.min) && argTypes.length == 1 then
    if ← o.isIterable (← diagnosticAt argTypes 0) then
      let correct := if o.equal f o.max then "maximum" else "minimum"
      printStr p io ("\nFinding the " ++ correct ++ " of an iterable is performed with `" ++ correct ++ "`.")
  if (o.equal f o.length || o.equal f o.size) && argTypes.length ≥ 1 then
    let args := o.tupleType argTypes
    if ← o.hasmethod o.iterate args then
      match ← o.iteratorSize (← diagnosticAt argTypes 0) with
      | .hasLength =>
        printStr p io "\nYou may need to implement the `length` method or define `IteratorSize` for this type to be `SizeUnknown`."
      | .hasShape _ =>
        printStr p io "\nYou may need to implement the `length` and `size` methods for `IteratorSize` `HasShape`."
      | _ => pure ()

/--
Julia source: base/errorshow.jl:1537-1546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fielderror_dict_hint_handler(io, exc)
    @nospecialize
    field = exc.field
    type = exc.type
    if type <: AbstractDict
        print(io, "\nDid you mean to access dict values using key: `:$field` ? Consider using indexing syntax ")
        printstyled(io, "dict[:$(field)]", color=:cyan)
        println(io)
    end
end
```
-/
def fieldErrorDictHintHandler {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (io : JIO Io V) (type : Ty) (field : String) : m Unit := do
  if ← o.types.subtype type o.abstractDict then
    printStr p io ("\nDid you mean to access dict values using key: `:" ++ field ++ "` ? Consider using indexing syntax ")
    o.styled io [fun stream => printStr p stream ("dict[:" ++ field ++ "]")] "cyan" false
    printStr p io "\n"

/--
Julia source: base/errorshow.jl:1566-1573 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _propertynames_bytype(T::Type)
    which(propertynames, (T,)) === which(propertynames, (Any,)) && return nothing
    inferred_names = promote_op(Val∘propertynames, T)
    inferred_names isa DataType && inferred_names <: Val || return nothing
    inferred_names = inferred_names.parameters[1]
    inferred_names isa NTuple{<:Any, Symbol} || return nothing
    return Symbol[inferred_names[i] for i in 1:length(inferred_names)]
end
```
-/
def propertynamesBytype {A World D Name Mod Ptr Alias Method : Type}
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (type : Ty) : m (Option (List String)) := do
  let specialized ← o.whichPropertynames type
  let fallback ← o.whichPropertynames o.diff.runtime.any
  if o.methodEqual specialized fallback then return none
  let inferred ← o.promoteValPropertynames type
  let some datatype := o.diff.runtime.asDatatype inferred | return none
  if !(← o.types.subtype inferred o.valType) then return none
  let parameters ← o.diff.liftRuntime (o.diff.runtime.parameters datatype)
  let names ← diagnosticAt parameters 0
  match o.diff.runtime.symbolTuple names with
  | none => return none
  | some symbols => return some symbols

/--
Julia source: base/errorshow.jl:1550-1564 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function fielderror_listfields_hint_handler(io, exc)
    # e.g. `fieldtype(Integer, :a)`: abstract types have no definite fields to list
    fieldcount_noerror(exc.type) === nothing && return
    fields = fieldnames(exc.type)
    if isempty(fields)
        print(io, "; $(exc.type.name.wrapper) has no fields at all.")
    else
        print(io, ", available fields: $(join(map(k -> "`$k`", fields), ", "))")
    end
    props = _propertynames_bytype(exc.type)
    isnothing(props) && return
    props = setdiff(props, fields)
    isempty(props) && return
    print(io, "\nAvailable properties: $(join(map(k -> "`$k`", props), ", "))")
end
```
-/
def fieldErrorListfieldsHintHandler {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (io : JIO Io V) (type : Ty) (_field : String) : m Unit := do
  let count ← o.diff.liftRuntime (JuliaLean.base.runtime_internals.fieldcountNoerror o.diff.runtime type)
  if count.isNone then return ()
  let fields ← o.fieldNames type
  if fields.isEmpty then
    let dt ← diagnosticDatatype o.diff type
    let wrapper := o.diff.runtime.wrapper (o.diff.runtime.nameOf dt)
    printStr p io ("; " ++ (← o.stringType wrapper) ++ " has no fields at all.")
  else printStr p io (", available fields: " ++ String.intercalate ", " (fields.map (fun name => "`" ++ name ++ "`")))
  let some props ← propertynamesBytype o type | return ()
  let props := props.filter (fun name => !fields.contains name)
  let props := props.eraseDups
  if props.isEmpty then return ()
  printStr p io ("\nAvailable properties: " ++ String.intercalate ", " (props.map (fun name => "`" ++ name ++ "`")))

/--
Julia source: base/errorshow.jl:1577-1582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function apply_type_unionall_hint_handler(io, ex)
    @nospecialize
    if ex.func === :apply_type && ex.expected === UnionAll
        print(io, "\nHint: `", ex.got, "` takes no type parameters.")
    end
end
```
-/
def applyTypeUnionallHintHandler {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (io : JIO Io V) (ex : TypeError A Ty) : m Unit := do
  if ex.func == lit "apply_type" && o.diff.runtime.egal ex.expected o.unionallType then
    printStr p io "\nHint: `"
    o.printValue io ex.got
    printStr p io "` takes no type parameters."

structure UndefinedHintOps (World Mod GlobalRef Binding Partition Restriction Groups Modules State : Type) where
  bindings : JuliaLean.base.runtime_internals.BindingOps World Mod String GlobalRef Binding Partition Restriction
  liftRuntime : {A : Type} → JuliaLean.base.io.M World A → m A
  restrictionGlobalRef : Restriction → m GlobalRef
  stringGlobalRef : GlobalRef → m String
  stringWorld : Culong → m String
  stringKind : JInt .u8 → m String
  baseModule : Mod
  coreModule : Mod
  mainModule : Mod
  activeModule : m Mod
  loadedModules : m Modules
  iterateModules : Modules → Option State → m (Option (Mod × State))
  moduleEqual : Mod → Mod → Bool
  moduleSame : Mod → Mod → Bool
  moduleSymbol : Mod → m String
  moduleName : Mod → m String
  stringModule : Mod → m String
  printModule : JIO Io V → Mod → m Unit
  isDefined : Mod → String → m Bool
  isDefinedGlobal : Mod → String → m Bool
  isExported : Mod → String → m Bool
  isPublic : Mod → String → m Bool
  bindingModule : Mod → String → m Mod
  moduleProperty : Mod → String → m (Option Mod)
  newGroups : m Groups
  hasGroup : Groups → Mod → m Bool
  appendGroup : Groups → Mod → Mod → m Unit
  setGroup : Groups → Mod → List Mod → m Unit
  groupsPairs : Groups → m (List (Mod × List Mod))

def filteredModuleNext {Mod State : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (next : Option State → m (Option (Mod × State))) (accept : Mod → Bool)
    (state : Option State) : m (Option (Mod × State)) := do
  match ← next state with
  | none => return none
  | some (module, state) =>
    if accept module then return some (module, state)
    filteredModuleNext next accept (some state)
partial_fixpoint

def moduleListNext {Mod : Type} (modules : List Mod) (state : Option Nat) : m (Option (Mod × Nat)) := do
  let index := state.getD 0
  return modules[index]?.map (fun module => (module, index + 1))

def collectUndefinedWarnings {World Mod GlobalRef Binding Partition Restriction Groups Modules State IterState : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : UndefinedHintOps (m := m) (Io := Io) (V := V) World Mod GlobalRef Binding Partition Restriction Groups Modules State)
    (next : Option IterState → m (Option (Mod × IterState))) (io : JIO Io V)
    (active : Mod) (groups : Groups) (var : String) (state : Option IterState) (warned : Bool) : m Bool := do
  let some (module, state) ← next state | return warned
  if !(← o.isDefined module var) then
    return ← collectUndefinedWarnings p o next io active groups var (some state) warned
  let available ← if ← o.isExported module var then pure true else o.isPublic module var
  if !available then
    return ← collectUndefinedWarnings p o next io active groups var (some state) warned
  if (← o.moduleSymbol module) == var then
    if !(← o.isDefined active var) then
      printStr p io ("\nHint: " ++ (← o.stringModule module) ++
        " is loaded but not imported in the active module " ++ (← o.stringModule active) ++ ".")
      return ← collectUndefinedWarnings p o next io active groups var (some state) true
  let bindingModule ← o.bindingModule module var
  if !(← o.hasGroup groups bindingModule) then o.setGroup groups bindingModule [module]
  else o.appendGroup groups bindingModule module
  collectUndefinedWarnings p o next io active groups var (some state) true
partial_fixpoint

/--
Julia source: base/errorshow.jl:1651-1696 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _UndefVarError_warnfor(io::IO, modules, var::Symbol)
    active_mod = Base.active_module()

    warned = false
    # collect modules which export or make public the variable by
    # the module in which the variable is defined
    to_warn_about = Dict{Module, Vector{Module}}()
    for m in modules
        # only include in info if binding has a value and is exported or public
        if !Base.isdefined(m, var) || (!Base.isexported(m, var) && !Base.ispublic(m, var))
            continue
        end
        warned = true

        # handle case where the undefined variable is the name of a loaded module
        if Symbol(m) == var && !isdefined(active_mod, var)
            print(io, "\nHint: $m is loaded but not imported in the active module $active_mod.")
            continue
        end

        binding_m = Base.binding_module(m, var)
        if !haskey(to_warn_about, binding_m)
            to_warn_about[binding_m] = [m]
        else
            push!(to_warn_about[binding_m], m)
        end
    end

    for (binding_m, modules) in pairs(to_warn_about)
        print(io, "\nHint: a global variable of this name also exists in ", binding_m, ".")
        for m in modules
            m == binding_m && continue
            how_available = if Base.isexported(m, var)
                "exported by"
            elseif Base.ispublic(m, var)
                "declared public in"
            end
            print(io, "\n    - Also $how_available $m")
            if !isdefined(active_mod, nameof(m)) || (getproperty(active_mod, nameof(m)) !== m)
                print(io, " (loaded but not imported in $active_mod)")
            end
            print(io, ".")
        end
    end
    return warned
end
```
-/
def undefVarErrorWarnfor {World Mod GlobalRef Binding Partition Restriction Groups Modules State IterState : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : UndefinedHintOps (m := m) (Io := Io) (V := V) World Mod GlobalRef Binding Partition Restriction Groups Modules State)
    (next : Option IterState → m (Option (Mod × IterState)))
    (io : JIO Io V) (var : String) : m Bool := do
  let active ← o.activeModule
  let groups ← o.newGroups
  let warned ← collectUndefinedWarnings p o next io active groups var none false
  for (bindingModule, modules) in ← o.groupsPairs groups do
    printStr p io "\nHint: a global variable of this name also exists in "
    o.printModule io bindingModule
    printStr p io "."
    for module in modules do
      if o.moduleEqual module bindingModule then continue
      let how ← if ← o.isExported module var then pure "exported by"
        else if ← o.isPublic module var then pure "declared public in"
        else pure "nothing"
      printStr p io ("\n    - Also " ++ how ++ " " ++ (← o.stringModule module))
      let name ← o.moduleName module
      let imported ← if !(← o.isDefined active name) then pure false
        else match ← o.moduleProperty active name with
          | none => pure false
          | some value => pure (o.moduleSame value module)
      if !imported then
        printStr p io (" (loaded but not imported in " ++ (← o.stringModule active) ++ ")")
      printStr p io "."
  return warned

/--
Julia source: base/errorshow.jl:1586-1649 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function UndefVarError_hint(io::IO, ex::UndefVarError)
    var = ex.var
    if isdefined(ex, :scope)
        scope = ex.scope
        if scope isa Module
            bpart = lookup_binding_partition(ex.world, GlobalRef(scope, var))
            kind = binding_kind(bpart)

            # Get the current world's binding partition for comparison
            curworld = tls_world_age()
            cur_bpart = lookup_binding_partition(curworld, GlobalRef(scope, var))
            cur_kind = binding_kind(cur_bpart)

            # Track if we printed the "too new" message
            printed_too_new = false

            # Check if the binding exists in the current world but was undefined in the error's world
            if kind === PARTITION_KIND_GUARD
                if isdefinedglobal(scope, var)
                    print(io, "\nThe binding may be too new: running in world age $(ex.world), while current world is $(curworld).")
                    printed_too_new = true
                else
                    print(io, "\nSuggestion: check for spelling errors or missing imports.")
                end
            elseif kind === PARTITION_KIND_GLOBAL || kind === PARTITION_KIND_UNDEF_CONST || kind == PARTITION_KIND_DECLARED
                print(io, "\nSuggestion: add an appropriate import or assignment. This global was declared but not assigned.")
            elseif kind === PARTITION_KIND_FAILED
                print(io, "\nHint: It looks like two or more modules export different ",
                "bindings with this name, resulting in ambiguity. Try explicitly ",
                "importing it from a particular module, or qualifying the name ",
                "with the module it should come from.")
            elseif is_some_explicit_imported(kind)
                print(io, "\nSuggestion: this global was defined as `$(partition_restriction(bpart).globalref)` but not assigned a value.")
            elseif kind === PARTITION_KIND_BACKDATED_CONST
                print(io, "\nSuggestion: define the const at top-level before running function that uses it (stricter Julia v1.12+ rule).")
            end

            # Check if binding kind changed between the error's world and current world
            if !printed_too_new && kind !== cur_kind
                print(io, "\nNote: the binding state changed since the error occurred (was: $(kind), now: $(cur_kind)).")
            end
        elseif scope === :static_parameter
            print(io, "\nSuggestion: run Test.detect_unbound_args to detect method arguments that do not fully constrain a type parameter.")
        elseif scope === :local
            print(io, "\nSuggestion: check for an assignment to a local variable that shadows a global of the same name.")
        end
    else
        scope = undef
    end
    if scope !== Base
        warned = _UndefVarError_warnfor(io, [Base], var)

        if !warned
            let scope = scope
                modules_to_check = (m for m in Base.loaded_modules_order
                                    if m !== Core && m !== Base && m !== Main && m !== scope)
                warned |= _UndefVarError_warnfor(io, modules_to_check, var)
            end
        end

        warned || _UndefVarError_warnfor(io, [Core, Main], var)
    end
    return nothing
end
```
-/
def undefVarErrorHint {World Mod GlobalRef Binding Partition Restriction Groups Modules State : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : UndefinedHintOps (m := m) (Io := Io) (V := V) World Mod GlobalRef Binding Partition Restriction Groups Modules State)
    (io : JIO Io V) (ex : UndefVarError Mod) : m Unit := do
  let var := ex.var
  match ex.scope with
  | some (.moduleScope module) =>
    let gr ← o.liftRuntime (o.bindings.globalRef module var)
    let partition ← o.liftRuntime (JuliaLean.base.runtime_internals.lookupBindingPartitionGlobalRef o.bindings ex.world gr)
    let kind := JuliaLean.base.runtime_internals.bindingKindPartition o.bindings partition
    let current ← o.liftRuntime o.bindings.tlsWorldAge
    let curGr ← o.liftRuntime (o.bindings.globalRef module var)
    let curPartition ← o.liftRuntime (JuliaLean.base.runtime_internals.lookupBindingPartitionGlobalRef o.bindings current curGr)
    let curKind := JuliaLean.base.runtime_internals.bindingKindPartition o.bindings curPartition
    let mut printedTooNew := false
    if kind.val == 9 then
      if ← o.isDefinedGlobal module var then
        printStr p io ("\nThe binding may be too new: running in world age " ++ (← o.stringWorld ex.world) ++
          ", while current world is " ++ (← o.stringWorld current) ++ ".")
        printedTooNew := true
      else printStr p io "\nSuggestion: check for spelling errors or missing imports."
    else if kind.val == 2 || kind.val == 10 || kind.val == 8 then
      printStr p io "\nSuggestion: add an appropriate import or assignment. This global was declared but not assigned."
    else if kind.val == 7 then
      printStr p io "\nHint: It looks like two or more modules export different "
      printStr p io "bindings with this name, resulting in ambiguity. Try explicitly "
      printStr p io "importing it from a particular module, or qualifying the name "
      printStr p io "with the module it should come from."
    else if JuliaLean.base.runtime_internals.isSomeExplicitImported kind then
      let restriction ← o.liftRuntime (JuliaLean.base.runtime_internals.partitionRestriction o.bindings partition)
      let gr ← o.restrictionGlobalRef restriction
      printStr p io ("\nSuggestion: this global was defined as `" ++ (← o.stringGlobalRef gr) ++ "` but not assigned a value.")
    else if kind.val == 11 then
      printStr p io "\nSuggestion: define the const at top-level before running function that uses it (stricter Julia v1.12+ rule)."
    if !printedTooNew && kind.val != curKind.val then
      printStr p io ("\nNote: the binding state changed since the error occurred (was: " ++ (← o.stringKind kind) ++
        ", now: " ++ (← o.stringKind curKind) ++ ").")
  | some .staticParameter =>
    printStr p io "\nSuggestion: run Test.detect_unbound_args to detect method arguments that do not fully constrain a type parameter."
  | some .localScope =>
    printStr p io "\nSuggestion: check for an assignment to a local variable that shadows a global of the same name."
  | _ => pure ()
  let isBase := match ex.scope with
    | some (.moduleScope module) => o.moduleSame module o.baseModule
    | _ => false
  if !isBase then
    let mut warned ← undefVarErrorWarnfor p o (moduleListNext [o.baseModule]) io var
    if !warned then
      let modules ← o.loadedModules
      let accept := fun module =>
        !o.moduleSame module o.coreModule && !o.moduleSame module o.baseModule && !o.moduleSame module o.mainModule &&
        match ex.scope with
        | some (.moduleScope scope) => !o.moduleSame module scope
        | _ => true
      warned := warned || (← undefVarErrorWarnfor p o (filteredModuleNext (o.iterateModules modules) accept) io var)
    if !warned then
      let _ ← undefVarErrorWarnfor p o (moduleListNext [o.coreModule, o.mainModule]) io var
      pure ()

structure ErrorHintRegistry (A Mod : Type) where
  methodError : (JIO Io V → MethodError A Ty → List Ty → List (String × Ty) → m Unit) → m Unit
  fieldError : (JIO Io V → Ty → String → m Unit) → m Unit
  typeError : (JIO Io V → TypeError A Ty → m Unit) → m Unit
  undefVarError : (JIO Io V → UndefVarError Mod → m Unit) → m Unit

/--
Julia source: base/errorshow.jl:1460-1460 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Experimental.register_error_hint(noncallable_number_hint_handler, MethodError)
```
-/
def registerNoncallableNumberHint {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (registry : ErrorHintRegistry (m := m) (Io := Io) (V := V) (Ty := Ty) A Mod) : m Unit :=
  registry.methodError (noncallableNumberHintHandler p o)

/--
Julia source: base/errorshow.jl:1485-1485 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Experimental.register_error_hint(nonsetable_type_hint_handler, MethodError)
```
-/
def registerNonsetableTypeHint {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (registry : ErrorHintRegistry (m := m) (Io := Io) (V := V) (Ty := Ty) A Mod) : m Unit :=
  registry.methodError (nonsetableTypeHintHandler p o)

/--
Julia source: base/errorshow.jl:1497-1497 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Experimental.register_error_hint(string_concatenation_hint_handler, MethodError)
```
-/
def registerStringConcatenationHint {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (registry : ErrorHintRegistry (m := m) (Io := Io) (V := V) (Ty := Ty) A Mod) : m Unit :=
  registry.methodError (stringConcatenationHintHandler p o)

/--
Julia source: base/errorshow.jl:1509-1509 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Experimental.register_error_hint(string_replace_hint_handler, MethodError)
```
-/
def registerStringReplaceHint {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (registry : ErrorHintRegistry (m := m) (Io := Io) (V := V) (Ty := Ty) A Mod) : m Unit :=
  registry.methodError (stringReplaceHintHandler p o)

/--
Julia source: base/errorshow.jl:1534-1534 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Experimental.register_error_hint(methods_on_iterable, MethodError)
```
-/
def registerMethodsOnIterableHint {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (registry : ErrorHintRegistry (m := m) (Io := Io) (V := V) (Ty := Ty) A Mod) : m Unit :=
  registry.methodError (methodsOnIterable p o)

/--
Julia source: base/errorshow.jl:1548-1548 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Experimental.register_error_hint(fielderror_dict_hint_handler, FieldError)
```
-/
def registerFieldErrorDictHint {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (registry : ErrorHintRegistry (m := m) (Io := Io) (V := V) (Ty := Ty) A Mod) : m Unit :=
  registry.fieldError (fieldErrorDictHintHandler p o)

/--
Julia source: base/errorshow.jl:1575-1575 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Experimental.register_error_hint(fielderror_listfields_hint_handler, FieldError)
```
-/
def registerFieldErrorListfieldsHint {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (registry : ErrorHintRegistry (m := m) (Io := Io) (V := V) (Ty := Ty) A Mod) : m Unit :=
  registry.fieldError (fieldErrorListfieldsHintHandler p o)

/--
Julia source: base/errorshow.jl:1584-1584 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Experimental.register_error_hint(apply_type_unionall_hint_handler, TypeError)
```
-/
def registerApplyTypeUnionallHint {A World D Name Mod Ptr Alias Method : Type}
    (p : IOPrims m Io V)
    (o : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (registry : ErrorHintRegistry (m := m) (Io := Io) (V := V) (Ty := Ty) A Mod) : m Unit :=
  registry.typeError (applyTypeUnionallHintHandler p o)

/--
Julia source: base/errorshow.jl:1698-1698 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
Base.Experimental.register_error_hint(UndefVarError_hint, UndefVarError)
```
-/
def registerUndefVarErrorHint {A World Mod GlobalRef Binding Partition Restriction Groups Modules State : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (o : UndefinedHintOps (m := m) (Io := Io) (V := V) World Mod GlobalRef Binding Partition Restriction Groups Modules State)
    (registry : ErrorHintRegistry (m := m) (Io := Io) (V := V) (Ty := Ty) A Mod) : m Unit :=
  registry.undefVarError (undefVarErrorHint p o)

def initializeErrorHints {A World D Name Mod Ptr Alias Method GlobalRef Binding Partition Restriction Groups Modules State : Type}
    [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V)
    (hints : ErrorHintOps (m := m) (Io := Io) (V := V) (Ty := Ty) A World D Name Mod Ptr Alias Method)
    (undefined : UndefinedHintOps (m := m) (Io := Io) (V := V) World Mod GlobalRef Binding Partition Restriction Groups Modules State)
    (registry : ErrorHintRegistry (m := m) (Io := Io) (V := V) (Ty := Ty) A Mod) : m Unit := do
  registerNoncallableNumberHint p hints registry
  registerNonsetableTypeHint p hints registry
  registerStringConcatenationHint p hints registry
  registerStringReplaceHint p hints registry
  registerMethodsOnIterableHint p hints registry
  registerFieldErrorDictHint p hints registry
  registerFieldErrorListfieldsHint p hints registry
  registerApplyTypeUnionallHint p hints registry
  registerUndefVarErrorHint p undefined registry


end
end JuliaLean.base.errorshow

namespace JuliaLean.base.errorshow.Models2Group17

/-!
These handlers have no type annotation on their `io` or exception arguments.
`V` represents the complete Julia value domain, including the genuine
`nothingValue`; selected dispatch is therefore retained for getproperty,
string, print, printstyled, and println.  The finite property/color tags below
denote the exact literal Symbols at these call sites, not a restriction on the
possible field values.  String literals are pre-existing constant values.

The classifier/identity operations and `subtypeAbstractDict` are builtin
runtime boundaries.  In particular the latter receives the uncoerced arbitrary
field value and may raise the native builtin type error.  It is not a callback
for the enclosing hint handler or for any Base-defined formatting method.
-/

inductive HintProperty where
  | f | field | type | func | expected | got

inductive HintColor where
  | cyan

structure HintBuiltinPrims (m : Type → Type) (V : Type) where
  literal : String → V
  nothingValue : V
  isaNumber : V → Bool
  subtypeAbstractDict : V → m Bool
  identicalApplyTypeSymbol : V → Bool
  identicalUnionAllType : V → Bool

structure HintDispatch (m : Type → Type) (V : Type) where
  getproperty : V → HintProperty → m V
  string : List V → m V
  print : V → List V → m V
  printstyled : V → List V → HintColor → m V
  println : V → m V

/--
Julia source (`base/errorshow.jl:1451–1458`):
```julia
function noncallable_number_hint_handler(io, ex, arg_types, kwargs)
    @nospecialize
    if ex.f isa Number
        print(io, "\nMaybe you forgot to use an operator such as ")
        printstyled(io, "*, ^, %, / etc. ", color=:cyan)
        print(io, "?")
    end
end
```
The ignored arguments remain in the full signature.  Each selected method's
effect is sequenced, and the final print's arbitrary result is returned.
-/
-- Source: base/errorshow.jl:1451-1458 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function noncallable_number_hint_handler(io, ex, arg_types, kwargs)
--     @nospecialize
--     if ex.f isa Number
--         print(io, "\nMaybe you forgot to use an operator such as ")
--         printstyled(io, "*, ^, %, / etc. ", color=:cyan)
--         print(io, "?")
--     end
-- end
-- /Source
def noncallableNumberHint [Monad m] (b : HintBuiltinPrims m V)
    (d : HintDispatch m V) (io ex _argTypes _kwargs : V) : m V := do
  let f ← d.getproperty ex .f
  if b.isaNumber f then
    let _ ← d.print io [b.literal "\nMaybe you forgot to use an operator such as "]
    let _ ← d.printstyled io [b.literal "*, ^, %, / etc. "] .cyan
    d.print io [b.literal "?"]
  else
    pure b.nothingValue

/--
Julia source (`base/errorshow.jl:1537–1546`):
```julia
function fielderror_dict_hint_handler(io, exc)
    @nospecialize
    field = exc.field
    type = exc.type
    if type <: AbstractDict
        print(io, "\nDid you mean to access dict values using key: `:$field` ? Consider using indexing syntax ")
        printstyled(io, "dict[:$(field)]", color=:cyan)
        println(io)
    end
end
```
Both property reads occur before the builtin subtype check.  Interpolation
dispatch remains open because the retrieved field has arbitrary runtime type;
each interpolation receives its exact three arguments.  Its arbitrary result
is passed unchanged to the selected print/printstyled method.  The final
one-argument println's raw return is retained.
-/
-- Source: base/errorshow.jl:1537-1546 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function fielderror_dict_hint_handler(io, exc)
--     @nospecialize
--     field = exc.field
--     type = exc.type
--     if type <: AbstractDict
--         print(io, "\nDid you mean to access dict values using key: `:$field` ? Consider using indexing syntax ")
--         printstyled(io, "dict[:$(field)]", color=:cyan)
--         println(io)
--     end
-- end
-- /Source
def fielderrorDictHint [Monad m] (b : HintBuiltinPrims m V)
    (d : HintDispatch m V) (io exc : V) : m V := do
  let field ← d.getproperty exc .field
  let type ← d.getproperty exc .type
  if ← b.subtypeAbstractDict type then
    let message ← d.string
      [b.literal "\nDid you mean to access dict values using key: `:", field,
       b.literal "` ? Consider using indexing syntax "]
    let _ ← d.print io [message]
    let styledMessage ← d.string [b.literal "dict[:", field, b.literal "]"]
    let _ ← d.printstyled io [styledMessage] .cyan
    d.println io
  else
    pure b.nothingValue

/--
Julia source (`base/errorshow.jl:1577–1582`):
```julia
function apply_type_unionall_hint_handler(io, ex)
    @nospecialize
    if ex.func === :apply_type && ex.expected === UnionAll
        print(io, "\nHint: `", ex.got, "` takes no type parameters.")
    end
end
```
The second getter and the got getter are short-circuited independently.  The
single selected variadic print receives all three values in order and returns
its arbitrary result unchanged.
-/
-- Source: base/errorshow.jl:1577-1582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function apply_type_unionall_hint_handler(io, ex)
--     @nospecialize
--     if ex.func === :apply_type && ex.expected === UnionAll
--         print(io, "\nHint: `", ex.got, "` takes no type parameters.")
--     end
-- end
-- /Source
def applyTypeUnionallHint [Monad m] (b : HintBuiltinPrims m V)
    (d : HintDispatch m V) (io ex : V) : m V := do
  let func ← d.getproperty ex .func
  if b.identicalApplyTypeSymbol func then
    let expected ← d.getproperty ex .expected
    if b.identicalUnionAllType expected then
      let got ← d.getproperty ex .got
      d.print io [b.literal "\nHint: `", got,
        b.literal "` takes no type parameters."]
    else
      pure b.nothingValue
  else
    pure b.nothingValue

end JuliaLean.base.errorshow.Models2Group17

namespace JuliaLean.base.errorshow.Models2Group17

open JuliaLean JuliaLean.base.show

/-- The native Cstring primitive on the installed 64-bit Julia target. Its
address bits are not decoded as Unicode and are not confused with a Julia
String. Source: base/refpointer.jl:83-92. -/
-- Source: base/refpointer.jl:83-92 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # C NUL-terminated string pointers; these can be used in ccall
-- # instead of Ptr{Cchar} and Ptr{Cwchar_t}, respectively, to enforce
-- # a check for embedded NUL chars in the string (to avoid silent truncation).
-- if Int === Int64
--     primitive type Cstring  64 end
--     primitive type Cwstring 64 end
-- else
--     primitive type Cstring  32 end
--     primitive type Cwstring 32 end
-- end
-- /Source
structure NativeCString where
  address : JInt .u64

/-- The only two concrete String literals used by this method. This is
representation data for fixed literal objects, not a restriction on the
AbstractString message. Source: base/errorshow.jl:453,455. -/
-- Source: base/errorshow.jl:450-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function showerror_nostdio(@nospecialize(err), msg::AbstractString)
--     stderr_stream = ccall(:jl_stderr_stream, Ptr{Cvoid}, ())
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, msg)
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, ":\n")
--     ccall(:jl_static_show, Csize_t, (Ptr{Cvoid},Any), stderr_stream, err)
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, "\n")
-- end
-- /Source
inductive NoStdioLiteral where
  | separator
  | newline

/-- Native pointer views of the two live immutable literal objects, in the
installed byte heap. The representation invariants identify their exact
code units and trailing NUL at valid nonnull addresses, retaining aliasing
instead of assigning unrelated bytes to a bare pointer. Each pointer is
the actual address returned by jl_string_ptr for its fixed String object.
This is native allocation/identity data, not a string-conversion callback
or a correctness law for a callee. Source: base/essentials.jl:746;
base/errorshow.jl:453,455. -/
-- Source: base/essentials.jl:746-746 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- unsafe_convert(::Type{Ptr{Int8}}, s::String) = ccall(:jl_string_ptr, Ptr{Int8}, (Any,), s)
-- /Source
structure NoStdioLiteralPointers where
  heap : JuliaLean.base.pointer.ByteHeap
  separator : JuliaLean.base.pointer.Ptr Int8
  newline : JuliaLean.base.pointer.Ptr Int8
  separatorNonnull : separator.address.val ≠ 0
  newlineNonnull : newline.address.val ≠ 0
  separatorLive : heap.validRange separator.address.val.toNat 3
  newlineLive : heap.validRange newline.address.val.toNat 2
  separatorBytes : heap.readBytes separator.address.val.toNat 3 =
    [JInt.lit .u8 58, JInt.lit .u8 10, JInt.lit .u8 0]
  newlineBytes : heap.readBytes newline.address.val.toNat 2 =
    [JInt.lit .u8 10, JInt.lit .u8 0]

/-- Concrete conversion of either actual fixed String literal. String
cconvert is identity. The installed jl_string_ptr adapter projects the
stored pointer view, and the memchr(0,sizeof(s)) test scans exactly the
native-length byte span of that same immutable object. Bitcasting to
Cstring preserves all 64 address bits. Both spans are NUL-free, so the
ArgumentError branch is unreachable; its two closed repr values are shown
explicitly rather than exposing a generic repr callback. This helper is
only the conversion at these two fixed call sites, not a proposed generic
unsafe_convert(String) model. Source: base/strings/cstring.jl:31,65,78-88;
base/essentials.jl:746. -/
-- Source: base/strings/cstring.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- Cstring(p::Union{Ptr{Int8},Ptr{UInt8},Ptr{Cvoid}}) = bitcast(Cstring, p)
-- /Source
-- Source: base/strings/cstring.jl:65-65 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- cconvert(::Type{Cstring}, s::String) = s
-- /Source
-- Source: base/strings/cstring.jl:78-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- containsnul(p::Ptr, len) =
--     C_NULL != ccall(:memchr, Ptr{Cchar}, (Ptr{Cchar}, Cint, Csize_t), p, 0, len)
-- containsnul(s::String) = containsnul(unsafe_convert(Ptr{Cchar}, s), sizeof(s))
-- containsnul(s::AbstractString) = '\0' in s
--
-- function unsafe_convert(::Type{Cstring}, s::String)
--     p = unsafe_convert(Ptr{Cchar}, s)
--     containsnul(p, sizeof(s)) &&
--         throw(ArgumentError("embedded NULs are not allowed in C strings: $(repr(s))"))
--     return Cstring(p)
-- end
-- /Source
def noStdioLiteralCString (pointers : NoStdioLiteralPointers)
    (literal : NoStdioLiteral) : Jl NativeCString :=
  let (text, pointer, representation) := match literal with
    | .separator => (":\n", pointers.separator, "\":\\n\"")
    | .newline => ("\n", pointers.newline, "\"\\n\"")
  let converted := text
  let pointer := JuliaLean.base.essentials.unsafeConvertStringInt8
    (fun _ => pointer) converted
  let length := JInt.wrap .u64 (Int.ofNat (lit converted).length)
  let span := pointers.heap.readBytes pointer.address.val.toNat length.val.toNat
  let containsNul := span.any (fun byte => byte.val == 0)
  if containsNul then
    .error (.argumentError ("embedded NULs are not allowed in C strings: " ++ representation))
  else
    .ok ⟨pointer.address⟩

/-- Open conversion dispatch for the unconstrained AbstractString subtype
and error value. The cconvert result may have an unrelated Julia type and
carry allocations. unsafe_convert keeps arbitrary errors and state effects;
the CString return assertion remains explicit. Any accepts every value,
so its unsafe-conversion result has no narrowing assertion. Automatic
conversion order is documented in doc/src/manual/calling-c-and-fortran-code.md:246-268
and base/docs/basedocs.jl:1490-1493. Source: base/errorshow.jl:452,454. -/
-- Source: base/errorshow.jl:450-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function showerror_nostdio(@nospecialize(err), msg::AbstractString)
--     stderr_stream = ccall(:jl_stderr_stream, Ptr{Cvoid}, ())
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, msg)
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, ":\n")
--     ccall(:jl_static_show, Csize_t, (Ptr{Cvoid},Any), stderr_stream, err)
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, "\n")
-- end
-- /Source
structure NoStdioDispatch (m : Type → Type) (Message MessageRoot Wrong Error ErrorRoot Value : Type) where
  cconvertMessage : Message → m MessageRoot
  unsafeConvertMessage : MessageRoot →
    m (JuliaLean.base.abstractarray.Models1Group1.TypeAssertion NativeCString Wrong)
  cconvertError : Error → m ErrorRoot
  unsafeConvertError : ErrorRoot → m Value

/-- The actual three native entry points used by this method. These are
C/runtime boundaries with the original argument order and ABI widths:
Ptr{Cvoid}, Cstring, Cint = Int32, and Csize_t = UInt64. The static-show Any
argument is retained as its arbitrary Julia value. Source:
base/errorshow.jl:451-455; doc/src/manual/calling-c-and-fortran-code.md:370-388. -/
-- Source: base/errorshow.jl:450-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function showerror_nostdio(@nospecialize(err), msg::AbstractString)
--     stderr_stream = ccall(:jl_stderr_stream, Ptr{Cvoid}, ())
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, msg)
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, ":\n")
--     ccall(:jl_static_show, Csize_t, (Ptr{Cvoid},Any), stderr_stream, err)
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, "\n")
-- end
-- /Source
structure NoStdioRuntime (m : Type → Type) (Value : Type) where
  stderrStream : m (JuliaLean.base.pointer.Ptr Unit)
  printf : JuliaLean.base.pointer.Ptr Unit → NativeCString → m (JInt .i32)
  staticShow : JuliaLean.base.pointer.Ptr Unit → Value → m (JInt .u64)

/-- Acquire stderr before message conversion, then execute the original
five native calls in source order. Concrete stream-pointer conversions use
the installed identity models; concrete literal conversions use their
actual immutable byte spans. The converted roots stay in scope through
their native call, reflecting ccall's GC-preserve extent. Custom conversions
and native errors propagate at their own call site without being replaced.
The three earlier numeric results are discarded; the final Cint, including
a negative value, is the method's raw return. Source: base/errorshow.jl:450-456.
Automatic conversions: base/docs/basedocs.jl:1490-1493;
doc/src/manual/calling-c-and-fortran-code.md:246-268. -/
-- Source: base/errorshow.jl:450-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function showerror_nostdio(@nospecialize(err), msg::AbstractString)
--     stderr_stream = ccall(:jl_stderr_stream, Ptr{Cvoid}, ())
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, msg)
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, ":\n")
--     ccall(:jl_static_show, Csize_t, (Ptr{Cvoid},Any), stderr_stream, err)
--     ccall(:jl_printf, Cint, (Ptr{Cvoid},Cstring), stderr_stream, "\n")
-- end
-- /Source
def showErrorNoStdio {m : Type → Type} [Monad m] [MonadExceptOf ShowError m]
    {Message MessageRoot Wrong Error ErrorRoot Value : Type}
    (runtime : NoStdioRuntime m Value)
    (dispatch : NoStdioDispatch m Message MessageRoot Wrong Error ErrorRoot Value)
    (literals : NoStdioLiteralPointers) (error : Error) (message : Message) : m (JInt .i32) := do
  let stream ← runtime.stderrStream
  let streamRoot := JuliaLean.base.essentials.cconvertPointer stream
  let messageRoot ← dispatch.cconvertMessage message
  let streamArg := JuliaLean.base.essentials.unsafeConvertPointerIdentity streamRoot
  let messageArg ← dispatch.unsafeConvertMessage messageRoot
  let messageArg ← match messageArg with
    | .accepted value => pure value
    | .rejected _ => throw ShowError.typeError
  let _ ← runtime.printf streamArg messageArg
  let streamRoot := JuliaLean.base.essentials.cconvertPointer stream
  let streamArg := JuliaLean.base.essentials.unsafeConvertPointerIdentity streamRoot
  let separator ← match noStdioLiteralCString literals .separator with
    | .ok value => pure value
    | .error error => throw (ShowError.jl error)
  let _ ← runtime.printf streamArg separator
  let streamRoot := JuliaLean.base.essentials.cconvertPointer stream
  let errorRoot ← dispatch.cconvertError error
  let streamArg := JuliaLean.base.essentials.unsafeConvertPointerIdentity streamRoot
  let errorArg ← dispatch.unsafeConvertError errorRoot
  let _ ← runtime.staticShow streamArg errorArg
  let streamRoot := JuliaLean.base.essentials.cconvertPointer stream
  let streamArg := JuliaLean.base.essentials.unsafeConvertPointerIdentity streamRoot
  let newline ← match noStdioLiteralCString literals .newline with
    | .ok value => pure value
    | .error error => throw (ShowError.jl error)
  runtime.printf streamArg newline

end JuliaLean.base.errorshow.Models2Group17

namespace JuliaLean.base.errorshow.Models2Group17

open JuliaLean.base.show

/-- The primitive `===` result and the printing methods selected for the
unrestricted left argument. `egal` is a pure builtin-identity observation,
not a user-defined equality callback. The plain and styled print targets
retain arbitrary raw results and all effects. `C` is the existing opaque
Symbol representation, so a color is forwarded without conversion to a
Unicode String or a restricted palette.
Relevant source: base/errorshow.jl:235-241;
doc/src/manual/types.md:1653-1661 (printing dispatch).
-/
structure CompareDispatch (m : Type → Type) (Io V A B C R : Type) where
  egal : A → B → Bool
  printValue : JIO Io V → A → m R
  printStyled : JIO Io V → A → C → m R

/-- Select plain printing for an egal pair and styled printing otherwise.
Both arguments remain unrestricted, the selected printer receives exactly
the original left argument and stream, and styled printing receives the
original Symbol color. The selected method's raw return and every effect
are preserved, including exceptions and non-`nothing` successful values.
Julia source: base/errorshow.jl:235-241.
-/
-- Source: base/errorshow.jl:235-241 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- function print_with_compare(io::IO, @nospecialize(a), @nospecialize(b), color::Symbol)
--     if a === b
--         print(io, a)
--     else
--         printstyled(io, a; color=color)
--     end
-- end
-- /Source
def printWithCompareAny {m : Type → Type} {Io V A B C R : Type}
    (ops : CompareDispatch m Io V A B C R)
    (io : JIO Io V) (a : A) (b : B) (color : C) : m R :=
  if ops.egal a b then ops.printValue io a else ops.printStyled io a color

end JuliaLean.base.errorshow.Models2Group17

namespace JuliaLean.base.errorshow.Models2Group17

/-- Results encode a returned Julia type by some and the Julia value nothing by
none. The argument is the runtime type value T; its identity is retained without
reflection calls. Julia source: base/errorshow.jl:417. -/
-- Source: base/errorshow.jl:417-417 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- striptype(::Type{T}) where {T} = T
-- /Source
def striptypeType {Ty : Type} (type : Ty) : Option Ty := some type

/-- The selected Any fallback does not read or convert its argument. A type
argument normally selects striptypeType instead. Nothing is none in the same
result representation. Julia source: base/errorshow.jl:418. -/
-- Source: base/errorshow.jl:418-418 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- striptype(::Any) = nothing
-- /Source
def striptypeAny {A Ty : Type} (_value : A) : Option Ty := none

end JuliaLean.base.errorshow.Models2Group17


namespace JuliaLean.ErrorShow


/-! ### Exception rendering -/

inductive Piece where
  | literal (text : String)
  | payload (text : String)
  deriving Repr, DecidableEq

def Piece.text : Piece → String
  | .literal text | .payload text => text

def concatenate (pieces : List Piece) : String :=
  String.intercalate "" (pieces.map Piece.text)

inductive FixedError where
  | divide
  | stackOverflow
  | undefRef
  | eof
  | interrupt
  deriving Repr, DecidableEq

def FixedError.text : FixedError → String
  | .divide => "DivideError: integer division error"
  | .stackOverflow => "StackOverflowError:"
  | .undefRef => "UndefRefError: access to undefined reference"
  | .eof => "EOFError: read end of file"
  | .interrupt => "InterruptException:"

inductive MessageError where
  | error
  | argument
  | dimension
  | assertion
  | overflow
  deriving Repr, DecidableEq

def MessageError.prefix : MessageError → String
  | .error => ""
  | .argument => "ArgumentError: "
  | .dimension => "DimensionMismatch: "
  | .assertion => "AssertionError: "
  | .overflow => "OverflowError: "

def commaPieces : List String → List Piece
  | [] => []
  | [value] => [.payload value]
  | value :: rest => .payload value :: .literal ", " :: commaPieces rest

inductive UndefScope where
  | moduleName (rendered : String)
  | staticParameter
  | localKind (rendered : String)
  deriving Repr, DecidableEq

inductive ErrorView where
  | fallback (shown : String)
  | parse (messageRepr : String) (detail : Option String)
  | typeName (unionComponentsDiffer : Bool)
  | bareBounds
  | bounds (summary : String) (indices : List String)
  | typeErrorBoolean (gotType : String)
  | typeErrorDictKey (gotRepr expected : String)
  | typeError (context expected got : String)
  | load (inner file line : String)
  | init (inner moduleName : String)
  | domain (value : String) (message : Option String)
  | system (sysPrefix errorText : String) (extra : Option String)
  | fixed (kind : FixedError)
  | message (kind : MessageError) (message : String)
  | key (keyRepr : String)
  | undefKeyword (name : String)
  | undefVar (name : String) (scope : Option UndefScope)
  | inexact (functionName typeName typeRepr firstArgument : String)
      (moreArguments : List String)
  | canonicalIndex (functionName typeRepr : String)
  | method (signature : String) (hints candidates : List String)
  | field (typeRepr fieldName : String) (hint : Option String)
  deriving Repr, DecidableEq

/-- The output-producing calls of the `showerror` methods at
`base/errorshow.jl:30-443`. Error-hint callbacks enter as rendered strings. -/
def renderPieces : ErrorView → List Piece
  | .fallback shown => [.payload shown]
  | .parse messageRepr none => [.literal "ParseError(", .payload messageRepr, .literal ")"]
  | .parse _ (some detail) => [.payload detail]
  | .typeName true =>
      [.literal "TypeNameError: typename does not apply to unions whose components have different typenames"]
  | .typeName false => [.literal "TypeNameError: typename does not apply to this type"]
  | .bareBounds => [.literal "BoundsError"]
  | .bounds summary [] => [.literal "BoundsError: attempt to access ", .payload summary]
  | .bounds summary indices =>
      [.literal "BoundsError: attempt to access ", .payload summary, .literal " at index ["] ++
        commaPieces indices ++ [.literal "]"]
  | .typeErrorBoolean gotType =>
      [.literal "TypeError: non-boolean (", .payload gotType,
       .literal ") used in boolean context"]
  | .typeErrorDictKey gotRepr expected =>
      [.literal "TypeError: ", .payload gotRepr,
       .literal " is not a valid key for type ", .payload expected]
  | .typeError context expected got =>
      [.literal "TypeError: ", .payload context, .literal ", expected ", .payload expected,
       .literal ", got ", .payload got]
  | .load inner file line =>
      [.literal "LoadError: ", .payload inner, .literal "\nin expression starting at ",
       .payload file, .literal ":", .payload line]
  | .init inner moduleName =>
      [.literal "InitError: ", .payload inner, .literal "\nduring initialization of module ",
       .payload moduleName]
  | .domain value none => [.literal "DomainError with ", .payload value]
  | .domain value (some message) =>
      [.literal "DomainError with ", .payload value, .literal ":\n", .payload message]
  | .system sysPrefix errorText none =>
      [.literal "SystemError: ", .payload sysPrefix, .literal ": ", .payload errorText]
  | .system sysPrefix errorText (some extra) =>
      [.literal "SystemError (with ", .payload extra, .literal "): ", .payload sysPrefix,
       .literal ": ", .payload errorText]
  | .fixed kind => [.literal kind.text]
  | .message kind message => [.literal kind.prefix, .payload message]
  | .key keyRepr => [.literal "KeyError: key ", .payload keyRepr, .literal " not found"]
  | .undefKeyword name =>
      [.literal "UndefKeywordError: keyword argument `", .payload name, .literal "` not assigned"]
  | .undefVar name none => [.literal "UndefVarError: `", .payload name, .literal "` not defined"]
  | .undefVar name (some (.moduleName scope)) =>
      [.literal "UndefVarError: `", .payload name, .literal "` not defined in `",
       .payload scope, .literal "`"]
  | .undefVar name (some .staticParameter) =>
      [.literal "UndefVarError: `", .payload name,
       .literal "` not defined in static parameter matching"]
  | .undefVar name (some (.localKind scope)) =>
      [.literal "UndefVarError: `", .payload name, .literal "` not defined in ",
       .payload scope, .literal " scope"]
  | .inexact functionName typeName typeRepr firstArgument moreArguments =>
      [.literal "InexactError: ", .payload functionName, .literal "("] ++
        (if typeName == functionName then [] else [.payload typeRepr, .literal ", "]) ++
        commaPieces (firstArgument :: moreArguments) ++ [.literal ")"]
  | .canonicalIndex functionName typeRepr =>
      [.literal "CanonicalIndexError: ", .payload functionName,
       .literal " not defined for ", .payload typeRepr]
  | .method signature hints candidates =>
      [.literal "MethodError: no method matching ", .payload signature] ++
        hints.map Piece.payload ++ candidates.map Piece.payload
  | .field typeRepr fieldName hint =>
      [.literal "FieldError: type ", .payload typeRepr, .literal " has no field `",
       .payload fieldName, .literal "`"] ++ hint.toList.map Piece.payload

def renderError (error : ErrorView) : String := concatenate (renderPieces error)

/-! ### Method display and MethodError candidates -/

structure Candidate where
  text : String
  score : Int
  deriving Repr, DecidableEq

def insertCandidate (candidate : Candidate) : List Candidate → List Candidate
  | [] => [candidate]
  | head :: tail =>
      if candidate.score ≤ head.score then candidate :: head :: tail
      else head :: insertCandidate candidate tail

def sortCandidates (candidates : List Candidate) : List Candidate :=
  candidates.foldr insertCandidate []

/-- `show_method_candidates`, `base/errorshow.jl:656-865`, sorts ascending by
the negated match score and prints at most three candidates. -/
def closestCandidates (candidates : List Candidate) : List Candidate :=
  (sortCandidates candidates).take 3

def candidatesTruncated (candidates : List Candidate) : Bool := candidates.length > 3

end JuliaLean.ErrorShow

namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

/-! ### Remaining `base/errorshow.jl` helpers -/

inductive TypeTree where
  | leaf (name : String)
  | node (name : String) (parameters : List TypeTree)
  deriving Repr

inductive DiffToken where
  | same (text : String)
  | mismatch (text : String)
  | literal (text : String)
  deriving Repr, DecidableEq

def renderTypeTree : TypeTree → String
  | .leaf name => name
  | .node name parameters =>
      name ++ "{" ++ String.intercalate "," (parameters.map renderTypeTree) ++ "}"

def typeDiff : TypeTree → TypeTree → List DiffToken
  | .leaf left, .leaf right =>
      if left == right then [.same left] else [.mismatch left]
  | .node left lp, .node right rp =>
      if left != right then [.mismatch (renderTypeTree (.node left lp))]
      else .literal (left ++ "{") :: diffLists lp rp ++ [.literal "}"]
  | left, _ => [.mismatch (renderTypeTree left)]
where
  diffLists : List TypeTree → List TypeTree → List DiffToken
    | [], _ => []
    | left :: rest, [] => .mismatch (renderTypeTree left) :: diffLists rest []
    | left :: rest, right :: rights =>
        typeDiff left right ++ (if rest.isEmpty then [] else [.literal ", "]) ++
          diffLists rest rights

def showSeparator (color : Bool) : List DiffToken :=
  if color then [.literal "color(light_black)", .literal ", ", .literal "color(default)"]
  else [.literal ", "]

def showTypeMismatch (typeText : String) (topLevel color : Bool) : List DiffToken :=
  if color then [.literal "error-color", .mismatch typeText, .literal "default-color"]
  else if topLevel then [.literal "!Matched{", .mismatch typeText, .literal "}"]
  else [.literal "!Matched::", .mismatch typeText]

def typesOf (runtimeTypes : List String) : List String := runtimeTypes

def stripType (isType : Bool) (typeText : String) : Option String :=
  if isType then some typeText else none

def printWithCompare (sameIdentity : Bool) (shown : String) : DiffToken :=
  if sameIdentity then .same shown else .mismatch shown

def showConvertError (targetType : Option String) (sourceType firstArgument : String) : String :=
  match targetType with
  | none => "First argument to `convert` must be a Type, got " ++ firstArgument
  | some target => "Cannot `convert` an object of type " ++ sourceType ++
      " to an object of type " ++ target

def showNamedTupleDiff (compatible : Bool) (tokens : List DiffToken) : Option (List DiffToken) :=
  if compatible then some tokens else none

def descendParameters (sameOuter nonempty : Bool) (parameters : List TypeTree) : Option (List TypeTree) :=
  if sameOuter && nonempty then some parameters else none

def resolvesToSelf (moduleDefined parentSame : Bool) : Bool :=
  !moduleDefined || parentSame

def shadowedTypeHints (shadows : List String) : List String := shadows.eraseDups

def envBool (value : Option Bool) (default : Bool) : Bool := value.getD default

def showErrorNoStdio (message staticError : String) : String :=
  message ++ ":\n" ++ staticError ++ "\n"

def stacktraceColor (fixedColor nextColor : Option String) : Option String :=
  fixedColor.orElse fun _ => nextColor

def parentBeforeMain : List String → Option String
  | [] => none
  | [moduleName] => some moduleName
  | moduleName :: "Main" :: _ => some moduleName
  | _ :: rest => parentBeforeMain rest

structure CycleClosing where
  startLine : Nat
  cycleLength : Nat
  repetitions : Nat
  frameAdvance : Nat
  deriving Repr, DecidableEq

def closeRepetitions (line : Nat) (frameCounter active : Nat) :
    List CycleClosing → Nat × Nat
  | [] => (frameCounter, active)
  | cycle :: rest =>
      if line = cycle.startLine + cycle.cycleLength - 1 then
        closeRepetitions line (frameCounter + cycle.frameAdvance) (active - 1) rest
      else (frameCounter, active)

def processedFrameNumbers (counts : List Nat) : List Nat :=
  counts.foldl (fun output count => output ++ [output.length + 1] ++
    List.replicate (count - 1) 0) []

def stackFrameLayout (linePrefix signature location : String) (number width active starts : Nat)
    (inlined : Bool) : String :=
  linePrefix ++ " " ++ String.ofList (List.replicate (active - starts) '├') ++
    String.ofList (List.replicate starts '┌') ++
    String.ofList (List.replicate (width - (toString number).length - 2) ' ') ++
    "[" ++ toString number ++ "] " ++
    signature ++ "\n" ++ linePrefix ++ " " ++ String.ofList (List.replicate active '│') ++
    " @ " ++ location ++ (if inlined then " [inlined]" else "")

def modulePathFile (moduleName directory file : String) (line column : Int) : String :=
  "@ " ++ (if moduleName.isEmpty then "" else moduleName ++ " ") ++
    (if directory.isEmpty then "" else directory ++ "/") ++ file ++ ":" ++
    (if line < 0 then "?" else toString line) ++
    (if column = 0 then "" else ":" ++ toString column)

inductive ShowBacktraceRoute where
  | empty
  | suppressTopLevel
  | direct
  | findCycles
  deriving Repr, DecidableEq

def showBacktraceRoute (empty singleUnknown large : Bool) : ShowBacktraceRoute :=
  if empty then .empty else if singleUnknown then .suppressTopLevel
  else if large then .findCycles else .direct

def showInterpreterIP (typeName code moduleName : String) (statement : Int)
    (topLevel : Bool) : String :=
  typeName ++ (if topLevel then " in top-level CodeInfo for " ++ moduleName
    else " in " ++ code) ++ " at statement " ++ toString statement

structure RepeatedCycle where
  start : Nat
  length : Nat
  repetitions : Nat
  deriving Repr, DecidableEq

def collapseRepeatedFrames [BEq α] : List α → List (α × Nat)
  | [] => []
  | head :: tail => loop head 1 tail
where
  loop [BEq α] (current : α) (count : Nat) : List α → List (α × Nat)
    | [] => [(current, count)]
    | head :: tail =>
        if head == current then loop current (count + 1) tail
        else (current, count) :: loop head 1 tail

structure TraceEntry where
  frameKey : String
  removeKwcall : Bool := false
  keepInclude : Bool := true
  loadingFrame : Bool := false
  loadingAnchor : Bool := false
  keepLocation : Bool := true
  deriving Repr, DecidableEq, BEq

def removeKwcallFrames (frames : List TraceEntry) : List TraceEntry :=
  frames.filter fun frame => !frame.removeKwcall

def simplifyIncludes (frames : List TraceEntry) : List TraceEntry :=
  frames.filter fun frame => frame.keepInclude

def isLoadingFrame (frame : TraceEntry) : Bool := frame.loadingFrame

def isLoadingAnchor (frame : TraceEntry) : Bool := frame.loadingAnchor

def simplifyLoading (fullLoading : Bool) (frames : List TraceEntry) : List TraceEntry :=
  if fullLoading then frames
  else frames.filter fun frame => !frame.loadingFrame || frame.loadingAnchor

def collapseLocations (frames : List TraceEntry) : List TraceEntry :=
  frames.filter fun frame => frame.keepLocation

def processBacktrace (fullLoading : Bool) (frames : List TraceEntry) : List (TraceEntry × Nat) :=
  collapseRepeatedFrames
    (collapseLocations (simplifyLoading fullLoading (simplifyIncludes (removeKwcallFrames frames))))

def showExceptionStack (exceptions : List String) : String :=
  String.intercalate "\ncaused by: " exceptions.reverse

inductive HintCase where
  | none
  | message (text : String)
  deriving Repr, DecidableEq

def hintWhen (condition : Bool) (message : String) : HintCase :=
  if condition then .message message else .none

def noncallableNumberHint (isNumber : Bool) : HintCase :=
  hintWhen isNumber "Maybe you forgot to use an operator such as *, ^, %, / etc. ?"

inductive NonsettableKind where
  | none | number | typeValue
  deriving Repr, DecidableEq

def nonsettableHint : NonsettableKind → HintCase
  | .none => .none
  | .number => .message "Use a[1, 2] rather than a[1][2]"
  | .typeValue => .message "Create an instance with its constructor before indexing"

def stringConcatenationHint (condition : Bool) : HintCase :=
  hintWhen condition "String concatenation is performed with *"

def stringReplaceHint (condition : Bool) : HintCase :=
  hintWhen condition "Strings cannot be modified with replace!; use replace"

def iterableMethodHint (message : Option String) : HintCase :=
  match message with | none => .none | some text => .message text

def fieldErrorHint (message : Option String) : HintCase :=
  match message with | none => .none | some text => .message text

def applyTypeHint (condition : Bool) (got : String) : HintCase :=
  hintWhen condition ("`" ++ got ++ "` takes no type parameters")

def undefVarHint (messages : List String) : List String := messages

def exceptionStackSize (stack : List String) : Nat := stack.length

def exceptionStackGet? (stack : List String) (index : Nat) : Option String := stack[index]?

def showExceptionStackPlain (stack : List String) : String :=
  s!"{stack.length}-element ExceptionStack" ++ (if stack.isEmpty then "" else ":\n") ++
    showExceptionStack stack

def propertyNamesByType (fieldNames propertyNames : List String) : List String :=
  (fieldNames ++ propertyNames).eraseDups

inductive IncompleteKind where
  | none | other | string | comment | block | command | character
  deriving Repr, DecidableEq

def incompleteTag (headIncomplete hasArgument : Bool) (kind : IncompleteKind) : IncompleteKind :=
  if !headIncomplete then .none else if !hasArgument then .other else kind

end JuliaLean.ErrorShow.Coverage


namespace JuliaLean.ErrorShow.ErrorshowFaithful

open JuliaLean.ErrorShow
open JuliaLean.ErrorShow.Coverage

abbrev R (α : Type) := Except String α

def showerrorFallback {α : Type} (showFn : α → String) (value : α) : String := showFn value

def showIndexAny {α : Type} (showFn : α → String) (value : α) := showFn value

def showIndexSlice (indicesOutput : String) := indicesOutput

def showIndexLogical (maskSummary : String) := maskSummary

def showIndexOneTo (stop : String) := "1:" ++ stop

def showIndexColon (_unit : Unit) := ":"

def showParseError (messageRepr : String) (detail : Option String) : String :=
  detail.getD ("ParseError(" ++ messageRepr ++ ")")

def showTypeNameError (differentUnionNames : Bool) : String :=
  "TypeNameError: " ++ if differentUnionNames then
    "typename does not apply to unions whose components have different typenames"
  else "typename does not apply to this type"

def showBoundsError (collectionSummary : Option String) (indices : Option (List String)) : String :=
  "BoundsError" ++ match collectionSummary with
  | none => ""
  | some summary => ": attempt to access " ++ summary ++ match indices with
    | none => "" | some values => " at index [" ++ String.intercalate ", " values ++ "]"

inductive TypeErrorCase where
  | booleanContext (gotType : String)
  | dictKey (got expected : String)
  | general (context expected got : String)
  deriving Repr, DecidableEq

def showTypeError : TypeErrorCase → String
  | .booleanContext got => "TypeError: non-boolean (" ++ got ++ ") used in boolean context"
  | .dictKey got expected => "TypeError: " ++ got ++ " is not a valid key for type " ++ expected
  | .general context expected got => "TypeError: " ++ context ++ ", expected " ++ expected ++ ", got " ++ got

structure ShowWithBacktraceResult where
  errorText : String
  backtraceText : String
  deriving Repr, DecidableEq

def showErrorWithBacktrace (errorAction : R String) (backtrace : Bool) (backtraceText : String) : R ShowWithBacktraceResult :=
  match errorAction with
  | .ok errorText => .ok { errorText, backtraceText := if backtrace then backtraceText else "" }
  | .error failure => .error (failure ++ if backtrace then backtraceText else "")

def showLoadErrorBacktrace (inner file line backtraceText : String) (backtrace : Bool) : String :=
  "LoadError: " ++ inner ++ (if backtrace then backtraceText else "") ++
    "\nin expression starting at " ++ file ++ ":" ++ line

def showLoadError (inner file line : String) := showLoadErrorBacktrace inner file line "" false

def showInitErrorBacktrace (inner moduleName backtraceText : String) (backtrace : Bool) : String :=
  "InitError: " ++ inner ++ (if backtrace then backtraceText else "") ++ "\nduring initialization of module " ++ moduleName

def showInitError (inner moduleName : String) := showInitErrorBacktrace inner moduleName "" false

def showDomainError (value : String) (message : Option String) :=
  "DomainError with " ++ value ++ (match message with | none => "" | some text => ":\n" ++ text)

def showSystemError (name errorText : String) (extra : Option String) :=
  match extra with
  | none => "SystemError: " ++ name ++ ": " ++ errorText
  | some text => "SystemError (with " ++ text ++ "): " ++ name ++ ": " ++ errorText

def showDivideError (_unit : Unit) := "DivideError: integer division error"

def showStackOverflowError (_unit : Unit) := "StackOverflowError:"

def showUndefRefError (_unit : Unit) := "UndefRefError: access to undefined reference"

def showEofError (_unit : Unit) := "EOFError: read end of file"

def showErrorException (message : String) := message

def showKeyError (keyShown : String) := "KeyError: key " ++ keyShown ++ " not found"

def showInterruptException (_unit : Unit) := "InterruptException:"

def showArgumentError (message : String) := "ArgumentError: " ++ message

def showDimensionMismatch (message : String) := "DimensionMismatch: " ++ message

def showAssertionError (message : String) := "AssertionError: " ++ message

def showOverflowError (message : String) := "OverflowError: " ++ message

def showUndefKeywordError (name : String) := "UndefKeywordError: keyword argument `" ++ name ++ "` not assigned"

inductive UndefScopeM where | absent | moduleName (name : String) | staticParameter | localKind (name : String) deriving Repr, DecidableEq

def showUndefVarError (name : String) : UndefScopeM → String
  | .absent => "UndefVarError: `" ++ name ++ "` not defined"
  | .moduleName scope => "UndefVarError: `" ++ name ++ "` not defined in `" ++ scope ++ "`"
  | .staticParameter => "UndefVarError: `" ++ name ++ "` not defined in static parameter matching"
  | .localKind scope => "UndefVarError: `" ++ name ++ "` not defined in " ++ scope ++ " scope"

def showInexactError (functionName typeName typeShown firstArg : String) (rest : List String) :=
  "InexactError: " ++ functionName ++ "(" ++ (if typeName = functionName then "" else typeShown ++ ", ") ++
    String.intercalate ", " (firstArg :: rest) ++ ")"

def showCanonicalIndexError (functionName typeShown : String) := "CanonicalIndexError: " ++ functionName ++ " not defined for " ++ typeShown

def typesOf (runtimeTypes : List String) := runtimeTypes

def printWithCompareDataType (sameName : Bool) (name : String) (left right : List TypeTree) : List DiffToken :=
  if sameName then typeDiff (.node name left) (.node name right) else [.mismatch (renderTypeTree (.node name left))]

def printWithCompareAny (sameIdentity : Bool) (shown : String) : DiffToken := if sameIdentity then .same shown else .mismatch shown

def showConvertError (target : Option String) (source firstArgument : String) := match target with
  | none => "First argument to `convert` must be a Type, got " ++ firstArgument
  | some type => "Cannot `convert` an object of type " ++ source ++ " to an object of type " ++ type

inductive MethodErrorCase where
  | convert (text : String)
  | abstractConstructor (type : String)
  | noncallable (type : String)
  | standard (signature : String)
  deriving Repr, DecidableEq

def methodErrorCore : MethodErrorCase → String
  | .convert text => text
  | .abstractConstructor type => "no constructors have been defined for " ++ type
  | .noncallable type => "objects of type " ++ type ++ " are not callable."
  | .standard signature => "no method matching " ++ signature

def showMethodError (input : MethodErrorCase) (hints candidates : List String) : String :=
  "MethodError: " ++ methodErrorCore input ++
    String.intercalate "" hints ++ String.intercalate "" candidates

def showFieldError (typeName field hint : String) := "FieldError: type " ++ typeName ++ " has no field `" ++ field ++ "`" ++ hint

def stripTypeYes (typeName : String) : Option String := some typeName

def stripTypeNo (_value : String) : Option String := none

def showAmbiguousError (signature : String) (candidates : List String) (fix : Option String) :=
  "MethodError: " ++ signature ++ " is ambiguous.\n\nCandidates:\n" ++ String.intercalate "\n" candidates ++ fix.getD ""

def showErrorNoStdio (message staticShown : String) := message ++ ":\n" ++ staticShown ++ "\n"

def stacktraceExpandBasepaths (environment : Option Bool) : Bool := environment.getD false

def stacktraceContractUserdir (environment : Option Bool) : Bool := environment.getD true

def stacktraceLinebreaks (environment : Option Bool) : Bool := environment.getD false

def stacktraceFullLoading (environment : Option Bool) : Bool := environment.getD false

def showTypeDiff (signature called : TypeTree) := typeDiff signature called

def showSeparatorFaithful (color : Bool) := showSeparator color

def showTypeMatch (typeText : String) (color : Bool) : List DiffToken :=
  if color then [.literal "light-black", .same typeText, .literal "default"] else [.same typeText]

def showNamedtupleDiff (compatible : Bool) (tokens : List DiffToken) : Option (List DiffToken) := if compatible then some tokens else none

def descendParams (sameName nonempty : Bool) (signature called : List TypeTree) : Option (List TypeTree × List TypeTree) :=
  if sameName && nonempty then some (signature, called) else none

def showTypeMismatchFaithful (typeText : String) (color topLevel : Bool) := showTypeMismatch typeText topLevel color

def resolvesToSelf (moduleDefined parentSame : Bool) := !moduleDefined || parentSame

def showShadowedTypeHint (reported : List String) (candidate : String) : List String :=
  if reported.contains candidate then reported else reported ++ [candidate]

def showMethodCandidates (candidates : List Candidate) : List Candidate := (sortCandidates candidates).take 3

def getStacktraceColor (existing : Option String) (next : String) : String := existing.getD next

structure CycleSummary where
  displayed : List (String × Nat)
  cycles : List RepeatedCycle
  maxNested : Nat
  deriving Repr, DecidableEq

def findAndRemoveCycles (trace : List String) : CycleSummary :=
  let displayed := collapseRepeatedFrames trace
  { displayed, cycles := [], maxNested := if displayed.any (fun item => 1 < item.2) then 1 else 0 }

def repetitionClosings (line frameCounter active : Nat) (cycles : List CycleClosing) :=
  closeRepetitions line frameCounter active cycles

def showProcessedBacktrace (frames : List String) (linebreaks : Bool) :=
  "\nStacktrace:\n" ++ String.intercalate (if linebreaks then "\n\n" else "\n") frames

def printStackframeColorLookup (moduleColor rendered : String) := (moduleColor, rendered)

def parentmoduleBeforeMain (parents : List String) : Option String := parentBeforeMain parents

def parentmoduleBeforeMainObject (parents : List String) := parentmoduleBeforeMain parents

def printStackframeLayout (linePrefix signature location : String) (number width active starts : Nat) (inlined : Bool) :=
  stackFrameLayout linePrefix signature location number width active starts inlined

def printModulePathFile (moduleName directory file : String) (line column : Int) := modulePathFile moduleName directory file line column

def showBacktrace (empty singleUnknown large : Bool) := showBacktraceRoute empty singleUnknown large

def collapseAndCountRepeatedFrames (frames : List TraceEntry) := collapseRepeatedFrames frames

def removeKwcallFramesFaithful (frames : List TraceEntry) := removeKwcallFrames frames

def simplifyIncludeFrames (frames : List TraceEntry) := simplifyIncludes frames

def isLoadingFrameFaithful (frame : TraceEntry) := isLoadingFrame frame

def isLoadingAnchorFaithful (frame : TraceEntry) := isLoadingAnchor frame

def simplifyLoadingFrames (full : Bool) (frames : List TraceEntry) := simplifyLoading full frames

def collapseRepeatedLocations (frames : List TraceEntry) := collapseLocations frames

def processBacktraceFrames (full : Bool) (frames : List TraceEntry) := processBacktrace full frames

def processBacktraceCounted (full : Bool) (frames : List TraceEntry) := processBacktrace full frames

def showExceptionStackFaithful (exceptions : List String) := showExceptionStack exceptions

def showInterpreterIpFaithful (typeName code moduleName : String) (statement : Int) (topLevel : Bool) :=
  showInterpreterIP typeName code moduleName statement topLevel

def noncallableNumberHint (isNumber : Bool) : Option String :=
  if isNumber then some "Maybe you forgot to use an operator such as *, ^, %, / etc. ?" else none

inductive NonsettableCase where | none | number | typeValue (name : String) deriving Repr, DecidableEq

def nonsettableHint : NonsettableCase → Option String
  | .none => none | .number => some "Use a[1, 2] rather than a[1][2]"
  | .typeValue name => some ("Construct " ++ name ++ " before indexing it")

def stringConcatenationHint (condition : Bool) := if condition then some "String concatenation is performed with *" else none

def stringReplaceHint (condition : Bool) := if condition then some "Strings cannot be modified with replace!; use replace" else none

def methodsOnIterable (maximumMinimum lengthSize : Option String) : List String := maximumMinimum.toList ++ lengthSize.toList

def fieldErrorDictHint (isDict : Bool) (field : String) := if isDict then some ("dict[:" ++ field ++ "]") else none

def fieldErrorListHint (fields properties : List String) := (fields, properties.filter fun property => !fields.contains property)

def propertyNamesByType (custom : Bool) (inferred : Option (List String)) := if custom then inferred else none

def applyTypeUnionallHint (condition : Bool) (got : String) := if condition then some ("`" ++ got ++ "` takes no type parameters.") else none

def undefVarErrorHint (scopeMessages baseMessages loadedMessages finalMessages : List String) :=
  scopeMessages ++ baseMessages ++ loadedMessages ++ finalMessages

def undefVarWarnFor (warnings : List String) : Bool × List String := (!warnings.isEmpty, warnings)

def exceptionStackSize (stack : List String) := stack.length

def exceptionStackGet? (stack : List String) (index : Nat) := stack[index]?

def showExceptionStackPlain (stack : List String) :=
  toString stack.length ++ "-element ExceptionStack" ++ (if stack.isEmpty then "" else ":\n") ++
    String.intercalate "\ncaused by: " stack.reverse

def showExceptionStackCompact (stack : List String) := showExceptionStackPlain stack

inductive IncompleteInput where | other | empty | text (kind : String) | nested (tag : String) deriving Repr, DecidableEq

def incompleteTag : IncompleteInput → String
  | .other => "none" | .empty => "other" | .text kind => kind | .nested tag => tag

def incompleteTagParseError (detail : IncompleteInput) := incompleteTag detail

end JuliaLean.ErrorShow.ErrorshowFaithful

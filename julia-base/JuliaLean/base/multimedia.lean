import JuliaLean.base.error
import JuliaLean.Core

/-!
# Model of `base/multimedia.jl`

MIME values retain their media-type string. User-defined `show` and display methods,
method applicability, byte/string conversion, and IO effects are explicit parameters.
The global display stack is modeled as a list passed into and returned from its operations.
-/

namespace JuliaLean.base.multimedia

abbrev Bytes := List UInt8

/--
Julia source: base/multimedia.jl:63-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct MIME{mime} end
```
-/

structure MIME where
  name : String
  deriving BEq, DecidableEq, Repr

private def textPlain : MIME := ⟨"text/plain"⟩

inductive MultimediaError where
  | methodError (functionName : String)
  | keyError (key : String)
  | argumentError (message : String)
  | other (message : String)
  deriving BEq, DecidableEq, Repr

-- The Julia string macro is compile-time type syntax; `mimeOfString` models runtime construction.

-- UNTRANSLATED
-- Source: base/multimedia.jl:73-75 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- macro MIME_str(s)
--     :(MIME{$(Expr(:quote, Symbol(s)))})
-- end
-- /Source

/--
Julia source: base/multimedia.jl:78-82 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, ::MIME"text/plain", x) = show(io, x)

MIME(s) = MIME{Symbol(s)}()
show(io::IO, ::MIME{mime}) where {mime} = print(io, "MIME type ", string(mime))
print(io::IO, ::MIME{mime}) where {mime} = print(io, mime)
```
-/

def mimeOfString (name : String) : MIME := ⟨name⟩

def showTextPlainFallback {Io X E : Type} (show2 : Io → X → Except E Unit)
    (io : Io) (_m : MIME) (x : X) : Except E Unit := show2 io x

def showMIME {Io E : Type} (print : Io → String → Except E Unit) (io : Io) (m : MIME) :
    Except E Unit := print io ("MIME type " ++ m.name)

def printMIME {Io E : Type} (print : Io → String → Except E Unit) (io : Io) (m : MIME) :
    Except E Unit := print io m.name

/--
Julia source: base/multimedia.jl:107-108 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
showable(::MIME{mime}, @nospecialize x) where {mime} = hasmethod(show, Tuple{IO, MIME{mime}, typeof(x)})
showable(m::AbstractString, @nospecialize x) = showable(MIME(m), x)
```
-/

def showable {X : Type} (hasShowMethod : MIME → X → Bool) (m : MIME) (x : X) : Bool :=
  hasShowMethod m x

def showableString {X : Type} (hasShowMethod : MIME → X → Bool) (m : String) (x : X) : Bool :=
  showable hasShowMethod (mimeOfString m) x

-- `show(io,mime,x)` is a Julia generic declaration; concrete show methods are supplied by dispatch.
-- UNTRANSLATED
-- Source: base/multimedia.jl:153-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- show(stream::IO, mime, x)
-- /Source

/--
Julia source: base/multimedia.jl:154-154 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, m::AbstractString, x) = show(io, MIME(m), x)
```
-/

def showString {Io X E : Type} (showMethod : Io → MIME → X → Except E Unit)
    (io : Io) (m : String) (x : X) : Except E Unit := showMethod io (mimeOfString m) x

/--
Julia source: base/multimedia.jl:226-237 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
istextmime(m::MIME) = startswith(string(m), "text/")
istextmime(m::AbstractString) = istextmime(MIME(m))

for mime in ["application/atom+xml", "application/ecmascript",
             "application/javascript", "application/julia",
             "application/json", "application/postscript",
             "application/rdf+xml", "application/rss+xml",
             "application/x-latex", "application/xhtml+xml", "application/xml",
             "application/xml-dtd", "image/svg+xml", "model/vrml",
             "model/x3d+vrml", "model/x3d+xml"]
    global istextmime(::MIME{Symbol(mime)}) = true
end
```
-/

def textualMIMEs : List String :=
  ["application/atom+xml", "application/ecmascript", "application/javascript",
   "application/julia", "application/json", "application/postscript",
   "application/rdf+xml", "application/rss+xml", "application/x-latex",
   "application/xhtml+xml", "application/xml", "application/xml-dtd",
   "image/svg+xml", "model/vrml", "model/x3d+vrml", "model/x3d+xml"]

def isTextMime (m : MIME) : Bool := m.name.startsWith "text/" || textualMIMEs.contains m.name

def isTextMimeString (m : String) : Bool := isTextMime (mimeOfString m)

inductive Representation where
  | text (value : String)
  | bytes (value : Bytes)
  deriving BEq, DecidableEq, Repr

structure ReprOps (X Context : Type) where
  showBytes : MIME → X → Option Context → Except MultimediaError Bytes
  stringFromBytes : Bytes → String

/--
Julia source: base/multimedia.jl:190-209 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repr(m::MIME, x; context=nothing) = istextmime(m) ? _textrepr(m, x, context) : _binrepr(m, x, context)
repr(m::AbstractString, x; context=nothing) = repr(MIME(m), x; context=context)

# strings are shown escaped for text/plain
_textrepr(m::MIME, x, context) = String(__binrepr(m, x, context))
_textrepr(::MIME, x::AbstractString, context) = x
_textrepr(m::MIME"text/plain", x::AbstractString, context) = String(__binrepr(m, x, context))


function __binrepr(m::MIME, x, context)
    s = IOBuffer()
    if context === nothing
        show(s, m, x)
    else
        show(IOContext(s, context), m, x)
    end
    take!(s)
end
_binrepr(m::MIME, x, context) = __binrepr(m, x, context)
_binrepr(m::MIME, x::Vector{UInt8}, context) = x
```
-/

def textRepr {X Context : Type} (ops : ReprOps X Context) (m : MIME) (x : X)
    (context : Option Context) : Except MultimediaError String := do
  pure (ops.stringFromBytes (← ops.showBytes m x context))

def textReprString {Context : Type} (ops : ReprOps String Context) (m : MIME) (x : String)
    (context : Option Context) : Except MultimediaError String :=
  if m == textPlain then textRepr ops m x context else .ok x

def binaryRepr {X Context : Type} (ops : ReprOps X Context) (m : MIME) (x : X)
    (context : Option Context) : Except MultimediaError Bytes := ops.showBytes m x context

def binaryReprBytes (x : Bytes) : Except MultimediaError Bytes := .ok x

def reprMIME {X Context : Type} (ops : ReprOps X Context) (m : MIME) (x : X)
    (context : Option Context) : Except MultimediaError Representation := do
  if isTextMime m then
    return .text (← textRepr ops m x context)
  else
    return .bytes (← binaryRepr ops m x context)

def reprString {Context : Type} (ops : ReprOps String Context) (m : MIME) (x : String)
    (context : Option Context) : Except MultimediaError Representation := do
  if isTextMime m then
    return .text (← textReprString ops m x context)
  else
    return .bytes (← binaryRepr ops m x context)

def reprBytes {Context : Type} (ops : ReprOps Bytes Context) (m : MIME) (x : Bytes)
    (context : Option Context) : Except MultimediaError Representation := do
  if isTextMime m then
    return .text (ops.stringFromBytes (← ops.showBytes m x context))
  else
    return .bytes (← binaryReprBytes x)

/--
Julia source: base/multimedia.jl:256-256 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
abstract type AbstractDisplay end
```
-/

abbrev AbstractDisplay (D : Type) := D

/--
Julia source: base/multimedia.jl:259-260 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
display(d::AbstractDisplay, mime::AbstractString, @nospecialize x) = display(d, MIME(mime), x)
display(mime::AbstractString, @nospecialize x) = display(MIME(mime), x)
```
-/

def displayBackendString {D X R : Type} (display : D → MIME → X → Except MultimediaError R)
    (d : D) (m : String) (x : X) : Except MultimediaError R := display d (mimeOfString m) x

def displayGlobalString {X R : Type} (display : MIME → X → Except MultimediaError R)
    (m : String) (x : X) : Except MultimediaError R := display (mimeOfString m) x

/--
Julia source: base/multimedia.jl:270-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
displayable(d::AbstractDisplay, mime::AbstractString) = displayable(d, MIME(mime))
displayable(mime::AbstractString) = displayable(MIME(mime))
```
-/

def displayableBackendString {D : Type} (displayable : D → MIME → Bool) (d : D)
    (m : String) : Bool := displayable d (mimeOfString m)

def displayableGlobalString {D : Type} (displayable : D → MIME → Bool) (displays : List D)
    (m : String) : Bool := displays.any (fun d => displayable d (mimeOfString m))

/--
Julia source: base/multimedia.jl:282-297 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct TextDisplay <: AbstractDisplay
    io::IO
end
display(d::TextDisplay, M::MIME"text/plain", @nospecialize x) = (show(d.io, M, x); println(d.io))
display(d::TextDisplay, @nospecialize x) = display(d, MIME"text/plain"(), x)

# if you explicitly call display("text/foo", x), it should work on a TextDisplay:
displayable(d::TextDisplay, M::MIME) = istextmime(M)
function display(d::TextDisplay, M::MIME, @nospecialize x)
    displayable(d, M) || throw(MethodError(display, (d, M, x)))
    show(d.io, M, x); println(d.io)
end

import Base: close, flush
flush(d::TextDisplay) = flush(d.io)
close(d::TextDisplay) = close(d.io)
```
-/
structure TextDisplay (Io : Type) where
  io : Io


structure TextDisplayOps (Io X : Type) where
  showOutput : Io → MIME → X → Except MultimediaError Unit
  printLine : Io → Except MultimediaError Unit
  flush : Io → Except MultimediaError Unit
  close : Io → Except MultimediaError Unit

def displayTextPlain {Io X : Type} (ops : TextDisplayOps Io X) (d : TextDisplay Io) (x : X) :
    Except MultimediaError Unit := do
  ops.showOutput d.io textPlain x
  ops.printLine d.io

def displayTextDefault {Io X : Type} (ops : TextDisplayOps Io X) (d : TextDisplay Io) (x : X) :
    Except MultimediaError Unit := displayTextPlain ops d x

def displayableText (m : MIME) : Bool := isTextMime m

def displayTextMime {Io X : Type} (ops : TextDisplayOps Io X) (d : TextDisplay Io) (m : MIME)
    (x : X) : Except MultimediaError Unit := do
  if !displayableText m then throw (.methodError "display")
  ops.showOutput d.io m x
  ops.printLine d.io

def flushTextDisplay {Io X : Type} (ops : TextDisplayOps Io X) (d : TextDisplay Io) :
    Except MultimediaError Unit := ops.flush d.io

def closeTextDisplay {Io X : Type} (ops : TextDisplayOps Io X) (d : TextDisplay Io) :
    Except MultimediaError Unit := ops.close d.io

/--
Julia source: base/multimedia.jl:303-303 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const displays = AbstractDisplay[]
```
-/

def emptyDisplayStack {D : Type} : List (AbstractDisplay D) := []

/--
Julia source: base/multimedia.jl:312-316 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function pushdisplay(d::AbstractDisplay)
    global displays
    push!(displays, d)
end

```
-/
def pushDisplay {D : Type} (displays : List (AbstractDisplay D)) (d : AbstractDisplay D) :
    List (AbstractDisplay D) := displays ++ [d]
private def popLast? {X : Type} : List X → Option (X × List X)
  | [] => none
  | [x] => some (x, [])
  | x :: xs =>
      match popLast? xs with
      | some (last, rest) => some (last, x :: rest)
      | none => none
private def popFirstBy {X : Type} (eq : X → X → Bool) (target : X) :
    List X → Option (X × List X)
  | [] => none
  | x :: xs =>
      if eq x target then some (x, xs)
      else
        match popFirstBy eq target xs with
        | some (found, rest) => some (found, x :: rest)
        | none => none
/--
Julia source: base/multimedia.jl:324-338 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
popdisplay() = pop!(displays)
function popdisplay(d::AbstractDisplay)
    for i = length(displays):-1:1
        if d == displays[i]
            return splice!(displays, i)
        end
    end
    throw(KeyError(d))
end
function reinit_displays()
    empty!(displays)
    pushdisplay(TextDisplay(stdout))
end

xdisplayable(D::AbstractDisplay, @nospecialize args...) = applicable(display, D, args...)
```
-/



def popDisplay {D : Type} (displays : List (AbstractDisplay D)) :
    Except MultimediaError (AbstractDisplay D × List (AbstractDisplay D)) :=
  match popLast? displays with
  | some result => .ok result
  | none => .error (.argumentError "array must be non-empty")


def popNamedDisplay {D : Type} (eq : AbstractDisplay D → AbstractDisplay D → Bool)
    (displays : List (AbstractDisplay D)) (d : AbstractDisplay D) :
    Except MultimediaError (AbstractDisplay D × List (AbstractDisplay D)) :=
  match popFirstBy eq d displays.reverse with
  | some (found, rest) => .ok (found, rest.reverse)
  | none => .error (.keyError "display")

def reinitDisplays {D : Type} (stdoutDisplay : AbstractDisplay D) : List (AbstractDisplay D) :=
  [stdoutDisplay]

def xdisplayable {D X : Type} (applicable : D → X → Bool) (d : D) (x : X) : Bool :=
  applicable d x

def xdisplayableMIME {D X : Type} (applicable : D → MIME → X → Bool) (d : D) (m : MIME)
    (x : X) : Bool := applicable d m x

/--
Julia source: base/multimedia.jl:367-403 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function display(@nospecialize x)
    for i = length(displays):-1:1
        if xdisplayable(displays[i], x)
            try
                return display(displays[i], x)
            catch e
                isa(e, MethodError) && (e.f === display || e.f === show) ||
                    rethrow()
            end
        end
    end
    throw(MethodError(display, (x,)))
end

function display(m::MIME, @nospecialize x)
    for i = length(displays):-1:1
        if xdisplayable(displays[i], m, x)
            try
                return display(displays[i], m, x)
            catch e
                isa(e, MethodError) && e.f == display ||
                    rethrow()
            end
        end
    end
    throw(MethodError(display, (m, x)))
end

displayable(d::D, ::MIME{mime}) where {D<:AbstractDisplay,mime} =
    hasmethod(display, Tuple{D,MIME{mime},Any})

function displayable(m::MIME)
    for d in displays
        displayable(d, m) && return true
    end
    return false
end
```
-/

structure DisplayDispatch (D X R : Type) where
  applicablePlain : D → X → Bool
  applicableMIME : D → MIME → X → Bool
  displayPlain : D → X → Except MultimediaError R
  displayMIME : D → MIME → X → Except MultimediaError R
  redisplayPlain : D → X → Except MultimediaError R
  redisplayMIME : D → MIME → X → Except MultimediaError R
  hasDisplayMIME : D → MIME → Bool

private def caughtMethodError (caught : List String) : MultimediaError → Bool
  | .methodError name => caught.contains name
  | _ => false

private def displayLoop {D R : Type} (functionName : String) (caught : List String)
    (applicable : D → Bool) (invoke : D → Except MultimediaError R) :
    List D → Except MultimediaError R
  | [] => .error (.methodError functionName)
  | d :: rest =>
      if !applicable d then displayLoop functionName caught applicable invoke rest
      else
        match invoke d with
        | .ok result => .ok result
        | .error e =>
            if caughtMethodError caught e then displayLoop functionName caught applicable invoke rest
            else .error e

def displayGlobal {D X R : Type} (ops : DisplayDispatch D X R) (displays : List D) (x : X) :
    Except MultimediaError R :=
  displayLoop "display" ["display", "show"] (fun d => ops.applicablePlain d x)
    (fun d => ops.displayPlain d x) displays.reverse

def displayGlobalMIME {D X R : Type} (ops : DisplayDispatch D X R) (displays : List D)
    (m : MIME) (x : X) : Except MultimediaError R :=
  displayLoop "display" ["display"] (fun d => ops.applicableMIME d m x)
    (fun d => ops.displayMIME d m x) displays.reverse

def displayableBackend {D X R : Type} (ops : DisplayDispatch D X R) (d : D) (m : MIME) : Bool :=
  ops.hasDisplayMIME d m

def displayableGlobal {D X R : Type} (ops : DisplayDispatch D X R) (displays : List D)
    (m : MIME) : Bool := displays.any (fun d => ops.hasDisplayMIME d m)

/--
Julia source: base/multimedia.jl:426-456 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function redisplay(@nospecialize x)
    for i = length(displays):-1:1
        if xdisplayable(displays[i], x)
            try
                return redisplay(displays[i], x)
            catch e
                isa(e, MethodError) && e.f in (redisplay, display, show) ||
                    rethrow()
            end
        end
    end
    throw(MethodError(redisplay, (x,)))
end

function redisplay(m::Union{MIME,AbstractString}, @nospecialize x)
    for i = length(displays):-1:1
        if xdisplayable(displays[i], m, x)
            try
                return redisplay(displays[i], m, x)
            catch e
                isa(e, MethodError) && e.f in (redisplay, display) ||
                    rethrow()
            end
        end
    end
    throw(MethodError(redisplay, (m, x)))
end

# default redisplay is simply to call display
redisplay(d::AbstractDisplay, @nospecialize x) = display(d, x)
redisplay(d::AbstractDisplay, m::Union{MIME,AbstractString}, @nospecialize x) = display(d, m, x)
```
-/

def redisplayBackendPlain {D X R : Type} (ops : DisplayDispatch D X R) (d : D) (x : X) :
    Except MultimediaError R := ops.displayPlain d x

def redisplayBackendMIME {D X R : Type} (ops : DisplayDispatch D X R) (d : D) (m : MIME)
    (x : X) : Except MultimediaError R := ops.displayMIME d m x

def redisplayGlobal {D X R : Type} (ops : DisplayDispatch D X R) (displays : List D) (x : X) :
    Except MultimediaError R :=
  displayLoop "redisplay" ["redisplay", "display", "show"]
    (fun d => ops.applicablePlain d x) (fun d => ops.redisplayPlain d x) displays.reverse

def redisplayGlobalMIME {D X R : Type} (ops : DisplayDispatch D X R) (displays : List D)
    (m : MIME) (x : X) : Except MultimediaError R :=
  displayLoop "redisplay" ["redisplay", "display"]
    (fun d => ops.applicableMIME d m x) (fun d => ops.redisplayMIME d m x) displays.reverse

end JuliaLean.base.multimedia


namespace JuliaLean.ErrorShow


/-! ### MIME, showability, and displayability -/

abbrev Mime := String

/-- `MIME(s) = MIME{Symbol(s)}()` and the `print`/`show` methods,
`base/multimedia.jl:73-82`. -/
def makeMime (text : String) : Mime := text

def printMime (mime : Mime) : String := mime

def showMime (mime : Mime) : String := "MIME type " ++ mime

def showable (hasShowMethod : Bool) : Bool := hasShowMethod

structure DisplayBackend where
  supported : List Mime
  deriving Repr, DecidableEq

def backendDisplayable (backend : DisplayBackend) (mime : Mime) : Bool :=
  backend.supported.contains mime

/-- `displayable(mime)`, `base/multimedia.jl:395-403`. -/
def displayable (stack : List DisplayBackend) (mime : Mime) : Bool :=
  stack.any fun backend => backendDisplayable backend mime

/-- The display loop at `base/multimedia.jl:367-393` checks the stack from the
top, which is the end of the backing vector. -/
def topDisplay (stack : List DisplayBackend) (mime : Mime) : Option DisplayBackend :=
  stack.reverse.find? fun backend => backendDisplayable backend mime

end JuliaLean.ErrorShow

namespace JuliaLean.ErrorShow.Coverage

open JuliaLean.ErrorShow

/-! ### Common list and rendering helpers -/

def removeFirst [BEq α] (value : α) : List α → List α
  | [] => []
  | head :: tail => if head == value then tail else head :: removeFirst value tail

def removeLast [BEq α] (value : α) (items : List α) : List α :=
  (removeFirst value items.reverse).reverse

def appendLine (text : String) : String := text ++ "\n"

/-! ### `base/multimedia.jl` -/

def textualMimes : List String :=
  ["application/atom+xml", "application/ecmascript", "application/javascript",
   "application/julia", "application/json", "application/postscript",
   "application/rdf+xml", "application/rss+xml", "application/x-latex",
   "application/xhtml+xml", "application/xml", "application/xml-dtd",
   "image/svg+xml", "model/vrml", "model/x3d+vrml", "model/x3d+xml"]

/-- `istextmime`, `base/multimedia.jl:226-236`. -/
def isTextMime (mime : String) : Bool :=
  mime.startsWith "text/" || textualMimes.contains mime

inductive MediaValue where
  | text (value : String)
  | bytes (value : List UInt8)
  | other
  deriving Repr, DecidableEq

inductive Representation where
  | text (value : String)
  | bytes (value : List UInt8)
  deriving Repr, DecidableEq

/-- `_binrepr` and `__binrepr`, lines 199-209. `shown` is the byte stream
written by the selected three-argument `show` method. -/
def binaryRepresentation (value : MediaValue) (shown : List UInt8) : List UInt8 :=
  match value with
  | .bytes bytes => bytes
  | _ => shown

/-- `_textrepr` and `repr`, lines 190-209. `decoded` is `String(shown)` from
Julia's String primitive. -/
def representation (mime : String) (value : MediaValue)
    (shown : List UInt8) (decoded : String) : Representation :=
  if isTextMime mime then
    match value with
    | .text text => if mime == "text/plain" then .text decoded else .text text
    | _ => .text decoded
  else
    .bytes (binaryRepresentation value shown)

inductive DisplayOutcome where
  | success (backend : String)
  | methodError (functionName : String)
  | otherError (message : String)
  deriving Repr, DecidableEq

structure DisplayAttempt where
  backend : String
  applicable : Bool
  outcome : DisplayOutcome
  deriving Repr, DecidableEq

def caughtBy (caught : List String) : DisplayOutcome → Bool
  | .methodError functionName => caught.contains functionName
  | _ => false

/-- The shared top-to-bottom display loop at lines 367-393 and 426-452.
Attempts arrive in stack order; the last attempt is the top backend. -/
def runDisplayLoop (functionName : String) (caught : List String) :
    List DisplayAttempt → DisplayOutcome
  | attempts => run attempts.reverse
where
  run : List DisplayAttempt → DisplayOutcome
    | [] => .methodError functionName
    | attempt :: rest =>
        if !attempt.applicable then run rest
        else match attempt.outcome with
          | .success backend => .success backend
          | error => if caughtBy caught error then run rest else error

def displayAny (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "display" ["display", "show"] attempts

def displayMime (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "display" ["display"] attempts

def redisplayAny (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "redisplay" ["redisplay", "display", "show"] attempts

def redisplayMime (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "redisplay" ["redisplay", "display"] attempts

/-- `TextDisplay` methods, lines 285-297. -/
def textDisplay (mime shown : String) : Result String :=
  if isTextMime mime then .ok (shown ++ "\n") else .error "MethodError(display)"

/-- Display stack mutation, lines 312-336. -/
def pushDisplay (stack : List String) (backend : String) : List String := stack ++ [backend]

def popDisplay : List String → Result (String × List String)
  | [] => .error "ArgumentError: array must be non-empty"
  | stack => .ok (stack.getLast!, stack.dropLast)

def popNamedDisplay (stack : List String) (backend : String) : Result (List String) :=
  if stack.contains backend then .ok (removeLast backend stack) else .error "KeyError"

def reinitDisplays (stdout : String) : List String := [stdout]

def delegateDisplayIO (result : Result Unit) : Result Unit := result

end JuliaLean.ErrorShow.Coverage


namespace JuliaLean.ErrorShow.MultimediaFaithful

open JuliaLean.ErrorShow.Coverage

abbrev R (α : Type) := Except String α

def mimeStr (text : String) : String := text

def showTextPlainFallback (twoArgumentShow : String) : String := twoArgumentShow

def mimeConstructor (text : String) : String := text

def showMime (mime : String) : String := "MIME type " ++ mime

def printMime (mime : String) : String := mime

def showableMime (hasShowMethod : Bool) : Bool := hasShowMethod

def showableString (mimeText : String) (hasShowMethod : String → Bool) : Bool :=
  showableMime (hasShowMethod (mimeConstructor mimeText))

def showStringMime (mimeText shown : String) : String :=
  let _mime := mimeConstructor mimeText
  shown

def reprMime (mime : String) (textResult : String) (binaryResult : List UInt8) : Representation :=
  if isTextMime mime then .text textResult else .bytes binaryResult

def reprString (mimeText : String) (textResult : String) (binaryResult : List UInt8) : Representation :=
  reprMime (mimeConstructor mimeText) textResult binaryResult

def textReprGeneric (decodedBinrepr : String) : String := decodedBinrepr

def textReprRawString (text : String) : String := text

def textReprPlainString (decodedBinrepr : String) : String := decodedBinrepr

def binreprBuffer (contextPresent : Bool) (plainShow contextShow : List UInt8) : List UInt8 :=
  if contextPresent then contextShow else plainShow

def binreprGeneric (bufferResult : List UInt8) : List UInt8 := bufferResult

def binreprBytes (bytes : List UInt8) : List UInt8 := bytes

def isTextMimePrefix (mime : String) : Bool := mime.startsWith "text/"

def isTextMimeString (mimeText : String) : Bool := isTextMimePrefix (mimeConstructor mimeText)

def isKnownTextMime (_mime : String) : Bool := true

def displayBackendString (mimeText result : String) : String :=
  let _mime := mimeConstructor mimeText
  result

def displayGlobalString (mimeText result : String) : String :=
  let _mime := mimeConstructor mimeText
  result

def displayableBackendString (mimeText : String) (backendCheck : String → Bool) : Bool :=
  backendCheck (mimeConstructor mimeText)

def displayableGlobalString (mimeText : String) (globalCheck : String → Bool) : Bool :=
  globalCheck (mimeConstructor mimeText)

def textDisplayPlain (shown : String) : String := shown ++ "\n"

def textDisplayDefault (shownPlain : String) : String := textDisplayPlain shownPlain

def textDisplayable (mime : String) : Bool := isTextMime mime

def textDisplayMime (mime shown : String) : R String :=
  if textDisplayable mime then .ok (shown ++ "\n") else .error "MethodError(display)"

def flushTextDisplay (flushResult : R Unit) : R Unit := flushResult

def closeTextDisplay (closeResult : R Unit) : R Unit := closeResult

def pushDisplayMethod (stack : List String) (backend : String) : List String := stack ++ [backend]

def popDisplayMethod : List String → R (String × List String)
  | [] => .error "ArgumentError: array must be non-empty"
  | stack => .ok (stack.getLast!, stack.dropLast)

def popNamedDisplayMethod (stack : List String) (backend : String) : R (List String) :=
  if stack.contains backend then .ok (removeLast backend stack) else .error "KeyError"

def reinitDisplaysMethod (stdout : String) : List String := [stdout]

def xdisplayable (applicable : Bool) : Bool := applicable

def displayAny (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "display" ["display", "show"] attempts

def displayMime (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "display" ["display"] attempts

def displayableBackendMime (hasMethod : Bool) : Bool := hasMethod

def displayableGlobalMime (backendResults : List Bool) : Bool := backendResults.any id

def redisplayAny (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "redisplay" ["redisplay", "display", "show"] attempts

def redisplayMime (attempts : List DisplayAttempt) : DisplayOutcome :=
  runDisplayLoop "redisplay" ["redisplay", "display"] attempts

def redisplayBackendDefault (displayResult : String) : String := displayResult

def redisplayBackendMimeDefault (displayResult : String) : String := displayResult

end JuliaLean.ErrorShow.MultimediaFaithful

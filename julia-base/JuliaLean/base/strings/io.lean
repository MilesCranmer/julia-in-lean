import JuliaLean.stdlib.Base64.src.Base64
import JuliaLean.base.show
import JuliaLean.Core
import JuliaLean.base.iobuffer
import JuliaLean.base.char
import JuliaLean.base.strings.basic
import JuliaLean.base.strings.string
import JuliaLean.base.strings.substring
import JuliaLean.base.strings.unicode
import JuliaLean.base.strings.search
import JuliaLean.base.strings.util
import JuliaLean.base.intfuncs
import JuliaLean.base.ryu.Ryu
import JuliaLean.base.coreio

/-!
# Model of `base/strings/io.jl`

Typed source models for string construction, IO, escaping, joining, and multiline text. Streams
are the installed `show.jl` interface (`IOPrims m Io V` wrapped in `JIO`); `IOBuffer` results use
the installed buffer model (`bufferPrims`, `newBufferState`, `takestring`). Typed parameters are
only: user `show`/`print` methods of values of other types, the string type's `AbstractString`
methods (`basic.StringOps`), the iterator passed to `join` (`show.IterOps`), the C library
`utf8proc` (`unicode.Utf8proc`), the `base/div.jl` record `intfuncs.DigitCallees`, and
`printstyled` (`show.PrintStyled`).
-/

namespace JuliaLean.base.strings.io

structure JuliaString where
  bytes : List UInt8
structure CodeUnitsVector where
  bytes : List UInt8

structure JuliaSymbol where
  name : List UInt8

structure JuliaSubString where
  string : JuliaString
  offset : Nat
  byteCount : Nat

structure RegionAnnotation where
  first : Nat
  last : Nat
  annotation : String

structure AnnotatedText where
  bytes : List UInt8
  annotations : List RegionAnnotation

structure QuoteNode where
  bytes : CodeUnitsVector

inductive Unindented (S : Type) where
  | original (value : S)
  | built (bytes : List UInt8)

inductive RawStringResult (S : Type) where
  | original (value : S)
  | copied (bytes : List UInt8)

/--
Julia source: base/strings/io.jl:643-643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro raw_str(s); s; end
```
-/
def rawStr {S : Type} (s : S) : S := s

-- UNTRANSLATED
-- Source: base/strings/io.jl:242-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- write(io::IO, s::Union{String,SubString{String}}; cancel::CancelTokenArg=DEFAULT_CANCEL) =
--     cancel === DEFAULT_CANCEL ?
--         GC.@preserve(s, (unsafe_write(io, pointer(s), reinterpret(UInt, sizeof(s))) % Int)::Int) :
--         GC.@preserve(s, (unsafe_write(io, pointer(s), reinterpret(UInt, sizeof(s)); cancel) % Int)::Int)
-- /Source

/-- UTF-8 code units written by `write(io, c::Char)` (`base/io.jl:973-980`). -/
def charUtf8BytesLoop : Nat → UInt32 → List UInt8
  | 0, _ => []
  | fuel + 1, u =>
      let b : UInt8 := (u &&& 0xff).toUInt8
      let next := u >>> 8
      if next == 0 then [b]
      else b :: charUtf8BytesLoop fuel next

def charUtf8Bytes (c : JuliaLean.base.char.JChar) : List UInt8 :=
  charUtf8BytesLoop 4 (JuliaLean.base.strings.basic.bswap32 c)

def writeCharBufferStateLoop :
    Nat → UInt32 → JuliaLean.base.iobuffer.I → JuliaLean.base.iobuffer.M JuliaLean.base.iobuffer.I
  | 0, _, n => pure n
  | fuel + 1, u, n => do
      let written ← JuliaLean.base.iobuffer.writeByte ((u &&& 0xff).toUInt8)
      let n := n + written
      let next := u >>> 8
      if next == 0 then pure n
      else writeCharBufferStateLoop fuel next n

/-- `write(io::IOBuffer, c::Char)` (`base/io.jl:973-980`). -/
def writeCharBufferState (io : JuliaLean.base.iobuffer.BufferState)
    (c : JuliaLean.base.char.JChar) :
    Except JuliaLean.base.iobuffer.IOErr
      (JuliaLean.base.iobuffer.BufferState × JuliaLean.base.iobuffer.I) :=
  let u := JuliaLean.base.strings.basic.bswap32 c
  match (writeCharBufferStateLoop 4 u (JuliaLean.base.iobuffer.i 0)).run io with
  | .ok count next => .ok (next, count)
  | .error err _ => .error err

inductive PrintError where
  | io (e : JuliaLean.base.iobuffer.IOErr)
  | char (e : JuliaLean.base.char.CharError)

/-- `print(io::IOBuffer, c::Char)` (`base/char.jl:305`). -/
def printCharBufferState (io : JuliaLean.base.iobuffer.BufferState)
    (c : JuliaLean.base.char.JChar) :
    Except JuliaLean.base.iobuffer.IOErr JuliaLean.base.iobuffer.BufferState := do
  let (next, _) ← writeCharBufferState io c
  pure next

/-- `print(io::IOBuffer, c::AbstractChar)` (`base/char.jl:306`). -/
def printAbstractCharBufferState {C : Type}
    (toChar : C → JuliaLean.base.char.CharResult JuliaLean.base.char.JChar)
    (io : JuliaLean.base.iobuffer.BufferState) (c : C) :
    Except PrintError JuliaLean.base.iobuffer.BufferState := do
  let ch ← (toChar c).mapError .char
  (printCharBufferState io ch).mapError .io

/-- `print(io::IOBuffer, c1::Char, c2::Char)`. -/
def printTwoCharsBufferState (io : JuliaLean.base.iobuffer.BufferState)
    (c1 c2 : JuliaLean.base.char.JChar) :
    Except JuliaLean.base.iobuffer.IOErr JuliaLean.base.iobuffer.BufferState := do
  let io ← printCharBufferState io c1
  printCharBufferState io c2

/-- `write(io::IOBuffer, bytes)` via `JuliaLean.base.iobuffer.unsafeWrite`. -/
def writeBytesBufferState (io : JuliaLean.base.iobuffer.BufferState) (bytes : List UInt8) :
    Except JuliaLean.base.iobuffer.IOErr
      (JuliaLean.base.iobuffer.BufferState × JuliaLean.base.iobuffer.I) :=
  match (JuliaLean.base.iobuffer.unsafeWrite bytes).run io with
  | .ok count next => .ok (next, count)
  | .error err _ => .error err

/-- `print(io::IOBuffer, s::Union{String,SubString{String}})` (`base/strings/io.jl:246`). -/
def printBytesBufferState (io : JuliaLean.base.iobuffer.BufferState) (bytes : List UInt8) :
    Except JuliaLean.base.iobuffer.IOErr JuliaLean.base.iobuffer.BufferState := do
  let (next, _) ← writeBytesBufferState io bytes
  pure next

/-- Bind the selected sizehint conversion in the installed IOBuffer constructor. -/
def newBufferState {Hint : Type} (hintConversion : JuliaLean.base.iobuffer.IntegerConversions Hint)
    (sizehint : Option Hint) :
    Except JuliaLean.base.iobuffer.IOErr JuliaLean.base.iobuffer.BufferState := do
  let (_, state) ← (JuliaLean.base.iobuffer.iobufferEmpty
    (JuliaLean.base.iobuffer.ctorStateAccess true)
    (JuliaLean.base.iobuffer.bitsConversions .i64)
    hintConversion
    (fun size => pure (List.replicate size.val.toNat (0 : UInt8)))
    (fun memory => pure memory)
    (fun memory : List UInt8 => pure (JuliaLean.base.iobuffer.i memory.length))
    JuliaLean.base.iobuffer.nativeInt
    (some true) (some true) none (some true)
    JuliaLean.base.iobuffer.imaxval sizehint).run
      (JuliaLean.base.iobuffer.newBuf [] true true true true false JuliaLean.base.iobuffer.imaxval)
  pure state

/-- `takestring!(io::IOBuffer)` (`base/iobuffer.jl:795-862`). -/
def takeStringBufferState (io : JuliaLean.base.iobuffer.BufferState) :
    Except JuliaLean.base.iobuffer.IOErr (List UInt8) :=
  match JuliaLean.base.iobuffer.takestring.run io with
  | .ok bytes _ => .ok bytes
  | .error err _ => .error err

/-- `position(io::IOBuffer)` (`base/iobuffer.jl:470-473`). -/
def positionBufferState (io : JuliaLean.base.iobuffer.BufferState) :
    Except JuliaLean.base.iobuffer.IOErr JuliaLean.base.iobuffer.I :=
  .ok (JuliaLean.base.iobuffer.position io)

/-- String wrapping followed by the installed specialized Vector constructor. -/
def ioBufferOfString {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    {Vector Memory MemoryRef Ref : Type}
    (a : JuliaLean.base.iobuffer.Access m Ref Memory)
    (unsafeWrap : JuliaString → m Vector)
    (reference : Vector → m MemoryRef) (memory : MemoryRef → m Memory)
    (memoryOffset : MemoryRef → m JuliaLean.base.iobuffer.I)
    (vectorLength : Vector → m JuliaLean.base.iobuffer.I)
    (memoryLength : Memory → m JuliaLean.base.iobuffer.I)
    (str : JuliaString) : m Ref := do
  JuliaLean.base.iobuffer.iobufferDataVector a reference memory memoryOffset vectorLength memoryLength
    (fun _ (hint : Empty) => nomatch hint)
    (JuliaLean.base.iobuffer.bitsConversions .i64) (← unsafeWrap str)
    none none none none JuliaLean.base.iobuffer.imaxval none

/-- Substring view construction followed by the installed AbstractVector constructor. -/
def ioBufferOfSubString {m : Type → Type} [Monad m]
    [MonadExceptOf JuliaLean.base.iobuffer.IOErr m]
    [MonadExceptOf JuliaLean.base.abstractarray.ArrayError m]
    [MonadExceptOf JuliaLean.base.range.Exc m]
    {Vector View Ref Index L : Type}
    (a : JuliaLean.base.iobuffer.Access m Ref View)
    (unsafeWrap : JuliaString → m Vector)
    (view : Vector → JuliaLean.base.range.UnitRange JuliaLean.base.iobuffer.I → m View)
    (firstindex : View → m Index) (toIndex : Index → m JuliaLean.base.iobuffer.I)
    (length : View → m L) (toLength : L → m JuliaLean.base.iobuffer.I)
    (s : JuliaSubString) : m Ref := do
  let data ← unsafeWrap s.string
  let first := JuliaLean.base.int.add (JuliaLean.base.iobuffer.i s.offset)
    (JuliaLean.base.iobuffer.i 1)
  let last := JuliaLean.base.int.add (JuliaLean.base.iobuffer.i s.offset)
    (JuliaLean.base.iobuffer.i s.byteCount)
  let indices ← match JuliaLean.base.range.colon_T_T_Real first last with
    | .ok indices => pure indices
    | .error error => throwThe JuliaLean.base.range.Exc error
  let data ← view data indices
  JuliaLean.base.iobuffer.iobufferData a firstindex toIndex length toLength
    (fun _ (hint : Empty) => nomatch hint)
    (JuliaLean.base.iobuffer.bitsConversions .i64) data
    none none none none JuliaLean.base.iobuffer.imaxval none

open JuliaLean JuliaLean.base.show

inductive Error (E : Type) where
  | buffer (error : JuliaLean.base.iobuffer.IOErr)
  | display (error : ShowError)
  | callback (error : E)

abbrev BufferShowM (E : Type) := EStateM (Error E) JuliaLean.base.iobuffer.BufferState

/-- IOContext methods keep their own exceptions; callback exceptions are a separate typed payload. -/
instance {E : Type} : MonadExceptOf ShowError (BufferShowM E) where
  throw error := fun state => .error (.display error) state
  tryCatch action handler := fun state =>
    match action state with
    | .ok value state => .ok value state
    | .error (.display error) state => handler error state
    | .error error state => .error error state

def throwCallback {E A : Type} (error : E) : BufferShowM E A :=
  fun state => .error (.callback error) state

/-- Lift an installed IOBuffer operation without dropping mutations before an error. -/
def liftBuffer {E A : Type} (action : JuliaLean.base.iobuffer.M A) : BufferShowM E A :=
  fun state => match action state with
  | .ok value state => .ok value state
  | .error error state => .error (.buffer error) state

inductive SprintContext (E V : Type) where
  | none
  | pair (key : Sym) (value : V)
  | tuple (pairs : List (Sym × V))
  | io {Parent : Type} (prims : IOPrims (BufferShowM E) Parent V) (parent : JIO Parent V)

/-- Byte-vector write through the IOContext forwarding path retains IOBuffer's native Int result. -/
def writeBufferBytes {E V : Type} (_io : JIO Unit V) (bytes : Bytes) : BufferShowM E JInt64 :=
  liftBuffer (JuliaLean.base.iobuffer.unsafeWrite bytes)

/-- Printer adapters ignore write's result; public callbacks can call writeBufferBytes directly.
The lock/unlock and property lookup entries are the IO defaults (io.jl:33-36, show.jl:371-382). -/
def bufferPrims {E V : Type} (displaySize : JInt64 × JInt64) :
    IOPrims (BufferShowM E) Unit V where
  write := fun io bytes => do let _ ← writeBufferBytes (V := V) (.plain io) bytes; pure ()
  lock := fun _ => pure ()
  unlock := fun _ => pure ()
  get := fun _ _ => none
  displaysize := fun _ => pure displaySize

/-- Each constructor below is the installed IOContext method. In particular IOContext(s)
wraps the stream when the tuple supplied to sprint is empty. -/
def sprintContext {E V Ty : Type} (p : IOPrims (BufferShowM E) Unit V) (a : AnyOps V Ty) :
    SprintContext E V → BufferShowM E (JIO Unit V)
  | .none => pure (.plain ())
  | .pair key value => do
    return .context (← IOContext_pair p a (JuliaLean.base.dict.fieldConv Sym)
      (JuliaLean.base.dict.fieldConv V) (.plain ()) (key,value))
  | .tuple [] => do
    return .context (← IOContext_IO p a (.plain ()))
  | .tuple (first :: rest) => do
    return .context (← IOContext_pairs p a (JuliaLean.base.dict.fieldConv Sym)
      (JuliaLean.base.dict.fieldConv V) (.plain ()) first rest)
  | .io parentPrims parent => do
    return .context (← IOContext_IO_IO parentPrims a (.plain ()) parent)

/--
Julia source: base/strings/io.jl:104-114 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function sprint(f::Function, args...; context=nothing, sizehint::Integer=0)
    s = IOBuffer(sizehint=sizehint)
    if context isa Tuple
        f(IOContext(s, context...), args...)
    elseif context !== nothing
        f(IOContext(s, context), args...)
    else
        f(s, args...)
    end
    takestring!(s)
end
```
-/
def sprintIOBuffer {E V Ty Args R Hint : Type}
    (hintConversion : JuliaLean.base.iobuffer.IntegerConversions Hint)
    (displaySize : JInt64 × JInt64) (a : AnyOps V Ty) (context : SprintContext E V)
    (sizehint : Hint) (f : JIO Unit V → Args → BufferShowM E R) (args : Args) :
    Except (Error E) JuliaLean.base.strings.io.JuliaString := do
  let initial ← (newBufferState hintConversion (some sizehint)).mapError Error.buffer
  let action : BufferShowM E Bytes := do
    let io ← sprintContext (bufferPrims displaySize) a context
    let _ ← f io args
    liftBuffer JuliaLean.base.iobuffer.takestring
  match action initial with
  | .ok bytes _ => pure ⟨bytes⟩
  | .error error _ => .error error

/--
Julia source: base/strings/io.jl:284-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repr(x; context=nothing) = sprint(show, x; context=context)
```
-/
def reprIOBuffer {E V Ty X R : Type} (displaySize : JInt64 × JInt64)
    (a : AnyOps V Ty) (context : SprintContext E V)
    (showOne : JIO Unit V → X → BufferShowM E R) (x : X) :
    Except (Error E) JuliaLean.base.strings.io.JuliaString :=
  sprintIOBuffer (JuliaLean.base.iobuffer.bitsConversions .i64) displaySize a context
    (JuliaLean.base.iobuffer.i 0) showOne x

open JuliaLean JuliaLean.base JuliaLean.base.show

abbrev JChar := JuliaLean.base.char.JChar
abbrev JString := JuliaLean.base.strings.string.JString
abbrev Index := JuliaLean.base.strings.basic.Index

/-! ## Errors

`show.jl` methods throw `ShowError`. The character and string methods below throw
`unicode.jl`/`char.jl` errors, `Int` arithmetic errors (`div`), or an error of the string type's
own methods (`E`); these travel in a second, separate exception class. -/

inductive StrIOError (E : Type) where
  | unicode (e : JuliaLean.base.strings.unicode.UnicodeError)
  | jl (e : JlError)
  | string (e : E)

/-! ## `write(io, ::Union{String,SubString{String}})` through `unsafe_write` (io.jl:242-246)

`write(io, s)` of a `String` or `SubString{String}` calls the `unsafe_write` method of the stream
type of `io`, with `pointer(s)` and `reinterpret(UInt, sizeof(s))`: `UnsafeWrite` is that pair of
methods for one stream type, bound to the installed model of the stream's `unsafe_write`. This file
binds `IOBuffer` (installed `iobuffer.unsafeWrite`), `devnull` (installed `coreio.unsafeWriteDevNull`)
and a stream type that defines only `write(::T, ::UInt8)` (installed `io.unsafeWrite`); the
`IOContext` forwarding is `UnsafeWrite.forwardContext`. The streams of `base/iostream.jl`,
`base/stream.jl`, `base/filesystem.jl`, the heap-world `IOBuffer` and `AnnotatedIOBuffer` are bound in
`JuliaLean.Bindings.base.strings.io`. -/

/-- One stream type's `unsafe_write` methods, called as `unsafe_write(io, p, n)` or, when an explicit
`cancel` token is passed, `unsafe_write(io, p, n; cancel)`. `N` is the result type of the selected
method (`Int` or `UInt`); `toInt` is the `% Int` of `write`. A stream type whose method has no `cancel`
keyword throws a `MethodError` in `explicit`. `Tok` is the token type of `cancel`; `nothing` is
`none`. -/
structure UnsafeWrite (m : Type → Type) (Io P Tok N : Type) where
  plain : Io → P → JInt .u64 → m N
  explicit : Io → P → JInt .u64 → Option Tok → m N
  toInt : N → JInt64

/-- `unsafe_write(io::AbstractPipe, p::Ptr{UInt8}, nb::UInt; cancel)` (io.jl:503-505) for an
`IOContext`: the call is forwarded to `pipe_writer(io)`, with the token when one was passed. -/
def UnsafeWrite.forwardContext {m : Type → Type} {Io V P Tok N : Type}
    (w : UnsafeWrite m Io P Tok N) : UnsafeWrite m (JIO Io V) P Tok N where
  plain io p n := match io with
    | .plain io => w.plain io p n
    | .context c => w.plain (pipe_writer c) p n
  explicit io p n token := match io with
    | .plain io => w.explicit io p n token
    | .context c => w.explicit (pipe_writer c) p n token
  toInt := w.toInt

/-- The same stream methods run in another monad (`JoinM` over `BufferShowM`). -/
def UnsafeWrite.hoist {m n : Type → Type} {Io P Tok N : Type}
    (lift : {α : Type} → m α → n α) (w : UnsafeWrite m Io P Tok N) :
    UnsafeWrite n Io P Tok N where
  plain io p k := lift (w.plain io p k)
  explicit io p k token := lift (w.explicit io p k token)
  toInt := w.toInt

/--
Julia source: base/strings/io.jl:242-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::IO, s::Union{String,SubString{String}}; cancel::CancelTokenArg=DEFAULT_CANCEL) =
    cancel === DEFAULT_CANCEL ?
        GC.@preserve(s, (unsafe_write(io, pointer(s), reinterpret(UInt, sizeof(s))) % Int)::Int) :
        GC.@preserve(s, (unsafe_write(io, pointer(s), reinterpret(UInt, sizeof(s)); cancel) % Int)::Int)
```
`GC.@preserve` keeps `s` alive only. `pointer`, `sizeof` and the stream's `unsafe_write` are the
methods of the string and stream types; `reinterpret(UInt, n)` of an `Int` is the wrapped value
`n % UInt`. The `cancel` value of `DEFAULT_CANCEL` selects the plain call. -/
def writeConcreteString {m : Type → Type} [Monad m] {S Io P Tok N : Type}
    (w : UnsafeWrite m Io P Tok N) (pointer : S → m P) (sizeof : S → JInt64)
    (io : Io) (s : S) : JuliaLean.base.io.CancelArg Tok → m JInt64
  | .default => do
      let p ← pointer s
      pure (w.toInt (← w.plain io p (JInt.wrap .u64 (sizeof s).val)))
  | .explicit token => do
      let p ← pointer s
      pure (w.toInt (← w.explicit io p (JInt.wrap .u64 (sizeof s).val) token))

/--
Julia source: base/strings/io.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, s::Union{String,SubString{String}}) = (write(io, s); nothing)
```
`print(io::IO, s::Union{String,SubString{String}}) = (write(io, s); nothing)` (io.jl:246): the
`write` call is the default-`cancel` one. -/
def printConcreteString {m : Type → Type} [Monad m] {S Io P Tok N : Type}
    (w : UnsafeWrite m Io P Tok N) (pointer : S → m P) (sizeof : S → JInt64)
    (io : Io) (s : S) : m Unit := do
  let _ ← writeConcreteString w pointer sizeof io s .default

/-- `Core.sizeof(s)` of a `String` (`ncodeunits(s::String) = Core.sizeof(s)`, string.jl:209): its number
of bytes. -/
def sizeofJString (s : JString) : JInt64 := JInt.wrap .i64 (Int.ofNat s.bytes.length)

/-- `sizeof(s::SubString{String})`: `ncodeunits(s)::Int * sizeof(codeunit(s)::CodeunitType)`
(basic.jl:178) with `ncodeunits(s::SubString) = s.ncodeunits` (substring.jl:139) and
`sizeof(UInt8) == 1`. -/
def sizeofJSubString (s : JuliaLean.base.strings.substring.SubString JString) : JInt64 :=
  JuliaLean.base.int.mul s.ncodeunits (JuliaLean.base.int.lit .i64 1)

/-- The pointer of the `BufferShowM` world: `iobuffer.unsafeWrite src` takes the bytes `p` designates
(`p` points at `src`); `p + k` drops `k` bytes. -/
def purePointerOps : JuliaLean.base.strings.substring.PointerOps JString where
  Pointer := List UInt8
  pointer s := s.bytes
  add p n := p.drop n.val.toNat

/-- `pointer(s::String)` (string.jl:206) in the `BufferShowM` world. -/
def pointerStringPure {m : Type → Type} [Monad m] (s : JString) : m (List UInt8) :=
  pure (purePointerOps.pointer s)

/-- `pointer(x::SubString{String}) = pointer(x.string) + x.offset` (substring.jl:200, installed
`substring.pointerSubString`) in the `BufferShowM` world. -/
def pointerSubStringPure {m : Type → Type} [Monad m]
    (x : JuliaLean.base.strings.substring.SubString JString) : m (List UInt8) :=
  pure (JuliaLean.base.strings.substring.pointerSubString purePointerOps x)

section BufferWorld

variable {E V : Type}

/-- `unsafe_write(to::GenericIOBuffer, p::Ptr{UInt8}, nb::UInt; cancel)` (iobuffer.jl:902-921) of an
`IOBuffer` in the `BufferShowM` world: the installed `iobuffer.unsafeWrite` of the `nb` bytes at `p`.
The world has no cancellation tokens (`Tok = Empty`), and `cancel = nothing` checks nothing
(`precheck_cancel_arg`, cancellation.jl:1129), so `explicit none` is the plain call. -/
def iobufferUnsafeWrite :
    UnsafeWrite (BufferShowM E) Unit (List UInt8) Empty JuliaLean.base.iobuffer.I where
  plain _ p n := liftBuffer (JuliaLean.base.iobuffer.unsafeWrite (p.take n.val.toNat))
  explicit _ p n token := match token with
    | none => liftBuffer (JuliaLean.base.iobuffer.unsafeWrite (p.take n.val.toNat))
    | some token => nomatch token
  toInt := JuliaLean.base.int.remT .i64

/-- `IOBuffer` or `IOContext{IOBuffer}`. -/
def bufferWriter : UnsafeWrite (BufferShowM E) (JIO Unit V) (List UInt8) Empty JInt64 :=
  iobufferUnsafeWrite.forwardContext

/-- `write(io, s::String)` on an `IOBuffer`. -/
def writeStringBuffer (io : JIO Unit V) (s : JString) :
    JuliaLean.base.io.CancelArg Empty → BufferShowM E JInt64 :=
  writeConcreteString bufferWriter pointerStringPure sizeofJString io s

/-- `write(io, s::SubString{String})` on an `IOBuffer`. -/
def writeSubStringBuffer (io : JIO Unit V)
    (s : JuliaLean.base.strings.substring.SubString JString) :
    JuliaLean.base.io.CancelArg Empty → BufferShowM E JInt64 :=
  writeConcreteString bufferWriter pointerSubStringPure sizeofJSubString io s

/-- `print(io, s::String)` on an `IOBuffer`. -/
def printStringBuffer (io : JIO Unit V) (s : JString) : BufferShowM E Unit :=
  printConcreteString bufferWriter pointerStringPure sizeofJString io s

/-- `print(io, s::SubString{String})` on an `IOBuffer`. -/
def printSubStringBuffer (io : JIO Unit V)
    (s : JuliaLean.base.strings.substring.SubString JString) : BufferShowM E Unit :=
  printConcreteString bufferWriter pointerSubStringPure sizeofJSubString io s

end BufferWorld

/-- `unsafe_write(::DevNull, ::Ptr{UInt8}, n::UInt)::Int = n` (coreio.jl:23, installed
`coreio.unsafeWriteDevNull`): the `::Int` return assertion converts `n` and fails above
`typemax(Int)`. The method has no `cancel` keyword. -/
def devnullUnsafeWrite {m : Type → Type} [Monad m] [MonadExceptOf ShowError m] {P Tok : Type} :
    UnsafeWrite m Unit P Tok JInt64 where
  plain _ p n := ofJl (JuliaLean.base.coreio.unsafeWriteDevNull
    (fun n => JuliaLean.base.int.convert .i64 n) JuliaLean.base.coreio.devnull p n)
  explicit _ _ _ _ := throwThe ShowError (.jl (.methodError "unsafe_write"))
  toInt := JuliaLean.base.int.remT .i64

/-- `unsafe_write(s::IO, p::Ptr{UInt8}, n::UInt)` (io.jl:358-364), for a stream type that defines
only `write(::T, ::UInt8)`: the installed `io.unsafeWrite`, run through the `liftIO` of
`show.IOPrims.ofIO`. `ops.writeByte` is that stream type's `write(io, ::UInt8)` and `load` the
`unsafe_load` of the pointer type. The method has no `cancel` keyword. -/
def fallbackUnsafeWrite {m : Type → Type} [Monad m] [MonadExceptOf ShowError m]
    {World Io P Tok : Type}
    (liftIO : {α : Type} → JuliaLean.base.io.M World α → m α)
    (ops : JuliaLean.base.io.Ops World Io)
    (load : P → JInt .u64 → JuliaLean.base.io.M World JuliaLean.base.io.Byte) :
    UnsafeWrite m Io P Tok JuliaLean.base.io.I where
  plain io p n := liftIO (JuliaLean.base.io.unsafeWrite ops load io p n)
  explicit _ _ _ _ := throwThe ShowError (.jl (.methodError "unsafe_write"))
  toInt := JuliaLean.base.int.remT .i64

/-! ## Iterating a string with its own methods

`for c in s` is `iterate(s)`, the body, then `iterate(s, state)` (the string type's
`iterateFirst`/`iterateAt`), so an `iterate` error comes after the writes of the earlier
characters. The number of steps is the string's iteration bound, exactly as in the installed
`basic.collectStringChars` that defines `characters`. -/

section Iterate

variable {m : Type → Type} [Monad m] {E : Type} [MonadExceptOf (StrIOError E) m]

def ofUnicode {α : Type} : JuliaLean.base.strings.unicode.UResult α → m α
  | .ok a => pure a
  | .error e => throwThe (StrIOError E) (.unicode e)

/-- A `char.jl` error, as `unicode.jl` reports it (installed `unicode.liftChar`). -/
def ofChar {α : Type} (r : JuliaLean.base.char.CharResult α) : m α :=
  ofUnicode (E := E) (JuliaLean.base.strings.unicode.liftChar r)

def ofString {α : Type} : Except E α → m α
  | .ok a => pure a
  | .error e => throwThe (StrIOError E) (.string e)

def ofJlStr {α : Type} : Jl α → m α
  | .ok a => pure a
  | .error e => throwThe (StrIOError E) (.jl e)

/-- The loop of `for c in s ... end` with a loop-carried value; `.done` is a `return`/`break`. -/
def foldCharsLoop {S R CU CT β : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E) (s : S)
    (body : JChar → β → m (ForInStep β)) : Nat → Option (JChar × Index) → β → m β
  | _, none, b => pure b
  | 0, some (c, _), b => do
    match ← body c b with
    | .done b => pure b
    | .yield b => pure b
  | fuel + 1, some (c, i), b => do
    match ← body c b with
    | .done b => pure b
    | .yield b => foldCharsLoop ops s body fuel (← ofString (ops.iterateAt s i)) b

def foldChars {S R CU CT β : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E) (s : S) (init : β)
    (body : JChar → β → m (ForInStep β)) : m β := do
  foldCharsLoop ops s body (ops.iterationBound s) (← ofString (ops.iterateFirst s)) init

/-- `Iterators.Stateful(s)` (iterators.jl): the pending `iterate` result is computed one step
ahead; `popfirst!` returns it and calls `iterate(s, state)` for the next one at once. `fuel` is
the remaining iteration bound. -/
structure Stateful where
  fuel : Nat
  next : Option (JChar × Index)

/-- `iterate(s, i)` of a string with its own `iterate` method. -/
def stringStep {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E) (s : S) (i : Index) :
    m (Option (JChar × Index)) :=
  ofString (ops.iterateAt s i)

/-- `iterate` of the view `SubString(s, i, j)` at a parent index: `nothing` past `j`, otherwise the
parent's `iterate` (substring.jl:151-158), as the installed-model `viewCharsLoop` below. -/
def viewStep {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E) (s : S) (j : Index)
    (i : Index) : m (Option (JChar × Index)) :=
  if i.val > j.val then pure none else ofString (ops.iterateAt s i)

/-- `Iterators.Stateful(s)` of a string: the first `iterate(s)`, with the string's bound. -/
def statefulOf {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E) (s : S) : m Stateful := do
  pure ⟨ops.iterationBound s, ← ofString (ops.iterateFirst s)⟩

/-- `popfirst!(a)` for the iteration step `step`; `none` when `isempty(a)`. -/
def popfirst (step : Index → m (Option (JChar × Index))) :
    Stateful → m (Option (JChar × Stateful))
  | ⟨_, none⟩ => pure none
  | ⟨0, some (c, _)⟩ => pure (some (c, ⟨0, none⟩))
  | ⟨fuel + 1, some (c, i)⟩ => do pure (some (c, ⟨fuel, ← step i⟩))

/-- `peek(a)`; `isempty(a)` is `peek a = none`. -/
def Stateful.peek (a : Stateful) : Option JChar := a.next.map (·.1)

end Iterate

section Stream

variable {m : Type → Type} [Monad m] [MonadExceptOf ShowError m] {Io V Ty E : Type}
variable [MonadExceptOf (StrIOError E) m]

/-- A stream type's methods: the installed `show.jl` record and its `write(io, ::UInt8)` method,
whose `Int` result `write(io, ::Char)` sums (io.jl:973-980). `IOBuffer` is the installed
`iobuffer.writeByte`, `devnull` the installed `coreio.writeDevNull`. -/
structure CharIO (m : Type → Type) (Io V : Type) where
  prims : IOPrims m Io V
  writeByte : Io → UInt8 → m JInt64

/-- `write(io, b::UInt8)`; an `IOContext` forwards it to `pipe_writer(io)` like `show.write`. -/
def writeByteIO (cio : CharIO m Io V) : JIO Io V → UInt8 → m JInt64
  | .plain io, b => cio.writeByte io b
  | .context c, b => cio.writeByte (pipe_writer c) b

/-! ## 1. `print`, `println` (io.jl:32-71)

`print(io, x) = (lock(io); try show(io, x) finally unlock(io) end; nothing)`: `unlock` runs after
every exception of the monad (`tryFinally`), whatever its class. `x`'s `show` method is the
caller's `show` argument (a user method, or an installed `show.jl` method). -/

/-- `lock(io); try body finally unlock(io) end`. -/
def lockedAll [MonadFinally m] (p : IOPrims m Io V) (io : JIO Io V) (body : m Unit) : m Unit := do
  lockIO p io
  tryFinally body (unlockIO p io)

/--
Julia source: base/strings/io.jl:32-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print(io::IO, x)
    lock(io)
    try
        show(io, x)
    finally
        unlock(io)
    end
    return nothing
end
```
`print(io::IO, x)` (io.jl:32-40).
-/
def printValue [MonadFinally m] {X : Type} (p : IOPrims m Io V) (showX : JIO Io V → X → m Unit)
    (io : JIO Io V) (x : X) : m Unit :=
  lockedAll p io (showX io x)

/--
Julia source: base/strings/io.jl:42-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print(io::IO, xs...)
    lock(io)
    try
        # xs[i] might be a known Union, and under --trim that gets split regardless of length.
        # In contrast, `for x in xs` will fall back to Any for unions longer than 3.
        for i in 1:nfields(xs)
            print(io, xs[i])
        end
    finally
        unlock(io)
    end
    return nothing
end
```
`print(io::IO, xs...)` (io.jl:41-52); each element is its own `print(io, x)` call.
-/
def printValues [MonadFinally m] (p : IOPrims m Io V) (io : JIO Io V) (xs : List (m Unit)) : m Unit :=
  lockedAll p io (do for x in xs do x)

/--
Julia source: base/strings/io.jl:77-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
println(io::IO, xs...) = print(io, xs..., "\n")
```
`println(io::IO, xs...) = print(io, xs..., "\n")` (io.jl:71).
-/
def printlnValues [MonadFinally m] (p : IOPrims m Io V) (io : JIO Io V) (xs : List (m Unit)) : m Unit :=
  printValues p io (xs ++ [printStr p io "\n"])

/-! ## 2. Character and string output (io.jl:192-194, 246-248; char.jl:305; io.jl:973-980) -/

/-- `write(io::IO, c::Char)` (io.jl:973-980): one `write(io, ::UInt8)` per UTF-8 code unit
(installed `charUtf8Bytes`, the bytes of `bswap(reinterpret(UInt32, c))` up to the last nonzero
one), summing their `Int` results. -/
def writeChar (cio : CharIO m Io V) (io : JIO Io V) (c : JChar) : m JInt64 := do
  let mut n := JuliaLean.base.int.lit .i64 0
  for b in charUtf8Bytes c do
    n := JuliaLean.base.int.add n (← writeByteIO cio io b)
  pure n

/-- `print(io::IO, c::Char) = (write(io, c); nothing)` (char.jl:305). -/
def printChar (cio : CharIO m Io V) (io : JIO Io V) (c : JChar) : m Unit := do
  let _ ← writeChar cio io c

/--
Julia source: base/strings/io.jl:192-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, s::AbstractString) = for c in s; print(io, c); end
```
`print(io::IO, s::AbstractString) = for c in s; print(io, c); end` (io.jl:192), with the
string type's own `iterate`.
-/
def printAbstractString {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (cio : CharIO m Io V) (io : JIO Io V) (s : S) : m Unit :=
  foldChars ops s () (fun c _ => do printChar cio io c; pure (.yield ()))

/--
Julia source: base/strings/io.jl:193-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::IO, s::AbstractString) = (len = 0; for c in s; len += Int(write(io, c))::Int; end; len)
```
`write(io::IO, s::AbstractString) = (len = 0; for c in s; len += Int(write(io, c))::Int;
end; len)` (io.jl:193).
-/
def writeAbstractString {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (cio : CharIO m Io V) (io : JIO Io V) (s : S) : m JInt64 :=
  foldChars ops s (JuliaLean.base.int.lit .i64 0) (fun c len => do
    pure (.yield (JuliaLean.base.int.add len (← writeChar cio io c))))

/-! ## 3. Escaping (io.jl:395-495)

`escape_string` walks `a = Iterators.Stateful(s)` (`popfirst!` advances before the body);
`peek(a)` is the pending character. `print(io, a, b)` of two arguments is one locked
`printValues` call whose arguments are computed first. -/

/-- A `Char` literal of an ASCII character: `reinterpret(UInt32, Char(u)) == u << 24` for
`u < 0x80` (char.jl:43-50), as in the installed `unicode.charOps` constants. -/
def asciiLit (u : UInt32) : JChar := u <<< 24

/--
Julia source: base/strings/io.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
need_full_hex(c::Union{Nothing, AbstractChar}) = c !== nothing && isxdigit(c)
```
`need_full_hex(c) = c !== nothing && isxdigit(c)` (io.jl:395), installed `isxdigit`.
-/
def needFullHex : Option JChar → Bool
  | none => false
  | some c => JuliaLean.base.strings.unicode.isxdigit JuliaLean.base.strings.unicode.charOps c

/--
Julia source: base/strings/io.jl:396-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
escape_nul(c::Union{Nothing, AbstractChar}) =
    (c !== nothing && '0' <= c <= '7') ? "\\x00" : "\\0"
```
`escape_nul(c) = (c !== nothing && '0' <= c <= '7') ? "\\x00" : "\\0"` (io.jl:396-397).
-/
def escapeNul : Option JChar → String
  | some c => if asciiLit 0x30 ≤ c ∧ c ≤ asciiLit 0x37 then "\\x00" else "\\0"
  | none => "\\0"

/-- `string(UInt32(c), base = 16, pad = k)` (installed `intfuncs.stringBits` through
`show.stringBits`); `UInt32(c)` is the installed `codepoint(::Char)`. -/
def hexCodepoint (digits : JuliaLean.base.intfuncs.DigitCallees) (c : JChar) (pad : Nat) :
    m Bytes := do
  let u ← ofChar (E := E) (JuliaLean.base.char.codepointChar c)
  show.stringBits digits (JInt.wrap .u32 u.toNat) (JInt.wrap .i64 16) (JInt.wrap .i64 pad)

/-- The C escape letter of `'\a' <= c <= '\r'`: `"abtnvfr"[Int(c)-6]`. -/
def controlLetter (c : JChar) : m JChar := do
  let u ← ofChar (E := E) (JuliaLean.base.char.codepointChar c)
  match ("abtnvfr".toList[u.toNat - 7]?) with
  | some l => pure (asciiLit l.toNat.toUInt32)
  | none => throwShow (.jl .boundsError)

/-- `print(io, "\\x", h)` with `h` already computed. -/
def printEscapePrefixed [MonadFinally m] (cio : CharIO m Io V) (io : JIO Io V) (pre : String) (h : Bytes) :
    m Unit :=
  printValues cio.prims io [printStr cio.prims io pre, printBytes cio.prims io h]

/-- The loop `for c::AbstractChar in a ... end` of `escape_string(io, s, esc; keep, ascii,
fullhex)` (io.jl:459-486). Each pass pops one character, so `passes` (the iteration bound plus
one) never ends the loop early. -/
def escapeLoop [MonadFinally m] (step : Index → m (Option (JChar × Index)))
    (cio : CharIO m Io V) (P : JuliaLean.base.strings.unicode.Utf8proc)
    (digits : JuliaLean.base.intfuncs.DigitCallees) (io : JIO Io V)
    (esc keep : List JChar) (ascii fullhex : Bool) : Nat → Stateful → m Unit
  | 0, _ => pure ()
  | passes + 1, a => do
    match ← popfirst step a with
    | none => pure ()
    | some (c, a) =>
      let next := a.peek
      let isprint := fun c =>
        ofUnicode (E := E) (JuliaLean.base.strings.unicode.isprint
          JuliaLean.base.strings.unicode.charOps P c)
      if esc.contains c then
        printValues cio.prims io [printChar cio io (asciiLit 0x5c), printChar cio io c]
      else if keep.contains c then
        printChar cio io c
      else if JuliaLean.base.strings.basic.isasciiChar c then
        if c == asciiLit 0 then printStr cio.prims io (escapeNul next)
        else if c == asciiLit 0x1b then printStr cio.prims io "\\e"
        else if c == asciiLit 0x5c then printStr cio.prims io "\\\\"
        else if asciiLit 0x07 ≤ c ∧ c ≤ asciiLit 0x0d then do
          let l ← controlLetter (E := E) c
          printValues cio.prims io [printChar cio io (asciiLit 0x5c), printChar cio io l]
        else if ← isprint c then printChar cio io c
        else printEscapePrefixed cio io "\\x" (← hexCodepoint (E := E) digits c 2)
      else if !JuliaLean.base.char.isoverlong_Char c && !JuliaLean.base.char.ismalformedChar c then
        if !ascii && (← isprint c) then printChar cio io c
        else if c ≤ asciiLit 0x7f then
          printEscapePrefixed cio io "\\x" (← hexCodepoint (E := E) digits c 2)
        else if c ≤ (0xefbfbf00 : UInt32) then
          printEscapePrefixed cio io "\\u" (← hexCodepoint (E := E) digits c
            (if fullhex || needFullHex next then 4 else 2))
        else
          printEscapePrefixed cio io "\\U" (← hexCodepoint (E := E) digits c
            (if fullhex || needFullHex next then 8 else 4))
      else
        -- malformed or overlong: `u = bswap(reinterpret(UInt32, c))`, one `print` per byte
        for b in charUtf8Bytes c do
          printEscapePrefixed cio io "\\x" (← show.stringBits digits (JInt.wrap .u8 b.toNat)
            (JInt.wrap .i64 16) (JInt.wrap .i64 2))
      escapeLoop step cio P digits io esc keep ascii fullhex passes a

/--
Julia source: base/strings/io.jl:459-486 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function escape_string(io::IO, s::AbstractString, esc=""; keep = (), ascii::Bool=false, fullhex::Bool=false)
    a = Iterators.Stateful(s)
    for c::AbstractChar in a
        if c in esc
            print(io, '\\', c)
        elseif c in keep
            print(io, c)
        elseif isascii(c)
            c == '\0'          ? print(io, escape_nul(peek(a)::Union{AbstractChar,Nothing})) :
            c == '\e'          ? print(io, "\\e") :
            c == '\\'          ? print(io, "\\\\") :
            '\a' <= c <= '\r'  ? print(io, '\\', "abtnvfr"[Int(c)-6]) :
            isprint(c)         ? print(io, c) :
                                 print(io, "\\x", string(UInt32(c), base = 16, pad = 2))
        elseif !isoverlong(c) && !ismalformed(c)
            !ascii && isprint(c) ? print(io, c) :
            c <= '\x7f'          ? print(io, "\\x", string(UInt32(c), base = 16, pad = 2)) :
            c <= '\uffff'        ? print(io, "\\u", string(UInt32(c), base = 16, pad = fullhex || need_full_hex(peek(a)::Union{AbstractChar,Nothing}) ? 4 : 2)) :
                                   print(io, "\\U", string(UInt32(c), base = 16, pad = fullhex || need_full_hex(peek(a)::Union{AbstractChar,Nothing}) ? 8 : 4))
        else # malformed or overlong
            u = bswap(reinterpret(UInt32, c)::UInt32)
            while true
                print(io, "\\x", string(u % UInt8, base = 16, pad = 2))
                (u >>= 8) == 0 && break
            end
        end
    end
end
```
`escape_string(io::IO, s::AbstractString, esc=""; keep=(), ascii=false, fullhex=false)`
(io.jl:459-486).
-/
def escapeStringIO [MonadFinally m] {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (cio : CharIO m Io V) (P : JuliaLean.base.strings.unicode.Utf8proc)
    (digits : JuliaLean.base.intfuncs.DigitCallees) (io : JIO Io V) (s : S)
    (esc keep : List JChar) (ascii fullhex : Bool) : m Unit := do
  let a ← statefulOf (E := E) ops s
  escapeLoop (E := E) (stringStep (E := E) ops s) cio P digits io esc keep ascii fullhex (a.fuel + 2) a

/--
Julia source: base/strings/io.jl:194-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, s::AbstractString) = print_quoted(io, s)
```
Julia source: base/strings/io.jl:491-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_quoted(io, s::AbstractString)
    print(io, '"')
    escape_string(io, s, ('\"','$')) #"# work around syntax highlighting problem
    print(io, '"')
end
```
`print_quoted(io, s::AbstractString)` (io.jl:491-495) and
`show(io::IO, s::AbstractString) = print_quoted(io, s)` (io.jl:194).
-/
def printQuoted [MonadFinally m] {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (cio : CharIO m Io V) (P : JuliaLean.base.strings.unicode.Utf8proc)
    (digits : JuliaLean.base.intfuncs.DigitCallees) (io : JIO Io V) (s : S) : m Unit := do
  printChar cio io (asciiLit 0x22)
  escapeStringIO ops cio P digits io s [asciiLit 0x22, asciiLit 0x24] [] false false
  printChar cio io (asciiLit 0x22)

/-- The digit value of `'0' <= c <= '9' ? n<<4 + (c-'0') : 'a' <= c <= 'f' ? ... :
'A' <= c <= 'F' ? ...` (io.jl:548-550). `c - '0'` is `Int(c) - Int('0')` (char.jl:236); in these
ASCII ranges `Int(c)` (installed `codepoint`) is `reinterpret(UInt32, c) >> 24`. -/
def hexValue (c : JChar) : Option Nat :=
  let u := (c >>> 24).toNat
  if asciiLit 0x30 ≤ c ∧ c ≤ asciiLit 0x39 then some (u - 0x30)
  else if asciiLit 0x61 ≤ c ∧ c ≤ asciiLit 0x66 then some (u - 0x61 + 10)
  else if asciiLit 0x41 ≤ c ∧ c ≤ asciiLit 0x46 then some (u - 0x41 + 10)
  else none

def octalValue (c : JChar) : Option Nat :=
  if asciiLit 0x30 ≤ c ∧ c ≤ asciiLit 0x37 then some ((c >>> 24).toNat - 0x30) else none

/-- `while (k += 1) <= m && !isempty(a); nc = peek(a); n = <digit> or break; popfirst!(a); end`
(io.jl:546-552, 566-570): with `room` digits left, returns the digits taken, `n` and `a`. `n`
stays below `2^32` (at most 8 hex or 3 octal digits), so `Int` `n<<4 + d` never wraps. -/
def takeDigits (step : Index → m (Option (JChar × Index)))
    (value : JChar → Option Nat) (radix : Nat) : Nat → Nat → Stateful → m (Nat × Nat × Stateful)
  | 0, n, a => pure (0, n, a)
  | room + 1, n, a =>
    match a.peek.bind value with
    | none => pure (0, n, a)
    | some d => do
      match ← popfirst step a with
      | none => pure (0, n, a)
      | some (_, a) => do
        let (k, n, a) ← takeDigits step value radix room (n * radix + d) a
        pure (k + 1, n, a)

/-- The standard escape letters of io.jl:576-585. -/
def standardEscape (c : JChar) : m JChar :=
  let table : List (UInt32 × UInt32) :=
    [(0x61, 0x07), (0x62, 0x08), (0x74, 0x09), (0x6e, 0x0a), (0x76, 0x0b), (0x66, 0x0c),
     (0x72, 0x0d), (0x65, 0x1b)]
  match table.find? (fun e => asciiLit e.1 == c) with
  | some e => pure (asciiLit e.2)
  | none =>
    if c == asciiLit 0x5c || c == asciiLit 0x22 then pure c
    else do
      let shown := charUtf8Bytes c
      throwShow (.jl (.argumentError ("invalid escape sequence \\" ++
        (String.fromUTF8? shown.toByteArray).getD "")))

/-- The loop `for c in a ... end` of `unescape_string(io::IO, s::AbstractString, keep = ())`
(io.jl:535-591) over `a = Iterators.Stateful(s)`. Each pass pops at least one character, so
`passes` (the iteration bound plus two) never ends the loop early. -/
def unescapeLoop [MonadFinally m] (step : Index → m (Option (JChar × Index)))
    (cio : CharIO m Io V) (io : JIO Io V) (keep : List JChar) : Nat → Stateful → m Unit
  | 0, _ => pure ()
  | passes + 1, a => do
    match ← popfirst step a with
    | none => pure ()
    | some (c, a) =>
      if a.peek.isSome && c == asciiLit 0x5c then do
        match ← popfirst step a with
        | none => pure ()
        | some (c, a) =>
          if keep.contains c then do
            printValues cio.prims io [printChar cio io (asciiLit 0x5c), printChar cio io c]
            unescapeLoop step cio io keep passes a
          else if c == asciiLit 0x78 || c == asciiLit 0x75 || c == asciiLit 0x55 then do
            let width := if c == asciiLit 0x78 then 2 else if c == asciiLit 0x75 then 4 else 8
            let (k, n, a) ← takeDigits step hexValue 16 width 0 a
            if k == 0 || n > 0x10ffff then
              throwShow (.jl (.argumentError (if width == 2 then "invalid hex (\\x) escape sequence"
                else if width == 4 then "invalid unicode (\\u) escape sequence"
                else "invalid unicode (\\U) escape sequence")))
            if width == 2 then do let _ ← writeByteIO cio io n.toUInt8
            else do
              let ch ← ofChar (E := E) (JuliaLean.base.char.char_UInt32 n.toUInt32)
              printChar cio io ch
            unescapeLoop step cio io keep passes a
          else match octalValue c with
          | some d => do
            let (_, n, a) ← takeDigits step octalValue 8 2 d a
            if n > 255 then throwShow (.jl (.argumentError "octal escape sequence out of range"))
            let _ ← writeByteIO cio io n.toUInt8
            unescapeLoop step cio io keep passes a
          | none => do
            printChar cio io (← standardEscape c)
            unescapeLoop step cio io keep passes a
      else do
        printChar cio io c
        unescapeLoop step cio io keep passes a

/--
Julia source: base/strings/io.jl:535-591 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unescape_string(io::IO, s::AbstractString, keep = ())
    a = Iterators.Stateful(s)
    for c in a
        if !isempty(a) && c == '\\'
            c = popfirst!(a)
            if c in keep
                print(io, '\\', c)
            elseif c == 'x' || c == 'u' || c == 'U'
                n = k = 0
                m = c == 'x' ? 2 :
                    c == 'u' ? 4 : 8
                while (k += 1) <= m && !isempty(a)
                    nc = peek(a)::AbstractChar
                    n = '0' <= nc <= '9' ? n<<4 + (nc-'0') :
                        'a' <= nc <= 'f' ? n<<4 + (nc-'a'+10) :
                        'A' <= nc <= 'F' ? n<<4 + (nc-'A'+10) : break
                    popfirst!(a)
                end
                if k == 1 || n > 0x10ffff
                    u = m == 4 ? 'u' : 'U'
                    throw(ArgumentError("invalid $(m == 2 ? "hex (\\x)" :
                                        "unicode (\\$u)") escape sequence"))
                end
                if m == 2 # \x escape sequence
                    write(io, UInt8(n))
                else
                    print(io, Char(n))
                end
            elseif '0' <= c <= '7'
                k = 1
                n = c-'0'
                while (k += 1) <= 3 && !isempty(a)
                    c = peek(a)::AbstractChar
                    n = ('0' <= c <= '7') ? n<<3 + c-'0' : break
                    popfirst!(a)
                end
                if n > 255
                    throw(ArgumentError("octal escape sequence out of range"))
                end
                write(io, UInt8(n))
            else
                print(io, c == 'a' ? '\a' :
                          c == 'b' ? '\b' :
                          c == 't' ? '\t' :
                          c == 'n' ? '\n' :
                          c == 'v' ? '\v' :
                          c == 'f' ? '\f' :
                          c == 'r' ? '\r' :
                          c == 'e' ? '\e' :
                          (c == '\\' || c == '"') ? c :
                          throw(ArgumentError("invalid escape sequence \\$c")))
            end
        else
            print(io, c)
        end
    end
end
```
`unescape_string(io::IO, s::AbstractString, keep = ())` (io.jl:535-591).
-/
def unescapeStringIO [MonadFinally m] {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (cio : CharIO m Io V) (io : JIO Io V) (s : S) (keep : List JChar) : m Unit := do
  let a ← statefulOf (E := E) ops s
  unescapeLoop (E := E) (stringStep (E := E) ops s) cio io keep (a.fuel + 2) a

/-! ## 5. Raw strings (io.jl:663-697) -/

/--
Julia source: base/strings/io.jl:663-693 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function escape_raw_string(io::IO, str::AbstractString, delim::Char='"')
    total = 0
    escapes = 0
    for c in str
        if c == '\\'
            escapes += 1
        else
            if c == delim
                # if one or more backslashes are followed by
                # a double quote then escape all backslashes
                # and the double quote
                escapes += 1
                total += escapes
                while escapes > 0
                    write(io, '\\')
                    escapes -= 1
                end
            end
            escapes = 0
        end
        write(io, c)
    end
    # also escape any trailing backslashes,
    # so they do not affect the closing quote
    total += escapes
    while escapes > 0
        write(io, '\\')
        escapes -= 1
    end
    total
end
```
`escape_raw_string(io::IO, str::AbstractString, delim::Char='"')` (io.jl:663-692): `for c
in str`, with `escapes` the pending backslashes and `total` the `Int` count of inserted ones; each
`write(io, c)` is its own call.
-/
def escapeRawStringIO {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (cio : CharIO m Io V) (io : JIO Io V) (s : S) (delim : JChar) : m JInt64 := do
  let (escapes, total) ← foldChars ops s (0, JuliaLean.base.int.lit .i64 0)
    (fun c (escapes, total) => do
      let state ← if c == asciiLit 0x5c then pure (escapes + 1, total)
        else if c == delim then do
          for _ in List.range (escapes + 1) do let _ ← writeChar cio io (asciiLit 0x5c)
          pure (0, JuliaLean.base.int.add total (JuliaLean.base.int.lit .i64 (escapes + 1)))
        else pure (0, total)
      let _ ← writeChar cio io c
      pure (.yield state))
  for _ in List.range escapes do let _ ← writeChar cio io (asciiLit 0x5c)
  pure (JuliaLean.base.int.add total (JuliaLean.base.int.lit .i64 escapes))

/-! ## 6. `join(io, iterator, ...)` (io.jl:330-354)

The iterator's own `iterate` methods are `it : IterOps I X St` (the installed `show.jl` iteration
record); `printX`/`printD` are the `print(io, x)` methods of the item and delimiter types. The
loops end when the iterator does, so they are `partial_fixpoint` definitions. -/

section Join

/-- `for item in iterator ... end` of the 3-delimiter `join` (io.jl:330-345): `prev` is the
previous item, `first` whether no delimiter was printed yet. -/
def join4Loop {I X D St : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (it : IterOps I X St)
    (printX : JIO Io V → X → m Unit) (printD : JIO Io V → D → m Unit) (io : JIO Io V) (itr : I)
    (delim last : D) (first : Bool) (prev : X) (st : St) : m Unit := do
  match it.iterateFrom itr st with
  | some (item, st) =>
    let first ← if first then pure false else do printD io delim; pure false
    printX io prev
    join4Loop p it printX printD io itr delim last first item st
  | none =>
    if !first then printD io last
    printX io prev
partial_fixpoint

/--
Julia source: base/strings/io.jl:330-345 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function join(io::IO, iterator, delim, last)
    first = true
    local prev
    for item in iterator
        if @isdefined prev
            first ? (first = false) : print(io, delim)
            print(io, prev)
        end
        prev = item
    end
    if @isdefined prev
        first || print(io, last)
        print(io, prev)
    end
    nothing
end
```
`join(io::IO, iterator, delim, last)` (io.jl:330-345).
-/
def join4 {I X D St : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (p : IOPrims m Io V) (it : IterOps I X St)
    (printX : JIO Io V → X → m Unit) (printD : JIO Io V → D → m Unit) (io : JIO Io V) (itr : I)
    (delim last : D) : m Unit :=
  match it.iterate itr with
  | none => pure ()
  | some (item, st) => join4Loop p it printX printD io itr delim last true item st

/-- `for item in iterator ... end` of `join(io, iterator, delim="")` (io.jl:346-352). -/
def join3Loop {I X D St : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (it : IterOps I X St)
    (printX : JIO Io V → X → m Unit) (printD : JIO Io V → D → m Unit) (io : JIO Io V) (itr : I)
    (delim : D) (st : St) : m Unit := do
  match it.iterateFrom itr st with
  | some (item, st) =>
    printD io delim
    printX io item
    join3Loop it printX printD io itr delim st
  | none => pure ()
partial_fixpoint

/--
Julia source: base/strings/io.jl:346-354 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function join(io::IO, iterator, delim="")
    # Specialization of the above code when delim==last,
    # which lets us emit (compile) less code
    first = true
    for item in iterator
        first ? (first = false) : print(io, delim)
        print(io, item)
    end
end
```
`join(io::IO, iterator, delim="")` (io.jl:346-352); `join(io, iterator)` passes the empty
`String` delimiter, printed with `printStringJoin`.
-/
def join3 {I X D St : Type} [∀ α, Lean.Order.CCPO (m α)] [Lean.Order.MonoBind m]
    (it : IterOps I X St)
    (printX : JIO Io V → X → m Unit) (printD : JIO Io V → D → m Unit) (io : JIO Io V) (itr : I)
    (delim : D) : m Unit :=
  match it.iterate itr with
  | none => pure ()
  | some (item, st) => do
    printX io item
    join3Loop it printX printD io itr delim st

end Join

/-! ## 7. `show(io, MIME"text/plain", str; limit)` (io.jl:197-240)

The truncation boundaries are the installed `util.stringTruncateBoundaries` over the string's own
methods. `string(str)`, `string(replacement)` and `*` on the string type are fields of the
installed `TruncateOps` record that `string_truncate_boundaries` never calls; they are the
caller's string-type methods (`stringify`, `stringifyRepl`, `concat`). `printstyled` is the
installed `show.jl` interface to `base/util.jl` (`PrintStyled`). -/

/-- The characters of the view `SubString(str, i, j)`: the string's own `iterate` from `i`,
while the index is at most `j` (substring.jl:151-158), with the string's iteration bound. -/
def viewCharsLoop {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E) (s : S) (j : Index) :
    Nat → Index → Except E (List JChar)
  | 0, _ => .ok []
  | fuel + 1, i =>
    if i.val > j.val then .ok []
    else do
      match ← ops.iterateAt s i with
      | none => .ok []
      | some (c, k) => return c :: (← viewCharsLoop ops s j fuel k)

def viewChars {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E) (s : S) (i j : Index) :
    Except E (List JChar) :=
  viewCharsLoop ops s j (ops.iterationBound s) i

/-- `show(io, @view str[i:j])`: `print_quoted` of the `SubString` view, whose `iterate` walks the
parent from `i` up to `j` (`viewStep`). -/
def printQuotedView [MonadFinally m] {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (cio : CharIO m Io V) (P : JuliaLean.base.strings.unicode.Utf8proc)
    (digits : JuliaLean.base.intfuncs.DigitCallees) (io : JIO Io V) (s : S) (i j : Index) :
    m Unit := do
  printChar cio io (asciiLit 0x22)
  let a : Stateful := ⟨ops.iterationBound s, ← viewStep (E := E) ops s j i⟩
  escapeLoop (E := E) (viewStep (E := E) ops s j) cio P digits io [asciiLit 0x22, asciiLit 0x24] [] false
    false (a.fuel + 2) a
  printChar cio io (asciiLit 0x22)

/-- The characters of a `String` in iteration order: the installed `string.stringIterate`, at most
one step per byte. -/
def stringCharsLoop (s : JString) : Nat → Index → List JChar
  | 0, _ => []
  | fuel + 1, i => match JuliaLean.base.strings.string.stringIterate s i with
    | none => []
    | some (c, k) => c :: stringCharsLoop s fuel k

def stringChars (s : JString) : List JChar :=
  stringCharsLoop s s.bytes.length (JuliaLean.base.int.lit .i64 1)

/-- The installed truncation record over the string's own methods; `textwidth(c::Char)` is the
installed `unicode.textwidthChar`, `textwidth(replacement::String)` its sum over the
replacement's characters (unicode.jl:297, `Int` addition). -/
def truncOps {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (P : JuliaLean.base.strings.unicode.Utf8proc) (liftJ : JlError → E)
    (stringify : S → Except E S) (stringifyRepl : JString → Except E S)
    (concat : List (JuliaLean.base.strings.util.TruncPiece S (List JChar)) → Except E S) :
    JuliaLean.base.strings.util.TruncateOps S (List JChar) JString JChar E where
  iterateFirst := ops.iterateFirst
  iterateAt := ops.iterateAt
  textwidthChar c := .ok (JInt.wrap .i64 (JuliaLean.base.strings.unicode.textwidthChar P c))
  textwidthReplacement r := some (.ok (JInt.wrap .i64
    ((stringChars r).foldl
      (fun w c => w + JuliaLean.base.strings.unicode.textwidthChar P c) 0)))
  getindex := JuliaLean.base.strings.basic.getindexString ops
  firstindex s := .ok (JuliaLean.base.strings.basic.firstindexString s)
  lastindex := ops.lastindex
  prevind := JuliaLean.base.strings.basic.previndOne ops
  nextind := JuliaLean.base.strings.basic.nextindOne ops
  substring := viewChars ops
  stringify := stringify
  stringifyReplacement := stringifyRepl
  concat := concat
  argumentError := ops.argumentError
  toInt z := match JInt.convert (IntTy.i64.name) .i64 z with
    | .ok i => .ok i
    | .error e => .error (liftJ e)

/--
Julia source: base/strings/io.jl:197-236 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show(
    io    :: IO,
    mime  :: MIME"text/plain",
    str   :: AbstractString;
    limit :: Union{Int, Nothing} = nothing,
)
    # compute limit in default case
    if limit === nothing
        get(io, :limit, false)::Bool || return show(io, str)
        limit = max(20, displaysize(io)[2])
        # one line in collection, seven otherwise
        get(io, :typeinfo, nothing) === nothing && (limit *= 7)
    end
    limit = max(0, limit-2) # quote chars

    # early out for short strings
    check_textwidth(str, limit) && return show(io, str)

    # these don't depend on string data
    units = codeunit(str) == UInt8 ? "bytes" : "code units"
    skip_text(skip) = " ⋯ $skip $units ⋯ "

    # longest possible replacement string for omitted chars
    max_replacement = skip_text(ncodeunits(str) * 100) # *100 for 2 inner quote chars

    head, tail = string_truncate_boundaries(str, limit, max_replacement, Val(:center))

    # threshold: min chars skipped to make elision worthwhile
    afterhead = nextind(str, head)
    n = tail - afterhead # skipped code units
    replacement = skip_text(n)
    t = ncodeunits(replacement) # length of replacement (textwidth == ncodeunits here)
    @views if 4t ≤ n || t ≤ n && t ≤ textwidth(str[afterhead:prevind(str,tail)])
        show(io, str[begin:head])
        printstyled(io, replacement; color=:light_yellow, bold=true)
        show(io, str[tail:end])
    else
        show(io, str)
    end
end
```
`show(io::IO, ::MIME"text/plain", str::AbstractString; limit=nothing)` (io.jl:197-240) for
`limit === nothing` (`none`) or an `Int`. `string_truncate_boundaries`' `while` loops are the
installed fuel-free loops; their non-termination is `none`, thrown here as `ErrorException`
"fuel" like the other installed callers.
-/
def showTextPlain [MonadFinally m] {S R CU CT : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E)
    (cio : CharIO m Io V) (a : AnyOps V Ty) (printstyled : PrintStyled m Io V)
    (P : JuliaLean.base.strings.unicode.Utf8proc) (digits : JuliaLean.base.intfuncs.DigitCallees)
    (liftJ : JlError → E) (stringify : S → Except E S) (stringifyRepl : JString → Except E S)
    (concat : List (JuliaLean.base.strings.util.TruncPiece S (List JChar)) → Except E S)
    (io : JIO Io V) (str : S) (limit : Option JInt64) : m Unit := do
  let p := cio.prims
  let showStr := printQuoted ops cio P digits io str
  let limit ← match limit with
    | some l => pure (some l)
    | none => do
      if !(← assertBool a (getIO p io "limit" false)) then pure none
      else do
        let cols := (← displaysize p a io).2
        let l := if cols.val < 20 then JuliaLean.base.int.lit .i64 20 else cols
        match getIO p io "typeinfo" () with
        | .inr () => pure (some (JuliaLean.base.int.mul l (JuliaLean.base.int.lit .i64 7)))
        | .inl _ => pure (some l)
  match limit with
  | none => showStr
  | some limit =>
    let limit := JuliaLean.base.int.sub limit (JuliaLean.base.int.lit .i64 2)
    let limit := if limit.val < 0 then JuliaLean.base.int.lit .i64 0 else limit
    let tops := truncOps ops P liftJ stringify stringifyRepl concat
    let fits ← match JuliaLean.base.strings.util.checkTextwidth tops str limit.val with
      | none => throwShow (.errorException "fuel")
      | some r => ofString (E := E) r
    if fits then showStr
    else
      let ncu := ops.ncodeunits str
      let units := if ops.codeunitSize (ops.codeunitType str) == JuliaLean.base.int.lit .i64 1 then
        "bytes" else "code units"
      let skipText := fun (skip : Int) => " ⋯ " ++ toString skip ++ " " ++ units ++ " ⋯ "
      let maxBytes := (skipText (JuliaLean.base.int.mul ncu (JuliaLean.base.int.lit .i64 100)).val).toUTF8.toList
      let maxReplacement : JString ← if h : maxBytes.length < 2 ^ 62 then pure ⟨maxBytes, h⟩
        else throwShow (.jl (.overflowError "String length"))
      let bounds ← match JuliaLean.base.strings.util.stringTruncateBoundaries tops
          JuliaLean.base.strings.util.truncModeOps str limit.val maxReplacement
          ⟨JuliaLean.base.strings.util.TruncMode.center⟩ with
        | none => throwShow (.errorException "fuel")
        | some r => ofString (E := E) r
      match bounds with
      | none => throwShow .typeError
      | some (head, tail) =>
        let afterhead ← ofString (E := E) (JuliaLean.base.strings.basic.nextindOne ops str head)
        let n := JuliaLean.base.int.sub tail afterhead
        let replacement := skipText n.val
        let t := JuliaLean.base.int.lit .i64 replacement.utf8ByteSize
        let middle := do
          let last ← ofString (E := E) (JuliaLean.base.strings.basic.previndOne ops str tail)
          let cs ← ofString (E := E) (viewChars ops str afterhead last)
          pure (cs.foldl (fun w c => JuliaLean.base.int.add w
            (JInt.wrap .i64 (JuliaLean.base.strings.unicode.textwidthChar P c)))
            (JuliaLean.base.int.lit .i64 0))
        let elide ← if (JuliaLean.base.int.mul (JuliaLean.base.int.lit .i64 4) t).val ≤ n.val then
            pure true
          else if t.val ≤ n.val then do pure (t.val ≤ (← middle).val)
          else pure false
        if elide then do
          let lastS ← ofString (E := E) (ops.lastindex str)
          printQuotedView ops cio P digits io str (JuliaLean.base.int.lit .i64 1) head
          printstyled io [fun io => printStr p io replacement] "light_yellow" true
          printQuotedView ops cio P digits io str tail lastS
        else showStr

end Stream

/-! ## 8. `sprint`, `repr`, `string` (io.jl:104-188, 284-286)

`sprint` and `repr` are the installed `sprintIOBuffer`/`reprIOBuffer` (accepted
`sprint-iobuffer3`). The `IOBuffer` of `print_to_string`/`string_with_env` is the installed
`newBufferState` with the computed size hint, printed through the installed `bufferPrims`. -/

section Buffer
open JuliaLean.base.strings.io (Error BufferShowM bufferPrims sprintIOBuffer reprIOBuffer
  SprintContext sprintContext liftBuffer newBufferState throwCallback Unindented)

variable {E V Ty : Type}

instance : MonadExceptOf (StrIOError E) (BufferShowM (StrIOError E)) where
  throw e := throwCallback e
  tryCatch action handler := fun state =>
    match action state with
    | .error (.callback e) state => handler e state
    | r => r

/-- The installed `IOBuffer` stream: `bufferPrims` and `write(to::IOBuffer, a::UInt8)`
(iobuffer.jl:948-963, installed `iobuffer.writeByte`). -/
def bufferCharIO (displaySize : JInt64 × JInt64) : CharIO (BufferShowM E) Unit V :=
  ⟨bufferPrims displaySize, fun _ b => liftBuffer (JuliaLean.base.iobuffer.writeByte b)⟩

/--
Julia source: base/strings/io.jl:286-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
limitrepr(x) = repr(x, context = :limit=>true)
```
`limitrepr(x) = repr(x, context = :limit=>true)` (io.jl:286).
-/
def limitrepr {X R : Type} (displaySize : JInt64 × JInt64) (a : AnyOps V Ty)
    (showOne : JIO Unit V → X → BufferShowM E R) (x : X) :
    Except (Error E) JuliaLean.base.strings.io.JuliaString :=
  reprIOBuffer displaySize a (.pair "limit" (a.ofBool true)) showOne x

/-- An argument of `print_to_string`/`string_with_env`: the types `_str_sizehint` tests
(io.jl:116-132), or any other value with its `print` method. -/
inductive StrArg (E V : Type) where
  | float64 (x : JuliaLean.Float.F64)
  | float32 (x : JuliaLean.Promotion.Fl JuliaLean.Promotion.single)
  | string (s : JString)
  | substring (s : JuliaLean.base.strings.substring.SubString JString)
  | char (c : JChar)
  | uint64 (x : JInt .u64)
  | uint32 (x : JInt .u32)
  | int64 (x : JInt .i64)
  | int32 (x : JInt .i32)
  | other (print : JIO Unit V → BufferShowM E Unit)

/-- `ndigits(x) = max(1, ndigits0z(x, 10))` (intfuncs.jl:874), the installed models. -/
def ndigits10 (c : JuliaLean.base.intfuncs.DigitCallees) {t : IntTy} (x : JInt t) : Jl JInt64 :=
  JuliaLean.base.intfuncs.ndigits
    (JuliaLean.base.intfuncs.ndigitsZero Subtype.val
      (JuliaLean.base.intfuncs.ndigitsNegativeBits c) JuliaLean.base.intfuncs.ndigitsPositiveBits)
    (fun pad n => .ok (if n.val < pad.val then pad else n))
    x (JuliaLean.base.int.lit .i64 10) (JuliaLean.base.int.lit .i64 1)

/--
Julia source: base/strings/io.jl:116-132 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _str_sizehint(x)
    if x isa Float64
        return 20
    elseif x isa Float32
        return 12
    elseif x isa String || x isa SubString{String}
        return sizeof(x)
    elseif x isa Char
        return ncodeunits(x)
    elseif x isa UInt64 || x isa UInt32
        return ndigits(x)
    elseif x isa Int64 || x isa Int32
        return ndigits(x) + (x < zero(x))
    else
        return 8
    end
end
```
`_str_sizehint(x)` (io.jl:116-132).
-/
def strSizehint (c : JuliaLean.base.intfuncs.DigitCallees) : StrArg E V → Jl JInt64
  | .float64 _ => .ok (JuliaLean.base.int.lit .i64 20)
  | .float32 _ => .ok (JuliaLean.base.int.lit .i64 12)
  | .string s => .ok (JuliaLean.base.strings.string.stringCoreSizeof s)
  | .substring s => .ok s.ncodeunits
  | .char ch => JuliaLean.base.char.ncodeunits_Char (JuliaLean.base.int.lit .i64 4)
      (fun x y => JInt.div x y) JuliaLean.base.char.charBitOps (· == 0) ch
  | .uint64 x => ndigits10 c x
  | .uint32 x => ndigits10 c x
  | .int64 x => do
    pure (JuliaLean.base.int.add (← ndigits10 c x)
      (JuliaLean.base.int.lit .i64 (if x.val < 0 then 1 else 0)))
  | .int32 x => do
    pure (JuliaLean.base.int.add (← ndigits10 c x)
      (JuliaLean.base.int.lit .i64 (if x.val < 0 then 1 else 0)))
  | .other _ => .ok (JuliaLean.base.int.lit .i64 8)

/-- `string(n)` of a BitInteger, the installed `show.stringBits` with base 10, pad 1. -/
def decimalString (c : JuliaLean.base.intfuncs.DigitCallees) {t : IntTy} (n : JInt t) :
    BufferShowM E Bytes :=
  show.stringBits c n (JuliaLean.base.int.lit .i64 10) (JuliaLean.base.int.lit .i64 1)

/-- `print(io, x)` of each argument kind: `print(io, x) = show(io, x)` under `lock` (io.jl:32)
for `Float64` (Ryu.jl `show`, with `get(io, :compact, false)::Bool`) and signed integers;
`print(io, x::Float32) = show(io, x, true, true)` (Ryu.jl); `print(io, n::Unsigned) =
print(io, string(n))` (show.jl); `String`/`SubString{String}`/`Char` as above. -/
def printArg (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : AnyOps V Ty) (io : JIO Unit V) : StrArg E V → BufferShowM E Unit
  | .float64 x => do
    let p := bufferPrims (E := E) (V := V) displaySize
    locked p io (do
      let compact ← assertBool a (getIO p io "compact" false)
      let bytes ← ofJl (JuliaLean.base.ryu.Ryu.writeshortest64 x false false true (-1) 101 false 46
        compact)
      write p io (bytes.map Nat.toUInt8))
  | .float32 x => do
    let p := bufferPrims (E := E) (V := V) displaySize
    let compact ← assertBool a (getIO p io "compact" false)
    let bytes ← ofJl (JuliaLean.base.ryu.Ryu.writeshortest32 x false false true (-1) 101 false 46
      false compact)
    write p io (bytes.map Nat.toUInt8)
  | .string s => printStringBuffer io s
  | .substring s => printSubStringBuffer io s
  | .char ch => printChar (bufferCharIO displaySize) io ch
  | .uint64 x => print_Unsigned (bufferPrims displaySize) (decimalString c) io x
  | .uint32 x => print_Unsigned (bufferPrims displaySize) (decimalString c) io x
  | .int64 x => printAll (bufferPrims displaySize) io
      [show_Signed (bufferPrims displaySize) (decimalString c) io x]
  | .int32 x => printAll (bufferPrims displaySize) io
      [show_Signed (bufferPrims displaySize) (decimalString c) io x]
  | .other print => print io

/-- The shared body of `print_to_string(xs...)` (io.jl:134-148) and `string_with_env(env, xs...)`
(io.jl:150-164): `siz::Int` sums the hints (wrapping `Int` addition), then
`s = IOBuffer(sizehint=siz)`, each `print`, and `takestring!(s)`. -/
def printArgsToString (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : AnyOps V Ty) (env : SprintContext E V) (xs : List (StrArg E V)) :
    Except (Error E) JuliaLean.base.strings.io.JuliaString := do
  if xs.isEmpty then return ⟨[]⟩
  let mut siz := JuliaLean.base.int.lit .i64 0
  for x in xs do
    siz := JuliaLean.base.int.add siz
      (← (strSizehint c x).mapError (fun e => Error.display (ShowError.jl e)))
  let initial ← (newBufferState (JuliaLean.base.iobuffer.bitsConversions .i64) (some siz)).mapError
    Error.buffer
  let action : BufferShowM E Bytes := do
    let io ← sprintContext (bufferPrims displaySize) a env
    for x in xs do printArg c displaySize a io x
    liftBuffer JuliaLean.base.iobuffer.takestring
  match action initial with
  | .ok bytes _ => pure ⟨bytes⟩
  | .error error _ => .error error

/--
Julia source: base/strings/io.jl:134-148 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_to_string(xs...)
    if isempty(xs)
        return ""
    end
    siz::Int = 0
    for x in xs
        siz += _str_sizehint(x)
    end
    # specialized for performance reasons
    s = IOBuffer(sizehint=siz)
    for i in 1:nfields(xs)
        print(s, xs[i])
    end
    takestring!(s)
end
```
Julia source: base/strings/io.jl:186-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
string(xs...) = print_to_string(xs...)
```
`print_to_string(xs...)` (io.jl:134-148) and `string(xs...) = print_to_string(xs...)`
(io.jl:186).
-/
def printToString (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : AnyOps V Ty) (xs : List (StrArg E V)) :
    Except (Error E) JuliaLean.base.strings.io.JuliaString :=
  printArgsToString c displaySize a .none xs

/--
Julia source: base/strings/io.jl:150-165 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function string_with_env(env, xs...)
    if isempty(xs)
        return ""
    end
    siz::Int = 0
    for x in xs
        siz += _str_sizehint(x)
    end
    # specialized for performance reasons
    s = IOBuffer(sizehint=siz)
    env_io = IOContext(s, env)
    for i in 1:nfields(xs)
        print(env_io, xs[i])
    end
    takestring!(s)
end
```
`string_with_env(env, xs...)` (io.jl:150-164): `env_io = IOContext(s, env)` for an `env`
pair or `IOContext` (`SprintContext.pair`/`.io`, the installed `IOContext` methods).
-/
def stringWithEnv (c : JuliaLean.base.intfuncs.DigitCallees) (displaySize : JInt64 × JInt64)
    (a : AnyOps V Ty) (env : SprintContext E V) (xs : List (StrArg E V)) :
    Except (Error E) JuliaLean.base.strings.io.JuliaString :=
  printArgsToString c displaySize a env xs

/--
Julia source: base/strings/io.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
string(a::Symbol) = String(a)
```
`string(a::Symbol) = String(a)` (io.jl:188): the symbol's name bytes.
-/
def stringSymbol (name : JuliaLean.base.strings.io.JuliaSymbol) :
    JuliaLean.base.strings.io.JuliaString := ⟨name.name⟩

/--
Julia source: base/strings/io.jl:488-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
escape_string(s::AbstractString, esc=('\"',); keep = (), ascii::Bool=false, fullhex::Bool=false) =
    sprint((io)->escape_string(io, s, esc; keep, ascii, fullhex), sizehint=lastindex(s))
```
`escape_string(s, esc=('"',); keep=(), ascii=false, fullhex=false) =
sprint((io)->escape_string(io, s, esc; keep, ascii, fullhex), sizehint=lastindex(s))`
(io.jl:488-489).
-/
def escapeString {S R CU CT E0 : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E0)
    (displaySize : JInt64 × JInt64) (a : AnyOps V Ty)
    (P : JuliaLean.base.strings.unicode.Utf8proc) (digits : JuliaLean.base.intfuncs.DigitCallees)
    (s : S) (esc keep : List JChar) (ascii fullhex : Bool) :
    Except (Error (StrIOError E0)) JuliaLean.base.strings.io.JuliaString := do
  let hint ← (ops.lastindex s).mapError (fun e => Error.callback (StrIOError.string e))
  sprintIOBuffer (JuliaLean.base.iobuffer.bitsConversions .i64) displaySize a .none hint
    (fun io (_ : Unit) => escapeStringIO (E := E0) ops (bufferCharIO displaySize) P digits io s esc
      keep ascii fullhex) ()

/--
Julia source: base/strings/io.jl:592-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unescape_string(s::AbstractString, keep = ()) =
    sprint(unescape_string, s, keep; sizehint=lastindex(s))
```
`unescape_string(s, keep=()) = sprint(unescape_string, s, keep; sizehint=lastindex(s))`
(io.jl:592-593).
-/
def unescapeString {S R CU CT E0 : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E0)
    (displaySize : JInt64 × JInt64) (a : AnyOps V Ty) (s : S) (keep : List JChar) :
    Except (Error (StrIOError E0)) JuliaLean.base.strings.io.JuliaString := do
  let hint ← (ops.lastindex s).mapError (fun e => Error.callback (StrIOError.string e))
  sprintIOBuffer (JuliaLean.base.iobuffer.bitsConversions .i64) displaySize a .none hint
    (fun io (_ : Unit) => unescapeStringIO (E := E0) ops (bufferCharIO displaySize) io s keep) ()

/--
Julia source: base/strings/io.jl:613-616 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro b_str(s::String)
    v = codeunits(unescape_string(s))
    QuoteNode(v)
end
```
`macro b_str(s)`: `codeunits(unescape_string(s))` (io.jl:613-616).
-/
def bStr (rt : JuliaLean.base.strings.search.StringRuntime) (displaySize : JInt64 × JInt64)
    (a : AnyOps V Ty) (s : JString) :
    Except (Error (StrIOError JuliaLean.base.strings.search.NativeError))
      JuliaLean.base.strings.io.QuoteNode := do
  let str ← unescapeString (JuliaLean.base.strings.search.stringBasic rt) displaySize a s []
  pure ⟨⟨str.bytes⟩⟩

/-! `devnull` (io.jl:694-697): writes nothing. -/

instance : MonadExceptOf ShowError (Except (Error E)) where
  throw e := .error (.display e)
  tryCatch action handler := match action with
    | .error (.display e) => handler e
    | r => r

instance : MonadExceptOf (StrIOError E) (Except (Error (StrIOError E))) where
  throw e := .error (.callback e)
  tryCatch action handler := match action with
    | .error (.callback e) => handler e
    | r => r

def devnullPrims (displaySize : JInt64 × JInt64) : IOPrims (Except (Error E)) Unit V where
  write := fun _ _ => pure ()
  lock := fun _ => pure ()
  unlock := fun _ => pure ()
  get := fun _ _ => none
  displaysize := fun _ => pure displaySize

/-- `devnull` with `write(::DevNull, ::UInt8) = 1` (coreio.jl:22, installed `coreio.writeDevNull`). -/
def devnullCharIO (displaySize : JInt64 × JInt64) : CharIO (Except (Error E)) Unit V :=
  ⟨devnullPrims displaySize,
    fun _ b => pure (JuliaLean.base.coreio.writeDevNull .new (JInt.wrap .u8 b.toNat))⟩

/--
Julia source: base/strings/io.jl:694-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function escape_raw_string(str::AbstractString, delim::Char='"')
    total = escape_raw_string(devnull, str, delim) # check whether the string even needs to be copied and how much to allocate for it
    return total == 0 ? str : sprint(escape_raw_string, str, delim; sizehint = sizeof(str) + total)
end
```
`escape_raw_string(str::AbstractString, delim::Char='"')` (io.jl:694-697): the count of
inserted backslashes from a pass on `devnull`, then `str` itself or
`sprint(escape_raw_string, str, delim; sizehint = sizeof(str) + total)`.
-/
def escapeRawString {S R CU CT E0 : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E0)
    (displaySize : JInt64 × JInt64) (a : AnyOps V Ty) (str : S) (delim : JChar) :
    Except (Error (StrIOError E0)) (JuliaLean.base.strings.io.RawStringResult S) := do
  let total ← escapeRawStringIO (E := E0) ops (devnullCharIO (V := V) displaySize) (.plain ()) str delim
  if total.val == 0 then return .original str
  let hint := JuliaLean.base.int.add (JuliaLean.base.strings.basic.sizeofString ops str) total
  let out ← sprintIOBuffer (JuliaLean.base.iobuffer.bitsConversions .i64) displaySize a .none hint
    (fun io (_ : Unit) => escapeRawStringIO (E := E0) ops (bufferCharIO displaySize) io str delim) ()
  pure (.copied out.bytes)

/-- The `sprint` of `join(iterator, args...)`: its `join` loop may not end (an infinite
iterator), so it runs in the installed `IOBuffer` state with divergence `none`. The installed
`bufferPrims` and the user `print` methods are lifted into it. -/
abbrev JoinM (E : Type) := StateT JuliaLean.base.iobuffer.BufferState (ExceptT (Error E) Option)

def liftShow {α : Type} (action : BufferShowM E α) : JoinM E α := fun s =>
  ExceptT.mk (some (match action s with
    | .ok v s => .ok (v, s)
    | .error e _ => .error e))

instance : MonadExceptOf ShowError (JoinM E) where
  throw e := liftShow (throwThe ShowError e)
  tryCatch action handler := fun s => ExceptT.mk (match (action s).run with
    | some (.error (.display e)) => (handler e s).run
    | r => r)

def liftPrims {Io : Type} (p : IOPrims (BufferShowM E) Io V) : IOPrims (JoinM E) Io V where
  write := fun io bytes => liftShow (p.write io bytes)
  lock := fun io => liftShow (p.lock io)
  unlock := fun io => liftShow (p.unlock io)
  get := p.get
  displaysize := fun io => liftShow (p.displaysize io)

/-- `print(io, s::String)` on the `IOBuffer` of `joinString` (io.jl:246), through the `unsafe_write` of
`IOBuffer`. -/
def printStringJoin (io : JIO Unit V) (s : JString) : JoinM E Unit :=
  printConcreteString ((bufferWriter (E := E) (V := V)).hoist liftShow) pointerStringPure
    sizeofJString io s

/--
Julia source: base/strings/io.jl:356-374 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _join_preserve_annotations(iterator, args...)
    et = @default_eltype(iterator)
    if isconcretetype(et) && !_isannotated(et) && !any(_isannotated, args)
        sprint(join, iterator, args...)
    else
        io = AnnotatedIOBuffer()
        join(io, iterator, args...)
        # If we know (from compile time information, or dynamically in the case
        # of iterators with a non-concrete eltype), that the result is annotated
        # in nature, we extract an `AnnotatedString`, otherwise we just extract
        # a plain `String` from `io`.
        if isconcretetype(et) || !isempty(io.annotations)
            seekstart(io)
            read(io, AnnotatedString{String})
        else
            String(take!(io.io))
        end
    end
end
```
Julia source: base/strings/io.jl:378-387 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function _join_preserve_annotations(iterator::Tuple, args...)
    if !any(_isannotated, iterator) && !any(_isannotated, args)
        sprint(join, iterator, args...)
    else
        io = AnnotatedIOBuffer()
        join(io, iterator, args...)
        seekstart(io)
        read(io, AnnotatedString{String})
    end
end
```
Julia source: base/strings/io.jl:389-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
join(iterator) = _join_preserve_annotations(iterator)
```
Julia source: base/strings/io.jl:390-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
join(iterator, delim) = _join_preserve_annotations(iterator, delim)
```
Julia source: base/strings/io.jl:391-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
join(iterator, delim, last) = _join_preserve_annotations(iterator, delim, last)
```
`join(iterator, args...)` for an iterator whose `@default_eltype` is a concrete
non-annotated type and non-annotated `args` (io.jl:356-360): `sprint(join, iterator, args...)`
(io.jl:104-114 with `context=nothing`, `sizehint=0`), `none` when the iteration does not end.
The `AnnotatedIOBuffer` branch is the named gap `join-annotated`.
-/
def joinString {I X D St : Type} (displaySize : JInt64 × JInt64)
    (it : IterOps I X St) (printX : JIO Unit V → X → JoinM E Unit)
    (printD : JIO Unit V → D → JoinM E Unit) (itr : I) (args : Option D × Option D) :
    Option (Except (Error E) JuliaLean.base.strings.io.JuliaString) :=
  match newBufferState (JuliaLean.base.iobuffer.bitsConversions .i64)
      (some (JuliaLean.base.iobuffer.i 0)) with
  | .error e => some (.error (.buffer e))
  | .ok initial =>
    let p := liftPrims (E := E) (bufferPrims (E := E) (V := V) displaySize)
    let io : JIO Unit V := .plain ()
    let body : JoinM E Unit := match args with
      | (none, _) => join3 it printX printStringJoin io itr (⟨[], by decide⟩ : JString)
      | (some delim, none) => join3 it printX printD io itr delim
      | (some delim, some last) => join4 p it printX printD io itr delim last
    let action : JoinM E Bytes := do
      body
      liftShow (liftBuffer JuliaLean.base.iobuffer.takestring)
    match (action initial).run with
    | none => none
    | some (.ok (bytes, _)) => some (.ok ⟨bytes⟩)
    | some (.error e) => some (.error e)

/-! ## 9. `String` from characters (io.jl:805-847) -/

/--
Julia source: base/strings/io.jl:805-816 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function String(a::AbstractVector{Char})
    n = 0
    for v in a
        n += ncodeunits(v)
    end
    out = _string_n(n)
    offs = 1
    for v in a
        offs += __unsafe_string!(out, v, offs)
    end
    return out
end
```
`String(a::AbstractVector{Char})` (io.jl:805-816): `n` sums `ncodeunits(v)`, `_string_n(n)`
allocates, and `__unsafe_string!(out, v, offs)` stores each character's code units
(installed `charUtf8Bytes`).
-/
def stringOfChars (a : List JChar) : Jl JuliaLean.base.strings.io.JuliaString := do
  let mut n := JuliaLean.base.int.lit .i64 0
  for v in a do
    n := JuliaLean.base.int.add n (← JuliaLean.base.char.ncodeunits_Char
      (JuliaLean.base.int.lit .i64 4) (fun x y => JInt.div x y) JuliaLean.base.char.charBitOps
      (· == 0) v)
  if n.val < 0 then .error (.argumentError "String length must be non-negative")
  pure ⟨(a.map charUtf8Bytes).flatten⟩

/--
Julia source: base/strings/io.jl:818-824 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function String(chars::AbstractVector{<:AbstractChar})
    sprint(sizehint=length(chars)) do io
        for c in chars
            print(io, c)
        end
    end
end
```
`String(chars::AbstractVector{<:AbstractChar})` (io.jl:818-824): `sprint(sizehint=length(chars))`
printing each `print(io, c::AbstractChar) = print(io, Char(c))` (char.jl:304), with the element
type's `Char` conversion (`unicode.CharOps`).
-/
def stringOfAbstractChars {C : Type} (cops : JuliaLean.base.strings.unicode.CharOps C)
    (displaySize : JInt64 × JInt64) (a : AnyOps V Ty) (chars : List C) :
    Except (Error (StrIOError E)) JuliaLean.base.strings.io.JuliaString :=
  sprintIOBuffer (JuliaLean.base.iobuffer.bitsConversions .i64) displaySize a .none
    (JuliaLean.base.iobuffer.i chars.length)
    (fun io (_ : Unit) => do
      for c in chars do
        printChar (bufferCharIO displaySize) io (← ofChar (E := E) (cops.toChar c))) ()

/-- An `AnnotatedChar`: its character and its annotations (strings/annotated.jl). -/
structure AnnotatedChar where
  char : JChar
  annotations : List String

/--
Julia source: base/strings/io.jl:826-847 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function AnnotatedString(chars::AbstractVector{C}) where {C<:AbstractChar}
    str = if C <: AnnotatedChar
        String(getfield.(chars, :char))
    else
        sprint(sizehint=length(chars)) do io
            for c in chars
                print(io, c)
            end
        end
    end
    annots = RegionAnnotation[]
    point = 1
    for c in chars
        if c isa AnnotatedChar
            for annot in c.annotations
                push!(annots, (point:point, annot...))
            end
        end
        point += ncodeunits(c)
    end
    AnnotatedString(str, annots)
end
```
`AnnotatedString(chars::AbstractVector{C})` (io.jl:826-847): for `C <: AnnotatedChar` the
string is `String(getfield.(chars, :char))`, and each annotation of the character at code-unit
point `point` becomes the region `point:point`.
-/
def annotatedStringOfChars (chars : List AnnotatedChar) :
    Jl JuliaLean.base.strings.io.AnnotatedText := do
  let str ← stringOfChars (chars.map (·.char))
  let mut annots : List JuliaLean.base.strings.io.RegionAnnotation := []
  let mut point := 1
  for c in chars do
    for annot in c.annotations do
      annots := annots ++ [⟨point, point, annot⟩]
    point := point + (charUtf8Bytes c.char).length
  pure ⟨str.bytes, annots⟩

/-- `AnnotatedString(chars)` for a vector of plain characters (io.jl:829-834): the `sprint` string
and no annotations. -/
def annotatedStringOfPlainChars {C : Type} (cops : JuliaLean.base.strings.unicode.CharOps C)
    (displaySize : JInt64 × JInt64) (a : AnyOps V Ty) (chars : List C) :
    Except (Error (StrIOError E)) JuliaLean.base.strings.io.AnnotatedText := do
  let str ← stringOfAbstractChars (E := E) cops displaySize a chars
  pure ⟨str.bytes, []⟩

/-! ## 11. Multiline strings (io.jl:701-803)

`tabwidth` is an `Int` (the keyword default `8`); a `tabwidth` of another type is the named gap
`indentation-tabwidth-type`. `count`/`col` are `Int`, `div` is the installed checked `Int`
division (`DivideError` for `tabwidth == 0` or `typemin(Int) ÷ -1`). -/

/--
Julia source: base/strings/io.jl:719-731 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function indentation(str::AbstractString; tabwidth=8)
    count = 0
    for ch in str
        if ch == ' '
            count += 1
        elseif ch == '\t'
            count = div(count + tabwidth, tabwidth) * tabwidth
        else
            return count, false
        end
    end
    count, true
end
```
`indentation(str::AbstractString; tabwidth=8)` (io.jl:719-731).
-/
def indentation {S R CU CT E0 : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E0) (str : S)
    (tabwidth : JInt64) : Except (StrIOError E0) (JInt64 × Bool) :=
  foldChars ops str (JuliaLean.base.int.lit .i64 0, true) (fun ch (count, _) =>
    if ch == asciiLit 0x20 then
      pure (.yield (JuliaLean.base.int.add count (JuliaLean.base.int.lit .i64 1), true))
    else if ch == asciiLit 0x09 then do
      let q ← ofJlStr (E := E0) (JInt.div (JuliaLean.base.int.add count tabwidth) tabwidth)
      pure (.yield (JuliaLean.base.int.mul q tabwidth, true))
    else pure (.done (count, false)))

/--
Julia source: base/strings/io.jl:749-803 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unindent(str::AbstractString, indent::Int; tabwidth=8)
    indent == 0 && return str
    # Note: this loses the type of the original string
    buf = IOBuffer(sizehint=sizeof(str))
    cutting = true
    col = 0     # current column (0 based)
    for ch in str
        if cutting
            if ch == ' '
                col += 1
            elseif ch == '\t'
                col = div(col + tabwidth, tabwidth) * tabwidth
            elseif ch == '\n'
                # Now we need to output enough indentation
                for _ = 1:col-indent
                    print(buf, ' ')
                end
                col = 0
                print(buf, '\n')
            else
                cutting = false
                # Now we need to output enough indentation to get to
                # correct place
                for _ = 1:col-indent
                    print(buf, ' ')
                end
                col += 1
                print(buf, ch)
            end
        elseif ch == '\t'       # Handle internal tabs
            upd = div(col + tabwidth, tabwidth) * tabwidth
            # output the number of spaces that would have been seen
            # with original indentation
            for _ = 1:(upd-col)
                print(buf, ' ')
            end
            col = upd
        elseif ch == '\n'
            cutting = true
            col = 0
            print(buf, '\n')
        else
            col += 1
            print(buf, ch)
        end
    end
    # If we were still "cutting" when we hit the end of the string,
    # we need to output the right number of spaces for the indentation
    if cutting
        for _ = 1:col-indent
            print(buf, ' ')
        end
    end
    takestring!(buf)
end
```
`unindent(str::AbstractString, indent::Int; tabwidth=8)` (io.jl:749-803): `buf =
IOBuffer(sizehint=sizeof(str))` is the installed `newBufferState`, each `print(buf, c)` the
installed `IOBuffer` `write(buf, c)`, and the result `takestring!(buf)`.
-/
def unindent {S R CU CT E0 : Type}
    (ops : JuliaLean.base.strings.basic.StringOps S R JChar CU CT E0)
    (displaySize : JInt64 × JInt64) (str : S) (indent tabwidth : JInt64) :
    Except (Error (StrIOError E0)) (Unindented S) := do
  if indent.val == 0 then return .original str
  let initial ← (newBufferState (JuliaLean.base.iobuffer.bitsConversions .i64)
    (some (JuliaLean.base.strings.basic.sizeofString ops str))).mapError Error.buffer
  let cio := bufferCharIO (E := StrIOError E0) (V := Unit) displaySize
  let io : JIO Unit Unit := .plain ()
  let space := asciiLit 0x20
  let pad := fun (col : JInt64) => do
    for _ in List.range (JuliaLean.base.int.sub col indent).val.toNat do printChar cio io space
  let nextTab := fun (col : JInt64) => do
    let q ← ofJlStr (E := E0) (JInt.div (JuliaLean.base.int.add col tabwidth) tabwidth)
    pure (JuliaLean.base.int.mul q tabwidth)
  let one := JuliaLean.base.int.lit .i64 1
  let action : BufferShowM (StrIOError E0) Bytes := do
    let (cutting, col) ← foldChars ops str (true, JuliaLean.base.int.lit .i64 0)
      (fun ch (cutting, col) => do
        if cutting then
          if ch == space then pure (.yield (true, JuliaLean.base.int.add col one))
          else if ch == asciiLit 0x09 then pure (.yield (true, ← nextTab col))
          else if ch == asciiLit 0x0a then do
            pad col
            printChar cio io ch
            pure (.yield (true, JuliaLean.base.int.lit .i64 0))
          else do
            pad col
            printChar cio io ch
            pure (.yield (false, JuliaLean.base.int.add col one))
        else if ch == asciiLit 0x09 then do
          let upd ← nextTab col
          for _ in List.range (JuliaLean.base.int.sub upd col).val.toNat do printChar cio io space
          pure (.yield (false, upd))
        else if ch == asciiLit 0x0a then do
          printChar cio io ch
          pure (.yield (true, JuliaLean.base.int.lit .i64 0))
        else do
          printChar cio io ch
          pure (.yield (false, JuliaLean.base.int.add col one)))
    if cutting then pad col
    liftBuffer JuliaLean.base.iobuffer.takestring
  match action initial with
  | .ok bytes _ => pure (.built bytes)
  | .error error _ => .error error

end Buffer

/-! ## 10. `IOBuffer(str::String)`, `IOBuffer(s::SubString{String})` (io.jl:306-307)

`unsafe_wrap(Vector{UInt8}, str)` is the vector of the string's bytes at memory offset 0;
`view(v, r)` of a `UnitRange` is `v[r]` after the installed `checkbounds`, as a 1-based vector.
Both go through the installed `iobufferDataVector`/`iobufferData` constructors on the installed
constructor state. -/

abbrev ViewM := StateT JuliaLean.base.iobuffer.BufferState (Except JuliaLean.base.iobuffer.IOErr)

def initialBufferState : JuliaLean.base.iobuffer.BufferState :=
  JuliaLean.base.iobuffer.newBuf [] true true true true false JuliaLean.base.iobuffer.imaxval

/--
Julia source: base/strings/io.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IOBuffer(str::String) = IOBuffer(unsafe_wrap(Vector{UInt8}, str))
```
`IOBuffer(str::String) = IOBuffer(unsafe_wrap(Vector{UInt8}, str))` (io.jl:306): the installed
`ioBufferOfString`.
-/
def ioBufferString (str : JuliaLean.base.strings.io.JuliaString) :
    Except JuliaLean.base.iobuffer.IOErr JuliaLean.base.iobuffer.BufferState := do
  let (_, state) ← (JuliaLean.base.strings.io.ioBufferOfString
    (JuliaLean.base.iobuffer.ctorStateAccess false)
    (fun s => pure s.bytes) (fun v : List UInt8 => pure v) (fun r => pure r)
    (fun _ => pure (JuliaLean.base.iobuffer.i 0))
    (fun v => pure (JuliaLean.base.iobuffer.i v.length))
    (fun mem => pure (JuliaLean.base.iobuffer.i mem.length)) str : ViewM Unit).run initialBufferState
  pure state

/-- Exceptions of `IOBuffer(s::SubString{String})`: the IOBuffer, array (`view` bounds) and range
constructor exceptions of the installed models. -/
inductive SubViewError where
  | io (e : JuliaLean.base.iobuffer.IOErr)
  | array (e : JuliaLean.base.abstractarray.ArrayError)
  | range (e : JuliaLean.base.range.Exc)

abbrev SubViewM := StateT JuliaLean.base.iobuffer.BufferState (Except SubViewError)

instance : MonadExceptOf JuliaLean.base.iobuffer.IOErr SubViewM where
  throw e := fun _ => .error (.io e)
  tryCatch action handler := fun s => match action s with
    | .error (.io e) => handler e s
    | r => r

instance : MonadExceptOf JuliaLean.base.abstractarray.ArrayError SubViewM where
  throw e := fun _ => .error (.array e)
  tryCatch action handler := fun s => match action s with
    | .error (.array e) => handler e s
    | r => r

instance : MonadExceptOf JuliaLean.base.range.Exc SubViewM where
  throw e := fun _ => .error (.range e)
  tryCatch action handler := fun s => match action s with
    | .error (.range e) => handler e s
    | r => r

def liftView {α : Type} (action : ViewM α) : SubViewM α := fun s =>
  match action s with
  | .ok r => .ok r
  | .error e => .error (.io e)

/-- The installed constructor-state access, in `SubViewM`. -/
def subViewAccess : JuliaLean.base.iobuffer.Access SubViewM Unit (List UInt8) where
  get r := liftView ((JuliaLean.base.iobuffer.ctorStateAccess false).get r)
  set r f := liftView ((JuliaLean.base.iobuffer.ctorStateAccess false).set r f)
  new f := liftView ((JuliaLean.base.iobuffer.ctorStateAccess false).new f)
  isIOBuffer r := liftView ((JuliaLean.base.iobuffer.ctorStateAccess false).isIOBuffer r)

/-- `view(v::Vector{UInt8}, r::UnitRange{Int})`: `checkbounds(v, r)` (`BoundsError` unless the
range is empty or inside `1:length(v)`), then the 1-based vector of `v[r]`. -/
def viewBytes (v : List UInt8) (r : JuliaLean.base.range.UnitRange JuliaLean.base.iobuffer.I) :
    SubViewM (List UInt8) :=
  if r.stop.val < r.start.val then pure []
  else if r.start.val < 1 ∨ r.stop.val > v.length then
    throwThe JuliaLean.base.abstractarray.ArrayError (.julia .boundsError)
  else pure ((v.drop (r.start.val - 1).toNat).take (r.stop.val - r.start.val + 1).toNat)

/--
Julia source: base/strings/io.jl:307-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IOBuffer(s::SubString{String}) = IOBuffer(view(unsafe_wrap(Vector{UInt8}, s.string), s.offset + 1 : s.offset + sizeof(s)))
```
`IOBuffer(s::SubString{String}) = IOBuffer(view(unsafe_wrap(Vector{UInt8}, s.string),
s.offset + 1 : s.offset + sizeof(s)))` (io.jl:307): the installed `ioBufferOfSubString`.
-/
def ioBufferSubString (s : JuliaLean.base.strings.io.JuliaSubString) :
    Except SubViewError JuliaLean.base.iobuffer.BufferState := do
  let (_, state) ← (JuliaLean.base.strings.io.ioBufferOfSubString subViewAccess
    (fun str => pure str.bytes) viewBytes
    (fun _ => pure (JuliaLean.base.iobuffer.i 1)) (fun i => pure i)
    (fun v => pure (JuliaLean.base.iobuffer.i v.length)) (fun l => pure l) s : SubViewM Unit).run
      initialBufferState
  pure state

end JuliaLean.base.strings.io

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

def isHexDigitC (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- The digit loop of the `\x`, `\u`, `\U` branch, `base/strings/io.jl:545-551`:
`(n, k, rest)` after reading at most `m` hex digits; `k` is the loop counter at exit. -/
def hexEscLoop (m : Nat) : Nat → Nat → List Char → Nat × Nat × List Char
  | n, k, a =>
    let k := k + 1
    if k ≤ m then
      match a with
      | [] => (n, k, a)
      | nc :: a' =>
        match isHexDigitC nc with
        | some d => hexEscLoop m (n * 16 + d) k a'
        | none => (n, k, a)
    else (n, k, a)

/-- The octal digit loop, `base/strings/io.jl:562-567`. -/
def octEscLoop : Nat → Nat → List Char → Nat × List Char
  | n, k, a =>
    let k := k + 1
    if k ≤ 3 then
      match a with
      | [] => (n, a)
      | c :: a' => if '0' ≤ c ∧ c ≤ '7' then octEscLoop (n * 8 + (c.toNat - '0'.toNat)) k a' else (n, a)
    else (n, a)

/-- `unescape_string(s)` with `keep = ()`, `base/strings/io.jl:535-590`: the bytes it
prints. The fuel is the number of characters left, which bounds the iterations. -/
def unescapeLoop : Nat → List Char → Jle (List Byte)
  | 0, _ => .ok []
  | _ + 1, [] => .ok []
  | fuel + 1, c :: a =>
    if !a.isEmpty && c == '\\' then
      match a with
      | [] => .ok []
      | c :: a =>
        if c == 'x' || c == 'u' || c == 'U' then
          let m := if c == 'x' then 2 else if c == 'u' then 4 else 8
          let (n, k, a) := hexEscLoop m 0 0 a
          if k == 1 || n > 0x10ffff then
            .error (argErr (if m == 2 then "invalid hex (\\x) escape sequence"
              else if m == 4 then "invalid unicode (\\u) escape sequence"
              else "invalid unicode (\\U) escape sequence"))
          else
            let out := if m == 2 then [b8 n] else utf8Enc n
            (unescapeLoop fuel a).map (out ++ ·)
        else if '0' ≤ c ∧ c ≤ '7' then
          let (n, a) := octEscLoop (c.toNat - '0'.toNat) 1 a
          if n > 255 then .error (argErr "octal escape sequence out of range")
          else (unescapeLoop fuel a).map ([b8 n] ++ ·)
        else
          let e : Option Nat :=
            if c == 'a' then some 7 else if c == 'b' then some 8 else if c == 't' then some 9
            else if c == 'n' then some 10 else if c == 'v' then some 11 else if c == 'f' then some 12
            else if c == 'r' then some 13 else if c == 'e' then some 27
            else if c == '\\' || c == '"' then some c.toNat else none
          match e with
          | none => .error (argErr "invalid escape sequence")
          | some e => (unescapeLoop fuel a).map (utf8Enc e ++ ·)
    else (unescapeLoop fuel a).map (utf8Enc c.toNat ++ ·)

def unescape_string (s : List Char) : Jle (List Byte) := unescapeLoop s.length s

end JuliaLean.Base64Uuid


namespace JuliaLean.Show

open JuliaLean JuliaLean.Strings

/-- `need_full_hex(c)`, `base/strings/io.jl:395`; `none` is `nothing`. -/
def needFullHex : Option UInt32 → Bool
  | none => false
  | some c => isxdigit c

/-- `escape_nul(c)`, `base/strings/io.jl:396-397`. -/
def escapeNul : Option UInt32 → List UInt8
  | some c => if decide (ac 0x30 ≤ c) && decide (c ≤ ac 0x37) then asc ['\\', 'x', '0', '0']
              else asc ['\\', '0']
  | none => asc ['\\', '0']

/-- The `else` branch of `escape_string` for malformed or overlong `c`,
`base/strings/io.jl:479-484`: `"\\x"` and two hex digits for each byte
`u % UInt8` of `u = bswap(c)` until `u >>= 8` is zero. -/
def hexBytesAux : Nat → UInt32 → List UInt8
  | 0, _ => []
  | k + 1, u => asc ['\\', 'x'] ++ hexStr u.toUInt8.toNat 2 ++
      (if u >>> 8 = 0 then [] else hexBytesAux k (u >>> 8))

/-- One iteration of the loop of `escape_string(io, s, esc; keep, ascii, fullhex)`,
`base/strings/io.jl:459-486`, for the char `c` with `peek(a) = nxt`. -/
def escChar (d : UData) (esc keep : List UInt32) (ascii fullhex : Bool) (c : UInt32)
    (nxt : Option UInt32) : List UInt8 :=
  if c ∈ esc then 0x5c :: writeChar c
  else if c ∈ keep then writeChar c
  else if isasciiChar c then
    if c = ac 0 then escapeNul nxt
    else if c = ac 0x1b then asc ['\\', 'e']
    else if c = ac 0x5c then asc ['\\', '\\']
    else if decide (ac 0x07 ≤ c) && decide (c ≤ ac 0x0d) then
      [0x5c, (asc ['a', 'b', 't', 'n', 'v', 'f', 'r']).getD ((cpOf c).toNat - 7) 0]
    else if isprint d c then writeChar c
    else asc ['\\', 'x'] ++ hexStr (cpOf c).toNat 2
  else if !isoverlong c && !ismalformed c then
    if !ascii && isprint d c then writeChar c
    else if c ≤ ac 0x7f then asc ['\\', 'x'] ++ hexStr (cpOf c).toNat 2
    else if c ≤ 0xefbfbf00 then
      asc ['\\', 'u'] ++ hexStr (cpOf c).toNat (if fullhex || needFullHex nxt then 4 else 2)
    else asc ['\\', 'U'] ++ hexStr (cpOf c).toNat (if fullhex || needFullHex nxt then 8 else 4)
  else hexBytesAux 4 (bswap32 c)

/-- The loop `for c in a` of `escape_string`, `base/strings/io.jl:461`, over the
remaining chars of `a = Iterators.Stateful(s)`. -/
def escLoop (d : UData) (esc keep : List UInt32) (ascii fullhex : Bool) : List UInt32 → List UInt8
  | [] => []
  | c :: rest => escChar d esc keep ascii fullhex c rest.head? ++ escLoop d esc keep ascii fullhex rest

/-- `escape_string(io, s, esc; keep, ascii, fullhex)`, `base/strings/io.jl:459-486`:
the bytes written to `io`. -/
def escapeStringIO (d : UData) (s : JStr) (esc keep : List UInt32) (ascii fullhex : Bool) :
    List UInt8 :=
  escLoop d esc keep ascii fullhex (chars s)

/-- The `String` that `sprint` returns for the bytes `bs` written to its buffer;
Julia cannot allocate `2^62` bytes. -/
def mkStr (bs : List UInt8) : SJl JStr :=
  if h : bs.length < 2 ^ 62 then .ok ⟨bs, h⟩ else .error .outOfMemory

/-- `escape_string(s, esc = ('"',); keep = (), ascii = false, fullhex = false)`,
`base/strings/io.jl:488-489`. -/
def escapeString (d : UData) (s : JStr) (esc : List UInt32 := [ac 0x22]) (keep : List UInt32 := [])
    (ascii : Bool := false) (fullhex : Bool := false) : SJl JStr :=
  mkStr (escapeStringIO d s esc keep ascii fullhex)

/-- `print_quoted(io, s)`, `base/strings/io.jl:491-495`; also `show(io, s::String)`
(`:194`), so `repr(s)`. -/
def printQuoted (d : UData) (s : JStr) : List UInt8 :=
  [0x22] ++ escapeStringIO d s [ac 0x22, ac 0x24] [] false false ++ [0x22]

/-! ## `unescape_string` -/

/-- The digit value of `nc` in the `\x`/`\u`/`\U` loop, `base/strings/io.jl:546-548`:
`nc - '0'`, `nc - 'a' + 10`, `nc - 'A' + 10` (`Char` differences are code point
differences, `base/char.jl:296`), or `nothing` for `break`. -/
def hexVal (nc : UInt32) : Option Nat :=
  if decide (ac 0x30 ≤ nc) && decide (nc ≤ ac 0x39) then some ((cpOf nc).toNat - 0x30)
  else if decide (ac 0x61 ≤ nc) && decide (nc ≤ ac 0x66) then some ((cpOf nc).toNat - 0x61 + 10)
  else if decide (ac 0x41 ≤ nc) && decide (nc ≤ ac 0x46) then some ((cpOf nc).toNat - 0x41 + 10)
  else none

/-- `while (k += 1) <= m && !isempty(a) ... end`, `base/strings/io.jl:544-551`,
from counter `k` and value `n`; returns the final `(k, n, a)`. `n` is an `Int`
that stays below `16^8`. -/
def unescHex (m : Nat) : Nat → Nat → Nat → List UInt32 → Nat × Nat × List UInt32
  | 0, k, n, a => (k, n, a)
  | f + 1, k, n, a =>
    if k + 1 ≤ m then
      match a with
      | [] => (k + 1, n, a)
      | nc :: a' =>
        match hexVal nc with
        | some v => unescHex m f (k + 1) (n * 16 + v) a'
        | none => (k + 1, n, a)
    else (k + 1, n, a)

/-- `while (k += 1) <= 3 && !isempty(a) ... end`, `base/strings/io.jl:563-567`;
`n<<3 + c-'0'` is `Char` arithmetic whose value is `8n + codepoint(c) - 0x30`. -/
def unescOct : Nat → Nat → Nat → List UInt32 → Nat × List UInt32
  | 0, _, n, a => (n, a)
  | f + 1, k, n, a =>
    if k + 1 ≤ 3 then
      match a with
      | [] => (n, a)
      | c :: a' =>
        if decide (ac 0x30 ≤ c) && decide (c ≤ ac 0x37) then
          unescOct f (k + 1) (n * 8 + (cpOf c).toNat - 0x30) a'
        else (n, a)
    else (n, a)

/-- The C escapes of `unescape_string`, `base/strings/io.jl:574-583`: the
character printed for `\c`, or `none` where Julia throws. -/
def unescSimple (c : UInt32) : Option UInt32 :=
  if c = ac 0x61 then some (ac 0x07)
  else if c = ac 0x62 then some (ac 0x08)
  else if c = ac 0x74 then some (ac 0x09)
  else if c = ac 0x6e then some (ac 0x0a)
  else if c = ac 0x76 then some (ac 0x0b)
  else if c = ac 0x66 then some (ac 0x0c)
  else if c = ac 0x72 then some (ac 0x0d)
  else if c = ac 0x65 then some (ac 0x1b)
  else if c = ac 0x5c || c = ac 0x22 then some c
  else none

/-- The loop of `unescape_string(io, s, keep)`, `base/strings/io.jl:535-591`, over
the remaining chars of `a`; the fuel bounds the iterations, each of which
consumes at least one char. Bytes written before an exception are discarded
with it. -/
def unescLoop (keep : List UInt32) : Nat → List UInt32 → SJl (List UInt8)
  | 0, _ => .ok []
  | _ + 1, [] => .ok []
  | f + 1, c :: a =>
    if !a.isEmpty && c = ac 0x5c then
      match a with
      | [] => .ok []
      | c :: a =>
        if c ∈ keep then (fun r => 0x5c :: writeChar c ++ r) <$> unescLoop keep f a
        else if c = ac 0x78 || c = ac 0x75 || c = ac 0x55 then
          let m := if c = ac 0x78 then 2 else if c = ac 0x75 then 4 else 8
          match unescHex m (m + 1) 0 0 a with
          | (k, n, a) =>
            if k = 1 || decide (n > 0x10ffff) then
              .error (.jl (.argumentError (if m = 2 then "invalid hex (\\x) escape sequence"
                else if m = 4 then "invalid unicode (\\u) escape sequence"
                else "invalid unicode (\\U) escape sequence")))
            else if m = 2 then (fun r => n.toUInt8 :: r) <$> unescLoop keep f a
            else (fun r => writeChar (charOfCp n) ++ r) <$> unescLoop keep f a
        else if decide (ac 0x30 ≤ c) && decide (c ≤ ac 0x37) then
          match unescOct 3 1 ((cpOf c).toNat - 0x30) a with
          | (n, a) =>
            if n > 255 then .error (.jl (.argumentError "octal escape sequence out of range"))
            else (fun r => n.toUInt8 :: r) <$> unescLoop keep f a
        else
          match unescSimple c with
          | some e => (fun r => writeChar e ++ r) <$> unescLoop keep f a
          | none => .error (.jl (.argumentError "invalid escape sequence"))
    else (fun r => writeChar c ++ r) <$> unescLoop keep f a

/-- `unescape_string(s, keep = ())`, `base/strings/io.jl:592-593`, on the chars
`cs` of `s`. -/
def unescapeStringOf (cs : List UInt32) (keep : List UInt32) : SJl JStr :=
  match unescLoop keep (cs.length + 1) cs with
  | .ok bs => mkStr bs
  | .error e => .error e

/-- `unescape_string(s, keep = ())`, `base/strings/io.jl:592-593`. -/
def unescapeString (s : JStr) (keep : List UInt32 := []) : SJl JStr := unescapeStringOf (chars s) keep

/-! ## JuliaSyntax `unescape_julia_string` -/

/-- The loop of `escape_raw_string(io, str, delim)`, `base/strings/io.jl:663-692`,
from `escapes` pending backslashes: the bytes written and the count `total` of
inserted backslashes. -/
def escRawLoop (delim : UInt32) : Nat → List UInt32 → List UInt8 × Nat
  | escapes, [] => (List.replicate escapes 0x5c, escapes)
  | escapes, c :: cs =>
    if c = ac 0x5c then
      match escRawLoop delim (escapes + 1) cs with
      | (o, t) => (writeChar c ++ o, t)
    else if c = delim then
      match escRawLoop delim 0 cs with
      | (o, t) => (List.replicate (escapes + 1) 0x5c ++ writeChar c ++ o, escapes + 1 + t)
    else
      match escRawLoop delim 0 cs with
      | (o, t) => (writeChar c ++ o, t)

/-- `escape_raw_string(str, delim = '"')`, `base/strings/io.jl:694-697`: `str`
itself when nothing needs escaping, else the escaped copy. -/
def escapeRawString (s : JStr) (delim : UInt32 := ac 0x22) : List UInt8 :=
  let r := escRawLoop delim 0 (chars s)
  if r.2 = 0 then s.bytes else r.1

end JuliaLean.Show


/-!
# `base/strings/io.jl`

`print`/`write` calls are recorded as `Ev` events so that `lock`/`unlock`
pairing is visible. A value's `show`/`print` output is given as its events
(or text), and may end in an exception (`Shown`). `IOContext` properties are
association lists `Props` (latest binding first).
-/

namespace JuliaLean.ShowCov.StringsIO

open JuliaLean.ShowCov

/-- Effects on a stream. -/
inductive Ev where
  | lock
  | unlock
  | write (s : String)
  deriving DecidableEq, Repr

/-- The text written by a list of events. -/
def evText : List Ev → String
  | [] => ""
  | .write s :: es => s ++ evText es
  | _ :: es => evText es

/-- Net lock depth after a list of events. -/
def lockDepth : List Ev → Int
  | [] => 0
  | .lock :: es => 1 + lockDepth es
  | .unlock :: es => lockDepth es - 1
  | _ :: es => lockDepth es

/-- What a `show`/`print` call does: events, then normal return or an exception. -/
structure Shown where
  evs : List Ev
  err : Option Err

/-- `print(io::IO, x)`, `base/strings/io.jl:32-40`:
`lock(io); try show(io, x) finally unlock(io) end; return nothing`. -/
def printAny (shown : Shown) : Shown :=
  ⟨[.lock] ++ shown.evs ++ [.unlock], shown.err⟩

/-- `print(io::IO, xs...)`, `base/strings/io.jl:42-54`: under one lock, `print(io, xs[i])`
for each argument until one throws. -/
def printMany (items : List Shown) : Shown :=
  let rec go : List Shown → List Ev × Option Err
    | [] => ([], none)
    | x :: xs =>
      let p := printAny x
      match p.err with
      | some e => (p.evs, some e)
      | none => let (r, e) := go xs; (p.evs ++ r, e)
  let (evs, e) := go items
  ⟨[.lock] ++ evs ++ [.unlock], e⟩

/-- A plain string argument: one write. -/
def strArg (s : String) : Shown := ⟨[.write s], none⟩

/-- `println(io::IO, xs...) = print(io, xs..., "\n")`, `base/strings/io.jl:77`. -/
def printlnMany (items : List Shown) : Shown := printMany (items ++ [strArg "\n"])

/-! ## `sprint`, `repr`, `string` -/

/-- `IOContext` properties, latest binding first (`ImmutableDict` lookup order). -/
abbrev Props := List (String × String)

/-- The `context` keyword of `sprint`/`repr`: `nothing`, one pair, a tuple of
pairs, or an `IO` whose properties are inherited. -/
inductive Ctx where
  | none
  | pair (kv : String × String)
  | tuple (kvs : List (String × String))
  | io (props : Props)

/-- The properties of the stream `f` receives: `IOContext(s, context...)`
adds the pairs in order (each new binding shadows earlier ones), and
`IOContext(s, io)` copies `io`'s properties, `base/strings/io.jl:106-112`. -/
def ctxProps : Ctx → Props
  | .none => []
  | .pair kv => [kv]
  | .tuple kvs => kvs.reverse
  | .io p => p

/-- `sprint(f, args...; context, sizehint)`, `base/strings/io.jl:104-114`. `f`
is what the called function writes given the stream properties; the result
is `takestring!(s)`. The `sizehint` does not affect the text. -/
def sprint (f : Props → Shown) (context : Ctx) (_sizehint : Nat := 0) : R String :=
  let shown := f (ctxProps context)
  match shown.err with
  | some e => .error e
  | none => .ok (evText shown.evs)

/-- `repr(x; context=nothing) = sprint(show, x; context=context)`, `base/strings/io.jl:284`. -/
def repr (shw : Props → Shown) (context : Ctx) : R String := sprint shw context

/-- `limitrepr(x) = repr(x, context = :limit=>true)`, `base/strings/io.jl:286`. -/
def limitrepr (shw : Props → Shown) : R String := repr shw (.pair ("limit", "true"))

/-- Kinds of values `_str_sizehint` distinguishes. -/
inductive Arg where
  | float64 | float32
  | str (s : List Char)
  | char (c : Char)
  | u64 (n : Nat) | u32 (n : Nat)
  | i64 (n : Int) | i32 (n : Int)
  | other

/-- `ndigits(x)` in base 10 for integer `x` (`ndigits(0) == 1`). -/
def ndigits10 (n : Int) : Nat := (Nat.toDigits 10 n.natAbs).length

/-- `_str_sizehint(x)`, `base/strings/io.jl:116-132`. String sizes are UTF-8 byte
counts. -/
def strSizehint : Arg → Nat
  | .float64 => 20
  | .float32 => 12
  | .str s => (s.map Char.utf8Size).sum
  | .char c => c.utf8Size
  | .u64 n => ndigits10 n
  | .u32 n => ndigits10 n
  | .i64 n => ndigits10 n + (if n < 0 then 1 else 0)
  | .i32 n => ndigits10 n + (if n < 0 then 1 else 0)
  | .other => 8

/-- `print_to_string(xs...)`, `base/strings/io.jl:134-148`: `""` for no arguments,
else every argument printed into one buffer (sized by the sum of hints). -/
def printToString (xs : List (Arg × Shown)) : R String :=
  if xs.isEmpty then .ok "" else
  let _siz := (xs.map (fun x => strSizehint x.1)).sum
  let p := printMany (xs.map (·.2))
  match p.err with
  | some e => .error e
  | none => .ok (evText p.evs)

/-- `string_with_env(env, xs...)`, `base/strings/io.jl:150-165`: as
`print_to_string`, printing to `IOContext(s, env)`; `pr env x` is what `x` prints
under the properties `env`. -/
def stringWithEnv (env : Props) (xs : List (Arg × (Props → Shown))) : R String :=
  if xs.isEmpty then .ok "" else
  let p := printMany (xs.map (fun x => x.2 env))
  match p.err with
  | some e => .error e
  | none => .ok (evText p.evs)

/-- `string(xs...) = print_to_string(xs...)`, `base/strings/io.jl:186`. -/
def string (xs : List (Arg × Shown)) : R String := printToString xs

/-- `string(a::Symbol) = String(a)`, `base/strings/io.jl:188`: the symbol's name. -/
def stringSym (name : String) : String := name

/-- `print(io::IO, s::AbstractString) = for c in s; print(io, c); end`,
`base/strings/io.jl:192`: one write per character. -/
def printAbstractString (s : List Char) : List Ev := s.map (fun c => .write (String.singleton c))

/-- `write(io::IO, s::AbstractString)`, `base/strings/io.jl:193`: writes each
character and returns the total byte count (`write(io, c)` returns `ncodeunits(c)`). -/
def writeAbstractString (s : List Char) : List Ev × Nat :=
  (s.map (fun c => .write (String.singleton c)), (s.map Char.utf8Size).sum)

/-- `write(io, s::Union{String,SubString{String}})`, `base/strings/io.jl:242-245`:
one `unsafe_write` of `sizeof(s)` bytes; the return value is `sizeof(s)`.
`print(io, s::String)` (`:246`) is that write, returning `nothing`. -/
def writeString (s : String) : List Ev × Nat := ([.write s], s.utf8ByteSize)
def printString (s : String) : List Ev := (writeString s).1

/-- `show(io, s::AbstractString) = print_quoted(io, s)`,
`base/strings/io.jl:194`; `quoted` is the output of the separately modelled
`print_quoted` body. -/
def showAbstractString (quoted : String) : String := quoted

/-! ## `join` -/

/-- `join(io, iterator, delim, last)`, `base/strings/io.jl:330-345`, on the
printed forms of the items; returns what is written. -/
def joinLast (items : List String) (delim last : String) : List String :=
  let rec go (first : Bool) (prev : Option String) : List String → List String
    | [] => match prev with
      | some p => (if first then [] else [last]) ++ [p]
      | none => []
    | x :: xs => match prev with
      | some p => (if first then [] else [delim]) ++ [p] ++ go false (some x) xs
      | none => go first (some x) xs
  go true none items

/-- `join(io, iterator, delim="")`, `base/strings/io.jl:346-354`. -/
def join2 (items : List String) (delim : String := "") : List String :=
  let rec go (first : Bool) : List String → List String
    | [] => []
    | x :: xs => (if first then [] else [delim]) ++ [x] ++ go false xs
  go true items

/-- Element kinds `_join_preserve_annotations` distinguishes. -/
structure JoinInfo where
  /-- `isconcretetype(@default_eltype(iterator))` (generic method). -/
  concrete : Bool
  /-- `_isannotated` of the element type, or of any tuple element (tuple method). -/
  eltAnnotated : Bool
  argsAnnotated : Bool
  /-- `!isempty(io.annotations)` after joining into the `AnnotatedIOBuffer`. -/
  gotAnnotations : Bool

/-- The result kind of `_join_preserve_annotations`: a plain `String` (via
`sprint(join, ...)` or `String(take!(io.io))`) or an `AnnotatedString`. -/
inductive JoinKind where
  | plain | annotated
  deriving DecidableEq, Repr

/-- `_join_preserve_annotations(iterator, args...)`, `base/strings/io.jl:356-374`. -/
def joinKindGeneric (j : JoinInfo) : JoinKind :=
  if j.concrete && !j.eltAnnotated && !j.argsAnnotated then .plain
  else if j.concrete || j.gotAnnotations then .annotated else .plain

/-- `_join_preserve_annotations(iterator::Tuple, args...)`, `base/strings/io.jl:378-387`. -/
def joinKindTuple (j : JoinInfo) : JoinKind :=
  if !j.eltAnnotated && !j.argsAnnotated then .plain else .annotated

/-- `join(iterator)`, `join(iterator, delim)`, `join(iterator, delim, last)`,
`base/strings/io.jl:389-391`: the text (both result kinds hold the joined text). -/
def joinText (items : List String) (delim : Option String) (last : Option String) : String :=
  match delim, last with
  | none, _ => String.join (join2 items)
  | some d, none => String.join (join2 items d)
  | some d, some l => String.join (joinLast items d l)

/-! ## Escaping -/

/-- `escape_raw_string(io, str, delim)`, `base/strings/io.jl:663-693`: the
characters written and the returned `total` (backslashes added). -/
def escRaw (delim : Char) : List Char → Nat → Nat → List Char × Nat
  | [], escapes, total => (List.replicate escapes '\\', total + escapes)
  | c :: cs, escapes, total =>
    if c = '\\' then
      let (o, t) := escRaw delim cs (escapes + 1) total
      ('\\' :: o, t)
    else if c = delim then
      let (o, t) := escRaw delim cs 0 (total + (escapes + 1))
      (List.replicate (escapes + 1) '\\' ++ c :: o, t)
    else
      let (o, t) := escRaw delim cs 0 total
      (c :: o, t)

def escapeRawStringIO (str : List Char) (delim : Char := '"') : List Char × Nat := escRaw delim str 0 0

/-- `escape_raw_string(str, delim)`, `base/strings/io.jl:694-697`: `str` itself when
nothing needs escaping, else the escaped copy. -/
def escapeRawString (str : List Char) (delim : Char := '"') : List Char :=
  let total := (escapeRawStringIO str delim).2
  if total = 0 then str else (escapeRawStringIO str delim).1

/-- `@raw_str s` returns `s`, `base/strings/io.jl:643`. -/
def rawStr (s : List Char) : List Char := s

/-- `@b_str s = QuoteNode(codeunits(unescape_string(s)))`, `base/strings/io.jl:613-616`. -/
def bStr (s : JuliaLean.Strings.JStr) : JuliaLean.Strings.SJl (List UInt8) :=
  (fun t => t.bytes) <$> JuliaLean.Show.unescapeString s

/-! ## Multiline strings -/

/-- `div(count + tabwidth, tabwidth) * tabwidth`: the next tab stop. -/
def nextTab (count tabwidth : Nat) : Nat := (count + tabwidth) / tabwidth * tabwidth

/-- `indentation(str; tabwidth=8)`, `base/strings/io.jl:719-731`. -/
def indentation (tabwidth : Nat) : List Char → Nat → Nat × Bool
  | [], count => (count, true)
  | c :: cs, count =>
    if c = ' ' then indentation tabwidth cs (count + 1)
    else if c = '\t' then indentation tabwidth cs (nextTab count tabwidth)
    else (count, false)

/-- `for _ = 1:col-indent; print(buf, ' '); end`. -/
def spaces (col indent : Int) : List Char := List.replicate (col - indent).toNat ' '

/-- The loop of `unindent(str, indent; tabwidth=8)`, `base/strings/io.jl:755-801`,
with state `cutting` and `col`. -/
def unindentLoop (indent : Int) (tabwidth : Nat) : Bool → Nat → List Char → List Char
  | cutting, col, [] => if cutting then spaces col indent else []
  | true, col, ch :: cs =>
    if ch = ' ' then unindentLoop indent tabwidth true (col + 1) cs
    else if ch = '\t' then unindentLoop indent tabwidth true (nextTab col tabwidth) cs
    else if ch = '\n' then spaces col indent ++ '\n' :: unindentLoop indent tabwidth true 0 cs
    else spaces col indent ++ ch :: unindentLoop indent tabwidth false (col + 1) cs
  | false, col, ch :: cs =>
    if ch = '\t' then
      let upd := nextTab col tabwidth
      List.replicate (upd - col) ' ' ++ unindentLoop indent tabwidth false upd cs
    else if ch = '\n' then '\n' :: unindentLoop indent tabwidth true 0 cs
    else ch :: unindentLoop indent tabwidth false (col + 1) cs

/-- `unindent(str, indent; tabwidth=8)`, `base/strings/io.jl:749-803`. -/
def unindent (str : List Char) (indent : Int) (tabwidth : Nat := 8) : List Char :=
  if indent = 0 then str else unindentLoop indent tabwidth true 0 str

/-! ## Strings from characters -/

/-- `String(a::AbstractVector{Char})`, `base/strings/io.jl:805-816`: the
characters' encodings written one after another into a string of the summed
length. -/
def stringOfChars (a : List Char) : List Char × Nat := (a, (a.map Char.utf8Size).sum)

/-- `String(chars::AbstractVector{<:AbstractChar})`, `base/strings/io.jl:818-824`:
`print(io, c)` for each; `pr c` is the text `c` prints. -/
def stringOfAbstractChars {C} (pr : C → List Char) (chars : List C) : List Char :=
  chars.flatMap pr

/-- An `AnnotatedChar`: the character and its annotations. -/
structure AChar where
  char : Char
  annotations : List (String × String)

/-- `AnnotatedString(chars)`, `base/strings/io.jl:826-847`: the text and the
annotation regions `point:point` at each annotated character's first byte. -/
def annotatedStringOfChars (chars : List AChar) : List Char × List ((Nat × Nat) × (String × String)) :=
  let rec go (point : Nat) : List AChar → List ((Nat × Nat) × (String × String))
    | [] => []
    | c :: cs => c.annotations.map (fun a => ((point, point), a)) ++ go (point + c.char.utf8Size) cs
  (chars.map (·.char), go 1 chars)

/-! ## `show(io, ::MIME"text/plain", str; limit)` -/

/-- `skip_text(skip) = " ⋯ $skip $units ⋯ "`, `base/strings/io.jl:217`. -/
def skipText (units : String) (skip : Int) : String := " ⋯ " ++ toString skip ++ " " ++ units ++ " ⋯ "

/-- The inputs `show(io, MIME"text/plain"(), str; limit)` takes from the stream,
the string, and helpers in other files. -/
structure LimitIn where
  ioLimit : Bool
  displayCols : Int
  typeinfoNothing : Bool
  /-- `check_textwidth(str, limit)`. -/
  fits : Int → Bool
  /-- `ncodeunits(str)`; `codeunit(str) == UInt8`. -/
  ncu : Nat
  bytes : Bool
  /-- `string_truncate_boundaries(str, limit, max_replacement, Val(:center))`. -/
  boundaries : Int → String → Nat × Nat
  /-- `nextind(str, head)`. -/
  nextind : Nat → Nat
  /-- `textwidth(str[afterhead:prevind(str,tail)])`. -/
  midWidth : Nat → Nat → Nat

/-- The pieces printed: either `show(io, str)` in full, or the head, the styled
replacement, and the tail (as code-unit ranges). -/
inductive LimitOut where
  | full
  | elided (headEnd : Nat) (replacement : String) (tailStart : Nat)
  deriving DecidableEq, Repr

/-- `units` of `show(io, MIME"text/plain", str; limit)`, `base/strings/io.jl:216`. -/
def limitedUnits (x : LimitIn) : String := if x.bytes then "bytes" else "code units"

/-- `n = tail - afterhead`, the skipped code units, `base/strings/io.jl:226-227`. -/
def elidedCount (x : LimitIn) (head tail : Nat) : Int := (tail : Int) - x.nextind head

/-- `replacement = skip_text(n)`, `base/strings/io.jl:228`. -/
def elidedReplacement (x : LimitIn) (head tail : Nat) : String :=
  skipText (limitedUnits x) (elidedCount x head tail)

/-- The elision decision once the boundaries are known, `base/strings/io.jl:225-235`. -/
def limitedElide (x : LimitIn) (head tail : Nat) : LimitOut :=
  if 4 * ((elidedReplacement x head tail).utf8ByteSize : Int) ≤ elidedCount x head tail ∨
      (((elidedReplacement x head tail).utf8ByteSize : Int) ≤ elidedCount x head tail ∧
        ((elidedReplacement x head tail).utf8ByteSize : Int) ≤ x.midWidth (x.nextind head) tail) then
    .elided head (elidedReplacement x head tail) tail
  else .full

/-- The body of `show(io, ::MIME"text/plain", str; limit)` once a limit `l`
applies, `base/strings/io.jl:209-236`. -/
def limitedAt (x : LimitIn) (l : Int) : LimitOut :=
  if x.fits (max 0 (l - 2)) then .full else
  let bounds := x.boundaries (max 0 (l - 2)) (skipText (limitedUnits x) (x.ncu * 100 : Nat))
  limitedElide x bounds.1 bounds.2

/-- The limit in effect, `base/strings/io.jl:198-202`: the `limit` keyword, else
`max(20, displaysize(io)[2])` (times 7 without a `:typeinfo`) on a `:limit` stream. -/
def effectiveLimit (x : LimitIn) (limit : Option Int) : Option Int :=
  match limit with
  | some l => some l
  | none => if !x.ioLimit then none else
      let l := max 20 x.displayCols
      some (if x.typeinfoNothing then l * 7 else l)

/-- `show(io, ::MIME"text/plain", str; limit)`, `base/strings/io.jl:197-236`. -/
def showLimited (x : LimitIn) (limit : Option Int) : LimitOut :=
  match effectiveLimit x limit with
  | none => .full
  | some l => limitedAt x l

end JuliaLean.ShowCov.StringsIO


namespace JuliaLean.ShowCov.Methods.StringsIOFile

open JuliaLean.ShowCov.StringsIO
open JuliaLean.Show JuliaLean.Strings

def m32 (shown : Shown) := printAny shown

def m42 (shown : List Shown) := printMany shown

def m77 (shown : List Shown) := printlnMany shown

def m104 (f : Props → Shown) (context : Ctx) (sizehint : Nat) := sprint f context sizehint

def m116 (x : Arg) := strSizehint x

def m134 (xs : List (Arg × Shown)) := printToString xs

def m150 (env : Props) (xs : List (Arg × (Props → Shown))) := stringWithEnv env xs

def m186 (xs : List (Arg × Shown)) := string xs

def m188 (symbolName : String) := stringSym symbolName

def m192 (chars : List Char) := printAbstractString chars

def m193 (chars : List Char) := writeAbstractString chars

def m194 (data : UData) (s : JStr) := printQuoted data s

def m197 (input : LimitIn) (limit : Option Int) := showLimited input limit

def m217 (units : String) (skip : Int) := skipText units skip

def m242 (s : String) := writeString s

def m246 (s : String) := printString s

def m284 (f : Props → Shown) (context : Ctx) := repr f context

def m286 (f : Props → Shown) := limitrepr f

structure BufferSlice where
  parentBytes : Nat
  firstByte : Nat
  byteCount : Nat
  deriving DecidableEq, Repr

/-- `IOBuffer(str::String)` wraps all string bytes, `base/strings/io.jl:306`. -/
def m306 (bytes : Nat) : BufferSlice := ⟨bytes, 1, bytes⟩

/-- `IOBuffer(s::SubString{String})` wraps the parent then views
`offset+1:offset+sizeof(s)`, `base/strings/io.jl:307`. -/
def m307 (parentBytes offset bytes : Nat) : BufferSlice := ⟨parentBytes, offset + 1, bytes⟩

def m330 (items : List String) (delim last : String) := joinLast items delim last

def m346 (items : List String) (delim : String) := join2 items delim

def m356 (info : JoinInfo) (items : List String) (delim last : Option String) :=
  (joinKindGeneric info, joinText items delim last)

def m378 (info : JoinInfo) (items : List String) (delim last : Option String) :=
  (joinKindTuple info, joinText items delim last)

def m389 (info : JoinInfo) (items : List String) := m356 info items none none

def m390 (info : JoinInfo) (items : List String) (delim : String) :=
  m356 info items (some delim) none

def m391 (info : JoinInfo) (items : List String) (delim last : String) :=
  m356 info items (some delim) (some last)

def m395 (c : Option UInt32) := needFullHex c

def m396 (c : Option UInt32) := escapeNul c

def m459 (d : UData) (s : JStr) (esc keep : List UInt32) (ascii fullhex : Bool) :=
  escapeStringIO d s esc keep ascii fullhex

def m488 (d : UData) (s : JStr) (esc keep : List UInt32) (ascii fullhex : Bool) :=
  escapeString d s esc keep ascii fullhex

def m491 (d : UData) (s : JStr) := printQuoted d s

def m535 (s : JStr) (keep : List UInt32) := unescapeString s keep

def m592 (s : JStr) (keep : List UInt32) := unescapeString s keep

def m613 (s : JStr) := bStr s

def m643 (s : List Char) := rawStr s

def m663 (s : List Char) (delim : Char) := escapeRawStringIO s delim

def m694 (s : List Char) (delim : Char) := escapeRawString s delim

def m719 (s : List Char) (tabwidth : Nat) := indentation tabwidth s 0

def m749 (s : List Char) (indent : Int) (tabwidth : Nat) := unindent s indent tabwidth

def m805 (chars : List Char) := stringOfChars chars

def m818 {C} (printChar : C → List Char) (chars : List C) := stringOfAbstractChars printChar chars

def m826 (chars : List AChar) := annotatedStringOfChars chars

end JuliaLean.ShowCov.Methods.StringsIOFile

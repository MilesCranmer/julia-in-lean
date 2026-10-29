import JuliaLean.Core

/-!
# Model of `base/strings/io.jl`

Typed source models for string construction, IO, escaping, joining, and multiline text. Stream
operations and methods from other Base files are parameters of `IOOps`; writes carry a buffer
append law in the property file. Abstract strings, characters, arrays, values, iterators, and
integer arguments remain generic in their Julia-facing definitions.
-/

namespace JuliaLean.base.strings.io

structure IOBuffer where
  bytes : List UInt8
  lockDepth : Nat := 0
  context : List (String × String) := []
  annotations : List String := []

def IOResult (E A : Type) := Except E A

inductive PrintArg (C X : Type) where
  | char (value : C)
  | string (bytes : List UInt8)
  | value (value : X)


inductive Context where
  | none
  | pair (key : String) (value : String)
  | tuple (pairs : List (String × String))
  | io (stream : IOBuffer)

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

structure ByteView where
  parent : List UInt8
  first : Nat
  last : Nat

structure IOBufferView where
  parent : List UInt8
  first : Nat
  length : Nat
  writable : Bool

structure StringBuilder where
  bytes : List UInt8

structure RegionAnnotation where
  first : Nat
  last : Nat
  annotation : String

structure AnnotatedText where
  bytes : List UInt8
  annotations : List RegionAnnotation

inductive CancelToken where
  | default
  | explicit (id : Nat)
  deriving DecidableEq
inductive JoinParams (X : Type) where
  | none
  | delim (value : X)
  | delimLast (delim last : X)

inductive Joined where
  | plain (bytes : List UInt8)
  | annotated (text : AnnotatedText)

def Joined.bytes : Joined → List UInt8
  | .plain bs => bs
  | .annotated text => text.bytes

structure IOOps (C E : Type) where
  writeBytes : IOBuffer → List UInt8 → Except E IOBuffer
  writeBytesAppend : ∀ io bs io', writeBytes io bs = .ok io' → io'.bytes = io.bytes ++ bs
  writeBytesPreservesLock : ∀ io bs io', writeBytes io bs = .ok io' →
    io'.lockDepth = io.lockDepth
  writeBytesPreservesContext : ∀ io bs io', writeBytes io bs = .ok io' →
    io'.context = io.context
  printChar : IOBuffer → C → Except E IOBuffer
  printCharBytes : C → List UInt8
  printCharAppend : ∀ io c io', printChar io c = .ok io' →
    io'.bytes = io.bytes ++ printCharBytes c
  printCharPreservesLock : ∀ io c io', printChar io c = .ok io' →
    io'.lockDepth = io.lockDepth
  printCharPreservesContext : ∀ io c io', printChar io c = .ok io' →
    io'.context = io.context
  writeChar : IOBuffer → C → Except E (IOBuffer × Int)
  charBytes : C → List UInt8
  writeCharAppend : ∀ io c io' n, writeChar io c = .ok (io', n) →
    io'.bytes = io.bytes ++ charBytes c ∧ n = Int.ofNat (charBytes c).length
  writeCharPreservesLock : ∀ io c io' n, writeChar io c = .ok (io', n) →
    io'.lockDepth = io.lockDepth
  writeCharPreservesContext : ∀ io c io' n, writeChar io c = .ok (io', n) →
    io'.context = io.context
  showOne : {X : Type} → IOBuffer → X → IOBuffer × Except E Unit
  showMany : {X : Type} → IOBuffer → List X → IOBuffer × Except E Unit
  showBytes : {X : Type} → List (String × String) → X → List UInt8
  showManyBytes : {X : Type} → List (String × String) → List X → List UInt8
  showManyAppend : ∀ {X : Type} io (xs : List X) out result,
    showMany io xs = (out, result) → result = .ok () →
      out.bytes = io.bytes ++ showManyBytes io.context xs
  showAppend : ∀ {X : Type} io (x : X) out result,
    showOne io x = (out, result) → result = .ok () →
      out.bytes = io.bytes ++ showBytes io.context x
  showOnePreservesLock : ∀ {X : Type} io (x : X) out result,
    showOne io x = (out, result) → out.lockDepth = io.lockDepth
  showManyPreservesLock : ∀ {X : Type} io (xs : List X) out result,
    showMany io xs = (out, result) → out.lockDepth = io.lockDepth
  showOnePreservesContext : ∀ {X : Type} io (x : X) out result,
    showOne io x = (out, result) → out.context = io.context
  showManyPreservesContext : ∀ {X : Type} io (xs : List X) out result,
    showMany io xs = (out, result) → out.context = io.context
  lock : IOBuffer → IOBuffer
  unlock : IOBuffer → IOBuffer
  lockPairLaw : ∀ io, (unlock (lock io)).lockDepth = io.lockDepth
  lockPreservesContext : ∀ io, (lock io).context = io.context
  unlockPreservesContext : ∀ io, (unlock io).context = io.context
  newBuffer : {I : Type} → I → IOBuffer
  newBufferLaw : ∀ {I : Type} (hint : I), (newBuffer hint).bytes = [] ∧
    (newBuffer hint).lockDepth = 0 ∧ (newBuffer hint).context = [] ∧
    (newBuffer hint).annotations = []
  takeString : IOBuffer → Except E (List UInt8)
  takeStringExact : ∀ io bs, takeString io = .ok bs → bs = io.bytes
  contextPair : IOBuffer → String → String → IOBuffer
  contextPairLaw : ∀ io key value,
    (contextPair io key value).context = (key, value) :: io.context
  contextPairPreservesStream : ∀ io key value,
    (contextPair io key value).bytes = io.bytes ∧
      (contextPair io key value).lockDepth = io.lockDepth
  contextTuple : IOBuffer → List (String × String) → IOBuffer
  contextTupleLaw : ∀ io pairs,
    (contextTuple io pairs).context = pairs.reverse ++ io.context
  contextTuplePreservesStream : ∀ io pairs,
    (contextTuple io pairs).bytes = io.bytes ∧
      (contextTuple io pairs).lockDepth = io.lockDepth
  contextEnv : {Env : Type} → IOBuffer → Env → IOBuffer
  environmentProperties : {Env : Type} → Env → List (String × String)
  contextEnvLaw : ∀ {Env : Type} io (env : Env),
    (contextEnv io env).context = environmentProperties env ++ io.context
  contextEnvPreservesStream : ∀ {Env : Type} io (env : Env),
    (contextEnv io env).bytes = io.bytes ∧ (contextEnv io env).lockDepth = io.lockDepth
  contextIO : IOBuffer → IOBuffer → IOBuffer
  contextIOLaw : ∀ io parent, (contextIO io parent).context = parent.context
  contextIOPreservesStream : ∀ io parent,
    (contextIO io parent).bytes = io.bytes ∧ (contextIO io parent).lockDepth = io.lockDepth
  isFloat64 : {X : Type} → X → Bool
  isFloat32 : {X : Type} → X → Bool
  isString : {X : Type} → X → Bool
  isSubStringString : {X : Type} → X → Bool
  isChar : {X : Type} → X → Bool
  isUInt64 : {X : Type} → X → Bool
  isUInt32 : {X : Type} → X → Bool
  isInt64 : {X : Type} → X → Bool
  isInt32 : {X : Type} → X → Bool
  ndigits : {X : Type} → X → Nat
  isNegative : {X : Type} → X → Bool
  symbolString : JuliaSymbol → List UInt8
  symbolStringLaw : ∀ symbol, symbolString symbol = symbol.name
  chars : {S : Type} → S → List C
  stringBytes : {S : Type} → S → List UInt8
  stringBytesByteList : ∀ bs, stringBytes (S := List UInt8) bs = bs
  stringValid : {S : Type} → S → Bool
  lastindex : {S : Type} → S → Nat
  sizeof : {S : Type} → S → Nat
  utf8Size : C → Nat
  charCode : C → Nat
  equalChar : C → C → Bool
  fromAscii : Nat → C
  isAscii : C → Bool
  isPrint : C → Bool
  isOverlong : C → Bool
  isMalformed : C → Bool
  isHexDigit : C → Bool
  contains : {Q : Type} → Q → C → Bool
  containsEmpty : ∀ c, contains ([] : List C) c = false
  containsSingleton : ∀ c, contains [c] c = true
  hexString : Nat → Nat → List UInt8
  malformedBytes : C → List Nat
  decimalBytes : Int → List UInt8
  devnull : IOBuffer
  charDisplay : C → String
  argumentError : String → E
  memoryBytes : Nat → Nat → List UInt8
  unsafeWriteDefault : IOBuffer → Nat → Nat → Except E (IOBuffer × Int)
  unsafeWriteCancel : IOBuffer → Nat → Nat → CancelToken → Except E (IOBuffer × Int)
  unsafeWriteAppend : ∀ io ptr n io' count, unsafeWriteDefault io ptr n = .ok (io', count) →
    io'.bytes = io.bytes ++ memoryBytes ptr n
  unsafeWriteCancelAppend : ∀ io ptr n cancel io' count,
    unsafeWriteCancel io ptr n cancel = .ok (io', count) →
      io'.bytes = io.bytes ++ memoryBytes ptr n
  unsafeWritePreservesContext : ∀ io ptr n io' count,
    unsafeWriteDefault io ptr n = .ok (io', count) → io'.context = io.context
  unsafeWriteCancelPreservesContext : ∀ io ptr n cancel io' count,
    unsafeWriteCancel io ptr n cancel = .ok (io', count) → io'.context = io.context
  unsafeWriteDefaultCount : ∀ io ptr n io' count,
    unsafeWriteDefault io ptr n = .ok (io', count) → count = Int.ofNat n
  unsafeWriteCancelCount : ∀ io ptr n cancel io' count,
    unsafeWriteCancel io ptr n cancel = .ok (io', count) → count = Int.ofNat n
  unsafeWritePreservesLock : ∀ io ptr n io' count,
    unsafeWriteDefault io ptr n = .ok (io', count) → io'.lockDepth = io.lockDepth
  unsafeWriteCancelPreservesLock : ∀ io ptr n cancel io' count,
    unsafeWriteCancel io ptr n cancel = .ok (io', count) → io'.lockDepth = io.lockDepth
  pointer : {S : Type} → S → Nat
  preserve : {S : Type} → S → (Unit → Except E (IOBuffer × Int)) → Except E (IOBuffer × Int)
  pointerBytes : {S : Type} → (s : S) →
    memoryBytes (pointer (S := S) s) (sizeof (S := S) s) = stringBytes (S := S) s
  preserveLaw : {S : Type} → (s : S) →
    (f : Unit → Except E (IOBuffer × Int)) → preserve (S := S) s f = f ()
  bufferLimit : IOBuffer → Bool
  displayCols : IOBuffer → Nat
  typeinfoNothing : IOBuffer → Bool
  checkTextWidth : {S : Type} → S → Nat → Bool
  codeunitIsUInt8 : {S : Type} → S → Bool
  ncodeunits : {S : Type} → S → Nat
  truncateBoundaries : {S : Type} → S → Nat → List UInt8 → Nat × Nat
  nextind : {S : Type} → S → Nat → Nat
  prevind : {S : Type} → S → Nat → Nat
  slice : {S : Type} → S → Nat → Nat → S
  textwidth : {S : Type} → S → Nat → Nat → Nat
  printStyled : IOBuffer → List UInt8 → Except E IOBuffer
  printStyledContainsText : ∀ io text out,
    printStyled io text = .ok out →
      ∃ before after, out.bytes = io.bytes ++ before ++ text ++ after
  iteratorItems : {I X : Type} → I → List X
  iteratorIsTuple : {I : Type} → I → Bool
  defaultEltypeConcrete : {I : Type} → I → Bool
  defaultEltypeAnnotated : {I : Type} → I → Bool
  anyAnnotated : {X : Type} → List X → Bool
  tupleAnyAnnotated : {T : Type} → T → Bool
  newAnnotatedBuffer : IOBuffer
  hasAnnotations : IOBuffer → Bool
  seekStart : IOBuffer → IOBuffer
  readAnnotated : IOBuffer → Except E Joined
  takeBufferString : IOBuffer → Except E (List UInt8)
  unsafeWrap : JuliaString → ByteView
  unsafeWrapLaw : ∀ s, unsafeWrap s = ⟨s.bytes, 1, s.bytes.length⟩
  viewBytes : ByteView → Nat → Nat → ByteView
  viewBytesLaw : ∀ view first last,
    viewBytes view first last = ⟨view.parent, first, last⟩
  ioBuffer : ByteView → IOBufferView
  ioBufferLaw : ∀ view,
    (ioBuffer view).parent = view.parent ∧
    (ioBuffer view).first = view.first ∧
    (ioBuffer view).length = if view.last < view.first then 0 else view.last - view.first + 1
  ioBufferWritableLaw : ∀ view, (ioBuffer view).writable = false
  arrayLength : {V : Type} → V → Nat
  arrayChars : {V : Type} → V → List C
  arrayLengthLaw : ∀ {V : Type} (v : V), arrayLength v = (arrayChars v).length
  newString : Nat → StringBuilder
  unsafeStringChar : StringBuilder → C → Nat → StringBuilder × Nat
  unsafeStringCharLaw : ∀ out c offset out' count,
    unsafeStringChar out c offset = (out', count) →
    count = utf8Size c ∧
      out'.bytes = out.bytes.take (offset - 1) ++ charBytes c ++
        out.bytes.drop (offset - 1 + (charBytes c).length)
  stringValue : StringBuilder → List UInt8
  stringValueLaw : ∀ out, stringValue out = out.bytes
  annotatedType : Bool
  isAnnotatedChar : C → Bool
  unwrappedChars : {V : Type} → V → List C
  charAnnotations : C → List String
  constructAnnotated : List UInt8 → List RegionAnnotation → AnnotatedText
  integerValue : {I : Type} → I → Int
  integerDiv : Int → Int → Except E Int
  divisionError : E
  integerDivZeroLaw : ∀ a, integerDiv a 0 = .error divisionError
  integerDivLaw : ∀ a b, b ≠ 0 → integerDiv a b = .ok (a.tdiv b)

/-! ## `print`, `println`, `sprint`, and string construction -/

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
-/
def printOne {C E X : Type} (ops : IOOps C E) (io : IOBuffer) (x : X) :
    IOBuffer × Except E Unit :=
  let locked := ops.lock io
  let (written, result) := ops.showOne locked x
  (ops.unlock written, result)

def printOneResult {C E X : Type} (ops : IOOps C E) (io : IOBuffer) (x : X) :
    Except E IOBuffer :=
  let (written, result) := printOne ops io x
  result.map (fun _ => written)

/--
Julia source: base/strings/io.jl:242-245 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::IO, s::Union{String,SubString{String}}; cancel::CancelTokenArg=DEFAULT_CANCEL) =
    cancel === DEFAULT_CANCEL ?
        GC.@preserve(s, (unsafe_write(io, pointer(s), reinterpret(UInt, sizeof(s))) % Int)::Int) :
        GC.@preserve(s, (unsafe_write(io, pointer(s), reinterpret(UInt, sizeof(s)); cancel) % Int)::Int)
```
-/
def writeConcreteString {C E S : Type} (ops : IOOps C E) (io : IOBuffer) (s : S)
    (cancel : CancelToken := .default) : Except E (IOBuffer × Int) := do
  let ptr := ops.pointer s
  ops.preserve s fun _ =>
    if cancel = .default then ops.unsafeWriteDefault io ptr (ops.sizeof s)
    else ops.unsafeWriteCancel io ptr (ops.sizeof s) cancel

def writeString (ops : IOOps C E) (io : IOBuffer) (bytes : List UInt8)
    (cancel : CancelToken) : Except E (IOBuffer × Int) :=
  writeConcreteString ops io bytes cancel

/--
Julia source: base/strings/io.jl:246-246 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, s::Union{String,SubString{String}}) = (write(io, s); nothing)
```
-/
def printString (ops : IOOps C E) (io : IOBuffer) (bytes : List UInt8) : Except E IOBuffer := do
  let (written, _) ← writeConcreteString ops io bytes .default
  pure written

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
-/
def printArgs {C E X : Type} (ops : IOOps C E) (io : IOBuffer) (args : List (PrintArg C X)) :
    IOBuffer × Except E Unit := Id.run do
  let locked := ops.lock io
  let rec loop (s : IOBuffer) : List (PrintArg C X) → IOBuffer × Except E Unit
    | [] => (s, .ok ())
    | .value x :: xs =>
        let (s, result) := printOne ops s x
        match result with
        | .error e => (s, .error e)
        | .ok _ => loop s xs
    | .char c :: xs =>
        match ops.printChar s c with
        | .error e => (s, .error e)
        | .ok s => loop s xs
    | .string bytes :: xs =>
        match printString ops s bytes with
        | .error e => (s, .error e)
        | .ok s => loop s xs
  let (written, result) := loop locked args
  return (ops.unlock written, result)

def printArgsResult {C E X : Type} (ops : IOOps C E) (io : IOBuffer)
    (args : List (PrintArg C X)) : Except E IOBuffer :=
  let (written, result) := printArgs ops io args
  result.map (fun _ => written)

/--
Julia source: base/strings/io.jl:77-77 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
println(io::IO, xs...) = print(io, xs..., "\n")
```
-/
def println {C E X : Type} (ops : IOOps C E) (io : IOBuffer)
    (args : List (PrintArg C X)) : IOBuffer × Except E Unit :=
  printArgs ops io (args ++ [.string [10]])

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
def sprint {C E X I R : Type} (ops : IOOps C E)
    (f : IOBuffer → List X → Except E (IOBuffer × R)) (args : List X)
    (context : Context) (sizehint : I) : Except E (List UInt8) := do
  let s := ops.newBuffer sizehint
  let io := match context with
    | .tuple pairs => ops.contextTuple s pairs
    | .none => s
    | .pair key value => ops.contextPair s key value
    | .io parent => ops.contextIO s parent
  let (written, _) ← f io args
  ops.takeString written

def bufferCallback {E X : Type}
    (f : IOBuffer → List X → Except E IOBuffer) :
    IOBuffer → List X → Except E (IOBuffer × Unit) :=
  fun io args => do
    let written ← f io args
    pure (written, ())

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
-/
def strSizehintMethod {C E X : Type} (ops : IOOps C E) (x : X) : Nat :=
  if ops.isFloat64 x then 20
  else if ops.isFloat32 x then 12
  else if ops.isString x || ops.isSubStringString x then ops.sizeof x
  else if ops.isChar x then ops.ncodeunits x
  else if ops.isUInt64 x || ops.isUInt32 x then ops.ndigits x
  else if ops.isInt64 x || ops.isInt32 x then
    ops.ndigits x + if ops.isNegative x then 1 else 0
  else 8

def printArgSizehint {C E X : Type} (ops : IOOps C E) : PrintArg C X → Nat
  | .char c => ops.ncodeunits c
  | .string bytes => bytes.length
  | .value x => strSizehintMethod ops x

def printArg {C E X : Type} (ops : IOOps C E) (io : IOBuffer) :
    PrintArg C X → Except E IOBuffer
  | .char c => ops.printChar io c
  | .string bytes => printString ops io bytes
  | .value x => printOneResult ops io x

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
-/
def printToString {C E X : Type} (ops : IOOps C E) (args : List (PrintArg C X)) :
    Except E (List UInt8) := do
  if args.isEmpty then return []
  let mut size := 0
  for arg in args do
    size := size + printArgSizehint ops arg
  let mut output := ops.newBuffer size
  for arg in args do
    output ← printArg ops output arg
  ops.takeString output

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
-/
def stringWithEnv {C E X Env : Type} (ops : IOOps C E) (env : Env)
    (args : List (PrintArg C X)) : Except E (List UInt8) := do
  if args.isEmpty then return []
  let mut size := 0
  for arg in args do
    size := size + printArgSizehint ops arg
  let mut output := ops.contextEnv (ops.newBuffer size) env
  for arg in args do
    output ← printArg ops output arg
  ops.takeString output

/--
Julia source: base/strings/io.jl:186-186 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
string(xs...) = print_to_string(xs...)
```
-/
def string {C E X : Type} (ops : IOOps C E) (args : List (PrintArg C X)) :
    Except E (List UInt8) :=
  printToString ops args

/--
Julia source: base/strings/io.jl:188-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
string(a::Symbol) = String(a)
```
-/
def stringSymbol {C E : Type} (ops : IOOps C E) (name : JuliaSymbol) : List UInt8 :=
  ops.symbolString name

/--
Julia source: base/strings/io.jl:192-192 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(io::IO, s::AbstractString) = for c in s; print(io, c); end
```
-/
def printAbstractString {C E S : Type} (ops : IOOps C E) (io : IOBuffer) (s : S) :
    Except E IOBuffer := do
  let mut output := io
  for c in ops.chars s do
    output ← ops.printChar output c
  pure output

/--
Julia source: base/strings/io.jl:193-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(io::IO, s::AbstractString) = (len = 0; for c in s; len += Int(write(io, c))::Int; end; len)
```
-/
def writeAbstractString {C E S : Type} (ops : IOOps C E) (io : IOBuffer) (s : S) :
    Except E (IOBuffer × Int) := do
  let mut output := io
  let mut len : Int := 0
  for c in ops.chars s do
    let (next, count) ← ops.writeChar output c
    output := next
    len := len + count
  pure (output, len)
def showOneCapture {C E X : Type} (ops : IOOps C E) :
    IOBuffer → List X → Except E (IOBuffer × Unit)
  | io, [x] =>
      let (written, result) := ops.showOne io x
      result.map (fun value => (written, value))
  | io, _ => .ok (io, ())
/--
Julia source: base/strings/io.jl:284-284 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
repr(x; context=nothing) = sprint(show, x; context=context)
```
-/
def repr {C E X : Type} (ops : IOOps C E) (x : X) (context : Context) :
    Except E (List UInt8) :=
  sprint ops (showOneCapture ops) [x] context (0 : Nat)

/--
Julia source: base/strings/io.jl:286-286 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
limitrepr(x) = repr(x, context = :limit=>true)
```
-/
def limitrepr {C E X : Type} (ops : IOOps C E) (x : X) :
    Except E (List UInt8) :=
  repr ops x (.pair "limit" "true")

/--
Julia source: base/strings/io.jl:306-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IOBuffer(str::String) = IOBuffer(unsafe_wrap(Vector{UInt8}, str))
```
-/
def ioBufferString {C E : Type} (ops : IOOps C E) (str : JuliaString) : IOBufferView :=
  ops.ioBuffer (ops.unsafeWrap str)

/--
Julia source: base/strings/io.jl:307-307 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
IOBuffer(s::SubString{String}) = IOBuffer(view(unsafe_wrap(Vector{UInt8}, s.string), s.offset + 1 : s.offset + sizeof(s)))
```
-/
def ioBufferSubString {C E : Type} (ops : IOOps C E) (s : JuliaSubString) : IOBufferView :=
  ops.ioBuffer (ops.viewBytes (ops.unsafeWrap s.string) (s.offset + 1)
    (s.offset + s.byteCount))

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
-/
def joinIO4 {C E I X : Type} (ops : IOOps C E) (io : IOBuffer)
    (iterator : I) (delim last : X) : Except E IOBuffer := do
  let mut first := true
  let mut previous : Option X := none
  let mut output := io
  for item in ops.iteratorItems (I := I) (X := X) iterator do
    match previous with
    | none => pure ()
    | some value => do
        if first then
          first := false
        else
          output ← printOneResult ops output delim
        output ← printOneResult ops output value
    previous := some item
  match previous with
  | none => pure output
  | some value => do
      if !first then output ← printOneResult ops output last
      printOneResult ops output value

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
-/
def joinIO3 {C E I X : Type} (ops : IOOps C E) (io : IOBuffer)
    (iterator : I) (delim : X) : Except E IOBuffer := do
  let mut first := true
  let mut output := io
  for item in ops.iteratorItems (I := I) (X := X) iterator do
    if first then
      first := false
    else
      output ← printOneResult ops output delim
    output ← printOneResult ops output item
  pure output

def joinIOPlainItems {C E X : Type} (ops : IOOps C E) (io : IOBuffer) : List X →
    Except E IOBuffer
  | [] => .ok io
  | item :: rest => do
      let io ← printOneResult ops io item
      joinIOPlainItems ops io rest

def joinIOParams {C E I X : Type} (ops : IOOps C E) (io : IOBuffer)
    (iterator : I) (params : JoinParams X) : Except E IOBuffer :=
  match params with
  | .none => joinIOPlainItems (X := X) ops io (ops.iteratorItems (I := I) (X := X) iterator)
  | .delim delim => joinIO3 ops io iterator delim
  | .delimLast delim last => joinIO4 ops io iterator delim last

def joinArgsAnnotated {C E X : Type} (ops : IOOps C E) : JoinParams X → Bool
  | .none => false
  | .delim d => ops.anyAnnotated [d]
  | .delimLast d l => ops.anyAnnotated [d, l]

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
-/
def joinPreserveGeneric {C E I X : Type} (ops : IOOps C E) (iterator : I)
    (params : JoinParams X) : Except E Joined := do
  let concrete := ops.defaultEltypeConcrete iterator
  if concrete && !ops.defaultEltypeAnnotated iterator && !joinArgsAnnotated ops params then
    let out ← sprint (X := Unit) ops (bufferCallback fun io _ =>
      joinIOParams ops io iterator params) ([] : List Unit) .none (0 : Nat)
    return .plain out
  let io ← joinIOParams ops ops.newAnnotatedBuffer iterator params
  if concrete || ops.hasAnnotations io then
    ops.readAnnotated (ops.seekStart io)
  else
    return .plain (← ops.takeBufferString io)

/--
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
-/
def joinPreserveTuple {C E T X : Type} (ops : IOOps C E) (iterator : T)
    (params : JoinParams X) : Except E Joined := do
  if !ops.tupleAnyAnnotated iterator && !joinArgsAnnotated ops params then
    let out ← sprint (X := Unit) ops (bufferCallback fun io _ =>
      joinIOParams ops io iterator params) ([] : List Unit) .none (0 : Nat)
    return .plain out
  let io ← joinIOParams ops ops.newAnnotatedBuffer iterator params
  ops.readAnnotated (ops.seekStart io)
def joinPreserve {C E I X : Type} (ops : IOOps C E) (iterator : I)
    (params : JoinParams X) : Except E Joined :=
  if ops.iteratorIsTuple iterator then joinPreserveTuple ops iterator params
  else joinPreserveGeneric ops iterator params

/--
Julia source: base/strings/io.jl:389-389 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
join(iterator) = _join_preserve_annotations(iterator)
```
-/
def join {C E I X : Type} (ops : IOOps C E) (iterator : I) : Except E Joined :=
  joinPreserve ops iterator (.none : JoinParams X)

/--
Julia source: base/strings/io.jl:390-390 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
join(iterator, delim) = _join_preserve_annotations(iterator, delim)
```
-/
def joinWithDelim {C E I X : Type} (ops : IOOps C E) (iterator : I) (delim : X) :
    Except E Joined :=
  joinPreserve ops iterator (.delim delim)

/--
Julia source: base/strings/io.jl:391-391 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
join(iterator, delim, last) = _join_preserve_annotations(iterator, delim, last)
```
-/
def joinWithLast {C E I X : Type} (ops : IOOps C E) (iterator : I) (delim last : X) :
    Except E Joined :=
  joinPreserve ops iterator (.delimLast delim last)

/--
Julia source: base/strings/io.jl:395-395 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
need_full_hex(c::Union{Nothing, AbstractChar}) = c !== nothing && isxdigit(c)
```
-/
def needFullHex {C E : Type} (ops : IOOps C E) : Option C → Bool
  | none => false
  | some c => ops.isHexDigit c

/--
Julia source: base/strings/io.jl:396-397 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
escape_nul(c::Union{Nothing, AbstractChar}) =
    (c !== nothing && '0' <= c <= '7') ? "\\x00" : "\\0"
```
-/
def escapeNul {C E : Type} (ops : IOOps C E) : Option C → List UInt8
  | some c =>
      if 48 ≤ ops.charCode c && ops.charCode c ≤ 55 then [92, 120, 48, 48]
      else [92, 48]
  | none => [92, 48]

def controlEscape (c : Nat) : Nat :=
  match c with
  | 7 => 97 | 8 => 98 | 9 => 116 | 10 => 110 | 11 => 118 | 12 => 102 | 13 => 114
  | _ => 0


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
-/
def escapeStringIO {C E S Q K : Type} (ops : IOOps C E) (io : IOBuffer) (s : S)
    (esc : Q) (keep : K) (ascii fullhex : Bool) : Except E IOBuffer := do
  let chars := ops.chars s
  let mut remaining := chars
  let mut output := io
  for c in chars do
    let nextChars := match remaining with
      | [] => []
      | _ :: rest => rest
    let next := nextChars.head?
    if ops.contains esc c then
      output ← printArgsResult (X := Unit) ops output
        [.char (ops.fromAscii 92), .char c]
    else if ops.contains keep c then
      output ← printArgsResult (X := Unit) ops output [.char c]
    else if ops.isAscii c then
      if ops.charCode c = 0 then
        output ← printArgsResult (X := Unit) ops output
          [.string (escapeNul ops next)]
      else if ops.charCode c = 27 then
        output ← printArgsResult (X := Unit) ops output [.string [92, 101]]
      else if ops.charCode c = 92 then
        output ← printArgsResult (X := Unit) ops output [.string [92, 92]]
      else if 7 ≤ ops.charCode c && ops.charCode c ≤ 13 then
        output ← printArgsResult (X := Unit) ops output
          [.char (ops.fromAscii 92), .char (ops.fromAscii (controlEscape (ops.charCode c)))]
      else if ops.isPrint c then
        output ← printArgsResult (X := Unit) ops output [.char c]
      else
        output ← printArgsResult (X := Unit) ops output
          [.string [92, 120], .string (ops.hexString (ops.charCode c) 2)]
    else if !ops.isOverlong c && !ops.isMalformed c then
      if !ascii && ops.isPrint c then
        output ← printArgsResult (X := Unit) ops output [.char c]
      else if ops.charCode c ≤ 0x7f then
        output ← printArgsResult (X := Unit) ops output
          [.string [92, 120], .string (ops.hexString (ops.charCode c) 2)]
      else if ops.charCode c ≤ 0xffff then
        let width := if fullhex || needFullHex ops next then 4 else 2
        output ← printArgsResult (X := Unit) ops output
          [.string [92, 117], .string (ops.hexString (ops.charCode c) width)]
      else
        let width := if fullhex || needFullHex ops next then 8 else 4
        output ← printArgsResult (X := Unit) ops output
          [.string [92, 85], .string (ops.hexString (ops.charCode c) width)]
    else
      for byte in ops.malformedBytes c do
        output ← printArgsResult (X := Unit) ops output
          [.string [92, 120], .string (ops.hexString byte 2)]
    remaining := nextChars
  pure output

/--
Julia source: base/strings/io.jl:488-489 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
escape_string(s::AbstractString, esc=('\"',); keep = (), ascii::Bool=false, fullhex::Bool=false) =
    sprint((io)->escape_string(io, s, esc; keep, ascii, fullhex), sizehint=lastindex(s))
```
-/
def escapeString {C E S Q K : Type} (ops : IOOps C E) (s : S)
    (esc : Q) (keep : K) (ascii fullhex : Bool) : Except E (List UInt8) :=
  sprint (X := Unit) ops (bufferCallback fun io _ =>
    escapeStringIO ops io s esc keep ascii fullhex)
    ([] : List Unit) .none (ops.lastindex s)
def escapeStringDefault {C E S : Type} (ops : IOOps C E) (s : S)
    (keep : List C := []) (ascii fullhex : Bool := false) :
    Except E (List UInt8) :=
  escapeString ops s [ops.fromAscii 34] keep ascii fullhex

/--
Julia source: base/strings/io.jl:491-495 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print_quoted(io, s::AbstractString)
    print(io, '"')
    escape_string(io, s, ('\"','$')) #"# work around syntax highlighting problem
    print(io, '"')
end
```
-/
def printQuoted {C E S : Type} (ops : IOOps C E) (io : IOBuffer) (s : S) : Except E IOBuffer := do
  let io ← ops.printChar io (ops.fromAscii 34)
  let io ← escapeStringIO ops io s [ops.fromAscii 34, ops.fromAscii 36] ([] : List C) false false
  ops.printChar io (ops.fromAscii 34)

def hexDigitValue {C E : Type} (ops : IOOps C E) (c : C) : Option Nat :=
  if 48 ≤ ops.charCode c && ops.charCode c ≤ 57 then some (ops.charCode c - 48)
  else if 97 ≤ ops.charCode c && ops.charCode c ≤ 102 then some (ops.charCode c - 97 + 10)
  else if 65 ≤ ops.charCode c && ops.charCode c ≤ 70 then some (ops.charCode c - 65 + 10)
  else none


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
-/
def unescapeStringIO {C E S K : Type} (ops : IOOps C E) (io : IOBuffer) (s : S)
    (keep : K) : Except E IOBuffer := do
  let chars := ops.chars s
  let mut remaining := chars
  let mut skipped := 0
  let mut output := io
  for c in chars do
    if skipped > 0 then
      skipped := skipped - 1
    else
      match remaining with
      | [] => pure ()
      | _ :: rest =>
          remaining := rest
          if ops.charCode c = 92 && !remaining.isEmpty then
            match remaining with
            | [] => pure ()
            | escaped :: tail =>
                remaining := tail
                skipped := skipped + 1
                if ops.contains keep escaped then
                  output ← printArgsResult (X := Unit) ops output
                    [.char (ops.fromAscii 92), .char escaped]
                else if ops.charCode escaped = 120 || ops.charCode escaped = 117 ||
                    ops.charCode escaped = 85 then
                  let digits := if ops.charCode escaped = 120 then 2 else
                    if ops.charCode escaped = 117 then 4 else 8
                  let mut k := 0
                  let mut code := 0
                  let mut parsing := true
                  for _ in List.range (digits + 1) do
                    if parsing then
                      k := k + 1
                      if k ≤ digits then
                        match remaining with
                        | [] => parsing := false
                        | nextChar :: restDigits =>
                            match hexDigitValue ops nextChar with
                            | some digit =>
                                code := code * 16 + digit
                                remaining := restDigits
                                skipped := skipped + 1
                            | none => parsing := false
                      else
                        parsing := false
                  if k = 1 || code > 0x10ffff then
                    let u := if digits = 4 then "u" else "U"
                    throw (ops.argumentError (if digits = 2 then
                      "invalid hex (\\x) escape sequence" else
                      "invalid unicode (\\" ++ u ++ ") escape sequence"))
                  else if digits = 2 then
                    output ← ops.writeBytes output [code.toUInt8]
                  else
                    output ← ops.printChar output (ops.fromAscii code)
                else if 48 ≤ ops.charCode escaped && ops.charCode escaped ≤ 55 then
                  let mut code := ops.charCode escaped - 48
                  let mut parsing := true
                  for _ in List.range 2 do
                    if parsing then
                      match remaining with
                      | [] => parsing := false
                      | nextChar :: restDigits =>
                          if 48 ≤ ops.charCode nextChar && ops.charCode nextChar ≤ 55 then
                            code := code * 8 + ops.charCode nextChar - 48
                            remaining := restDigits
                            skipped := skipped + 1
                          else
                            parsing := false
                  if code > 255 then
                    throw (ops.argumentError "octal escape sequence out of range")
                  else
                    output ← ops.writeBytes output [code.toUInt8]
                else
                  let code := ops.charCode escaped
                  let value :=
                    if code = 97 then some 7 else if code = 98 then some 8 else
                    if code = 116 then some 9 else if code = 110 then some 10 else
                    if code = 118 then some 11 else if code = 102 then some 12 else
                    if code = 114 then some 13 else if code = 101 then some 27 else
                    if code = 92 || code = 34 then some code else none
                  match value with
                  | some byte => output ← ops.printChar output (ops.fromAscii byte)
                  | none => throw (ops.argumentError
                      ("invalid escape sequence " ++ String.singleton '\\' ++
                        ops.charDisplay escaped))
          else
            output ← ops.printChar output c
  pure output

/--
Julia source: base/strings/io.jl:592-593 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unescape_string(s::AbstractString, keep = ()) =
    sprint(unescape_string, s, keep; sizehint=lastindex(s))
```
-/
def unescapeString {C E S K : Type} (ops : IOOps C E) (s : S) (keep : K) :
    Except E (List UInt8) :=
  sprint (X := Unit) ops (bufferCallback fun io _ =>
    unescapeStringIO ops io s keep)
    ([] : List Unit) .none (ops.lastindex s)
def unescapeStringDefault {C E S : Type} (ops : IOOps C E) (s : S) :
    Except E (List UInt8) :=
  unescapeString ops s ([] : List C)

/--
Julia source: base/strings/io.jl:194-194 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, s::AbstractString) = print_quoted(io, s)
```
-/
def showAbstractString {C E S : Type} (ops : IOOps C E) (io : IOBuffer) (s : S) :
    Except E IOBuffer :=
  printQuoted ops io s

/--
Julia source: base/strings/io.jl:217-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    skip_text(skip) = " ⋯ $skip $units ⋯ "
```
-/
def skipText {C E : Type} (ops : IOOps C E) (units : List UInt8) (skip : Int) :
    List UInt8 :=
  [32, 0xe2, 0x8b, 0xaf, 32] ++ ops.decimalBytes skip ++ [32] ++ units ++
    [32, 0xe2, 0x8b, 0xaf, 32]

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
-/
def showTextPlain {C E S : Type} (ops : IOOps C E) (io : IOBuffer) (str : S)
    (limit : Option Int) : Except E IOBuffer := do
  let limit := match limit with
    | some l => some l
    | none =>
        if !ops.bufferLimit io then none
        else
          let l := Int.ofNat (max 20 (ops.displayCols io))
          some (if ops.typeinfoNothing io then l * 7 else l)
  match limit with
  | none => showAbstractString ops io str
  | some limit =>
      let limit := max 0 (limit - 2)
      if ops.checkTextWidth str limit.toNat then
        showAbstractString ops io str
      else
        let units := if ops.codeunitIsUInt8 str then
          [98, 121, 116, 101, 115] else [99, 111, 100, 101, 32, 117, 110, 105, 116, 115]
        let maxReplacement := skipText ops units (Int.ofNat (ops.ncodeunits str * 100))
        let (head, tail) := ops.truncateBoundaries str limit.toNat maxReplacement
        let afterHead := ops.nextind str head
        let n := Int.ofNat tail - Int.ofNat afterHead
        let replacement := skipText ops units n
        let t := Int.ofNat replacement.length
        if 4 * t ≤ n || t ≤ n &&
            t ≤ Int.ofNat (ops.textwidth str afterHead (ops.prevind str tail)) then
          let io ← showAbstractString ops io (ops.slice str 1 head)
          let io ← ops.printStyled io replacement
          showAbstractString ops io (ops.slice str tail (ops.lastindex str))
        else
          showAbstractString ops io str
structure QuoteNode where
  bytes : CodeUnitsVector

inductive Unindented (S : Type) where
  | original (value : S)
  | built (bytes : List UInt8)
inductive RawStringResult (S : Type) where
  | original (value : S)
  | copied (bytes : List UInt8)

/--
Julia source: base/strings/io.jl:613-616 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro b_str(s::String)
    v = codeunits(unescape_string(s))
    QuoteNode(v)
end
```
-/
def bStr {C E : Type} (ops : IOOps C E) (s : JuliaString) : Except E QuoteNode := do
  let bytes ← unescapeString ops s ([] : List C)
  pure ⟨⟨bytes⟩⟩

/--
Julia source: base/strings/io.jl:643-643 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
macro raw_str(s); s; end
```
-/
def rawStr {S : Type} (s : S) : S := s


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
-/
def escapeRawStringIO {C E S : Type} (ops : IOOps C E) (io : IOBuffer)
    (str : S) (delim : C) : Except E (IOBuffer × Nat) := do
  let mut output := io
  let mut escapes := 0
  let mut total := 0
  for c in ops.chars str do
    if ops.charCode c = 92 then
      escapes := escapes + 1
    else
      if ops.equalChar c delim then
        escapes := escapes + 1
        total := total + escapes
        for _ in List.range escapes do
          let (next, _) ← ops.writeChar output (ops.fromAscii 92)
          output := next
      escapes := 0
    let (next, _) ← ops.writeChar output c
    output := next
  total := total + escapes
  for _ in List.range escapes do
    let (next, _) ← ops.writeChar output (ops.fromAscii 92)
    output := next
  pure (output, total)

/--
Julia source: base/strings/io.jl:694-697 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function escape_raw_string(str::AbstractString, delim::Char='"')
    total = escape_raw_string(devnull, str, delim) # check whether the string even needs to be copied and how much to allocate for it
    return total == 0 ? str : sprint(escape_raw_string, str, delim; sizehint = sizeof(str) + total)
end
```
-/
def escapeRawString {C E S : Type} (ops : IOOps C E) (str : S) (delim : C) :
    Except E (RawStringResult S) := do
  let (_, total) ← escapeRawStringIO ops ops.devnull str delim
  if total = 0 then pure (.original str)
  else do
    let bytes ← sprint (X := Unit) ops (bufferCallback fun io _ => do
      let (io, _) ← escapeRawStringIO ops io str delim
      pure io) ([] : List Unit) .none (ops.sizeof str + total)
    pure (.copied bytes)

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
-/
def indentation {C E S I : Type} (ops : IOOps C E) (str : S) (tabwidth : I) :
    Except E (Int × Bool) := do
  let width := ops.integerValue tabwidth
  let mut count : Int := 0
  for ch in ops.chars str do
    if ops.charCode ch = 32 then
      count := count + 1
    else if ops.charCode ch = 9 then
      let quotient ← ops.integerDiv (count + width) width
      count := quotient * width
    else
      return (count, false)
  return (count, true)


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
-/
def unindent {C E S I : Type} (ops : IOOps C E) (str : S) (indent : Int)
    (tabwidth : I) : Except E (Unindented S) := do
  if indent = 0 then return .original str
  let width := ops.integerValue tabwidth
  let mut output := ops.newBuffer (ops.sizeof str)
  let mut cutting := true
  let mut column : Int := 0
  for c in ops.chars str do
    if cutting then
      if ops.charCode c = 32 then
        column := column + 1
      else if ops.charCode c = 9 then
        let quotient ← ops.integerDiv (column + width) width
        column := quotient * width
      else if ops.charCode c = 10 then
        for _ in List.range (column - indent).toNat do
          output ← ops.printChar output (ops.fromAscii 32)
        column := 0
        output ← ops.printChar output c
      else
        cutting := false
        for _ in List.range (column - indent).toNat do
          output ← ops.printChar output (ops.fromAscii 32)
        column := column + 1
        output ← ops.printChar output c
    else if ops.charCode c = 9 then
      let quotient ← ops.integerDiv (column + width) width
      let updated := quotient * width
      for _ in List.range (updated - column).toNat do
        output ← ops.printChar output (ops.fromAscii 32)
      column := updated
    else if ops.charCode c = 10 then
      cutting := true
      column := 0
      output ← ops.printChar output c
    else
      column := column + 1
      output ← ops.printChar output c
  if cutting then
    for _ in List.range (column - indent).toNat do
      output ← ops.printChar output (ops.fromAscii 32)
  return .built (← ops.takeString output)

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
-/
def stringCharArray {C E V : Type} (ops : IOOps C E) (a : V) : List UInt8 :=
  let chars := ops.arrayChars a
  let n := (chars.map ops.utf8Size).sum
  let rec write (out : StringBuilder) (offs : Nat) : List C → StringBuilder
    | [] => out
    | c :: rest =>
        let (out, count) := ops.unsafeStringChar out c offs
        write out (offs + count) rest
  ops.stringValue (write (ops.newString n) 1 chars)

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
-/
def stringAbstractCharArray {C E V : Type} (ops : IOOps C E) (chars : V) :
    Except E (List UInt8) :=
  sprint (X := Unit) ops (bufferCallback fun io _ => do
    let mut output := io
    for c in ops.arrayChars chars do
      output ← ops.printChar output c
    pure output) ([] : List Unit) .none (ops.arrayLength chars)

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
-/
def annotatedString {C E V : Type} (ops : IOOps C E) (chars : V) :
    Except E AnnotatedText := do
  let text ← if ops.annotatedType then
    pure (stringCharArray ops (ops.unwrappedChars chars))
  else
    stringAbstractCharArray ops chars
  let mut annotations : List RegionAnnotation := []
  let mut point := 1
  for c in ops.arrayChars chars do
    if ops.isAnnotatedChar c then
      for annotation in ops.charAnnotations c do
        annotations := annotations ++ [⟨point, point, annotation⟩]
    point := point + ops.utf8Size c
  pure (ops.constructAnnotated text annotations)

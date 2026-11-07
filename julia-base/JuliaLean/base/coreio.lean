import JuliaLean.Core

/-!
# Model of `base/coreio.jl`

`CoreStdIO` and `DevNull` represent this file's three concrete I/O endpoints. Printing and runtime
operations from later-loaded files remain typed interfaces, and Julia's abstract `IO` hierarchy
is not encoded here.
-/

namespace JuliaLean.base.coreio

open JuliaLean

-- These declarations have no method bodies in `coreio.jl`.
-- UNTRANSLATED: `print` is declared here without a method body; the adjacent line sets compiler metadata.
/-
Julia source: base/coreio.jl:3-4 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function print end
typeof(print).name.max_methods = UInt8(1)
```
-/

-- UNTRANSLATED: `show` and `repr` are generic declarations without method bodies here.
/-
Julia source: base/coreio.jl:15-16 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function show end
function repr end
```
-/

/-- Heterogeneous arguments passed through Julia's variadic `print` methods. -/
inductive PrintValue where
  | of {α : Type} (value : α)

/-- Julia's `Core.CoreSTDOUT` and `Core.CoreSTDERR` endpoints. -/
inductive CoreStdIO where
  | stdout
  | stderr
  deriving Repr, DecidableEq

/--
Julia source: base/coreio.jl:18-20 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
struct DevNull <: IO
    DevNull() = new()
end
```
-/
inductive DevNull where
  | new
  deriving Repr, DecidableEq

/-- The I/O endpoints handled in this file's `CoreIO` union. -/
inductive CoreIO where
  | standard (value : CoreStdIO)
  | devNull (value : DevNull)

/--
Julia source: base/coreio.jl:19-19 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    DevNull() = new()
```
-/
def newDevNull : DevNull := .new

/--
Julia source: base/coreio.jl:21-21 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
const devnull = DevNull()
```
-/
def devnull : DevNull := newDevNull

/--
Julia source: base/coreio.jl:6-6 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(x) = print(stdout, x)
```
-/
def printOne {IO α ε : Type}
    (print : IO → List PrintValue → Except ε Unit) (stdout : IO) (x : α) : Except ε Unit :=
  print stdout [.of x]

/--
Julia source: base/coreio.jl:7-7 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(x1, x2) = print(stdout, x1, x2)
```
-/
def printTwo {IO α β ε : Type}
    (print : IO → List PrintValue → Except ε Unit) (stdout : IO) (x : α) (y : β) : Except ε Unit :=
  print stdout [.of x, .of y]

/--
Julia source: base/coreio.jl:8-8 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
println(x) = print(stdout, x, "\n")
```
-/
def printlnOne {IO α ε : Type}
    (print : IO → List PrintValue → Except ε Unit) (stdout : IO) (x : α) : Except ε Unit :=
  print stdout [.of x, .of "\n"]

/--
Julia source: base/coreio.jl:9-9 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
println(x1, x2) = print(stdout, x1, x2, "\n")
```
-/
def printlnTwo {IO α β ε : Type}
    (print : IO → List PrintValue → Except ε Unit) (stdout : IO) (x : α) (y : β) : Except ε Unit :=
  print stdout [.of x, .of y, .of "\n"]

/--
Julia source: base/coreio.jl:11-11 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
print(xs...)   = print(stdout, xs...)
```
-/
def printMany {IO ε : Type}
    (print : IO → List PrintValue → Except ε Unit) (stdout : IO)
    (xs : List PrintValue) : Except ε Unit :=
  print stdout xs

/--
Julia source: base/coreio.jl:12-12 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
println(xs...) = print(stdout, xs..., "\n")  # fewer allocations than `println(stdout, xs...)`
```
-/
def printlnMany {IO ε : Type}
    (print : IO → List PrintValue → Except ε Unit) (stdout : IO)
    (xs : List PrintValue) : Except ε Unit :=
  print stdout (xs ++ [.of "\n"])

/--
Julia source: base/coreio.jl:13-13 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
println(io::IO) = print(io, "\n")
```
-/
def printlnIO {IO ε : Type}
    (print : IO → List PrintValue → Except ε Unit) (io : IO) : Except ε Unit :=
  print io [.of "\n"]

/--
Julia source: base/coreio.jl:22-22 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
write(::DevNull, ::UInt8) = 1
```
-/
def writeDevNull (_io : DevNull) (_byte : JInt .u8) : JInt .i64 := JInt.lit .i64 1

/--
Julia source: base/coreio.jl:23-23 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
unsafe_write(::DevNull, ::Ptr{UInt8}, n::UInt)::Int = n
```
-/
def unsafeWriteDevNull {Ptr ε : Type}
    (assertInt : JInt .u64 → Except ε (JInt .i64))
    (_io : DevNull) (_pointer : Ptr) (n : JInt .u64) : Except ε (JInt .i64) :=
  assertInt n

/--
Julia source: base/coreio.jl:24-24 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
closewrite(::DevNull) = nothing
```
-/
def closewriteDevNull (_io : DevNull) : Unit := ()

/--
Julia source: base/coreio.jl:25-25 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
close(::DevNull) = nothing
```
-/
def closeDevNull (_io : DevNull) : Unit := ()

/--
Julia source: base/coreio.jl:26-26 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
wait_close(::DevNull) = wait()
```
-/
def waitCloseDevNull {ε : Type} (wait : Unit → Except ε Unit)
    (_io : DevNull) : Except ε Unit := wait ()

/--
Julia source: base/coreio.jl:27-27 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
bytesavailable(io::DevNull) = 0
```
-/
def bytesavailableDevNull (_io : DevNull) : JInt .i64 := JInt.lit .i64 0

/-- `CoreIO` is `CoreStdIO` combined with `DevNull`. -/
def standardIO (io : CoreStdIO) : CoreIO := .standard io

/--
Julia source: base/coreio.jl:30-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global write(io::CoreIO, x::UInt8) = Core.write(io, x)
```
-/
def writeCoreIO {ε : Type}
    (coreWrite : CoreStdIO → JInt .u8 → Except ε (JInt .i64))
    (io : CoreStdIO) (x : JInt .u8) : Except ε (JInt .i64) :=
  coreWrite io x

/--
Julia source: base/coreio.jl:31-31 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global unsafe_write(io::CoreIO, x::Ptr{UInt8}, nb::UInt) = Core.unsafe_write(io, x, nb)
```
-/
def unsafeWriteCoreIO {Ptr ε : Type}
    (coreUnsafeWrite : CoreStdIO → Ptr → JInt .u64 → Except ε (JInt .i64))
    (io : CoreStdIO) (pointer : Ptr) (n : JInt .u64) : Except ε (JInt .i64) :=
  coreUnsafeWrite io pointer n

/--
Julia source: base/coreio.jl:34-34 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global read(::CoreIO, ::Type{UInt8}) = throw(EOFError())
```
-/
def readCoreIO {ε : Type} (eofError : ε) (_io : CoreIO) : Except ε (JInt .u8) := .error eofError

/--
Julia source: base/coreio.jl:35-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global isopen(::CoreIO) = true
```
-/
def isopenCoreIO (_io : CoreIO) : Bool := true

/--
Julia source: base/coreio.jl:36-36 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global isreadable(::CoreIO) = false
```
-/
def isreadableCoreIO (_io : CoreIO) : Bool := false

/--
Julia source: base/coreio.jl:37-37 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global iswritable(::CoreIO) = true
```
-/
def iswritableCoreIO (_io : CoreIO) : Bool := true

/--
Julia source: base/coreio.jl:38-38 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global flush(::CoreIO) = nothing
```
-/
def flushCoreIO (_io : CoreIO) : Unit := ()

/--
Julia source: base/coreio.jl:39-39 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global eof(::CoreIO) = true
```
-/
def eofCoreIO (_io : CoreIO) : Bool := true

/--
Julia source: base/coreio.jl:40-40 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    global wait_readnb(::CoreIO, nb::Int) = nothing
```
-/
def waitReadNbCoreIO (_io : CoreIO) (_n : JInt .i64) : Unit := ()

/--
Julia source: base/coreio.jl:43-43 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stdin::IO = devnull
```
-/
def stdin : CoreIO := .devNull devnull

/--
Julia source: base/coreio.jl:44-44 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stdout::IO = Core.stdout
```
-/
def stdout : CoreIO := .standard .stdout

/--
Julia source: base/coreio.jl:45-45 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
stderr::IO = Core.stderr
```
-/
def stderr : CoreIO := .standard .stderr

end JuliaLean.base.coreio

namespace JuliaLean.ShowCov

/-- Julia exceptions thrown by the modelled methods. -/
inductive Err where
  | errorException (msg : String)
  | argumentError (msg : String)
  | keyError (key : String)
  | methodError (fn : String)
  | eofError
  | boundsError
  | inexactError (fn : String)
  | typeError
  deriving Repr, DecidableEq, Inhabited

/-- Julia computations that may throw. -/
abbrev R (α : Type) := Except Err α

instance instDecidableEqR {α : Type} [DecidableEq α] : DecidableEq (R α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .error a, .error b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .ok _, .error _ => isFalse (fun e => by cases e)
  | .error _, .ok _ => isFalse (fun e => by cases e)

/-- Pieces printed to a stream, in order. -/
abbrev Out := List String

/-- The text a list of printed pieces forms. -/
def Out.text (o : Out) : String := String.join o

/-- `string(n::Int)`: decimal digits with a leading `-` for negatives. -/
def intStr (n : Int) : String := toString n

end JuliaLean.ShowCov

namespace JuliaLean.ShowCov.Terminals

open JuliaLean.ShowCov

/-! ## `base/coreio.jl` -/

/-- Streams `print` can target. -/
inductive Stream where
  | stdout | stderr | other (n : Nat)
  deriving DecidableEq, Repr

/-- `print(io, x)` for a value whose print text is `x`: one write of `x` to `io`. -/
def printIO (io : Stream) (xs : List String) : List (Stream × String) := xs.map (io, ·)

/-- `print(x) = print(stdout, x)`, `print(x1, x2)`, `print(xs...)`,
`base/coreio.jl:6-7,11`. -/
def print0 (xs : List String) : List (Stream × String) := printIO .stdout xs
/-- `println(x) = print(stdout, x, "\n")`, `println(x1, x2)`, `println(xs...)`,
`base/coreio.jl:8-9,12`. -/
def println0 (xs : List String) : List (Stream × String) := printIO .stdout (xs ++ ["\n"])
/-- `println(io::IO) = print(io, "\n")`, `base/coreio.jl:13`. -/
def printlnIO (io : Stream) : List (Stream × String) := printIO io ["\n"]

/-- `typemax(Int)` for the `::Int` return conversion. -/
def int64Max : Nat := 2 ^ 63 - 1

/-- `write(::DevNull, ::UInt8) = 1`, `base/coreio.jl:22`. -/
def writeDevNull (_b : UInt8) : Int := 1
/-- `unsafe_write(::DevNull, ::Ptr{UInt8}, n::UInt)::Int = n`: the return
annotation converts `n` to `Int`, `base/coreio.jl:23`. -/
def unsafeWriteDevNull (n : Nat) : R Int :=
  if n ≤ int64Max then .ok n else .error (.inexactError "Int64")
/-- `bytesavailable(io::DevNull) = 0`, `base/coreio.jl:27`. -/
def bytesavailableDevNull : Int := 0

/-- Outcome of a call that may block forever. -/
inductive Wait where
  | returns
  | blocksForever
  deriving DecidableEq, Repr

/-- `closewrite(::DevNull) = nothing`, `close(::DevNull) = nothing`
(`base/coreio.jl:24-25`) return; `wait_close(::DevNull) = wait()`
(`base/coreio.jl:26`) waits on the current task with nothing to wake it. -/
def closewriteDevNull : Wait := .returns
def closeDevNull : Wait := .returns
def waitCloseDevNull : Wait := .blocksForever

/-- `write(io::CoreIO, x::UInt8) = Core.write(io, x)` and
`unsafe_write(io::CoreIO, x::Ptr{UInt8}, nb::UInt) = Core.unsafe_write(io, x, nb)`,
`base/coreio.jl:30-31`: the bytes go to the C stream. -/
def writeCore (bytes : List UInt8) : List UInt8 := bytes

/-- The read-side and status methods shared by `CoreSTDOUT`, `CoreSTDERR` and
`DevNull`, `base/coreio.jl:34-40`. -/
def readCore : R UInt8 := .error .eofError
def isopenCore : Bool := true
def isreadableCore : Bool := false
def iswritableCore : Bool := true
def flushCore : Unit := ()
def eofCore : Bool := true
def waitReadnbCore (_nb : Int) : Unit := ()

/-- `DevNull() = new()`, `base/coreio.jl:19`: the singleton, so every call is the same object. -/
def devNullCtor : Unit := ()

end JuliaLean.ShowCov.Terminals

namespace JuliaLean.ShowCov.Methods.CoreIO

open JuliaLean.ShowCov.Terminals

/-- `print(x) = print(stdout, x)`, `base/coreio.jl:6`. -/
def m6 (x : String) := print0 [x]
/-- `print(x1, x2) = print(stdout, x1, x2)`, `base/coreio.jl:7`. -/
def m7 (x1 x2 : String) := print0 [x1, x2]
/-- `println(x) = print(stdout, x, "\n")`, `base/coreio.jl:8`. -/
def m8 (x : String) := println0 [x]
/-- `println(x1, x2) = print(stdout, x1, x2, "\n")`, `base/coreio.jl:9`. -/
def m9 (x1 x2 : String) := println0 [x1, x2]
/-- `print(xs...) = print(stdout, xs...)`, `base/coreio.jl:11`. -/
def m11 (xs : List String) := print0 xs
/-- `println(xs...) = print(stdout, xs..., "\n")`, `base/coreio.jl:12`. -/
def m12 (xs : List String) := println0 xs
/-- `println(io::IO) = print(io, "\n")`, `base/coreio.jl:13`. -/
def m13 (io : Stream) := printlnIO io
/-- `DevNull() = new()`, `base/coreio.jl:19`. -/
def m19 (_args : Unit) := devNullCtor
/-- `write(::DevNull, ::UInt8) = 1`, `base/coreio.jl:22`. -/
def m22 (b : UInt8) := writeDevNull b
/-- `unsafe_write(::DevNull, ptr, n)::Int = n`, including the Int conversion,
`base/coreio.jl:23`. -/
def m23 (n : Nat) := unsafeWriteDevNull n
/-- `closewrite(::DevNull) = nothing`, `base/coreio.jl:24`. -/
def m24 (_io : Unit) := closewriteDevNull
/-- `close(::DevNull) = nothing`, `base/coreio.jl:25`. -/
def m25 (_io : Unit) := closeDevNull
/-- `wait_close(::DevNull) = wait()`, `base/coreio.jl:26`. -/
def m26 (_io : Unit) := waitCloseDevNull
/-- `bytesavailable(::DevNull) = 0`, `base/coreio.jl:27`. -/
def m27 (_io : Unit) := bytesavailableDevNull
/-- `write(io::CoreIO, x::UInt8) = Core.write(io, x)`, `base/coreio.jl:30`.
The byte list is the observable Core write. -/
def m30 (x : UInt8) := writeCore [x]
/-- `unsafe_write(io::CoreIO, ptr, nb) = Core.unsafe_write(io, ptr, nb)`,
`base/coreio.jl:31`; `bytes` is the pointer range selected by `nb`. -/
def m31 (bytes : List UInt8) := writeCore bytes
/-- `read(::CoreIO, ::Type{UInt8}) = throw(EOFError())`, `base/coreio.jl:34`. -/
def m34 (_io : Stream) := readCore
/-- `isopen(::CoreIO) = true`, `base/coreio.jl:35`. -/
def m35 (_io : Stream) := isopenCore
/-- `isreadable(::CoreIO) = false`, `base/coreio.jl:36`. -/
def m36 (_io : Stream) := isreadableCore
/-- `iswritable(::CoreIO) = true`, `base/coreio.jl:37`. -/
def m37 (_io : Stream) := iswritableCore
/-- `flush(::CoreIO) = nothing`, `base/coreio.jl:38`. -/
def m38 (_io : Stream) := flushCore
/-- `eof(::CoreIO) = true`, `base/coreio.jl:39`. -/
def m39 (_io : Stream) := eofCore
/-- `wait_readnb(::CoreIO, nb) = nothing`, `base/coreio.jl:40`. -/
def m40 (nb : Int) := waitReadnbCore nb

end JuliaLean.ShowCov.Methods.CoreIO

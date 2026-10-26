import JuliaLean.BootCov.IntConv

/-!
Remaining methods of `base/boot.jl` and `base/essentials.jl` (master
`bbfa0ce4150`): the stand-alone `Core` printing functions, identity
conversions, tuple helpers, `Pairs`, small predicates and the `Core` hooks.
-/

namespace JuliaLean.BootCov.Misc

open JuliaLean
open JuliaLean.BootCov
open JuliaLean.BootCov.IntConv

/-! ## `Core` printing, `base/boot.jl:970-1006`

The two `Core` streams write to the runtime's `jl_uv_stdout`/`jl_uv_stderr`; the
state is the byte list written so far to each. `staticShow x` is the output of
`jl_static_show` for `x`, and `utf8 c` the bytes `jl_uv_putc` writes for `c`. -/

inductive CoreIO where
  | stdout
  | stderr
  deriving DecidableEq, Repr

/-- `CoreSTDOUT()` and `CoreSTDERR()`, lines 974-977. -/
def coreSTDOUT : CoreIO := .stdout
def coreSTDERR : CoreIO := .stderr

structure Out where
  out : List Nat
  err : List Nat

/-- `io_pointer(::CoreSTDOUT)` and `io_pointer(::CoreSTDERR)`, lines 981-982: the stream's
runtime handle, given as `(stdoutHandle, stderrHandle)`. -/
def ioPointer (handles : Nat × Nat) : CoreIO → Nat
  | .stdout => handles.1
  | .stderr => handles.2

def emit (io : CoreIO) (bs : List Nat) (s : Out) : Out :=
  match io with
  | .stdout => { s with out := s.out ++ bs }
  | .stderr => { s with err := s.err ++ bs }

/-- `unsafe_write(io, x::Ptr{UInt8}, nb::UInt)` and the `nb::Int` method, lines 984-987:
write the `nb` bytes at `x` (`bytes`) and return `nb`. -/
def unsafeWrite (io : CoreIO) (bytes : List Nat) (nb : Nat) (s : Out) : Nat × Out :=
  (nb, emit io (bytes.take nb) s)

/-- `write(io, x::UInt8)`, lines 988-989. -/
def writeByte (io : CoreIO) (x : Nat) (s : Out) : Nat × Out := (1, emit io [x] s)

/-- `write(io, x::String)`, lines 990-994: `sizeof(x)` bytes. -/
def writeString (io : CoreIO) (x : List Nat) (s : Out) : Nat × Out :=
  let nb := x.length
  let r := unsafeWrite io x nb s
  (nb, r.2)

/-- Printable arguments of the `Core` printing functions. -/
inductive PrintArg where
  | char (bytes : List Nat)
  | string (bytes : List Nat)
  | other (shown : List Nat)

/-- `show(io, x)`, line 996 (`jl_static_show`). -/
def coreShow (io : CoreIO) (staticShow : PrintArg → List Nat) (x : PrintArg) (s : Out) : Out :=
  emit io (staticShow x) s

/-- `print(io, x::AbstractChar)`, `print(io, x::String)`, `print(io, x)`, lines 997-999. -/
def print1 (io : CoreIO) (staticShow : PrintArg → List Nat) (x : PrintArg) (s : Out) : Out :=
  match x with
  | .char b => emit io b s
  | .string b => (writeString io b s).2
  | v => coreShow io staticShow v s

/-- `print(io, x, a...) = (print(io, x); print(io, a...))`, line 1000. -/
def printN (io : CoreIO) (staticShow : PrintArg → List Nat) : List PrintArg → Out → Out
  | [], s => s
  | x :: a, s => printN io staticShow a (print1 io staticShow x s)

/-- `println(io) = (write(io, 0x0a); nothing)` and `println(io, x...)`, lines 1001-1002. -/
def println0 (io : CoreIO) (s : Out) : Out := (writeByte io 10 s).2
def printlnN (io : CoreIO) (staticShow : PrintArg → List Nat) (xs : List PrintArg) (s : Out) : Out :=
  println0 io (printN io staticShow xs s)

/-- `show(a)`, `print(a...)`, `println(a...)` on `Core.stdout`, lines 1004-1006. -/
def show0 (staticShow : PrintArg → List Nat) (a : PrintArg) (s : Out) : Out :=
  coreShow .stdout staticShow a s
def print0 (staticShow : PrintArg → List Nat) (a : List PrintArg) (s : Out) : Out :=
  printN .stdout staticShow a s
def printlnStdout (staticShow : PrintArg → List Nat) (a : List PrintArg) (s : Out) : Out :=
  printlnN .stdout staticShow a s

/-- The bytes `print` produces for one argument. -/
def printBytes (staticShow : PrintArg → List Nat) : PrintArg → List Nat
  | .char b => b
  | .string b => b
  | v => staticShow v

/-! ## Identity conversions and `Union{}` -/

/-- `convert(::Type{Any}, x) = x`, `convert(::Type{T}, x::T) = x` (`base/boot.jl:381-382`),
`convert(::Type{Type}, x::Type) = x` and `convert(::Type{String}, x::String) = x`
(`base/essentials.jl:476-480`), `convert(::Type{T}, x::T) where T<:Tuple` (line 652). -/
def convertSame {α : Type} (x : α) : α := x
/-- `cconvert(::Type{T}, x) = convert(T, x)` in `Core`, `base/boot.jl:383`. -/
def coreCconvert {α β : Type} (convert : α → β) (x : α) : β := convert x
/-- `unsafe_convert(::Type{T}, x::T) = x`, `base/boot.jl:384` and `base/essentials.jl:742-743`. -/
def unsafeConvertSame {α : Type} (x : α) : α := x
/-- `cconvert(::Type{T}, x) = x isa T ? x : convert(T, x)`, `base/essentials.jl:739`. -/
def cconvert {α : Type} (isT : α → Bool) (convert : α → R α) (x : α) : R α :=
  if isT x then .ok x else convert x
/-- `cconvert(::Type{<:Ptr}, x) = x`, `base/essentials.jl:741`. -/
def cconvertPtr {α : Type} (x : α) : α := x
/-- `unsafe_convert(::Type{P}, x::Ptr) = convert(P, x)`: pointer conversion keeps the
address, `base/essentials.jl:744`. -/
def unsafeConvertPtr (x : Ptr) : Ptr := ⟨x.addr⟩
/-- `unsafe_convert(Ptr{UInt8}, s)` and `unsafe_convert(Ptr{Int8}, s)` (`jl_string_ptr`),
`base/essentials.jl:745-746`: the address of the string data. -/
def unsafeConvertString (dataAddr : JInt .u64) : Ptr := ⟨dataAddr⟩

/-- `Union{}(a...)` and `kwcall(kwargs, ::Type{Union{}}, a...)` (`base/boot.jl:398-399`),
`convert(::Type{Union{}}, _...)` (`base/essentials.jl:474`) and
`cconvert(::Type{Union{}}, x...) = convert(Union{}, x...)` (line 740). -/
def unionBottomCtor {α : Type} (_ : List α) : R α :=
  .error (.argument "cannot construct a value of type Union{} for return result")
def kwcallUnionBottom {α : Type} (_kwargs : α) (a : List α) : R α := unionBottomCtor a
def convertUnionBottom {α : Type} (_ : List α) : R α :=
  .error (.argument "cannot convert a value to Union{} for assignment")
def cconvertUnionBottom {α : Type} (x : List α) : R α := convertUnionBottom x

/-! ## Tuples, `base/essentials.jl:521-667` -/

/-- `argtail(_, rest...) = rest`. -/
def argtail {α : Type} : List α → R (List α)
  | _ :: rest => .ok rest
  | [] => .error (.method "argtail")
/-- `tail(x::Tuple) = argtail(x...)` and `tail(::Tuple{}) = throw(ArgumentError(...))`. -/
def tail {α : Type} : List α → R (List α)
  | [] => .error (.argument "Cannot call tail on an empty tuple.")
  | x => argtail x

/-- `_tuple_error(T, x) = throw(MethodError(convert, (T, x)))`, line 650. -/
def tupleError {α : Type} : R α := .error (.method "convert")

/-- `cvt1(n)`, lines 659-665: the `n`-th element converted to the `n`-th field type. -/
def cvt1 {α : Type} (isa : Nat → α → Bool) (convert : Nat → α → R α) (x : List α) (n : Nat) :
    R α :=
  match x[n - 1]? with
  | some xn => if isa n xn then .ok xn else convert n xn
  | none => .error .bounds

/-- `ntuple(cvt1, Val(N))`: apply `cvt1` to positions `n, n+1, ...` in order, stopping at the
first error. -/
def cvtFrom {α : Type} (isa : Nat → α → Bool) (convert : Nat → α → R α) : Nat → List α → R (List α)
  | _, [] => .ok []
  | n, xn :: xs => do
    let y ← if isa n xn then pure xn else convert n xn
    let ys ← cvtFrom isa convert (n + 1) xs
    pure (y :: ys)

/-- `convert(::Type{T}, x::NTuple{N,Any}) where {N, T<:Tuple}`, lines 653-667: `fits` is
`typeintersect(NTuple{N,Any}, T) !== Union{}`. -/
def convertTuple {α : Type} (fits : Bool) (isa : Nat → α → Bool) (convert : Nat → α → R α)
    (x : List α) : R (List α) :=
  if !fits then tupleError else cvtFrom isa convert 1 x

/-! ## Small functions -/

/-- `blackbox(x) = compilerbarrier(:blackbox, x)` and `inferencebarrier(x)`
(`base/essentials.jl:9`, 1201): the value is unchanged. -/
def blackbox {α : Type} (x : α) : α := x
def inferencebarrier {α : Type} (x : α) : α := x

/-- `throw_boundserror(A)`, `throw_boundserror(A, I)`, `throw_boundserror(A, i1, i2, I...)`,
`_throw_boundserror_indices(A)` and `(A, i1, I...)`, `base/essentials.jl:15-19`:
`BoundsError(A, indices)`. -/
def throwBoundserror (A : JVal) (I : List JVal) : R JVal × JVal :=
  (.error .bounds, .obj "BoundsError" [some A, some (.tuple I)])
def throwBoundserror1 (A : JVal) : R JVal × JVal := throwBoundserror A []
def throwBoundserror2 (A I : JVal) : R JVal × JVal :=
  (.error .bounds, .obj "BoundsError" [some A, some I])
def throwBoundserror3 (A i1 i2 : JVal) (I : List JVal) : R JVal × JVal :=
  throwBoundserror A (i1 :: i2 :: I)
def throwBoundserrorIndices (A : JVal) (I : List JVal) : R JVal × JVal := throwBoundserror A I

/-- `==(a::GlobalRef, b::GlobalRef) = a.mod === b.mod && a.name === b.name`, line 23. -/
def globalRefEq (a b : String × String) : Bool := a.1 == b.1 && a.2 == b.2

/-- `oftype(x, y) = y isa typeof(x) ? y : convert(typeof(x), y)::typeof(x)`, line 718. -/
def oftype {α : Type} (isa : α → Bool) (convert : α → R α) (y : α) : R α :=
  if isa y then .ok y
  else do
    let r ← convert y
    if isa r then .ok r else .error (.typeError "typeassert")

/-- `unsigned(x::Int) = reinterpret(UInt, x)` and `signed(x::UInt) = reinterpret(Int, x)`,
lines 720-721. -/
def unsignedInt (x : JInt64) : JInt .u64 := bitcastInt .u64 x
def signedUInt (x : JInt .u64) : JInt64 := bitcastInt .i64 x

/-- `reinterpret(::Type{Out}, x)`, lines 787-794: `bitcast` when both types are primitive,
otherwise the full `_reinterpret` defined later in Base. -/
def reinterpret {α β : Type} (primitive : Bool) (bitcast : α → β) (full : α → R β) (x : α) : R β :=
  if primitive then .ok (bitcast x) else full x

/-- `sizeof(x) = Core.sizeof(x)`, line 841, and `ifelse(c, x, y) = Core.ifelse(c, x, y)`,
line 884. -/
def sizeof {α : Type} (coreSizeof : α → Nat) (x : α) : Nat := coreSizeof x
def ifelse {α : Type} (c : Bool) (x y : α) : α := if c then x else y

/-- `isempty(itr)`, lines 1225-1229; `isdone` returns `none` for `missing`. -/
def isempty {σ α : Type} (isdone : σ → Option Bool) (iterate : σ → Option α) (itr : σ) : Bool :=
  match isdone itr with
  | some d => d
  | none => (iterate itr).isNone

/-- `values(itr) = itr`, line 1253. -/
def values {α : Type} (itr : α) : α := itr

/-- `(+)(x::Int, y::Int) = add_int(x, y)`, `(-)(x::Int, y::Int) = sub_int(x, y)` and
`!(x::Bool) = not_int(x)`, lines 1257-1284. -/
def addInt (x y : JInt64) : JInt64 := JInt.wrap .i64 (x.val + y.val)
def subInt (x y : JInt64) : JInt64 := JInt.wrap .i64 (x.val - y.val)
def notBool (x : Bool) : Bool := !x

/-- `ismissing(x) = x === missing` and `isdone(_, _...) = missing`, lines 1532, 1591. -/
def ismissing (x : Option JVal) : Bool := x.isNone
def isdoneDefault {α : Type} (_ : α) : Option Bool := none

/-- `isiterable(T) = hasmethod(iterate, Tuple{T})`, lines 1608-1610. -/
def isiterable {τ : Type} (hasmethod : τ → Bool) (T : τ) : Bool := hasmethod T

/-- `_resolve_in_world(world, gr) = invoke_in_world(UInt(world), Core.getglobal, gr.mod, gr.name)`,
lines 1662-1663. -/
def resolveInWorld (getglobal : JInt .u64 → String → String → R JVal) (world : BuiltinInt)
    (gr : String × String) : R JVal := do
  let w ← ctor .u64 world
  getglobal w gr.1 gr.2

/-- `Pairs{K,V,I,A}(data, itr)` (line 508): each argument is converted unless it already
has the declared type. -/
def pairsKVIA {α : Type} (isA isI : α → Bool) (convA convI : α → R α) (data itr : α) : R (α × α) := do
  let d ← if isA data then pure data else convA data
  let i ← if isI itr then pure itr else convI itr
  pure (d, i)

/-- The parameters `(K, V, I, A)` the outer `Pairs` constructors choose, lines 509-511:
`Pairs{K,V}` takes `I`, `A` from the arguments, `Pairs{K}` also takes `V = eltype(A)`, and
`Pairs(data, itr)` takes `K = eltype(I)` unless `I === Nothing`, then `keytype(A)`. -/
def pairsKV (K V I A : String) : String × String × String × String := (K, V, I, A)
def pairsK (eltype : String → String) (K I A : String) : String × String × String × String :=
  (K, eltype A, I, A)
def pairs0 (eltype keytype : String → String) (I A : String) : String × String × String × String :=
  (if I != "Nothing" then eltype I else keytype A, eltype A, I, A)

/-- `pairs(::Type{NamedTuple}) = Pairs{Symbol, V, Nothing, NT} where {V, NT <: NamedTuple}`,
line 513: the key type is `Symbol` and the iterator type `Nothing`. -/
def pairsNamedTupleType : String × String := ("Symbol", "Nothing")

/-- `Colon() = new()`, line 1160. -/
def colonCtor : JVal := .obj "Colon" []

/-- `Val{x}() = new()` and `Val(x) = Val{x}()`, lines 1190-1193: the parameter `x` lives
in the type, paired here with the field-less instance. -/
def valT (x : JVal) : JVal × JVal := (x, .obj "Val" [])
def valCtor (x : JVal) : JVal × JVal := valT x

/-- `show(io, ::Colon)`, lines 1164-1167: the type name, then `"()"`. -/
def showColon (showTypeName : String) : String := showTypeName ++ "()"

/-! ## `Core` hooks and shims, `base/boot.jl:1227-1281` -/

/-- `struct_name_shim(x, name, mod, t) = x === mod ? t : getfield(x, name)`. -/
def structNameShim {α : Type} (getfield : α → String → R α) (eqMod : Bool) (x : α) (name : String)
    (t : α) : R α :=
  if eqMod then .ok t else getfield x name

/-- `Core._parse`, `Core._lower` and `Core._toplevel_eval` hooks. -/
structure Hooks (α : Type) where
  parse : α
  lower : α
  toplevelEval : α

/-- `_setparser!(p)`, `_setlowerer!(l)` and `_set_toplevel_eval!(f)`, lines 1252-1254:
`setglobal!` installs the hook and returns it. -/
def setparser {α : Type} (h : Hooks α) (p : α) : α × Hooks α := (p, { h with parse := p })
def setlowerer {α : Type} (h : Hooks α) (l : α) : α × Hooks α := (l, { h with lower := l })
def setToplevelEval {α : Type} (h : Hooks α) (f : α) : α × Hooks α := (f, { h with toplevelEval := f })

/-- `_hasmethod(tt)`, lines 1276-1281: whether `jl_gf_invoke_lookup(tt, nothing, world)` finds
a method in the current world. -/
def hasmethod {τ μ : Type} (lookup : τ → Nat → Option μ) (world : Nat) (tt : τ) : Bool :=
  !(lookup tt world).isNone

end JuliaLean.BootCov.Misc

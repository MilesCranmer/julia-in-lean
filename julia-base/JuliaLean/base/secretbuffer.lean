import JuliaLean.base.io
import JuliaLean.Registry.Types
import JuliaLean.Core
import JuliaLean.base.int
import JuliaLean.base.char
import JuliaLean.base.iobuffer

/-!
# Model of `base/secretbuffer.jl`

Typed model of every method in Julia `f755f49a9e41380d7da126b3c1db9fe7f83dd027`. `SecretBuffer`
keeps its `Memory{UInt8}` handle and the wrapping `Int64` size and pointer. Memory access,
allocation, copying, secure zeroing, finalizer registration, string conversion, C-pointer access,
and IO writes are typed interfaces. The source checks, updates, loops, error types, and method call
order are modelled below.
-/

namespace JuliaLean.base.secretbuffer

open JuliaLean

abbrev I64 := JInt .i64
abbrev IOErr := JuliaLean.base.iobuffer.IOErr
abbrev JuliaString := JuliaLean.base.iobuffer.JuliaString

/-- Runtime operations on the `Memory{UInt8}` backing a `SecretBuffer`. -/
structure MemoryOps (M : Type) where
  length : M → Except IOErr I64
  allocate : I64 → Except IOErr M
  copy : M → Except IOErr M
  copyTo : M → M → Except IOErr Unit
  securezero : M → Except IOErr Unit
  get : M → I64 → Except IOErr UInt8
  set : M → I64 → UInt8 → Except IOErr Unit
  allZero : M → Except IOErr Bool

/-- Abstract-vector operations used by `SecretBuffer!(d)`. -/
structure ByteVectorOps (V : Type) where
  length : V → Except IOErr I64
  get : V → I64 → Except IOErr UInt8
  securezero : V → Except IOErr Unit

/-- Pointer operations used by the two unsafe constructors. -/
structure PointerOps (P : Type) where
  isNull : P → Bool
  load : P → I64 → Except IOErr UInt8
  securezero : P → I64 → Except IOErr Unit

/-- `Cstring` operations selected by Julia's C and pointer layers. -/
structure CStringOps (C P : Type) where
  isNull : C → Bool
  strlen : C → Except IOErr I64
  toPointer : C → Except IOErr P

-- UNTRANSLATED
-- Source: base/secretbuffer.jl:1-30 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # This file is a part of Julia. License is MIT: https://julialang.org/license
-- 
-- """
--     Base.SecretBuffer()
-- 
-- An [`IOBuffer`](@ref)-like object where the contents will be securely wiped when garbage collected.
-- 
-- It is considered best practice to wipe the buffer using `Base.shred!(::SecretBuffer)` as
-- soon as the secure data are no longer required. When initializing with existing data, the
-- `SecretBuffer!` method is highly recommended to securely zero the passed argument. Avoid
-- initializing with and converting to `String`s as they are unable to be securely zeroed.
-- 
-- # Examples
-- ```jldoctest
-- julia> s = Base.SecretBuffer()
-- SecretBuffer("*******")
-- 
-- julia> write(s, 's', 'e', 'c', 'r', 'e', 't')
-- 6
-- 
-- julia> seek(s, 0); Char(read(s, UInt8))
-- 's': ASCII/Unicode U+0073 (category Ll: Letter, lowercase)
-- 
-- julia> Base.shred!(s)
-- SecretBuffer("*******")
-- 
-- julia> eof(s)
-- true
-- ```
-- """
-- /Source
-- Reason: the license header and constructor documentation do not define additional methods.

/--
Julia source: base/secretbuffer.jl:31-35 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
mutable struct SecretBuffer <: IO
    data::Memory{UInt8}
    size::Int
    ptr::Int

```
-/
structure SecretBuffer (M : Type) where
  data : M
  size : I64
  ptr : I64

/--
Julia source: base/secretbuffer.jl:36-41 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
    function SecretBuffer(; sizehint=128)
        s = new(Memory{UInt8}(undef, sizehint), 0, 1)
        finalizer(final_shred!, s)
        return s
    end
end
```
-/
def secretBufferNew {M Size : Type} (ops : MemoryOps M)
    (toInt : Size → Except IOErr I64)
    (registerFinalizer : (SecretBuffer M → Except IOErr (SecretBuffer M)) → SecretBuffer M → Except IOErr Unit)
    (finalShred : SecretBuffer M → Except IOErr (SecretBuffer M)) (sizehint : Size) :
    Except IOErr (SecretBuffer M) := do
  let capacity ← toInt sizehint
  let data ← ops.allocate capacity
  let buffer : SecretBuffer M := ⟨data, JInt.lit .i64 0, JInt.lit .i64 1⟩
  let _ ← registerFinalizer finalShred buffer
  pure buffer

/--
Julia source: base/secretbuffer.jl:43-54 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    SecretBuffer(str::AbstractString)

A convenience constructor to initialize a `SecretBuffer` from a non-secret string.

Strings are bad at keeping secrets because they are unable to be securely
zeroed or destroyed. Therefore, avoid using this constructor with secret data.
Instead of starting with a string, either construct the `SecretBuffer`
incrementally with `SecretBuffer()` and [`write`](@ref), or use a `Vector{UInt8}` with
the `Base.SecretBuffer!(::AbstractVector{UInt8})` constructor.
"""
SecretBuffer(str::AbstractString) = SecretBuffer(String(str))
```
-/
def secretBufferFromAbstractString {M S : Type}
    (toString : S → Except IOErr JuliaString)
    (constructString : JuliaString → Except IOErr (SecretBuffer M)) (str : S) :
    Except IOErr (SecretBuffer M) := do
  constructString (← toString str)

/--
Julia source: base/secretbuffer.jl:55-63 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function SecretBuffer(str::String)
    buf = codeunits(str)
    s = SecretBuffer(sizehint=length(buf))
    for c in buf
        write(s, c)
    end
    seek(s, 0)
    s
end
```
-/
def secretBufferFromString {M : Type}
    (newBuffer : I64 → Except IOErr (SecretBuffer M))
    (writeByte : SecretBuffer M → UInt8 → Except IOErr (SecretBuffer M × I64))
    (seek : SecretBuffer M → I64 → Except IOErr (SecretBuffer M))
    (str : JuliaString) : Except IOErr (SecretBuffer M) := do
  let bytes := str.bytes
  let length := JInt.lit .i64 (Int.ofNat bytes.length)
  let buffer ← newBuffer length
  let rec writeBytes : List UInt8 → SecretBuffer M → Except IOErr (SecretBuffer M)
    | [], buffer => pure buffer
    | byte :: rest, buffer => do
        let (buffer, _) ← writeByte buffer byte
        writeBytes rest buffer
  let buffer ← writeBytes bytes buffer
  seek buffer (JInt.lit .i64 0)

/--
Julia source: base/secretbuffer.jl:64-64 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
convert(::Type{SecretBuffer}, s::AbstractString) = SecretBuffer(String(s))
```
-/
def convertSecretBuffer {M S : Type}
    (toString : S → Except IOErr JuliaString)
    (constructString : JuliaString → Except IOErr (SecretBuffer M)) (str : S) :
    Except IOErr (SecretBuffer M) := do
  constructString (← toString str)

/--
Julia source: base/secretbuffer.jl:66-80 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    SecretBuffer!(data::Vector{UInt8})

Initialize a new `SecretBuffer` from `data`, securely zeroing `data` afterwards.
"""
function SecretBuffer!(d::AbstractVector{UInt8})
    len = length(d)
    s = SecretBuffer(sizehint=len)
    for i in 1:len
        write(s, d[i])
    end
    seek(s, 0)
    securezero!(d)
    s
end
```
-/
def secretBufferFromVectorBang {M V : Type} (vector : ByteVectorOps V)
    (newBuffer : I64 → Except IOErr (SecretBuffer M))
    (writeByte : SecretBuffer M → UInt8 → Except IOErr (SecretBuffer M × I64))
    (seek : SecretBuffer M → I64 → Except IOErr (SecretBuffer M)) (d : V) :
    Except IOErr (SecretBuffer M) := do
  let length ← vector.length d
  let buffer ← newBuffer length
  let count := if length.val > 0 then length.val.toNat else 0
  let rec copyBytes : Nat → I64 → SecretBuffer M → Except IOErr (SecretBuffer M)
    | 0, _, buffer => pure buffer
    | remaining + 1, index, buffer => do
        let byte ← vector.get d index
        let (buffer, _) ← writeByte buffer byte
        copyBytes remaining (JuliaLean.base.int.add_int index (JInt.lit .i64 1)) buffer
  let buffer ← copyBytes count (JInt.lit .i64 1) buffer
  let buffer ← seek buffer (JInt.lit .i64 0)
  vector.securezero d
  pure buffer

/--
Julia source: base/secretbuffer.jl:82-88 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_SecretBuffer!(s::Cstring)
    if s == C_NULL
        throw(ArgumentError("cannot convert NULL to SecretBuffer"))
    end
    len = Int(ccall(:strlen, Csize_t, (Cstring,), s))
    unsafe_SecretBuffer!(convert(Ptr{UInt8}, s), len)
end
```
-/
def unsafeSecretBufferFromCString {M C P : Type} (ops : CStringOps C P)
    (fromPointer : P → I64 → Except IOErr (SecretBuffer M)) (str : C) :
    Except IOErr (SecretBuffer M) := do
  if ops.isNull str then
    .error (.jl (.argumentError "cannot convert NULL to SecretBuffer"))
  else
    let length ← ops.strlen str
    let pointer ← ops.toPointer str
    fromPointer pointer length

/--
Julia source: base/secretbuffer.jl:89-100 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function unsafe_SecretBuffer!(p::Ptr{UInt8}, len=1)
    if p == C_NULL
        throw(ArgumentError("cannot convert NULL to SecretBuffer"))
    end
    s = SecretBuffer(sizehint=len)
    for i in 1:len
        write(s, unsafe_load(p, i))
    end
    seek(s, 0)
    unsafe_securezero!(p, len)
    s
end
```
-/
def unsafeSecretBufferFromPointer {M P : Type} (ops : PointerOps P)
    (newBuffer : I64 → Except IOErr (SecretBuffer M))
    (writeByte : SecretBuffer M → UInt8 → Except IOErr (SecretBuffer M × I64))
    (seek : SecretBuffer M → I64 → Except IOErr (SecretBuffer M))
    (pointer : P) (length : I64 := JInt.lit .i64 1) : Except IOErr (SecretBuffer M) := do
  if ops.isNull pointer then
    .error (.jl (.argumentError "cannot convert NULL to SecretBuffer"))
  else
    let buffer ← newBuffer length
    let count := if length.val > 0 then length.val.toNat else 0
    let rec copyBytes : Nat → I64 → SecretBuffer M → Except IOErr (SecretBuffer M)
      | 0, _, buffer => pure buffer
      | remaining + 1, index, buffer => do
          let byte ← ops.load pointer index
          let (buffer, _) ← writeByte buffer byte
          copyBytes remaining (JuliaLean.base.int.add_int index (JInt.lit .i64 1)) buffer
    let buffer ← copyBytes count (JInt.lit .i64 1) buffer
    let buffer ← seek buffer (JInt.lit .i64 0)
    ops.securezero pointer length
    pure buffer

/--
Julia source: base/secretbuffer.jl:103-103 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
show(io::IO, s::SecretBuffer) = print(io, "SecretBuffer(\"*******\")")
```
-/
def showSecretBuffer {M IO E : Type} (printString : IO → String → Except E Unit)
    (io : IO) (_buffer : SecretBuffer M) : Except E Unit :=
  printString io "SecretBuffer(\"*******\")"

/--
Julia source: base/secretbuffer.jl:105-106 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Unlike other IO objects, equality is computed by value for convenience
==(s1::SecretBuffer, s2::SecretBuffer) = (s1.ptr == s2.ptr) && (s1.size == s2.size) && (UInt8(0) == _bufcmp(s1.data, s2.data, min(s1.size, s2.size)))
```
-/
def equalSecretBuffer {M : Type} (ops : MemoryOps M)
    (compare : MemoryOps M → M → M → I64 → Except IOErr UInt8)
    (left right : SecretBuffer M) : Except IOErr Bool := do
  if left.ptr.val != right.ptr.val then pure false
  else if left.size.val != right.size.val then pure false
  else
    let size := if left.size.val ≤ right.size.val then left.size else right.size
    pure ((← compare ops left.data right.data size) == UInt8.ofNat 0)

/--
Julia source: base/secretbuffer.jl:107-115 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# Also attempt a constant time buffer comparison algorithm — the length of the secret might be
# inferred by a timing attack, but not its values.
@noinline function _bufcmp(data1::Memory{UInt8}, data2::Memory{UInt8}, sz::Int)
    res = UInt8(0)
    for i = 1:sz
        res |= xor(data1[i], data2[i])
    end
    return res
end
```
-/
def bufcmp {M : Type} (ops : MemoryOps M) (data1 data2 : M) (size : I64) :
    Except IOErr UInt8 :=
  let count := if size.val > 0 then size.val.toNat else 0
  let rec loop : Nat → I64 → UInt8 → Except IOErr UInt8
    | 0, _, result => pure result
    | remaining + 1, index, result => do
        let left ← ops.get data1 index
        let right ← ops.get data2 index
        let result := result ||| (left ^^^ right)
        loop remaining (JuliaLean.base.int.add_int index (JInt.lit .i64 1)) result
  loop count (JInt.lit .i64 1) (UInt8.ofNat 0)

/--
Julia source: base/secretbuffer.jl:116-118 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
# All SecretBuffers hash the same to avoid leaking information or breaking consistency with ==
const _sb_hash = UInt === UInt32 ? 0x111c0925 : 0xb06061e370557428
hash(s::SecretBuffer, h::UInt) = hash(_sb_hash, h)
```
-/
def hashSecretBuffer {M : Type} (hash : {T : Type} → T → JInt .u64 → JInt .u64)
    (_buffer : SecretBuffer M) (seed : JInt .u64) : JInt .u64 :=
  hash (JInt.lit .u64 0xb06061e370557428) seed

/--
Julia source: base/secretbuffer.jl:120-120 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
copy(s::SecretBuffer) = copy!(SecretBuffer(sizehint=length(s.data)), s)
```
-/
def copySecretBuffer {M : Type} (ops : MemoryOps M)
    (newBuffer : I64 → Except IOErr (SecretBuffer M))
    (copyBang : SecretBuffer M → SecretBuffer M → Except IOErr (SecretBuffer M))
    (source : SecretBuffer M) : Except IOErr (SecretBuffer M) := do
  let length ← ops.length source.data
  let destination ← newBuffer length
  copyBang destination source

/--
Julia source: base/secretbuffer.jl:121-131 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function copy!(dest::SecretBuffer, src::SecretBuffer)
    if length(dest.data) != length(src.data)
        securezero!(dest.data)
        dest.data = copy(src.data)
    else
        copyto!(dest.data, src.data)
    end
    dest.size = src.size
    dest.ptr = src.ptr
    return dest
end
```
-/
def copySecretBufferBang {M : Type} (ops : MemoryOps M)
    (destination source : SecretBuffer M) : Except IOErr (SecretBuffer M) := do
  let destinationLength ← ops.length destination.data
  let sourceLength ← ops.length source.data
  let data ←
    if destinationLength.val != sourceLength.val then do
      ops.securezero destination.data
      ops.copy source.data
    else do
      ops.copyTo destination.data source.data
      pure destination.data
  pure { destination with data, size := source.size, ptr := source.ptr }

/--
Julia source: base/secretbuffer.jl:133-145 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(io::SecretBuffer, b::UInt8)
    if io.ptr > length(io.data)
        # We need to resize! the array: do this manually to ensure no copies are left behind
        newdata = Memory{UInt8}(undef, (io.size+16)*2)
        copyto!(newdata, io.data)
        securezero!(io.data)
        io.data = newdata
    end
    io.size == io.ptr-1 && (io.size += 1)
    io.data[io.ptr] = b
    io.ptr += 1
    return 1
end
```
-/
def writeSecretBufferByte {M : Type} (ops : MemoryOps M)
    (io : SecretBuffer M) (byte : UInt8) : Except IOErr (SecretBuffer M × I64) := do
  let length ← ops.length io.data
  let data ←
    if io.ptr.val > length.val then do
      let newLength := JuliaLean.base.int.mul_int
        (JuliaLean.base.int.add_int io.size (JInt.lit .i64 16)) (JInt.lit .i64 2)
      let newData ← ops.allocate newLength
      ops.copyTo newData io.data
      ops.securezero io.data
      pure newData
    else pure io.data
  let size :=
    if io.size.val == (JuliaLean.base.int.sub_int io.ptr (JInt.lit .i64 1)).val then
      JuliaLean.base.int.add_int io.size (JInt.lit .i64 1)
    else io.size
  ops.set data io.ptr byte
  let buffer := { io with data, size, ptr := JuliaLean.base.int.add_int io.ptr (JInt.lit .i64 1) }
  pure (buffer, JInt.lit .i64 1)

/--
Julia source: base/secretbuffer.jl:147-153 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function write(io::IO, s::SecretBuffer)
    nb = 0
    for i in 1:s.size
        nb += write(io, s.data[i])
    end
    return nb
end
```
-/
def writeSecretBufferTo {M IO : Type} (ops : MemoryOps M)
    (writeByte : IO → UInt8 → Except IOErr (IO × I64))
    (io : IO) (buffer : SecretBuffer M) : Except IOErr (IO × I64) := do
  let count := if buffer.size.val > 0 then buffer.size.val.toNat else 0
  let rec loop : Nat → I64 → IO → I64 → Except IOErr (IO × I64)
    | 0, _, io, written => pure (io, written)
    | remaining + 1, index, io, written => do
        let byte ← ops.get buffer.data index
        let (io, amount) ← writeByte io byte
        loop remaining (JuliaLean.base.int.add_int index (JInt.lit .i64 1)) io
          (JuliaLean.base.int.add_int written amount)
  loop count (JInt.lit .i64 1) io (JInt.lit .i64 0)

private def containsNulBytes {M : Type} (ops : MemoryOps M) (data : M) (size : I64) :
    Except IOErr Bool :=
  let count := if size.val > 0 then size.val.toNat else 0
  let rec loop : Nat → I64 → Except IOErr Bool
    | 0, _ => pure false
    | remaining + 1, index => do
        let byte ← ops.get data index
        if byte == UInt8.ofNat 0 then pure true
        else loop remaining (JuliaLean.base.int.add_int index (JInt.lit .i64 1))
  loop count (JInt.lit .i64 1)
/--
Julia source: base/secretbuffer.jl:155-167 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function cconvert(::Type{Cstring}, s::SecretBuffer)
    # Ensure that no nuls appear in the valid region
    if any(==(0x00), s.data[i] for i in 1:s.size)
        throw(ArgumentError("`SecretBuffers` containing nul bytes cannot be converted to C strings"))
    end
    # Add a hidden nul byte just past the end of the valid region
    p = s.ptr
    s.ptr = s.size + 1
    write(s, '\0')
    s.ptr = p
    s.size -= 1
    return s.data
end
```
-/
def cconvertSecretBuffer {M : Type} (ops : MemoryOps M)
    (writeChar : SecretBuffer M → JuliaLean.base.char.JChar → Except IOErr (SecretBuffer M × I64))
    (buffer : SecretBuffer M) : Except IOErr (M × SecretBuffer M) := do
  let hasNul ← containsNulBytes ops buffer.data buffer.size
  if hasNul then throw (.jl (.argumentError "`SecretBuffers` containing nul bytes cannot be converted to C strings"))
  let pointer := buffer.ptr
  let atEnd := { buffer with ptr := JuliaLean.base.int.add_int buffer.size (JInt.lit .i64 1) }
  let (written, _) ← writeChar atEnd (UInt32.ofNat 0)
  let restored : SecretBuffer M := ⟨written.data,
    JuliaLean.base.int.sub_int written.size (JInt.lit .i64 1), pointer⟩
  pure (restored.data, restored)

-- UNTRANSLATED
-- Source: base/secretbuffer.jl:168-169 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-- # optional shim for manual calls to unsafe_convert:
-- #   unsafe_convert(::Type{Cstring}, s::SecretBuffer) = unsafe_convert(Cstring, cconvert(Cstring, s))
-- /Source
-- Reason: the optional unsafe_convert shim is commented out and defines no method.

/--
Julia source: base/secretbuffer.jl:171-171 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
seek(io::SecretBuffer, n::Integer) = (io.ptr = max(min(n+1, io.size+1), 1); io)
```
-/
def seekSecretBuffer {M N N1 R1 R2 : Type}
    (addOne : N → Except IOErr N1) (min : N1 → I64 → Except IOErr R1)
    (max : R1 → I64 → Except IOErr R2) (toInt : R2 → Except IOErr I64)
    (buffer : SecretBuffer M) (n : N) : Except IOErr (SecretBuffer M) := do
  let next ← addOne n
  let upper := JuliaLean.base.int.add_int buffer.size (JInt.lit .i64 1)
  let limited ← min next upper
  let clamped ← max limited (JInt.lit .i64 1)
  let pointer ← toInt clamped
  pure { buffer with ptr := pointer }

/--
Julia source: base/secretbuffer.jl:172-172 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
seekend(io::SecretBuffer) = seek(io, io.size+1)
```
-/
def seekendSecretBuffer {M : Type} (seek : SecretBuffer M → I64 → Except IOErr (SecretBuffer M))
    (buffer : SecretBuffer M) : Except IOErr (SecretBuffer M) :=
  seek buffer (JuliaLean.base.int.add_int buffer.size (JInt.lit .i64 1))

/--
Julia source: base/secretbuffer.jl:173-173 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
skip(io::SecretBuffer, n::Integer) = seek(io, position(io) + n)
```
-/
def skipSecretBuffer {M N N1 : Type}
    (addPosition : I64 → N → Except IOErr N1)
    (position : SecretBuffer M → I64)
    (seek : SecretBuffer M → N1 → Except IOErr (SecretBuffer M))
    (buffer : SecretBuffer M) (n : N) : Except IOErr (SecretBuffer M) := do
  let target ← addPosition (position buffer) n
  seek buffer target

/--
Julia source: base/secretbuffer.jl:175-175 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
bytesavailable(io::SecretBuffer) = io.size - io.ptr + 1
```
-/
def bytesavailableSecretBuffer (buffer : SecretBuffer M) : I64 :=
  JuliaLean.base.int.add_int
    (JuliaLean.base.int.sub_int buffer.size buffer.ptr) (JInt.lit .i64 1)

/--
Julia source: base/secretbuffer.jl:176-176 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
position(io::SecretBuffer) = io.ptr-1
```
-/
def positionSecretBuffer (buffer : SecretBuffer M) : I64 :=
  JuliaLean.base.int.sub_int buffer.ptr (JInt.lit .i64 1)

/--
Julia source: base/secretbuffer.jl:177-177 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
eof(io::SecretBuffer) = io.ptr > io.size
```
-/
def eofSecretBuffer (buffer : SecretBuffer M) : Bool := buffer.ptr.val > buffer.size.val

/--
Julia source: base/secretbuffer.jl:178-178 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isempty(io::SecretBuffer) = io.size == 0
```
-/
def isemptySecretBuffer (buffer : SecretBuffer M) : Bool := buffer.size.val == 0

/--
Julia source: base/secretbuffer.jl:179-182 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function peek(io::SecretBuffer, ::Type{UInt8})
    eof(io) && throw(EOFError())
    return io.data[io.ptr]
end
```
-/
def peekSecretBuffer {M : Type} (ops : MemoryOps M) (buffer : SecretBuffer M) :
    Except IOErr UInt8 :=
  if eofSecretBuffer buffer then .error .eofError else ops.get buffer.data buffer.ptr

/--
Julia source: base/secretbuffer.jl:183-188 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function read(io::SecretBuffer, ::Type{UInt8})
    eof(io) && throw(EOFError())
    byte = io.data[io.ptr]
    io.ptr += 1
    return byte
end
```
-/
def readSecretBuffer {M : Type} (ops : MemoryOps M) (buffer : SecretBuffer M) :
    Except IOErr (UInt8 × SecretBuffer M) := do
  if eofSecretBuffer buffer then throw .eofError
  let byte ← ops.get buffer.data buffer.ptr
  pure (byte, { buffer with ptr := JuliaLean.base.int.add_int buffer.ptr (JInt.lit .i64 1) })

/--
Julia source: base/secretbuffer.jl:190-193 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
function final_shred!(s::SecretBuffer)
    !isshredded(s) && @async @warn("a SecretBuffer was `shred!`ed by the GC; use `shred!` manually after use to minimize exposure.")
    shred!(s)
end
```
-/
def finalShredSecretBuffer {M : Type} (ops : MemoryOps M)
    (scheduleWarning : String → Except IOErr Unit)
    (shred : SecretBuffer M → Except IOErr (SecretBuffer M))
    (buffer : SecretBuffer M) : Except IOErr (SecretBuffer M) := do
  if !(← ops.allZero buffer.data) then
    scheduleWarning "a SecretBuffer was `shred!`ed by the GC; use `shred!` manually after use to minimize exposure."
  shred buffer

/--
Julia source: base/secretbuffer.jl:195-215 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
````julia
"""
    shred!(s::SecretBuffer)

Shreds the contents of a `SecretBuffer` by securely zeroing its data and
resetting its pointer and size.
This function is used to securely erase the sensitive data held in the buffer,
reducing the potential for information leaks.

# Examples
```julia
s = SecretBuffer()
write(s, 's', 'e', 'c', 'r', 'e', 't')
shred!(s)  # s is now empty
```
"""
function shred!(s::SecretBuffer)
    securezero!(s.data)
    s.ptr = 1
    s.size = 0
    return s
end
````
-/
def shredSecretBuffer {M : Type} (ops : MemoryOps M) (buffer : SecretBuffer M) :
    Except IOErr (SecretBuffer M) := do
  ops.securezero buffer.data
  pure { buffer with ptr := JInt.lit .i64 1, size := JInt.lit .i64 0 }

/--
Julia source: base/secretbuffer.jl:217-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
isshredded(s::SecretBuffer) = all(iszero, s.data)
```
-/
def isshreddedSecretBuffer {M : Type} (ops : MemoryOps M) (buffer : SecretBuffer M) :
    Except IOErr Bool := ops.allZero buffer.data

/--
Julia source: base/secretbuffer.jl:219-232 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
```julia
"""
    shred!(f::Function, x)

Applies function `f` to the argument `x` and then shreds `x`.
This function is useful when you need to perform some operations on e.g. a
`SecretBuffer` and then want to ensure that it is securely shredded afterwards.
"""
function shred!(f::Function, x)
    try
        f(x)
    finally
        shred!(x)
    end
end
```
-/
def shredFinally {F X A E : Type} (apply : F → X → Except E A)
    (shred : X → Except E X) (f : F) (x : X) : Except E A :=
  match apply f x with
  | .ok result => do
      let _ ← shred x
      pure result
  | .error error => do
      let _ ← shred x
      .error error

end JuliaLean.base.secretbuffer

section

set_option linter.unusedSimpArgs false
namespace JuliaLean.IOCov.Secret

open JuliaLean JuliaLean.IOCov

structure SB where
  content : List UInt8
  slack : List UInt8
  ptr : Nat
  deriving DecidableEq, Repr

def SB.size (s : SB) : Nat := s.content.length
def SB.data (s : SB) : List UInt8 := s.content ++ s.slack

/-- `SecretBuffer(; sizehint=128)`, lines 36-40. -/
def create (sizehint : Nat := 128) : SB := ⟨[], List.replicate sizehint 0, 1⟩

/-- `securezero!(d)`. -/
def zeros (d : List UInt8) : List UInt8 := d.map (fun _ => 0)

/-- `write(io::SecretBuffer, b::UInt8)`, lines 133-145: when `ptr > length(data)` the
memory is replaced by `(size+16)*2` bytes holding a copy (the old one is zeroed and
dropped); `io.size == io.ptr-1 && (io.size += 1)`; `data[ptr] = b`; `ptr += 1`. -/
def writeByte (s : SB) (b : UInt8) : SB :=
  let slack := if s.ptr > s.data.length then List.replicate ((s.size + 16) * 2 - s.size) 0 else s.slack
  if s.ptr == s.size + 1 then ⟨s.content ++ [b], slack.drop 1, s.ptr + 1⟩
  else ⟨s.content.set (s.ptr - 1) b, slack, s.ptr + 1⟩

def writeBytes (s : SB) (bs : List UInt8) : SB := bs.foldl writeByte s

/-- `seek(io, n) = (io.ptr = max(min(n+1, io.size+1), 1); io)`, line 171: for `n < 0` the
pointer is 1, otherwise `min(n+1, size+1)`. -/
def seek (s : SB) (n : Int) : SB := { s with ptr := if n < 0 then 1 else min (n.toNat + 1) (s.size + 1) }
/-- `seekend(io) = seek(io, io.size+1)`, line 172. -/
def seekend (s : SB) : SB := seek s (s.size + 1)
/-- `position(io) = io.ptr-1`, line 176. -/
def position (s : SB) : Int := (s.ptr : Int) - 1
/-- `skip(io, n) = seek(io, position(io) + n)`, line 173. -/
def skip (s : SB) (n : Int) : SB := seek s (position s + n)
/-- `bytesavailable(io) = io.size - io.ptr + 1`, line 175. -/
def bytesavailable (s : SB) : Int := (s.size : Int) - s.ptr + 1
/-- `eof(io) = io.ptr > io.size`, line 177. -/
def eof (s : SB) : Bool := s.ptr > s.size
/-- `isempty(io) = io.size == 0`, line 178. -/
def isempty (s : SB) : Bool := s.size == 0
/-- `peek(io, UInt8)`, lines 179-182. -/
def peek (s : SB) : R UInt8 := if eof s then .error .eofError else .ok (s.content.getD (s.ptr - 1) 0)
/-- `read(io, UInt8)`, lines 183-188. -/
def read (s : SB) : R (UInt8 × SB) :=
  if eof s then .error .eofError else .ok (s.content.getD (s.ptr - 1) 0, { s with ptr := s.ptr + 1 })

/-- `SecretBuffer(str::String)`, lines 55-63: write each code unit, then `seek(s, 0)`. -/
def ofString (str : List UInt8) : SB := seek (writeBytes (create str.length) str) 0
/-- `SecretBuffer(str::AbstractString)`, line 54, and `convert(SecretBuffer, s)`, line 64. -/
def ofAbstractString (str : List UInt8) : SB := ofString str
def convertSB (str : List UInt8) : SB := ofString str
/-- `SecretBuffer!(d)`, lines 71-80: the buffer, and `d` after `securezero!`. -/
def ofBytesBang (d : List UInt8) : SB × List UInt8 := (seek (writeBytes (create d.length) d) 0, zeros d)
/-- `unsafe_SecretBuffer!(p::Ptr{UInt8}, len)`, lines 89-100, on the `len` bytes at `p`
(`none` is `C_NULL`); the second component is the memory after `unsafe_securezero!`. -/
def unsafeOfPtr (p : Option (List UInt8)) : R (SB × List UInt8) :=
  match p with
  | none => argErr "cannot convert NULL to SecretBuffer"
  | some bytes => .ok (ofBytesBang bytes)
/-- `unsafe_SecretBuffer!(s::Cstring)`, lines 82-88: the `strlen` bytes. -/
def unsafeOfCstring (p : Option (List UInt8)) : R (SB × List UInt8) :=
  match p with
  | none => argErr "cannot convert NULL to SecretBuffer"
  | some bytes => unsafeOfPtr (some (bytes.takeWhile (· != 0)))

/-- `show(io, s::SecretBuffer)`, line 103. -/
def showSB (_s : SB) : String := "SecretBuffer(\"*******\")"

/-- `_bufcmp(data1, data2, sz)`, lines 109-115. -/
def bufcmp (d1 d2 : List UInt8) (sz : Nat) : UInt8 :=
  ((List.range sz).map fun i => d1.getD i 0 ^^^ d2.getD i 0).foldl (· ||| ·) 0
/-- `==(s1, s2)`, line 106. -/
def eq (s1 s2 : SB) : Bool :=
  s1.ptr == s2.ptr && s1.size == s2.size && 0 == bufcmp s1.data s2.data (min s1.size s2.size)
/-- `hash(s::SecretBuffer, h) = hash(_sb_hash, h)`, line 118. -/
def hash (mix : UInt64 → UInt64 → UInt64) (_s : SB) (h : UInt64) : UInt64 := mix 0xb06061e370557428 h

/-- `copy!(dest, src)`, lines 121-131: either branch leaves `dest.data` equal to `src.data`. -/
def copyBang (_dest src : SB) : SB := ⟨src.content, src.slack, src.ptr⟩
/-- `copy(s) = copy!(SecretBuffer(sizehint=length(s.data)), s)`, line 120. -/
def copy (s : SB) : SB := copyBang (create s.data.length) s

/-- `write(io::IO, s::SecretBuffer)`, lines 147-153: bytes `1:s.size`, whatever `ptr` is. -/
def writeTo (s : SB) : List UInt8 × Nat := (s.content, s.size)

/-- `cconvert(::Type{Cstring}, s)`, lines 155-167: reject NULs, write a NUL after the
contents, restore `ptr` and `size`; the data is returned. -/
def cconvert (s : SB) : R (List UInt8 × SB) :=
  if s.content.contains 0 then
    argErr "`SecretBuffers` containing nul bytes cannot be converted to C strings"
  else
    let w := writeByte { s with ptr := s.size + 1 } 0
    let r : SB := ⟨w.content.dropLast, w.content.getLast?.toList ++ w.slack, s.ptr⟩
    .ok (r.data, r)

/-- `shred!(s)`, lines 210-215. -/
def shred (s : SB) : SB := ⟨[], zeros s.data, 1⟩
/-- `isshredded(s) = all(iszero, s.data)`, line 217. -/
def isshredded (s : SB) : Bool := s.data.all (· == 0)
/-- `final_shred!(s)`, lines 190-193: warns (first component) when not shredded, then shreds. -/
def finalShred (s : SB) : Bool × SB := (!isshredded s, shred s)
/-- `shred!(f, x)`, lines 226-232: `f(x)`, then `shred!(x)` in `finally`. -/
def shredDo {α} (f : SB → R α) (x : SB) : R α × SB := (f x, shred x)

/-- The generic `peek(s::IO, T)` (`base/io.jl:382-388`) starts with `mark(s)`, which sets
`s.mark`; `SecretBuffer` has no `mark` field. -/
def peekGeneric (_s : SB) : R Char := .error (.fieldError "mark")

def readAll : Nat → SB → List UInt8
  | 0, _ => []
  | n + 1, s => match read s with
    | .ok (b, s') => b :: readAll n s'
    | .error _ => []
end JuliaLean.IOCov.Secret
end

section
namespace JuliaLean.IOCov.SecretFaithful

open JuliaLean JuliaLean.Registry JuliaLean.IOCov

abbrev ByteMem := List (Option UInt8)

structure SB where
  data : ByteMem
  size : Int
  ptr : Int
  finalizerRegistered : Bool
  deriving DecidableEq, Repr

def initializedPrefix (s : SB) : List UInt8 :=
  (s.data.take s.size.toNat).map (Option.getD · 0)

/-- `SecretBuffer(; sizehint)`, `base/secretbuffer.jl:36-40`. -/
def create (sizehint : Int) : R SB :=
  if sizehint < 0 then .error (.jl (.argumentError "invalid Memory size"))
  else .ok ⟨List.replicate sizehint.toNat none, 0, 1, true⟩

def setAt (data : ByteMem) (idx : Int) (b : UInt8) : R ByteMem :=
  if 1 <= idx && idx <= data.length then .ok (data.set (idx - 1).toNat (some b))
  else .error (.jl .boundsError)

/-- `write(::SecretBuffer, ::UInt8)`, `base/secretbuffer.jl:133-145`.
The optional byte list is the old allocation passed to securezero! on growth. -/
def writeByte (s : SB) (b : UInt8) : R (Nat × SB × Option ByteMem) := do
  let growth := s.ptr > s.data.length
  let old := if growth then some s.data else none
  let data := if growth then
    s.data ++ List.replicate (((s.size + 16) * 2 - s.data.length).toNat) none
    else s.data
  let size := if s.size = s.ptr - 1 then s.size + 1 else s.size
  let data <- setAt data s.ptr b
  pure (1, { s with data, size, ptr := s.ptr + 1 }, old)

def writeBytes : SB -> List UInt8 -> R SB
  | s, [] => .ok s
  | s, b :: bs => do let (_, s', _) <- writeByte s b; writeBytes s' bs

/-- `SecretBuffer(str::String)`, `base/secretbuffer.jl:55-63`. -/
def ofString (bytes : List UInt8) : R SB := do
  let s <- create bytes.length
  let s <- writeBytes s bytes
  pure { s with ptr := 1 }

/-- AbstractString constructor, `base/secretbuffer.jl:54`. -/
def ofAbstractString {alpha : Type} (stringBytes : alpha -> List UInt8) (str : alpha) : R SB :=
  ofString (stringBytes str)
/-- `convert(SecretBuffer, s::AbstractString)`, `base/secretbuffer.jl:64`. -/
def convertAbstract {alpha : Type} (stringBytes : alpha -> List UInt8) (str : alpha) : R SB :=
  ofString (stringBytes str)

/-- `SecretBuffer!(d)`, `base/secretbuffer.jl:71-80`: result and securely
zeroed source vector. -/
def ofVectorBang (d : List UInt8) : R (SB × List UInt8) := do
  let s <- create d.length
  let s <- writeBytes s d
  pure ({ s with ptr := 1 }, d.map (fun _ => 0))

/-- Pointer overload, `base/secretbuffer.jl:89-100`. -/
def unsafeOfPtr (p : Option (List UInt8)) (len : Int) : R (SB × List UInt8) :=
  match p with
  | none => argErr "cannot convert NULL to SecretBuffer"
  | some mem =>
      if len < 0 || mem.length < len then .error (.jl .boundsError)
      else ofVectorBang (mem.take len.toNat)

/-- Cstring overload, `base/secretbuffer.jl:82-88`. -/
def unsafeOfCstring (p : Option (List UInt8)) : R (SB × List UInt8) :=
  match p with
  | none => argErr "cannot convert NULL to SecretBuffer"
  | some mem => unsafeOfPtr (some mem) (mem.takeWhile (· != 0)).length

/-- `show(io, s)`, `base/secretbuffer.jl:103`, as appended IO text. -/
def showMethod (out : String) (_s : SB) : String := out ++ "SecretBuffer(\"*******\")"

/-- `_bufcmp`, `base/secretbuffer.jl:109-115`, with checked Memory accesses. -/
def bufcmp (d1 d2 : ByteMem) (sz : Int) : R UInt8 :=
  if sz <= 0 then .ok 0
  else if d1.length < sz || d2.length < sz then .error (.jl .boundsError)
  else .ok ((List.range sz.toNat).foldl (fun r k =>
    r ||| ((d1.getD k none).getD 0 ^^^ (d2.getD k none).getD 0)) 0)

/-- `==`, `base/secretbuffer.jl:106`. -/
def eq (a b : SB) : R Bool := do
  if a.ptr != b.ptr then pure false
  else if a.size != b.size then pure false
  else pure ((<- bufcmp a.data b.data (min a.size b.size)) == 0)

/-- `hash`, `base/secretbuffer.jl:116-118`. -/
def hash (isUInt32 : Bool) (mix : UInt64 -> UInt64 -> UInt64) (h : UInt64) : UInt64 :=
  mix (if isUInt32 then 0x111c0925 else 0xb06061e370557428) h

/-- `copy!`, `base/secretbuffer.jl:121-131`. -/
def copyBang (dest src : SB) : SB × Option ByteMem :=
  if dest.data.length != src.data.length then
    ({ dest with data := src.data, size := src.size, ptr := src.ptr }, some dest.data)
  else ({ dest with data := src.data, size := src.size, ptr := src.ptr }, none)

/-- `copy`, `base/secretbuffer.jl:120`. -/
def copy (src : SB) : R SB := do
  let dest <- create src.data.length
  pure (copyBang dest src).1

/-- `write(io::IO, s)`, `base/secretbuffer.jl:147-153`. -/
def writeTo {state : Type} (write : state -> UInt8 -> Nat × state)
    (out : state) (s : SB) : Nat × state :=
  (initializedPrefix s).foldl (fun acc b =>
    let r := write acc.2 b
    (acc.1 + r.1, r.2)) (0, out)

/-- `cconvert(Cstring, s)`, `base/secretbuffer.jl:155-167`, returning the same
Memory alias after a hidden NUL is written and ptr/size restored. -/
def cconvert (s : SB) : R (ByteMem × SB) := do
  if (initializedPrefix s).contains 0 then
    argErr "`SecretBuffers` containing nul bytes cannot be converted to C strings"
  else
    let oldPtr := s.ptr
    let r <- writeByte { s with ptr := s.size + 1 } 0
    let s' := { r.2.1 with ptr := oldPtr, size := r.2.1.size - 1 }
    pure (s'.data, s')

/-- `seek`, `base/secretbuffer.jl:171`, over every Integer value represented by Int. -/
def seek (s : SB) (n : Int) : SB :=
  { s with ptr := max (min (n + 1) (s.size + 1)) 1 }
/-- `seekend`, `base/secretbuffer.jl:172`. -/
def seekend (s : SB) : SB := seek s (s.size + 1)
/-- `position`, `base/secretbuffer.jl:176`. -/
def position (s : SB) : Int := s.ptr - 1
/-- `skip`, `base/secretbuffer.jl:173`. -/
def skip (s : SB) (n : Int) : SB := seek s (position s + n)
/-- `bytesavailable`, `base/secretbuffer.jl:175`. -/
def bytesavailable (s : SB) : Int := s.size - s.ptr + 1
/-- `eof`, `base/secretbuffer.jl:177`. -/
def eof (s : SB) : Bool := s.ptr > s.size
/-- `isempty`, `base/secretbuffer.jl:178`. -/
def isempty (s : SB) : Bool := s.size = 0

/-- `peek(..., UInt8)`, `base/secretbuffer.jl:179-182`. -/
def peek (s : SB) : R UInt8 :=
  if eof s then .error .eofError
  else match s.data.getD (s.ptr - 1).toNat none with
    | some b => .ok b
    | none => .error (.jl .boundsError)

/-- `read(..., UInt8)`, `base/secretbuffer.jl:183-188`. -/
def read (s : SB) : R (UInt8 × SB) := do
  let b <- peek s
  pure (b, { s with ptr := s.ptr + 1 })

def zeroMem (d : ByteMem) : ByteMem := d.map (fun _ => some 0)
/-- `shred!`, `base/secretbuffer.jl:210-215`. -/
def shred (s : SB) : SB := { s with data := zeroMem s.data, ptr := 1, size := 0 }
/-- `isshredded`, `base/secretbuffer.jl:217`. -/
def isshredded (s : SB) : Bool := s.data.all (· = some 0)

structure FinalShredResult where
  warningScheduled : Bool
  value : SB
  deriving DecidableEq

/-- `final_shred!`, `base/secretbuffer.jl:190-193`. -/
def finalShred (s : SB) : FinalShredResult := ⟨!isshredded s, shred s⟩

abbrev CallbackResult (alpha : Type) := R alpha × SB
/-- `shred!(f, x)`, `base/secretbuffer.jl:226-232`, including finally state. -/
def shredDo {alpha : Type} (f : SB -> CallbackResult alpha) (x : SB) : CallbackResult alpha :=
  let result := f x
  (result.1, shred result.2)
end JuliaLean.IOCov.SecretFaithful
end

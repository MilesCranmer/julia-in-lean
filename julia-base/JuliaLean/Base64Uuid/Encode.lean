import JuliaLean.Base64Uuid.Basic

/-!
Model of `stdlib/Base64/src/encode.jl` (master `bbfa0ce4150`; 1.13.2 differs only in
the pipe's type parameter).

`Base64EncodePipe` is modelled by `EPipe`: `out` is everything written to the target
stream `pipe.io` so far, and `buf` is the pipe's `Buffer` contents `data[1:size]`. The
encode pipe never moves `buffer.offset` away from 0, so its capacity is always 512.
Pointer arguments `(ptr, n)` are the list of the `n` bytes at `ptr`.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- `BASE64_ENCODE`, `encode.jl:4`: `'A':'Z'`, `'a':'z'`, `'0':'9'`, `'+'`, `'/'`. -/
def BASE64_ENCODE : List Byte :=
  ((List.range 26).map (fun i => b8 (65 + i))) ++ ((List.range 26).map (fun i => b8 (97 + i))) ++
    ((List.range 10).map (fun i => b8 (48 + i))) ++ [b8 43, b8 47]

/-- `encode(x) = BASE64_ENCODE[(x & 0x3f) + 1]`, `encode.jl:5`. -/
def encode (x : Byte) : Byte := BASE64_ENCODE.getD (bn (band x (b8 0x3f))) (b8 0)

/-- `encodepadding() = UInt8('=')`, `encode.jl:6`. -/
def encodepadding : Byte := b8 61

/-- The four characters `encode.jl:74-77` and `130-134` write for a full triplet. -/
def enc4 (b1 b2 b3 : Byte) : List Byte :=
  [encode (shr b1 2), encode (bor (shl b1 4) (shr b2 4)),
   encode (bor (shl b2 2) (shr b3 6)), encode b3]

/-- Encode pipe state: bytes written to `pipe.io`, and `buffer.data[1:buffer.size]`. -/
structure EPipe where
  out : List Byte
  buf : List Byte
  deriving Repr, DecidableEq

/-- `Base64EncodePipe(io)` on an empty target stream, `encode.jl:38-47`. -/
def EPipe.new : EPipe := ⟨[], []⟩

/-- `loadtriplet!(buffer, ptr, n)`, `encode.jl:140-188`: `(b1, b2, b3, k)`; the buffer
is emptied (`empty!`). Bytes at `ptr` are `xs`, `n = length(xs)`. -/
def loadtriplet (buf xs : List Byte) : Byte × Byte × Byte × Nat :=
  let z := b8 0
  match buf with
  | [] =>
    match xs with
    | [] => (z, z, z, 0)
    | [x1] => (x1, z, z, 1)
    | [x1, x2] => (x1, x2, z, 2)
    | x1 :: x2 :: x3 :: _ => (x1, x2, x3, 3)
  | [c1] =>
    match xs with
    | [] => (c1, z, z, 1)
    | [x1] => (c1, x1, z, 2)
    | x1 :: x2 :: _ => (c1, x1, x2, 3)
  | [c1, c2] =>
    match xs with
    | [] => (c1, c2, z, 2)
    | x1 :: _ => (c1, c2, x1, 3)
  | c1 :: c2 :: c3 :: _ => (c1, c2, c3, 3)

/-- The main loop of `unsafe_write`, `encode.jl:73-91`. `rem` holds the bytes from `p`
to `p_end`; `chunk` is `buffer[1:i]`, the encoded characters not yet written to
`pipe.io`. Returns the output after the loop, the pending chunk and `rem`. -/
def encLoop (b1 b2 b3 : Byte) (out chunk : List Byte) : List Byte → List Byte × List Byte × List Byte
  | x1 :: x2 :: x3 :: rem =>
    let chunk := chunk ++ enc4 b1 b2 b3
    -- `if i + 4 > capacity(buffer)`, capacity 512
    if chunk.length + 4 > 512 then encLoop x1 x2 x3 (out ++ chunk) [] rem
    else encLoop x1 x2 x3 out chunk rem
  | rem => (out, chunk ++ enc4 b1 b2 b3, rem)

/-- `encode.jl:71-99`: the main loop from the first triplet `b1, b2, b3` with `rem`
the bytes after it, the final flush of `buffer[1:i]`, and the leftover bytes stored
in the buffer. -/
def encMain (out : List Byte) (b1 b2 b3 : Byte) (rem : List Byte) : EPipe :=
  let (out, chunk, rem) := encLoop b1 b2 b3 out [] rem
  -- `if i > 0; unsafe_write(pipe.io, pointer(buffer), i)`
  let out := if chunk.length > 0 then out ++ chunk else out
  -- `while p < p_end; buffer[buffer.size+=1] = unsafe_load(p)`
  ⟨out, rem⟩

/-- `Base.unsafe_write(pipe, ptr, n)`, `encode.jl:52-101`, on the bytes `xs`. Returns the
new pipe and the count it returns. -/
def unsafeWrite (pipe : EPipe) (xs : List Byte) : EPipe × Nat :=
  let m := pipe.buf.length
  let (b1, b2, b3, k) := loadtriplet pipe.buf xs
  -- `p = ptr + k - m`
  let rem := xs.drop (k - m)
  if k < 3 then
    if k == 1 then (⟨pipe.out, [b1]⟩, k - m)
    else if k == 2 then (⟨pipe.out, [b1, b2]⟩, k - m)
    else (⟨pipe.out, []⟩, k - m)
  else (encMain pipe.out b1 b2 b3 rem, xs.length)

/-- `Base.write(pipe, x::UInt8)`, `encode.jl:103-110`. -/
def writeByte (pipe : EPipe) (x : Byte) : EPipe :=
  let pipe : EPipe := ⟨pipe.out, pipe.buf ++ [x]⟩
  if pipe.buf.length == 3 then (unsafeWrite pipe []).1 else pipe

/-- `Base.close(pipe)`, `encode.jl:112-137`. -/
def close (pipe : EPipe) : List Byte :=
  let (b1, b2, b3, k) := loadtriplet pipe.buf []
  if k == 0 then pipe.out
  else if k == 1 then
    pipe.out ++ [encode (shr b1 2), encode (shl b1 4), encodepadding, encodepadding]
  else if k == 2 then
    pipe.out ++ [encode (shr b1 2), encode (bor (shl b1 4) (shr b2 4)), encode (shl b2 2),
      encodepadding]
  else pipe.out ++ enc4 b1 b2 b3

/-- One `write` to the pipe: a single `UInt8`, or a byte vector or string, which
`write(io, A)` passes to `unsafe_write(io, pointer(A), sizeof(A))`. -/
inductive WriteOp where
  | byte (x : Byte)
  | bytes (xs : List Byte)
  deriving Repr, DecidableEq

def WriteOp.data : WriteOp → List Byte
  | .byte x => [x]
  | .bytes xs => xs

def applyWrite (pipe : EPipe) : WriteOp → EPipe
  | .byte x => writeByte pipe x
  | .bytes xs => (unsafeWrite pipe xs).1

/-- Writing `ops` to a fresh `Base64EncodePipe(IOBuffer())` and closing it. -/
def encodeStream (ops : List WriteOp) : List Byte := close (ops.foldl applyWrite EPipe.new)

/-- `base64encode(x::Vector{UInt8})`, `encode.jl:207-218`: `write(b, x)`, `close(b)`,
`takestring!(s)`. -/
def base64encode (x : List Byte) : List Byte := close (unsafeWrite EPipe.new x).1

end JuliaLean.Base64Uuid

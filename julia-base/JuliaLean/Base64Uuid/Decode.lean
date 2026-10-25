import JuliaLean.Base64Uuid.Encode

/-!
Model of `stdlib/Base64/src/decode.jl` and `buffer.jl` (master `bbfa0ce4150`; 1.13.2
differs only in the pipe's type parameter and in `decode_slow`'s output closure, which
master turned into `_output`), together with the generic `read(s::IO, nb)` of
`base/io.jl:1326-1335` that `base64decode` calls.

`Base64DecodePipe(IOBuffer(s))` is `DPipe`: `io` is the unread part of the source
`IOBuffer` (so `eof(io)` is `io = []` and `bytesavailable(io)` is its length), `buf` is
the pipe buffer's valid region `data[offset+1 : offset+size]`, and `rest` is
`pipe.rest`. The buffer offset only matters through `capacity`, which `read_to_buffer`
evaluates right after resetting the offset to 0, so it is not tracked.

Loops are given explicit fuel; running out of fuel returns `none`. Every caller in
`Props.lean` supplies enough fuel for the loops to finish whenever Julia's do, except
where a property is about termination itself.
-/

namespace JuliaLean.Base64Uuid

open JuliaLean JuliaLean.ParsePrint

/-- `BASE64_CODE_END`, `BASE64_CODE_PAD`, `BASE64_CODE_IGN`, `decode.jl:4-6`. -/
def CODE_END : Byte := b8 0x40
def CODE_PAD : Byte := b8 0x41
def CODE_IGN : Byte := b8 0x42

/-- `decode(x) = BASE64_DECODE[x + 1]`, `decode.jl:7-12`: the table holds the index of
`x` in `BASE64_ENCODE` (zero-based) for alphabet characters, `CODE_PAD` for `'='`, and
`CODE_IGN` for every other byte. -/
def decode (x : Byte) : Byte :=
  if bn x == 61 then CODE_PAD
  else match BASE64_ENCODE.idxOf? x with
    | some i => b8 i
    | none => CODE_IGN

/-- Decoding pipe state. -/
structure DPipe where
  io : List Byte
  buf : List Byte
  rest : List Byte
  deriving Repr, DecidableEq

/-- `Base64DecodePipe(IOBuffer(s))`, `decode.jl:40-46`. -/
def DPipe.new (s : List Byte) : DPipe := ⟨s, [], []⟩

/-- `read_to_buffer(io, buffer)`, `buffer.jl:29-39`: move the valid region to the front
(offset 0) and append `min(bytesavailable(io), capacity(buffer) - buffer.size)` bytes. -/
def readToBuffer (buf io : List Byte) : List Byte × List Byte :=
  if io.isEmpty then (buf, io)
  else
    let n := min io.length (512 - buf.length)
    (buf ++ io.take n, io.drop n)

/-- `_output(b, p, p_end, rest)`, `decode.jl:184-192`: `out` holds the bytes stored at
`ptr` so far and `room = p_end - ptr`. -/
def output (b : Byte) (out rest : List Byte) (room : Nat) : List Byte × List Byte :=
  if out.length < room then (out ++ [b], rest) else (out, rest ++ [b])

/-- The ignore-skipping loop of `decode_slow`, `decode.jl:137-156`. `buf` is the whole
buffer region and `i` the index of the last buffer byte read; returns the quadruplet,
`i`, and the source `input` after any direct `read(input, UInt8)`. -/
def skipIgn : Nat → Byte → Byte → Byte → Byte → List Byte → Nat → List Byte →
    Option (Byte × Byte × Byte × Byte × Nat × List Byte)
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, b1, b2, b3, b4, buf, i, input =>
    let shifted : Option (Byte × Byte × Byte) :=
      if b1 == CODE_IGN then some (b2, b3, b4)
      else if b2 == CODE_IGN then some (b1, b3, b4)
      else if b3 == CODE_IGN then some (b1, b2, b4)
      else if b4 == CODE_IGN then some (b1, b2, b3)
      else none
    match shifted with
    | none => some (b1, b2, b3, b4, i, input)
    | some (c1, c2, c3) =>
      if i + 1 ≤ buf.length then skipIgn fuel c1 c2 c3 (decode (buf.getD i (b8 0))) buf (i + 1) input
      else match input with
        | x :: input' => skipIgn fuel c1 c2 c3 (decode x) buf i input'
        | [] => skipIgn fuel c1 c2 c3 CODE_END buf i []

/-- Result of `decode_slow`: `(i, p, k == 0)` plus the updated output, `rest` and source. -/
structure SlowRes where
  i : Nat
  out : List Byte
  rest : List Byte
  input : List Byte
  ended : Bool
  deriving Repr, DecidableEq

def isCode (b : Byte) : Bool := b.val < 0x40
def padOrEnd (b : Byte) : Bool := b == CODE_PAD || b == CODE_END

/-- `decode_slow(b1, b2, b3, b4, buffer, i, input, ptr, n, rest)`, `decode.jl:135-182`.
`out` holds the bytes already stored from the caller's `ptr`; `room` is `n` plus their
count, i.e. the distance from the caller's pointer to `p_end`. -/
def decodeSlow (b1 b2 b3 b4 : Byte) (buf : List Byte) (i : Nat) (input : List Byte)
    (out : List Byte) (room : Nat) (rest : List Byte) : Option (Jle SlowRes) :=
  -- fuel for the skip loop: one iteration per remaining character, then at most four
  match skipIgn (buf.length - i + input.length + 6) b1 b2 b3 b4 buf i input with
  | none => none
  | some (b1, b2, b3, b4, i, input) =>
    let z := b8 0
    let r : Option (Byte × Byte × Byte × Byte × Nat) :=
      if isCode b1 && isCode b2 && isCode b3 && isCode b4 then some (b1, b2, b3, b4, 3)
      else if isCode b1 && isCode b2 && isCode b3 && padOrEnd b4 then some (b1, b2, b3, z, 2)
      else if isCode b1 && isCode b2 && padOrEnd b3 && padOrEnd b4 then some (b1, b2, z, z, 1)
      else if b1 == CODE_END && b2 == CODE_END && b3 == CODE_END && b4 == CODE_END then
        some (z, z, z, z, 0)
      else none
    match r with
    | none => some (.error (argErr "malformed base64 sequence"))
    | some (b1, b2, b3, b4, k) =>
      let o1 := bor (shl b1 2) (shr b2 4)
      let o2 := bor (shl b2 4) (shr b3 2)
      let o3 := bor (shl b3 6) b4
      let (out, rest) := if k ≥ 1 then output o1 out rest room else (out, rest)
      let (out, rest) := if k ≥ 2 then output o2 out rest room else (out, rest)
      let (out, rest) := if k ≥ 3 then output o3 out rest room else (out, rest)
      some (.ok ⟨i, out, rest, input, k == 0⟩)

/-- The decoding part of one iteration of `read_until_end`'s loop, `decode.jl:72-83`:
the fast path, or `decode_slow`. Returns `i`, the source, the output, `rest` and
whether the end was reached. -/
def rueStep (b1 b2 b3 b4 : Byte) (buf : List Byte) (i : Nat) (io out : List Byte) (room : Nat)
    (rest : List Byte) : Option (Jle (Nat × List Byte × List Byte × List Byte × Bool)) :=
  if isCode b1 && isCode b2 && isCode b3 && isCode b4 && out.length + 2 < room then
    some (.ok (i, io, out ++ [bor (shl b1 2) (shr b2 4), bor (shl b2 4) (shr b3 2), bor (shl b3 6) b4],
      rest, false))
  else match decodeSlow b1 b2 b3 b4 buf i io out room rest with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok r) => some (.ok (r.i, r.input, r.out, r.rest, r.ended))

/-- The main loop of `read_until_end`, `decode.jl:71-100`, from the top of an iteration
with quadruplet `b1..b4`. `buf` is the buffer region, `i` the local index into it, `io`
the source, `out` the bytes stored at `ptr` so far and `room = n`. Returns `i`, the
buffer, the source, the output and `rest` when the loop exits. -/
def rueLoop : Nat → Byte → Byte → Byte → Byte → List Byte → Nat → List Byte → List Byte → Nat →
    List Byte → Option (Jle (Nat × List Byte × List Byte × List Byte × List Byte))
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | fuel + 1, b1, b2, b3, b4, buf, i, io, out, room, rest =>
    match rueStep b1 b2 b3 b4 buf i io out room rest with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (i, io, out, rest, ended)) =>
      if ended then some (.ok (i, buf, io, out, rest))
      else if out.length < room then
        if i + 4 ≤ buf.length then
          rueLoop fuel (decode (buf.getD i (b8 0))) (decode (buf.getD (i + 1) (b8 0)))
            (decode (buf.getD (i + 2) (b8 0))) (decode (buf.getD (i + 3) (b8 0))) buf (i + 4) io
            out room rest
        else
          -- `consumed!(buffer, i); read_to_buffer(pipe.io, buffer); i = 0`
          let (buf', io') := readToBuffer (buf.drop i) io
          rueLoop fuel CODE_IGN CODE_IGN CODE_IGN CODE_IGN buf' 0 io' out room rest
      else some (.ok (i, buf, io, out, rest))

/-- Fuel that suffices for `read_until_end` on a pipe (see `Proofs`). -/
def rueFuel (pipe : DPipe) : Nat := 4 * (pipe.io.length + pipe.buf.length) + 16

/-- `read_until_end(pipe, ptr, n)`, `decode.jl:60-104`: the bytes stored at `ptr` and the
new pipe. -/
def readUntilEnd (fuel : Nat) (pipe : DPipe) (n : Nat) : Option (Jle (List Byte × DPipe)) :=
  -- `while !isempty(pipe.rest) && p < p_end; unsafe_store!(p, popfirst!(pipe.rest))`
  let k := min n pipe.rest.length
  let out := pipe.rest.take k
  let rest := pipe.rest.drop k
  match rueLoop fuel CODE_IGN CODE_IGN CODE_IGN CODE_IGN pipe.buf 0 pipe.io out n rest with
  | none => none
  | some (.error e) => some (.error e)
  -- `consumed!(buffer, i)`
  | some (.ok (i, buf, io, out, rest)) => some (.ok (out, ⟨io, buf.drop i, rest⟩))

/-- `Base.eof(pipe)`, `decode.jl:131`. -/
def eof (pipe : DPipe) : Bool := pipe.rest.isEmpty && pipe.io.isEmpty

/-- `Base.read(pipe, UInt8)`, `decode.jl:106-114`, via `unsafe_read(pipe, C_NULL, 0)`
(`decode.jl:51-57`, which cannot throw for `n = 0`). -/
def readByte (pipe : DPipe) : Option (Jle (Byte × DPipe)) := do
  let pipe ← if pipe.rest.isEmpty then
      match readUntilEnd (rueFuel pipe) pipe 0 with
      | none => none
      | some (.error e) => return .error e
      | some (.ok (_, pipe)) => pure pipe
    else pure pipe
  match pipe.rest with
  | [] => return .error .eof
  | b :: rest => return .ok (b, { pipe with rest := rest })

/-- A `Vector{UInt8}` argument of `readbytes!`: its length and its first elements. Only
the prefix that `readbytes!` writes matters to the properties; the remaining elements
(old contents, or undefined memory after `resize!`) are not represented. -/
structure Vec where
  len : Nat
  pre : List Byte
  deriving Repr, DecidableEq

/-- One test-and-iteration of the `while` loop of `readbytes!(pipe, data, nb)`,
`decode.jl:119-126`: `.inl` is the state when the loop exits, `.inr` the state after
the iteration. -/
def rbStep (pipe : DPipe) (data : Vec) (filled : Nat) (nb : Int) :
    Option (Jle ((DPipe × Vec × Nat) ⊕ (DPipe × Vec × Nat))) :=
  if (filled : Int) < nb && !eof pipe then
    let data : Vec :=
      if data.len == filled then ⟨(min (2 * (data.len : Int)) nb).toNat, data.pre⟩ else data
    let room := ((min (data.len : Int) nb) - filled).toNat
    match readUntilEnd (rueFuel pipe) pipe room with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (got, pipe)) =>
      some (.ok (.inr (pipe, ⟨data.len, data.pre.take filled ++ got⟩, filled + got.length)))
  else some (.ok (.inl (pipe, data, filled)))

/-- The `while` loop of `readbytes!(pipe, data, nb)`, `decode.jl:119-126`. -/
def readbytesLoop : Nat → DPipe → Vec → Nat → Int → Option (Jle (DPipe × Vec × Nat))
  | 0, _, _, _, _ => none
  | fuel + 1, pipe, data, filled, nb =>
    match rbStep pipe data filled nb with
    | none => none
    | some (.error e) => some (.error e)
    | some (.ok (.inl r)) => some (.ok r)
    | some (.ok (.inr (pipe, data, filled))) => readbytesLoop fuel pipe data filled nb

/-- `readbytes!(pipe, data, nb)`, `decode.jl:116-129`, with explicit fuel for its loop:
the pipe afterwards, `data` after the final `resize!(data, filled)`, and `filled`. -/
def readbytesF (fuel : Nat) (pipe : DPipe) (data : Vec) (nb : Int) : Option (Jle (DPipe × Vec × Nat)) :=
  match readbytesLoop fuel pipe data 0 nb with
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok (pipe, data, filled)) => some (.ok (pipe, ⟨filled, data.pre.take filled⟩, filled))

/-- Fuel that suffices for `readbytes!` whenever the destination is nonempty or `nb ≤ 0`. -/
def rbFuel (pipe : DPipe) (data : Vec) : Nat :=
  2 * (pipe.io.length + pipe.buf.length + pipe.rest.length + data.len) + 8

/-- `typemax(Int)`. -/
def typemaxInt : Int := 2 ^ 63 - 1

/-- `read(pipe, nb)`, `base/io.jl:1326-1335`: `b = Vector{UInt8}(undef, nb == typemax(Int)
? 1024 : nb)` (an `ArgumentError` for `nb < 0`), `readbytes!(pipe, b, nb)`, `resize!(b, nr)`. -/
def readN (pipe : DPipe) (nb : Int) : Option (Jle (List Byte × DPipe)) :=
  if nb < 0 then some (.error (argErr "invalid GenericMemory size")) else
  let data : Vec := ⟨if nb == typemaxInt then 1024 else nb.toNat, []⟩
  match readbytesF (rbFuel pipe data) pipe data nb with
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok (pipe, data, _)) => some (.ok (data.pre, pipe))

/-- `read(pipe)` = `read(pipe, typemax(Int))`. -/
def readAll (pipe : DPipe) : Option (Jle (List Byte × DPipe)) := readN pipe typemaxInt

/-- `base64decode(s)`, `decode.jl:217-224`: `read(Base64DecodePipe(IOBuffer(s)))`. -/
def base64decode (s : List Byte) : Option (Jle (List Byte)) :=
  match readAll (DPipe.new s) with
  | none => none
  | some (.error e) => some (.error e)
  | some (.ok (out, _)) => some (.ok out)

end JuliaLean.Base64Uuid

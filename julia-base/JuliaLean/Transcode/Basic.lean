import JuliaLean.Strings.Char

/-!
# Transcoding between UTF-8, UTF-16 and UTF-32, `base/strings/cstring.jl`

Model of the `transcode` methods, `cwstring`, the `Cstring`/`Cwstring` NUL
checks and `containsnul` (master `bbfa0ce4150`).

* Byte, code-unit and `Char` values are Lean `UInt8`/`UInt16`/`UInt32`, whose
  operators wrap exactly like Julia's unsigned operators (`+%`, `<<`, `xor`).
* The source vector is read strictly left to right: every `src[i += 1]` in the
  Julia loops is guarded by `i < n`. The model keeps the unread suffix `rest`
  of `src` (so `i < n` is `rest ≠ []`) and reads with `nextB`, which throws
  `BoundsError` on an empty suffix exactly as `src[n + 1]` would.
* `while true` loops are structural recursion on a bound on the remaining
  iterations; every iteration reads at least one element, so `rest.length + 1`
  never runs out (`Transcode/Utf16.lean` proves it).
* The size `m` and index `j` of `transcode(UInt8, ::AbstractVector{UInt16})`
  are `Int` (`JInt64`) values; the written prefix of `dst` is a list whose
  length is `j`.
-/

namespace JuliaLean.Transcode

open JuliaLean.Strings

/-- `b % Int8` as an integer. -/
def sx (b : UInt8) : Int := if b.toNat < 128 then b.toNat else (b.toNat : Int) - 256

/-- `src[i += 1]` on the unread suffix of `src`. -/
def nextB {α : Type} : List α → SJl (α × List α)
  | [] => .error boundsErr
  | b :: r => .ok (b, r)

/-- The end of every loop body: `i < n || break; a = src[i += 1]`, then the next
iteration `loop a rest dst`. -/
def stepNext {α β : Type} (loop : α → List α → β → SJl β) (dst : β) (rest : List α) : SJl β :=
  if rest.isEmpty then .ok dst
  else do let (a, rest) ← nextB rest; loop a rest dst

/-! ## UTF-8 to UTF-16 -/

/-- `xor(0x3080, UInt16(a) << 6, b)`, the 2-byte branch (`base/strings/cstring.jl:200`). -/
def dec2 (a b : UInt8) : UInt16 := (0x3080 : UInt16) ^^^ (a.toUInt16 <<< 6) ^^^ b.toUInt16

/-- `xor(0x2080, UInt16(a) << 12, UInt16(b) << 6, c)`, the 3-byte branch (`:207`)
and, applied to `b, c, d`, the overlong 4-byte branch (`:214`). -/
def dec3 (a b c : UInt8) : UInt16 :=
  (0x2080 : UInt16) ^^^ (a.toUInt16 <<< 12) ^^^ (b.toUInt16 <<< 6) ^^^ c.toUInt16

/-- First unit of the 4-byte branch (`:216`). -/
def dec4hi (a b c : UInt8) : UInt16 :=
  (0xe5b8 : UInt16) + (a.toUInt16 <<< 8) + (b.toUInt16 <<< 2) + (c >>> 4).toUInt16

/-- Second unit of the 4-byte branch (`:217`). -/
def dec4lo (c d : UInt8) : UInt16 :=
  (0xdc80 : UInt16) ^^^ ((c &&& 0xf).toUInt16 <<< 6) ^^^ d.toUInt16

/-- `-64 <= a % Int8 <= -12` (`base/strings/cstring.jl:193`): `a` is one of the
lead bytes `C0..F4`. -/
def isLead (a : UInt8) : Bool := decide (-64 ≤ sx a) && decide (sx a ≤ -12)

/-- The `while true` loop of `transcode(::Type{UInt16}, src::AbstractVector{UInt8})`,
`base/strings/cstring.jl:192-232`: `a` is the current byte, `rest` the unread
bytes, `dst` the code units pushed so far. -/
def u16Loop : Nat → UInt8 → List UInt8 → List UInt16 → SJl (List UInt16)
  | 0, _, _, _ => .error .assertion
  | k + 1, a, rest, dst =>
    if !rest.isEmpty && isLead a then do
      let (b, rest) ← nextB rest
      if decide (-64 ≤ sx b) || (a == 0xf4 && decide (0x8f < b)) then
        u16Loop k b rest (dst ++ [a.toUInt16])
      else if a < 0xe0 then
        stepNext (u16Loop k) (dst ++ [dec2 a b]) rest
      else if !rest.isEmpty then do
        let (c, rest) ← nextB rest
        if decide (-64 ≤ sx c) then
          u16Loop k c rest (dst ++ [a.toUInt16, b.toUInt16])
        else if a < 0xf0 then
          stepNext (u16Loop k) (dst ++ [dec3 a b c]) rest
        else if !rest.isEmpty then do
          let (d, rest) ← nextB rest
          if decide (-64 ≤ sx d) then
            u16Loop k d rest (dst ++ [a.toUInt16, b.toUInt16, c.toUInt16])
          else if a == 0xf0 && b < 0x90 then
            stepNext (u16Loop k) (dst ++ [dec3 b c d]) rest
          else
            stepNext (u16Loop k) (dst ++ [dec4hi a b c, dec4lo c d]) rest
        else .ok (dst ++ [a.toUInt16, b.toUInt16, c.toUInt16])
      else .ok (dst ++ [a.toUInt16, b.toUInt16])
    else stepNext (u16Loop k) (dst ++ [a.toUInt16]) rest

/-- `transcode(UInt16, src::AbstractVector{UInt8})`, `base/strings/cstring.jl:185-234`;
`transcode(UInt16, s::String)` is this on `codeunits(s)` (`:178`). -/
def transcode16 (src : List UInt8) : SJl (List UInt16) :=
  match src with
  | [] => .ok []
  | a :: rest => u16Loop src.length a rest []

/-! ## UTF-16 to UTF-8 -/

/-- First loop of `transcode(::Type{UInt8}, src::AbstractVector{UInt16})`,
`base/strings/cstring.jl:249-269`: the number `m` of bytes to allocate. -/
def cntLoop : Nat → UInt16 → List UInt16 → JInt64 → SJl JInt64
  | 0, _, _, _ => .error .assertion
  | k + 1, a, rest, m =>
    if a < 0x80 then stepNext (cntLoop k) (m + ix 1) rest
    else if a < 0x800 then stepNext (cntLoop k) (m + ix 2) rest
    else if (a &&& 0xfc00) == 0xd800 && !rest.isEmpty then do
      let (b, rest) ← nextB rest
      if (b &&& 0xfc00) == 0xdc00 then stepNext (cntLoop k) (m + ix 4) rest
      else cntLoop k b rest (m + ix 3)
    else stepNext (cntLoop k) (m + ix 3) rest

/-- `dst[j += 1] = x` for `dst = StringVector(m)`, with `j = dst.length`. -/
def put (m : JInt64) (dst : List UInt8) (x : UInt8) : SJl (List UInt8) :=
  if (dst.length : Int) + 1 ≤ m.val then .ok (dst ++ [x]) else .error boundsErr

/-- `0x80 | (x & 0x3f)`: a continuation byte holding the low six bits of `x`. -/
def cont (x : UInt8) : UInt8 := (0x80 : UInt8) ||| (x &&& (0x3f : UInt8))

/-- The bytes of the 2-byte branch, `base/strings/cstring.jl:278-279`. -/
def enc2 (a : UInt16) : List UInt8 := [(0xc0 : UInt8) ||| (a >>> 6).toUInt8, cont a.toUInt8]

/-- The bytes of the 3-byte branches, `base/strings/cstring.jl:290-292,298-300`. -/
def enc3 (a : UInt16) : List UInt8 :=
  [(0xe0 : UInt8) ||| (a >>> 12).toUInt8, cont (a >>> 6).toUInt8, cont a.toUInt8]

/-- The bytes of the surrogate-pair branch, `base/strings/cstring.jl:284-288`
(`a +%= 0x2840` first). -/
def enc4 (a b : UInt16) : List UInt8 :=
  let a := a + 0x2840
  [(0xf0 : UInt8) ||| (a >>> 8).toUInt8, (0x80 : UInt8) ||| (a.toUInt8 >>> 2),
   (0xf0 : UInt8) ^^^ ((a.toUInt8 <<< 4) &&& (0x3f : UInt8)) ^^^ (b >>> 6).toUInt8,
   cont b.toUInt8]

/-- `dst[j += 1] = x` for each byte of `xs`, in order. -/
def putAll (m : JInt64) (dst : List UInt8) : List UInt8 → SJl (List UInt8)
  | [] => .ok dst
  | x :: xs => do let dst ← put m dst x; putAll m dst xs

/-- Second loop of `transcode(::Type{UInt8}, src::AbstractVector{UInt16})`,
`base/strings/cstring.jl:274-304`: writes the bytes into `StringVector(m)`. -/
def wrLoop (m : JInt64) : Nat → UInt16 → List UInt16 → List UInt8 → SJl (List UInt8)
  | 0, _, _, _ => .error .assertion
  | k + 1, a, rest, dst =>
    if a < 0x80 then do
      let dst ← putAll m dst [a.toUInt8]
      stepNext (wrLoop m k) dst rest
    else if a < 0x800 then do
      let dst ← putAll m dst (enc2 a)
      stepNext (wrLoop m k) dst rest
    else if (a &&& 0xfc00) == 0xd800 && !rest.isEmpty then do
      let (b, rest) ← nextB rest
      if (b &&& 0xfc00) == 0xdc00 then do
        let dst ← putAll m dst (enc4 a b)
        stepNext (wrLoop m k) dst rest
      else do
        let dst ← putAll m dst (enc3 a)
        wrLoop m k b rest dst
    else do
      let dst ← putAll m dst (enc3 a)
      stepNext (wrLoop m k) dst rest

/-- Result of `transcode(UInt8, ::AbstractVector{UInt16})`: the allocated length
`m` of `StringVector(m)` and the bytes written into it (positions beyond
`written.length` are left uninitialized). -/
structure Out where
  m : JInt64
  written : List UInt8
  deriving DecidableEq, Repr

/-- `transcode(::Type{UInt8}, src::AbstractVector{UInt16})`, `base/strings/cstring.jl:236-306`. -/
def transcode8 (src : List UInt16) : SJl Out :=
  match src with
  | [] => .ok ⟨ix 0, []⟩
  | a :: rest => do
    let m ← cntLoop src.length a rest (ix 0)
    let w ← wrLoop m src.length a rest []
    .ok ⟨m, w⟩

/-! ## UTF-32 -/

/-- `transcode(::Type{UInt32}, src::String) = UInt32[UInt32(c) for c in src]`,
`base/strings/cstring.jl:164`, with `UInt32(c::Char) = codepoint(c)`. -/
def transcode32 (s : JStr) : SJl (List UInt32) := (chars s).mapM codepoint

/-- `transcode(::Type{UInt8}, src::Vector{UInt32})`, `base/strings/cstring.jl:170-176`:
`print(buf, Char(c))` for each element, `Char(::UInt32)` from `base/char.jl`. -/
def transcode8of32 (src : List UInt32) : SJl (List UInt8) := do
  let cs ← src.mapM charOfU32
  .ok (cs.flatMap charBytes)

/-- `Char(x::Int32) = Char(UInt32(x))`: `InexactError` for negative `x`. -/
def charOfI32 (x : Int) : SJl UInt32 :=
  if 0 ≤ x then charOfU32 (UInt32.ofNat x.toNat) else .error (.jl (.inexactError "convert"))

/-- `transcode(::Type{UInt8}, src::Vector{Int32})`, `base/strings/cstring.jl:170-176`:
each element is converted in turn, so the first failing element decides the exception. -/
def transcode8ofI32 (src : List Int) : SJl (List UInt8) := do
  let cs ← src.mapM charOfI32
  .ok (cs.flatMap charBytes)

/-! ## NUL checks -/

/-- `containsnul(s::String)`, `base/strings/cstring.jl:80`: `memchr` for a zero byte. -/
def containsnulStr (s : JStr) : Bool := s.bytes.contains 0

/-- `containsnul(s::AbstractString) = '\0' in s`, `base/strings/cstring.jl:81`;
`'\0'` is the bit pattern `0`. -/
def containsnulAbs (s : JStr) : Bool := (chars s).contains 0

/-- `unsafe_convert(::Type{Cstring}, s::String)`, `base/strings/cstring.jl:83-88`:
the bytes the C function sees (up to the trailing NUL every `String` has). -/
def unsafeConvertCstring (s : JStr) : SJl (List UInt8) :=
  if containsnulStr s then .error (.jl (.argumentError "embedded NULs are not allowed in C strings"))
  else .ok s.bytes

/-- `cconvert(::Type{Cwstring}, v::Vector{Cwchar_t})`, `base/strings/cstring.jl:92-100`. -/
def cconvertCwVec {α : Type} [BEq α] [OfNat α 0] (v : List α) : SJl (List α) :=
  if v.dropLast.any (· == 0) then
    .error (.jl (.argumentError "embedded NULs are not allowed in C strings"))
  else match v.getLast? with
    | none => .error boundsErr
    | some x => if x == 0 then .ok v
      else .error (.jl (.argumentError "C string data must be NUL terminated"))

/-- `cconvert(::Type{Cwstring}, s::AbstractString)` on Windows, where
`Cwchar_t = UInt16`, `base/strings/cstring.jl:69-73`. -/
def cconvertCwstringWin (s : JStr) : SJl (List UInt16) := do
  let v ← transcode16 s.bytes
  cconvertCwVec (v ++ [0])

/-- `cconvert(::Type{Cwstring}, s::AbstractString)` on Linux and macOS, where
`Cwchar_t = Int32`: `transcode(Int32, s)`, whose values are `codepoint`s
(below `2^21`, so `Int32(codepoint(c))` never throws). -/
def cconvertCwstringUnix (s : JStr) : SJl (List UInt32) := do
  let v ← transcode32 s
  cconvertCwVec (v ++ [0])

/-- `Base.cwstring(s)` (Windows only), `base/strings/cstring.jl:119-123`. -/
def cwstring (s : JStr) : SJl (List UInt16) :=
  if s.bytes.contains 0 then
    .error (.jl (.argumentError "embedded NULs are not allowed in C strings"))
  else do
    let w ← transcode16 s.bytes
    .ok (w ++ [0])

end JuliaLean.Transcode

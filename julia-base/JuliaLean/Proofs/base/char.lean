import JuliaLean.base.char
import JuliaLean.base.int
import JuliaLean.base.float
import JuliaLean.base.strings.io
import JuliaLean.base.intfuncs
import JuliaLean.base.strings.unicode
import JuliaLean.Proofs.base.int
import JuliaLean.Proofs.base.float
import JuliaLean.Registry.Types

/-!
# Properties of `base/char.jl`

The properties use `JChar` as the raw 32-bit storage of a Julia `Char`. Generic Julia callees that live outside `base/char.jl` remain typed parameters in the relevant statement.
-/

namespace JuliaLean.Proofs.base.char

open JuliaLean JuliaLean.base.char JuliaLean.base.int

/-! Nothing to promise: AbstractChar(x::Number)@55: this is a pure fallback to the Char numeric constructor. -/
/-! Nothing to promise: (::Type{T})(x::T)@58: this is the identity conversion for an already-correct AbstractChar type. -/
/-! Nothing to promise: UInt32_cold@222: this is the cold-path forwarding call to UInt32(c). -/
/-! Nothing to promise: Char_cold@228: this is the cold-path forwarding call to Char(b). -/
/-! Nothing to promise: convert(::Type{AbstractChar}, x::Number)@233: this forwards to Char(x). -/
/-! Nothing to promise: convert(::Type{T}, x::Number)@234: this forwards to T(x). -/
/-! Nothing to promise: convert(::Type{T}, x::AbstractChar) where T<:Number@235: this forwards to T(x). -/
/-! Nothing to promise: convert(::Type{T}, c::AbstractChar) where T<:AbstractChar@236: this forwards to T(c). -/
/-! Nothing to promise: convert(::Type{T}, c::T)@237: this returns its already-correct input unchanged. -/

/-!
## Method coverage

| Julia method | Registry property or Nothing to promise |
|---|---|
| `(::Type{T})(x::Number) where T<:AbstractChar`@54 | `char-integer-conversions` |
| `AbstractChar(x::Number)`@55 | Nothing to promise |
| `(::Type{T})(x::AbstractChar) where T<:Union{Number,AbstractChar}`@56 | `char-integer-conversions` |
| `(::Type{T})(x::AbstractChar) where T<:Union{Int32,Int64}`@57 | `char-integer-conversions` |
| `(::Type{T})(x::T) where T<:AbstractChar`@58 | Nothing to promise |
| `ncodeunits(c::Char)`@71 | `missingchar-ncodeunits-write` |
| `codepoint(c::Char)`@100 | `missingchar-codepoint-malformed`, `missingchar-codepoint-wellformed`, `missingchar-char-codepoint-roundtrip` |
| `throw_invalid_char(c::AbstractChar)`@108 | `missingchar-codepoint-malformed` |
| `throw_code_point_err(u::Integer)`@109 | `missingchar-char-codepoint-roundtrip` |
| `ismalformed(c::Char)`@111 | `missingchar-codepoint-malformed`, `intfuncscov-char-encoding` |
| `is_overlong_enc(u::UInt32)`@119 | `char-overlong-encoding` |
| `isoverlong(c::Char)`@121 | `char-overlong-encoding`, `missingchar-char-codepoint-roundtrip` |
| `ismalformed(c::AbstractChar)`@146 | `intfuncscov-char-encoding` |
| `isoverlong(c::AbstractChar)`@156 | `intfuncscov-char-encoding` |
| `UInt32(c::Char)`@158 | `missingchar-codepoint-malformed`, `missingchar-codepoint-wellformed`, `intfuncscov-char-encoding` |
| `unsafe_codepoint(c::AbstractChar)`@183 | `char-unsafe-codepoint` |
| `unsafe_codepoint(c::Char)`@184 | `char-unsafe-codepoint` |
| `decode_overlong(c::AbstractChar)`@209 | `char-overlong-decode` |
| `Char(u::UInt32)`@211 | `missingchar-char-codepoint-roundtrip`, `missingchar-char-order-codepoint` |
| `UInt32_cold(c::Char)`@222 | Nothing to promise |
| `(T::Union{Type{Int8},Type{UInt8}})(c::Char)`@223 | `char-smallinteger-conversions` |
| `Char_cold(b::UInt32)`@228 | Nothing to promise |
| `Char(b::Union{Int8,UInt8})`@229 | `char-smallinteger-conversions` |
| `convert(::Type{AbstractChar}, x::Number)`@233 | Nothing to promise |
| `convert(::Type{T}, x::Number) where T<:AbstractChar`@234 | Nothing to promise |
| `convert(::Type{T}, x::AbstractChar) where T<:Number`@235 | Nothing to promise |
| `convert(::Type{T}, c::AbstractChar) where T<:AbstractChar`@236 | Nothing to promise |
| `convert(::Type{T}, c::T) where T<:AbstractChar`@237 | Nothing to promise |
| `rem(x::AbstractChar, ::Type{T}) where T<:Number`@239 | `char-remainder-codepoint` |
| `typemax(::Type{Char})`@241 | `intfuncscov-char-scalar` |
| `typemin(::Type{Char})`@242 | `intfuncscov-char-scalar` |
| `size(c::AbstractChar)`@244 | `intfuncscov-char-scalar` |
| `size(c::AbstractChar, d::Integer)`@245 | `intfuncscov-char-scalar` |
| `ndims(c::AbstractChar)`@246 | `intfuncscov-char-scalar` |
| `ndims(::Type{<:AbstractChar})`@247 | `intfuncscov-char-scalar` |
| `length(c::AbstractChar)`@248 | `intfuncscov-char-scalar` |
| `IteratorSize(::Type{<:AbstractChar})`@249 | `intfuncscov-char-scalar` |
| `firstindex(c::AbstractChar)`@250 | `intfuncscov-char-scalar` |
| `lastindex(c::AbstractChar)`@251 | `intfuncscov-char-scalar` |
| `getindex(c::AbstractChar)`@252 | `intfuncscov-char-scalar` |
| `getindex(c::AbstractChar, i::Integer)`@253 | `intfuncscov-char-scalar` |
| `getindex(c::AbstractChar, I::Integer...)`@254 | `intfuncscov-char-scalar` |
| `first(c::AbstractChar)`@255 | `intfuncscov-char-scalar` |
| `last(c::AbstractChar)`@256 | `intfuncscov-char-scalar` |
| `eltype(::Type{T}) where T<:AbstractChar`@257 | `intfuncscov-char-scalar` |
| `iterate(c::AbstractChar, done=false)`@259 | `intfuncscov-char-scalar` |
| `isempty(c::AbstractChar)`@260 | `intfuncscov-char-scalar` |
| `in(x::AbstractChar, y::AbstractChar)`@261 | `intfuncscov-char-scalar` |
| `==(x::Char, y::Char)`@263 | `missingchar-char-order-codepoint`, `char-hash-equality` |
| `isless(x::Char, y::Char)`@264 | `missingchar-char-order-codepoint` |
| `hash(x::Char, h::UInt)`@265 | `char-hash-equality` |
| `isless(x::AbstractChar, y::AbstractChar)`@269 | `char-abstract-comparisons` |
| `==(x::AbstractChar, y::AbstractChar)`@270 | `char-abstract-comparisons` |
| `hash(x::AbstractChar, h::UInt)`@271 | `char-hash-equality` |
| `widen(::Type{T}) where T<:AbstractChar`@272 | `intfuncscov-char-scalar` |
| `-%(x::AbstractChar, y::AbstractChar)`@274 | `char-difference-codepoint` |
| `-(x::AbstractChar, y::AbstractChar)`@275 | `char-difference-codepoint` |
| `-%(x::T, y::Integer) where T<:AbstractChar`@276 | `char-sub-codepoint` |
| `+%(x::T, y::Integer) where T<:AbstractChar`@286 | `missingchar-char-add-codepoint` |
| `+%(x::Integer, y::AbstractChar)`@296 | `missingchar-char-add-codepoint` |
| `-(x::AbstractChar, y::Integer)`@298 | `char-sub-codepoint` |
| `+(x::AbstractChar, y::Integer)`@299 | `missingchar-char-add-codepoint` |
| `+(x::Integer, y::AbstractChar)`@300 | `missingchar-char-add-codepoint` |
| `print(io::IO, c::Char)`@305 | `intfuncscov-char-display` |
| `print(io::IO, c::AbstractChar)`@306 | `char-abstract-print`, `intfuncscov-char-display` |
| `show_invalid(io::IO, c::Char)`@313 | `char-show-invalid-bytes`, `intfuncscov-char-display` |
| `show(io::IO, c::AbstractChar)`@336 | `missingchar-show-char-roundtrip`, `char-show-control-escapes`, `char-show-printable` |
| `show(io::IO, ::MIME"text/plain", c::T)`@372 | `char-show-plain-compact`, `char-show-plain-category`, `char-show-plain-state`, `intfuncscov-char-display` |
-/

/-! ## Unicode codepoints and Char construction -/

/-- The UTF-8 byte count of a left-aligned Char storage pattern, with NUL requiring one byte. -/
def rawCharByteCount (c : JChar) : Nat :=
  let n := c.toNat
  if n % 256 != 0 then 4 else if n / 256 % 256 != 0 then 3
  else if n / 65536 % 256 != 0 then 2 else 1

/-- A hex digit in the lowercase alphabet used by show_invalid. -/
def specHexDigit (digit : Nat) : UInt8 :=
  if digit < 10 then UInt8.ofNat (0x30 + digit) else UInt8.ofNat (0x61 + digit - 10)

/-- The per-byte write events promised by show_invalid. -/
def showInvalidTraceLoopSpec : Nat → JChar → List CharOutput
  | 0, _ => []
  | fuel + 1, u =>
    let a := specHexDigit (((ushr32 u 28) &&& 0xf).toNat)
    let b := specHexDigit (((ushr32 u 24) &&& 0xf).toNat)
    [.bytes [0x5c, 0x78, a, b]] ++
      (if shl32 u 8 == 0 then [] else showInvalidTraceLoopSpec fuel (shl32 u 8))

def showInvalidTraceSpec (c : JChar) : List CharOutput :=
  [.bytes [0x27]] ++ showInvalidTraceLoopSpec 4 c ++ [.bytes [0x27]]

/-- Escape mapping for the control characters handled before the general display path. -/
def controlEscapeSpec (c : JChar) : Option UInt8 :=
  if c == 0 then some 0x30 else
  if c == 0x07000000 then some 0x61 else
  if c == 0x08000000 then some 0x62 else
  if c == 0x09000000 then some 0x74 else
  if c == 0x0a000000 then some 0x6e else
  if c == 0x0b000000 then some 0x76 else
  if c == 0x0c000000 then some 0x66 else
  if c == 0x0d000000 then some 0x72 else
  if c == 0x1b000000 then some 0x65 else
  if c == 0x27000000 then some 0x27 else
  if c == 0x5c000000 then some 0x5c else none


/-- `codepoint(c::Char)` throws on malformed storage, as promised by the codepoint and malformed-character documentation. -/
def CodepointThrowsMalformed : Prop :=
  ∀ c : JChar, ismalformed_Char charBitOps c = true →
    ∃ e, codepoint_Char charBitOps c = .error e

/-- `codepoint(c)` succeeds for every non-malformed Char, including overlong encodings and invalid Unicode codepoints. -/
def CodepointWellFormed : Prop :=
  ∀ c : JChar, ismalformed_Char charBitOps c = false →
    ∃ u, codepoint_Char charBitOps c = .ok u

/-- `Char(u)` encodes every accepted unsigned codepoint and rejects values at or above `0x200000`. -/
def CharCodepointRoundTrip : Prop :=
  ∀ u : JChar,
    (0x00200000 ≤ u → char_UInt32 u = .error (.codePointError u)) ∧
    (u < 0x00200000 → ∃ c, char_UInt32 u = .ok c ∧
      codepoint_Char charBitOps c = .ok u ∧
      ismalformed_Char charBitOps c = false ∧ isoverlong_Char c = false)

/-- The safe and unsafe decoders agree on non-malformed input; the generic fallbacks forward. -/
def UnsafeCodepointAgrees : Prop :=
  (∀ c u, ismalformed_Char charBitOps c = false →
    codepoint_Char charBitOps c = .ok u → unsafe_codepoint_Char charBitOps c = u) ∧
  (∀ {C : Type} (toUInt32 : C → CharResult JChar) (c : C),
    unsafe_codepoint_AbstractChar toUInt32 c = toUInt32 c)

def OverlongDecodeCodepoint : Prop :=
  (∀ c u, isoverlong_Char c = true → codepoint_Char charBitOps c = .ok u →
    decodeOverlongChar c = .ok u) ∧
  (∀ {C N : Type} (codepoint : C → CharResult N) (c : C),
    decode_overlong_AbstractChar codepoint c = codepoint c)


/- The generic fallback methods reject no malformed or overlong encodings by default. -/
def CharAbstractDefaults : Prop :=
  ∀ {C : Type} (c : C),
    ismalformed_AbstractChar c = false ∧ isoverlong_AbstractChar c = false

/- The fallback comparison methods compare the converted Char values. -/
def CharAbstractComparison : Prop :=
  ∀ {C : Type} (toChar : C → CharResult JChar) (x y : C) c d,
    toChar x = .ok c → toChar y = .ok d →
    isless_AbstractChar toChar toChar isless_Char x y = .ok (isless_Char c d) ∧
    eq_AbstractChar toChar toChar eq_Char x y = .ok (eq_Char c d)

/- The codepoint/validity methods in this file distinguish overlong UTF-8 sequences by their encoded byte count. -/
def minimumUtf8Bytes (u : JChar) : Nat :=
  if u ≤ 0x7f then 1 else if u ≤ 0x7ff then 2 else if u ≤ 0xffff then 3 else 4

def CharOverlongEncoding : Prop :=
  ∀ c u, ismalformed_Char charBitOps c = false →
    codepoint_Char charBitOps c = .ok u →
    isoverlong_Char c = decide (rawCharByteCount c > minimumUtf8Bytes u)

def CharIntegerConversions : Prop :=
  (∀ c u, codepoint_Char charBitOps c = .ok u →
    constructor_Integer_AbstractChar .i32 codepointChar remUInt32ToIntTy c =
      .ok (remT .i32 (jUInt32 u))) ∧
  (∀ c u, codepoint_Char charBitOps c = .ok u →
    constructor_Integer_AbstractChar .i64 codepointChar remUInt32ToIntTy c =
      .ok (remT .i64 (jUInt32 u))) ∧
  (∀ {N C : Type} (toUInt32 : N → CharResult JChar)
    (construct : JChar → CharResult C) (x : N) u c,
    toUInt32 x = .ok u → construct u = .ok c →
    constructor_Number_AbstractChar toUInt32 construct x = .ok c) ∧
  (∀ {C N D : Type} (codepoint : C → CharResult N)
    (construct : N → CharResult D) (x : C) u value,
    codepoint x = .ok u → construct u = .ok value →
    constructor_AbstractChar_AbstractChar codepoint construct x = .ok value) ∧
  (∀ {C : Type} (c : C), constructor_Same_AbstractChar c = c)

/-- The character remainder method applies integer remainder to the decoded codepoint. -/
def CharRemainderCodepoint : Prop :=
  ∀ {C N R : Type} (codepoint : C → CharResult N)
    (rem : N → R → CharResult R) (c : C) (target : R) n,
    codepoint c = .ok n →
    rem_AbstractChar_Number codepoint rem c target = rem n target

def CharSmallIntegerConstruction : Prop :=
  (∀ {B : Type} (isAscii : B → Bool) (smallBits : B → JChar)
    (toUInt32 : B → CharResult JChar) (b : B),
    (isAscii b = true → char_SmallInteger isAscii smallBits toUInt32 b =
      .ok (shl32 (smallBits b) 24)) ∧
    (isAscii b = false → ∀ u, toUInt32 b = .ok u →
      char_SmallInteger isAscii smallBits toUInt32 b = char_cold u)) ∧
  (∀ {T : Type} (bitcastInt32 : JChar → Int32) (nonnegative : Int32 → Bool)
    (logicalShift : Int32 → Int32) (narrow : Int32 → CharResult T)
    (construct : JChar → CharResult T) (ops : CharBitOps) (c : JChar),
    (nonnegative (bitcastInt32 c) = true →
      smallIntegerFromChar bitcastInt32 nonnegative logicalShift narrow construct ops c =
        narrow (logicalShift (bitcastInt32 c))) ∧
    (nonnegative (bitcastInt32 c) = false →
      ∀ u, uint32_cold c ops = .ok u →
        smallIntegerFromChar bitcastInt32 nonnegative logicalShift narrow construct ops c =
          construct u))

def CharHashRespectsEquality : Prop :=
  (∀ (hashFinalizer : UInt64 → UInt64) (x y : JChar) (h : UInt64),
    eq_Char x y = true → hash_Char hashFinalizer x h = hash_Char hashFinalizer y h) ∧
  (∀ {C : Type} (toChar : C → CharResult JChar)
    (hashFinalizer : UInt64 → UInt64) (x : C) (h : UInt64) c,
    toChar x = .ok c →
    hash_AbstractChar toChar (hash_Char hashFinalizer) x h = .ok (hash_Char hashFinalizer c h))
/-- Char print passes the character to `write` and returns its updated IO state. -/
def CharPrintWritesChar : Prop :=
  ∀ {IO : Type} (writeChar : IO → JChar → CharResult (IO × JInt64))
    (io : IO) (c : JChar) (io' : IO) (count : JInt64),
    writeChar io c = .ok (io', count) →
    print_Char writeChar io c = .ok (io', ())

/-- The AbstractChar print fallback converts through Char before using print. -/
def AbstractCharPrintUsesChar : Prop :=
  ∀ {C IO : Type} (toChar : C → CharResult JChar)
    (printChar : IO → JChar → CharResult (IO × Unit))
    (io : IO) (c : C) value (io' : IO),
    toChar c = .ok value →
    printChar io value = .ok (io', ()) →
    print_AbstractChar toChar printChar io c = .ok (io', ())

/-- Non-compact plain display appends the category abbreviation and description last. -/
def PlainDisplayReportsCategory : Prop :=
  ∀ (ops : CharPlainShowOps JChar (List CharOutput) JChar) (c : JChar)
    (trace : List CharOutput) (abbreviation description : String),
    ops.compact [] = .ok false →
    ops.categoryAbbrev c = .ok abbreviation →
    ops.categoryString c = .ok description →
    ops.printStrings = printStringsTrace →
    show_MIMETextPlain ops [] c = .ok (trace, ()) →
    trace.getLast? = some (.text [" (category ", abbreviation, ": ", description, ")"])

/-- Plain display reports malformed, overlong, and decoded codepoint state. -/
def PlainDisplayReportsState : Prop :=
  ∀ (ops : CharPlainShowOps JChar (List CharOutput) JChar) (c : JChar)
    (initial trace : List CharOutput),
    ops.printStrings = printStringsTrace →
    ops.showValue [] c = .ok (initial, ()) →
    ops.compact initial = .ok false →
    show_MIMETextPlain ops [] c = .ok (trace, ()) →
    (ops.isMalformed c = true →
      CharOutput.text [": Malformed UTF-8"] ∈ trace) ∧
    (∀ u converted padded, ops.isMalformed c = false → ops.isOverlong c = true →
      ops.decodeOverlong c = .ok u → ops.constructFromNumber u = .ok converted →
      ops.stringBase16Pad4 u = .ok padded →
      CharOutput.text [": "] ∈ trace ∧
      CharOutput.text ["[overlong] "] ∈ trace ∧
      CharOutput.text [if ops.isAscii converted then "ASCII/" else "",
        "Unicode U+", ops.uppercase padded] ∈ trace) ∧
    (∀ u padded, ops.isMalformed c = false → ops.isOverlong c = false →
      ops.codepoint c = .ok u → ops.stringBase16Pad4 u = .ok padded →
      CharOutput.text [": "] ∈ trace ∧
      CharOutput.text [if ops.isAscii c then "ASCII/" else "",
        "Unicode U+", ops.uppercase padded] ∈ trace)

/-- `ncodeunits(c)` equals the number of bytes needed to encode every raw Char pattern. -/
def NcodeunitsWrite : Prop :=
  ∀ c : JChar,
    ncodeunits_Char (E := CharError) (JInt.lit .i64 4) divInt64 charBitOps iszeroUInt32 c =
      .ok (JInt.lit .i64 (Int.ofNat (rawCharByteCount c)))

/-- Each malformed display escape consists of one quoted `\x` escape per stored leading byte. -/
def ShowInvalidEscapes : Prop :=
  ∀ c : JChar,
    show_invalid_Char writeBytesTrace [] c =
      .ok (showInvalidTraceSpec c, JInt.lit .i64 1)

/-- The `show` method uses the documented short escapes for ASCII controls and quotes. -/
def ShowControlEscapes : Prop :=
  ∀ (isPrint : JChar → Bool) (c : JChar) (escape : UInt8),
    controlEscapeSpec c = some escape →
    show_AbstractChar (charShowOps isPrint) [] c =
      .ok ([.bytes [0x27, 0x5c, escape, 0x27]], ())

/-- Printable, well-formed Chars are displayed between single quotes using `print`. -/
def ShowPrintableChars : Prop :=
  ∀ (isPrint : JChar → Bool) (c : JChar),
    controlEscapeSpec c = none → isPrint c = true →
    ismalformed_Char charBitOps c = false → isoverlong_Char c = false →
    show_AbstractChar (charShowOps isPrint) [] c =
      .ok ([.bytes [0x27], .character c, .bytes [0x27]], ())

/-- The show output for every non-malformed, non-overlong Char is accepted as a Char literal by a parser that accepts ordinary Char literals. -/
/- The parser belongs to JuliaSyntax and remains an external typed callee. -/
def ShowCharParses : Prop :=
  ∀ (isPrint : JChar → Bool) (parse : List CharOutput → Option JChar),
    (∀ c, parse [.bytes [0x27], .character c, .bytes [0x27]] = some c) →
    ∀ (c : JChar) (trace : List CharOutput),
      ismalformed_Char charBitOps c = false → isoverlong_Char c = false →
      show_AbstractChar (charShowOps isPrint) [] c = .ok (trace, ()) →
      parse trace = some c


/-- Compact plain-text display adds no category annotation after the ordinary Char display. -/
def PlainDisplayCompact : Prop :=
  ∀ {C IO N : Type} (ops : CharPlainShowOps C IO N) (io : IO) (c : C),
    ops.compact io = .ok true →
    show_MIMETextPlain ops io c = do
      let (io, _) ← ops.showValue io c
      pure (io, ())

def CharEncodingBehavior : Prop :=
  CodepointThrowsMalformed ∧ CodepointWellFormed ∧ CharCodepointRoundTrip ∧
  UnsafeCodepointAgrees ∧ OverlongDecodeCodepoint ∧ CharOverlongEncoding ∧
  CharAbstractDefaults ∧ CharIntegerConversions ∧ CharSmallIntegerConstruction ∧
  CharRemainderCodepoint

def CharDisplayBehavior : Prop :=
  CharPrintWritesChar ∧ AbstractCharPrintUsesChar ∧ ShowInvalidEscapes ∧
  ShowControlEscapes ∧ ShowPrintableChars ∧ ShowCharParses ∧ PlainDisplayCompact ∧
  PlainDisplayReportsCategory ∧ PlainDisplayReportsState

/-! ## Approved statements (round 1)

The specification side is independent of the model: a Julia `Char` stores the UTF-8 bytes of
one character left-aligned in 32 bits (char.jl:5-51). The adapters only change representation
(Lean `Int32`/`UInt32` to `JInt`) around installed `int` definitions. -/

open JuliaLean.base

/-- Byte `k` (0 = most significant) of the 32-bit storage of a Char. -/
def storageByte (c : JChar) (k : Nat) : Nat := c.toNat / 2 ^ (8 * (3 - k)) % 256

/-- Number of stored bytes: the leading bytes up to the last nonzero one; `'\0'` stores one. -/
def storedCount (c : JChar) : Nat :=
  if storageByte c 3 ≠ 0 then 4 else if storageByte c 2 ≠ 0 then 3
  else if storageByte c 1 ≠ 0 then 2 else 1

/-- The bytes a Char stores, in order. -/
def storedBytes (c : JChar) : List Nat := (List.range (storedCount c)).map (storageByte c)

/-- `bytes` is exactly one UTF-8 sequence, shortest or overlong, for the integer `u`. -/
def Utf8Seq : List Nat → Nat → Prop
  | [b], u => b < 0x80 ∧ u = b
  | [b1, b2], u => b1 / 32 = 6 ∧ b2 / 64 = 2 ∧ u = (b1 % 32) * 64 + b2 % 64
  | [b1, b2, b3], u => b1 / 16 = 14 ∧ b2 / 64 = 2 ∧ b3 / 64 = 2 ∧
      u = (b1 % 16) * 4096 + (b2 % 64) * 64 + b3 % 64
  | [b1, b2, b3, b4], u => b1 / 8 = 30 ∧ b2 / 64 = 2 ∧ b3 / 64 = 2 ∧ b4 / 64 = 2 ∧
      u = (b1 % 8) * 262144 + (b2 % 64) * 4096 + (b3 % 64) * 64 + b4 % 64
  | _, _ => False

/-- Length of the shortest UTF-8 sequence for `u`. -/
def minimalUtf8Length (u : Nat) : Nat :=
  if u < 0x80 then 1 else if u < 0x800 then 2 else if u < 0x10000 then 3 else 4

/-- `c` is the standard (shortest) UTF-8 encoding of `u`. -/
def ProperlyEncoded (c : JChar) (u : Nat) : Prop :=
  Utf8Seq (storedBytes c) u ∧ (storedBytes c).length = minimalUtf8Length u

/-- `z` is representable in the Julia integer type `t`. -/
def fitsIntTy (t : IntTy) (z : Int) : Prop :=
  if t.signed then -(2 ^ (t.bits - 1) : Int) ≤ z ∧ z < 2 ^ (t.bits - 1)
  else 0 ≤ z ∧ z < 2 ^ t.bits

/-- Output bytes of a display trace: raw byte writes, the stored bytes of written characters,
and the UTF-8 bytes of printed strings (as approved in round 1). -/
def flattenOutput : List CharOutput → List Nat
  | [] => []
  | .bytes bs :: rest => bs.map UInt8.toNat ++ flattenOutput rest
  | .character c :: rest => storedBytes c ++ flattenOutput rest
  | .text parts :: rest =>
      (parts.map fun s => s.toUTF8.data.toList.map UInt8.toNat).flatten ++ flattenOutput rest

/-- ASCII byte of the lowercase hexadecimal digit `d < 16`. -/
def hexDigitByte (d : Nat) : Nat := if d < 10 then 0x30 + d else 0x61 + (d - 10)

/-- The `\xHH` escape (lowercase digits) of one byte. -/
def hexByteEscape (b : Nat) : List Nat := [0x5c, 0x78, hexDigitByte (b / 16), hexDigitByte (b % 16)]

/-- `T(x::UInt32)` for an integer type `T`: installed `int.convert`. -/
def convertUInt32To (t : IntTy) (u : JChar) : CharResult (JInt t) := liftJl (int.convert t (jUInt32 u))

/-- `rem(x::UInt32, T)`: installed `int.remT`; the model passes the target type as a value. -/
def remUInt32Target {t : IntTy} (u : JChar) (_target : JInt t) : CharResult (JInt t) :=
  .ok (int.remT t (jUInt32 u))

/-- `Int(x)` for a Char: the model's own `(::Type{Int64})(x::AbstractChar)` at char.jl:57. -/
def charToInt64 (c : JChar) : CharResult JInt64 :=
  constructor_Integer_AbstractChar .i64 (codepoint_Char charBitOps) remUInt32ToIntTy c

/-- `bitcast(Int32, c)`: installed `int.bitcast`. -/
def bitcastInt32Of (c : JChar) : Int32 :=
  Int32.ofInt (int.bitcast .i32 (jUInt32 c) (by decide)).val

/-- `i ≥ 0` for `i::Int32` against the `Int` literal: installed `int.lePromote`. -/
def nonnegativeInt32 (i : Int32) : Bool := int.lePromote (JInt.lit .i64 0) (JInt.lit .i32 i.toInt)

/-- `i >>> 24` for `i::Int32`: installed `int.lshr_Int`. -/
def lshr24Int32 (i : Int32) : Int32 :=
  Int32.ofInt (int.lshr_Int (JInt.lit .i32 i.toInt) (JInt.lit .i64 24)).val

/-- `x % T` for `x::Int32`: installed `int.remT`. -/
def remInt32To (t : IntTy) (i : Int32) : CharResult (JInt t) := .ok (int.remT t (JInt.lit .i32 i.toInt))

/-- missingchar-codepoint-malformed: codepoint(c) and UInt32(c) throw exactly when c is
malformed (char.jl:83-92, 135-142, 46-48). -/
def CodepointThrowsExactlyMalformed : Prop :=
  ∀ c : JChar,
    ((∃ e, codepoint_Char charBitOps c = .error e) ↔ ismalformed_Char charBitOps c = true) ∧
    ((∃ e, uint32_Char charBitOps c = .error e) ↔ ismalformed_Char charBitOps c = true)

/-- missingchar-codepoint-wellformed: a Char storing one UTF-8 sequence for `u` is not
malformed and codepoint(c) and UInt32(c) return `u` (char.jl:80-92, 135-142). -/
def CodepointDecodesUtf8 : Prop :=
  ∀ (c : JChar) (u : Nat), Utf8Seq (storedBytes c) u →
    ismalformed_Char charBitOps c = false ∧
    codepoint_Char charBitOps c = .ok (UInt32.ofNat u) ∧
    uint32_Char charBitOps c = .ok (UInt32.ofNat u)

/-- char-ismalformed-exact-sequence: a non-malformed Char stores exactly one UTF-8 sequence
(char.jl:129-142). -/
def NonMalformedIsOneSequence : Prop :=
  ∀ c : JChar, ismalformed_Char charBitOps c = false → ∃ u, Utf8Seq (storedBytes c) u

/-- char-overlong-encoding: isoverlong(c) iff c stores one UTF-8 sequence longer than the
shortest one for its value (char.jl:148-152, 16-22). -/
def IsoverlongExactlyOverlong : Prop :=
  ∀ c : JChar, isoverlong_Char c = true ↔
    ∃ u, Utf8Seq (storedBytes c) u ∧ minimalUtf8Length u < (storedBytes c).length

/-- char-unsafe-codepoint: for every non-malformed Char, unsafe_codepoint(c) equals
codepoint(c) (char.jl:173-181). -/
def UnsafeCodepointMatches : Prop :=
  ∀ c : JChar, ismalformed_Char charBitOps c = false →
    codepoint_Char charBitOps c = .ok (unsafe_codepoint_Char charBitOps c)

/-- char-overlong-decode: whenever isoverlong(c), decode_overlong(c) returns the codepoint
the stored sequence encodes (char.jl:194-206). -/
def DecodeOverlongCodepoint : Prop :=
  ∀ c : JChar, isoverlong_Char c = true →
    ∃ u, Utf8Seq (storedBytes c) u ∧
      decode_overlong_AbstractChar (codepoint_Char charBitOps) c = .ok (UInt32.ofNat u)

/-- missingchar-char-codepoint-roundtrip: Char(u::UInt32) throws for `u ≥ 0x200000`;
otherwise it is the standard encoding of `u`, well-formed, not overlong, and
codepoint(Char(u)) == u (char.jl:9-14, 16-22, 39-51). -/
def CharFromUInt32 : Prop :=
  ∀ u : JChar,
    (0x00200000 ≤ u → ∃ e, char_UInt32 u = .error e) ∧
    (u < 0x00200000 → ∃ c, char_UInt32 u = .ok c ∧ ProperlyEncoded c u.toNat ∧
      codepoint_Char charBitOps c = .ok u ∧
      ismalformed_Char charBitOps c = false ∧ isoverlong_Char c = false)

/-- missingchar-char-order-codepoint: for standard encodings, Char order and equality are
codepoint order and equality (char.jl:10-12). -/
def CharOrderCodepoint : Prop :=
  ∀ (c d : JChar) (u v : Nat), ProperlyEncoded c u → ProperlyEncoded d v →
    isless_Char c d = decide (u < v) ∧ eq_Char c d = decide (u = v)

/-- char-remainder-codepoint: rem(c, T) for an integer type T is the codepoint reduced to T;
a malformed Char throws (char.jl:80-92). -/
def RemainderCodepoint : Prop :=
  ∀ (t : IntTy) (c : JChar) (target : JInt t),
    let r := rem_AbstractChar_Number (codepoint_Char charBitOps) remUInt32Target c target
    (∀ u, Utf8Seq (storedBytes c) u → r = .ok (JInt.lit t u)) ∧
    (ismalformed_Char charBitOps c = true → ∃ e, r = .error e)

/-- char-smallinteger-conversions: Char(b::Int8/UInt8) is the standard encoding of a
nonnegative `b` and throws for a negative one; Int8(c)/UInt8(c) return the codepoint when it
fits and throw otherwise or for a malformed Char (char.jl:9-10, 39-51, 80-92). -/
def SmallIntegerConversions : Prop :=
  ∀ t ∈ [IntTy.i8, IntTy.u8],
    (∀ b : JInt t,
      let r := char_SmallInteger isAsciiSmall smallBitsUInt32 uint32OfInteger b
      (0 ≤ b.val → ∃ c, r = .ok c ∧ ProperlyEncoded c b.val.toNat) ∧
      (b.val < 0 → ∃ e, r = .error e)) ∧
    (∀ c : JChar,
      let r := smallIntegerFromChar bitcastInt32Of nonnegativeInt32 lshr24Int32
        (remInt32To t) (convertUInt32To t) charBitOps c
      (∀ u, Utf8Seq (storedBytes c) u →
        (fitsIntTy t u → r = .ok (JInt.lit t u)) ∧ (¬ fitsIntTy t u → ∃ e, r = .error e)) ∧
      (ismalformed_Char charBitOps c = true → ∃ e, r = .error e))

/-- char-difference-codepoint: for two Chars, c - d and c -% d are the Int difference of the
codepoints; a malformed operand throws (char.jl:9-12, 80-92). -/
def CharDifferenceCodepoint : Prop :=
  ∀ c d : JChar,
    let r1 := sub_AbstractChar_AbstractChar charToInt64 charToInt64 int.sub c d
    let r2 := subWrap_AbstractChar_AbstractChar charToInt64 charToInt64 int.subWrap c d
    (∀ u v, Utf8Seq (storedBytes c) u → Utf8Seq (storedBytes d) v →
      r1 = .ok (JInt.lit .i64 ((u : Int) - v)) ∧ r2 = .ok (JInt.lit .i64 ((u : Int) - v))) ∧
    (ismalformed_Char charBitOps c = true ∨ ismalformed_Char charBitOps d = true →
      (∃ e, r1 = .error e) ∧ (∃ e, r2 = .error e))

/-- missingchar-char-add-codepoint (Int64 component; full Integer domain needs model R2):
Char with Int in either order is the standard encoding of codepoint(c) + n when that is in
[0, 0x200000), an error otherwise or for a malformed Char. -/
def CharAddInt64 : Prop :=
  ∀ (c : JChar) (n : JInt64),
    ∀ r ∈ [addWrap_AbstractChar_Integer charIntegerOps c n, add_AbstractChar_Integer charIntegerOps c n,
        addWrap_Integer_AbstractChar charIntegerOps n c, add_Integer_AbstractChar charIntegerOps n c],
      (ismalformed_Char charBitOps c = true → ∃ e, r = .error e) ∧
      (∀ u, Utf8Seq (storedBytes c) u →
        ((0 ≤ (u : Int) + n.val ∧ (u : Int) + n.val < 0x200000) →
          ∃ d, r = .ok d ∧ ProperlyEncoded d ((u : Int) + n.val).toNat) ∧
        (¬ (0 ≤ (u : Int) + n.val ∧ (u : Int) + n.val < 0x200000) → ∃ e, r = .error e))

/-- char-sub-codepoint (Int64 component; full Integer domain needs model R2): Char minus Int
is the standard encoding of codepoint(c) - n when representable, an error otherwise or for a
malformed Char. -/
def CharSubInt64 : Prop :=
  ∀ (c : JChar) (n : JInt64),
    ∀ r ∈ [subWrap_AbstractChar_Integer charIntegerOps c n, sub_AbstractChar_Integer charIntegerOps c n],
      (ismalformed_Char charBitOps c = true → ∃ e, r = .error e) ∧
      (∀ u, Utf8Seq (storedBytes c) u →
        ((0 ≤ (u : Int) - n.val ∧ (u : Int) - n.val < 0x200000) →
          ∃ d, r = .ok d ∧ ProperlyEncoded d ((u : Int) - n.val).toNat) ∧
        (¬ (0 ≤ (u : Int) - n.val ∧ (u : Int) - n.val < 0x200000) → ∃ e, r = .error e))

/-- intfuncscov-char-scalar: typemax(Char) and typemin(Char) are the largest and smallest
Char under isless. -/
def CharTypeExtrema : Prop :=
  ∀ c : JChar,
    isless_Char (typemax_Char (UInt32.ofNat (int.typemax .u32).val.toNat)) c = false ∧
    isless_Char c (typemin_Char (UInt32.ofNat (int.typemin .u32).val.toNat)) = false

/-- char-show-invalid-bytes: show_invalid writes a quoted `\xHH` escape for each stored byte
and nothing else (char.jl:325-331, 46-48). -/
def ShowInvalidEscapesStoredBytes : Prop :=
  ∀ c : JChar, ∃ io n, show_invalid_Char writeBytesTrace [] c = .ok (io, n) ∧
    flattenOutput io = [0x27] ++ (storedBytes c).flatMap hexByteEscape ++ [0x27]

/-! ## Approved statements (round 2) -/

/-- `UInt32(x::Bool)`: installed `int.ofBool`. -/
def uint32OfBool (b : Bool) : CharResult JChar := .ok (UInt32.ofNat (int.ofBool .u32 b).val.toNat)

/-- `UInt32(x::IEEEFloat)`: installed `float.intOfFloat` (InexactError unless exact). -/
def uint32OfFloat {Tf : float.FTy} (x : float.FV Tf) : CharResult JChar := do
  let u ← liftJl (float.intOfFloat .u32 x)
  pure (UInt32.ofNat u.val.toNat)

/-- `T(x::UInt32)` for an IEEE float type `T`: installed `float.floatOfInt`. -/
def floatOfUInt32 (Tf : float.FTy) (u : JChar) : CharResult (float.FV Tf) :=
  .ok (float.floatOfInt Tf (jUInt32 u))


/-- `string(u, base = 16, pad = 4)` for `u::UInt32`: installed `intfuncs.stringBits` (its
buffer bytes are the String's bytes). -/
def hexPad4 (digits : intfuncs.DigitCallees) (u : JChar) : CharResult String := do
  let buf ← liftJl (intfuncs.stringBits digits (jUInt32 u) (JInt.lit .i64 16) (JInt.lit .i64 4))
  pure (String.ofList (buf.bytes.map Char.ofNat))

/-- `Unicode.category_abbrev(c::Char)`: installed `unicode.category_abbrev_Char`. -/
def categoryAbbrevChar (P : strings.unicode.Utf8proc) (c : JChar) : CharResult String :=
  .ok (strings.unicode.category_abbrev_Char P c)

/-- `Unicode.category_string(c::Char)`: installed `unicode.category_string_Char`. Its
`UnicodeError` is carried unchanged in `CharError.unicodeError`; for a Char the
installed category code never fails. -/
def categoryStringChar (P : strings.unicode.Utf8proc)
    (bounds : strings.unicode.CategoryCodeBounds
      (strings.unicode.category_code_AbstractChar strings.unicode.charOps P))
    (c : JChar) : CharResult String :=
  match strings.unicode.category_string_Char strings.unicode.charOps P bounds c with
  | .ok s => .ok s
  | .error e => .error (.unicodeError e)
/-- `Char(x)` for an integer `x::T`, by Julia dispatch: `Char(::UInt32)` (char.jl:211),
`Char(::Union{Int8,UInt8})` (229), otherwise `(::Type{T})(x::Number)` (54). -/
def charOfIntegerDispatch : (t : IntTy) → JInt t → CharResult JChar
  | .u32, x => char_UInt32 (UInt32.ofNat x.val.toNat)
  | .u8, x => char_SmallInteger isAsciiSmall smallBitsUInt32 uint32OfInteger x
  | .i8, x => char_SmallInteger isAsciiSmall smallBitsUInt32 uint32OfInteger x
  | .i16, x => constructor_Number_AbstractChar uint32OfInteger char_UInt32 x
  | .i32, x => constructor_Number_AbstractChar uint32OfInteger char_UInt32 x
  | .i64, x => constructor_Number_AbstractChar uint32OfInteger char_UInt32 x
  | .i128, x => constructor_Number_AbstractChar uint32OfInteger char_UInt32 x
  | .u16, x => constructor_Number_AbstractChar uint32OfInteger char_UInt32 x
  | .u64, x => constructor_Number_AbstractChar uint32OfInteger char_UInt32 x
  | .u128, x => constructor_Number_AbstractChar uint32OfInteger char_UInt32 x

/-- The four public routes from a number to a Char, given the `Char(x)` method Julia selects:
`Char(x)`, `AbstractChar(x)` (char.jl:55), `convert(AbstractChar, x)` (233), `convert(Char, x)` (234). -/
def numberToCharRoutes {N : Type} (charOf : N → CharResult JChar) (x : N) : List (CharResult JChar) :=
  [charOf x,
   constructor_AbstractChar_Number charOf x,
   convert_AbstractChar_Number charOf x,
   convert_TypeAbstractChar_Number charOf x]

/-- Output bytes of a display trace, with written characters as the bytes of the installed
`write(io, ::Char)` model and printed strings as their UTF-8 bytes. -/
def flattenWritten : List CharOutput → List Nat
  | [] => []
  | .bytes bs :: rest => bs.map UInt8.toNat ++ flattenWritten rest
  | .character c :: rest => (strings.io.charUtf8Bytes c).map UInt8.toNat ++ flattenWritten rest
  | .text parts :: rest =>
      (parts.map fun s => s.toUTF8.data.toList.map UInt8.toNat).flatten ++ flattenWritten rest

def hexDigitValue (d : Nat) : Option Nat :=
  if 0x30 ≤ d ∧ d ≤ 0x39 then some (d - 0x30)
  else if 0x61 ≤ d ∧ d ≤ 0x66 then some (d - 0x61 + 10)
  else if 0x41 ≤ d ∧ d ≤ 0x46 then some (d - 0x41 + 10)
  else none

def hexValue (digits : List Nat) : Option Nat :=
  digits.foldl (fun acc d => acc.bind fun v => (hexDigitValue d).map fun x => v * 16 + x) (some 0)

/-- Julia's one-character escapes inside a character literal and the codepoint each denotes
(`\0` is the octal escape for NUL). -/
def letterEscape : Nat → Option Nat
  | 0x30 => some 0x00 | 0x61 => some 0x07 | 0x62 => some 0x08 | 0x74 => some 0x09
  | 0x6e => some 0x0a | 0x76 => some 0x0b | 0x66 => some 0x0c | 0x72 => some 0x0d
  | 0x65 => some 0x1b | 0x27 => some 0x27 | 0x5c => some 0x5c | 0x22 => some 0x22
  | _ => none

/-- Julia character-literal syntax: `CharLiteral bytes c` means the source bytes read back as
the Char `c`. -/
inductive CharLiteral : List Nat → JChar → Prop where
  | raw (c : JChar) (u : Nat) : ProperlyEncoded c u → c ≠ 0x27000000 → c ≠ 0x5c000000 →
      CharLiteral ([0x27] ++ storedBytes c ++ [0x27]) c
  | letter (b u : Nat) : letterEscape b = some u →
      CharLiteral [0x27, 0x5c, b, 0x27] (UInt32.ofNat (u * 0x1000000))
  | bytes (c : JChar) :
      CharLiteral ([0x27] ++ (storedBytes c).flatMap hexByteEscape ++ [0x27]) c
  | shortU (digits : List Nat) (u : Nat) (c : JChar) :
      1 ≤ digits.length → digits.length ≤ 4 → hexValue digits = some u → ProperlyEncoded c u →
      CharLiteral ([0x27, 0x5c, 0x75] ++ digits ++ [0x27]) c
  | longU (digits : List Nat) (u : Nat) (c : JChar) :
      1 ≤ digits.length → digits.length ≤ 8 → hexValue digits = some u → ProperlyEncoded c u →
      CharLiteral ([0x27, 0x5c, 0x55] ++ digits ++ [0x27]) c

/-- char-integer-conversions: with Julia's dispatch, every number equal to an integer `n` with
`0 ≤ n < 0x200000` becomes the standard encoding of `n` through each public route, and every
other number throws (char.jl:9-10, 16-18, 39-51). -/
def NumberToChar : Prop :=
  (∀ (t : IntTy) (x : JInt t), ∀ r ∈ numberToCharRoutes (charOfIntegerDispatch t) x,
    (0 ≤ x.val ∧ x.val < 0x200000 → ∃ c, r = .ok c ∧ ProperlyEncoded c x.val.toNat) ∧
    (¬ (0 ≤ x.val ∧ x.val < 0x200000) → ∃ e, r = .error e)) ∧
  (∀ b : Bool,
    ∀ r ∈ numberToCharRoutes (constructor_Number_AbstractChar uint32OfBool char_UInt32) b,
    ∃ c, r = .ok c ∧ ProperlyEncoded c (if b then 1 else 0)) ∧
  (∀ (Tf : float.FTy) (x : float.FV Tf),
    ∀ r ∈ numberToCharRoutes (constructor_Number_AbstractChar uint32OfFloat char_UInt32) x,
    let exact (n : Int) : Prop := x.isfinite = true ∧ x.toRat.1 = n * (x.toRat.2 : Int)
    (∀ n : Int, exact n → 0 ≤ n → n < 0x200000 → ∃ c, r = .ok c ∧ ProperlyEncoded c n.toNat) ∧
    ((¬ ∃ n : Int, exact n ∧ 0 ≤ n ∧ n < 0x200000) → ∃ e, r = .error e)) ∧
  (∀ (N : Type) (toUInt32 : N → CharResult JChar) (x : N),
    ∀ r ∈ numberToCharRoutes (constructor_Number_AbstractChar toUInt32 char_UInt32) x,
    (∀ u, toUInt32 x = .ok u →
      (u < 0x00200000 → ∃ c, r = .ok c ∧ ProperlyEncoded c u.toNat) ∧
      (0x00200000 ≤ u → ∃ e, r = .error e)) ∧
    (∀ e, toUInt32 x = .error e → r = .error e)) ∧
  (∀ (C : Type) (codepoint : C → CharResult JChar) (x : C),
    let r := constructor_AbstractChar_AbstractChar codepoint char_UInt32 x
    (∀ u, codepoint x = .ok u →
      (u < 0x00200000 → ∃ c, r = .ok c ∧ ProperlyEncoded c u.toNat) ∧
      (0x00200000 ≤ u → ∃ e, r = .error e)) ∧
    (∀ e, codepoint x = .error e → r = .error e))

/-- char-numeric-from-char: converting a Char to a number gives its codepoint; a malformed
Char throws (char.jl:9-10, 26-28, 46-48, 80-92). -/
def NumericFromChar : Prop :=
  (∀ t ∈ [IntTy.i32, IntTy.i64], ∀ c : JChar,
    let toInt := constructor_Integer_AbstractChar t (codepoint_Char charBitOps) remUInt32ToIntTy
    ∀ r ∈ [toInt c, convert_TypeNumber_AbstractChar toInt c],
      (∀ u, Utf8Seq (storedBytes c) u → r = .ok (JInt.lit t u)) ∧
      (ismalformed_Char charBitOps c = true → ∃ e, r = .error e)) ∧
  (∀ (t : IntTy), t ∉ [IntTy.i8, IntTy.u8, IntTy.i32, IntTy.i64, IntTy.u32] → ∀ c : JChar,
    let conv := constructor_AbstractChar_AbstractChar (codepoint_Char charBitOps) (convertUInt32To t)
    ∀ r ∈ [conv c, convert_TypeNumber_AbstractChar conv c],
      (∀ u, Utf8Seq (storedBytes c) u →
        (fitsIntTy t u → r = .ok (JInt.lit t u)) ∧ (¬ fitsIntTy t u → ∃ e, r = .error e)) ∧
      (ismalformed_Char charBitOps c = true → ∃ e, r = .error e)) ∧
  (∀ c : JChar,
    let r := convert_TypeNumber_AbstractChar (uint32_Char charBitOps) c
    (∀ u, Utf8Seq (storedBytes c) u → r = .ok (UInt32.ofNat u)) ∧
    (ismalformed_Char charBitOps c = true → ∃ e, r = .error e)) ∧
  (∀ (Tf : float.FTy) (c : JChar),
    let r := constructor_AbstractChar_AbstractChar (codepoint_Char charBitOps) (floatOfUInt32 Tf) c
    (∀ u, Utf8Seq (storedBytes c) u → r = .ok (float.floatOfInt Tf (JInt.lit .u32 u))) ∧
    (ismalformed_Char charBitOps c = true → ∃ e, r = .error e))

/-- missingchar-ncodeunits-write: ncodeunits(c) is the number of bytes `write(io, c)` emits
(installed `strings.io.charUtf8Bytes`), which is the number of stored UTF-8 bytes
(char.jl:60-65). -/
def NcodeunitsCountsWrittenBytes : Prop :=
  ∀ c : JChar,
    ncodeunits_Char (JInt.lit .i64 (int.sizeofT .u32)) divInt64 charBitOps iszeroUInt32 c =
      .ok (JInt.lit .i64 (strings.io.charUtf8Bytes c).length) ∧
    ncodeunits_Char (JInt.lit .i64 (int.sizeofT .u32)) divInt64 charBitOps iszeroUInt32 c =
      .ok (JInt.lit .i64 (storedBytes c).length)

/-- missingchar-show-char-roundtrip: show(io, c) never throws and its output, with characters
written by the installed `write(io, ::Char)` model, reads back as `c` under Julia's
character-literal syntax, for every Char and whatever isprint answers. -/
def ShowCharLiteralRoundTrip : Prop :=
  ∀ (isPrint : JChar → Bool) (c : JChar), ∃ trace,
    show_AbstractChar (charShowOps isPrint) [] c = .ok (trace, ()) ∧
    CharLiteral (flattenWritten trace) c

/-! ## Refutations (concrete `reinterpret(Char, ·)` values; repro/<id>.jl) -/

theorem ok_error_absurd {α : Type} {x : CharResult α} {v : α} {e : CharError}
    (hv : x = .ok v) (he : x = .error e) : False := by
  rw [hv] at he; cases he

theorem mal_6162 : ismalformed_Char charBitOps 0x61620000 = true := by decide
theorem cp_6162 : codepoint_Char charBitOps 0x61620000 = .ok 0x61 := by rfl
theorem mal_41c0 : ismalformed_Char charBitOps 0x41c00000 = true := by decide
theorem mal_4180 : ismalformed_Char charBitOps 0x41800000 = false := by decide
theorem sb_4180 : storedBytes 0x41800000 = [0x41, 0x80] := by decide
theorem ov_c0 : isoverlong_Char 0xc0000000 = true := by decide
theorem sb_c0 : storedBytes 0xc0000000 = [0xc0] := by decide
theorem wr_4180 : (strings.io.charUtf8Bytes 0x41800000).map UInt8.toNat = [0x41, 0x80] := by decide

theorem show_4180 :
    show_AbstractChar (charShowOps (fun _ => true)) [] 0x41800000 =
      .ok ([.bytes [0x27], .character 0x41800000, .bytes [0x27]], ()) := by rfl

/-- `reinterpret(Char, 0x61620000)` is malformed, yet codepoint returns 0x61. -/
theorem refute_codepoint_malformed : ¬ CodepointThrowsExactlyMalformed := by
  intro h
  obtain ⟨e, he⟩ := (h 0x61620000).1.2 mal_6162
  exact ok_error_absurd cp_6162 he

/-- `Int32(reinterpret(Char, 0x41c00000))` returns 65 for a malformed Char. -/
theorem refute_numeric_from_char : ¬ NumericFromChar := by
  intro h
  obtain ⟨e, he⟩ := (h.1 IntTy.i32 (by simp) 0x41c00000 _ (List.mem_cons_self ..)).2 mal_41c0
  obtain ⟨v, hv⟩ : ∃ v, constructor_Integer_AbstractChar .i32 (codepoint_Char charBitOps)
      remUInt32ToIntTy 0x41c00000 = .ok v := ⟨_, rfl⟩
  exact ok_error_absurd hv he

/-- `reinterpret(Char, 0x41c00000) % UInt8` returns 0x41 for a malformed Char. -/
theorem refute_remainder : ¬ RemainderCodepoint := by
  intro h
  obtain ⟨e, he⟩ := (h .u8 0x41c00000 (JInt.lit .u8 0)).2 mal_41c0
  obtain ⟨v, hv⟩ : ∃ v, rem_AbstractChar_Number (codepoint_Char charBitOps) remUInt32Target
      (0x41c00000 : JChar) (JInt.lit .u8 0) = .ok v := ⟨_, rfl⟩
  exact ok_error_absurd hv he

/-- `reinterpret(Char, 0x41c00000) - 'A'` returns 0 for a malformed Char. -/
theorem refute_difference : ¬ CharDifferenceCodepoint := by
  intro h
  obtain ⟨⟨e, he⟩, _⟩ := (h 0x41c00000 0x41000000).2 (Or.inl mal_41c0)
  obtain ⟨v, hv⟩ : ∃ v, sub_AbstractChar_AbstractChar charToInt64 charToInt64 int.sub
      (0x41c00000 : JChar) 0x41000000 = .ok v := ⟨_, rfl⟩
  exact ok_error_absurd hv he

/-- `UInt8(reinterpret(Char, 0x41c00000))` returns 0x41 for a malformed Char. -/
theorem refute_smallinteger : ¬ SmallIntegerConversions := by
  intro h
  obtain ⟨e, he⟩ := ((h .u8 (by simp)).2 0x41c00000).2 mal_41c0
  obtain ⟨v, hv⟩ : ∃ v, smallIntegerFromChar bitcastInt32Of nonnegativeInt32 lshr24Int32
      (remInt32To .u8) (convertUInt32To .u8) charBitOps 0x41c00000 = .ok v := ⟨_, rfl⟩
  exact ok_error_absurd hv he

/-- `reinterpret(Char, 0x41c00000) + 1` returns 'B' for a malformed Char. -/
theorem refute_add : ¬ CharAddInt64 := by
  intro h
  obtain ⟨e, he⟩ := (h 0x41c00000 (JInt.lit .i64 1) _ (List.mem_cons_self ..)).1 mal_41c0
  obtain ⟨v, hv⟩ : ∃ v, addWrap_AbstractChar_Integer charIntegerOps (0x41c00000 : JChar)
      (JInt.lit .i64 1) = .ok v := ⟨_, rfl⟩
  exact ok_error_absurd hv he

/-- `reinterpret(Char, 0x41c00000) - 1` returns '@' for a malformed Char. -/
theorem refute_sub : ¬ CharSubInt64 := by
  intro h
  obtain ⟨e, he⟩ := (h 0x41c00000 (JInt.lit .i64 1) _ (List.mem_cons_self ..)).1 mal_41c0
  obtain ⟨v, hv⟩ : ∃ v, subWrap_AbstractChar_Integer charIntegerOps (0x41c00000 : JChar)
      (JInt.lit .i64 1) = .ok v := ⟨_, rfl⟩
  exact ok_error_absurd hv he

/-- `reinterpret(Char, 0x41800000)` ('A' plus a stray 0x80) is not malformed but stores two
UTF-8 units that are not one sequence. -/
theorem refute_exact_sequence : ¬ NonMalformedIsOneSequence := by
  intro h
  obtain ⟨u, hu⟩ := h 0x41800000 mal_4180
  rw [sb_4180] at hu
  simp [Utf8Seq] at hu

/-- `reinterpret(Char, 0xc0000000)` (a lone 0xc0) is classified overlong. -/
theorem refute_overlong_encoding : ¬ IsoverlongExactlyOverlong := by
  intro h
  obtain ⟨u, hu, _⟩ := (h 0xc0000000).1 ov_c0
  rw [sb_c0] at hu
  simp [Utf8Seq] at hu

/-- `reinterpret(Char, 0xc0000000)` is overlong, but stores no sequence to decode. -/
theorem refute_overlong_decode : ¬ DecodeOverlongCodepoint := by
  intro h
  obtain ⟨u, hu, _⟩ := h 0xc0000000 ov_c0
  rw [sb_c0] at hu
  simp [Utf8Seq] at hu

theorem not_literal_4180 : ∀ l d, CharLiteral l d → l = [0x27, 0x41, 0x80, 0x27] →
    d = (0x41800000 : JChar) → False := by
  intro l d h
  cases h with
  | raw c u hp _ _ =>
      intro _ hd
      subst hd
      have hs := hp.1
      rw [sb_4180] at hs
      simp [Utf8Seq] at hs
  | letter b u _ => intro hl _; simp at hl
  | bytes c =>
      intro hl hd
      subst hd
      rw [sb_4180] at hl
      simp [hexByteEscape, hexDigitByte] at hl
  | shortU digits u c _ _ _ _ => intro hl _; simp at hl
  | longU digits u c _ _ _ _ => intro hl _; simp at hl

/-- show of `reinterpret(Char, 0x41800000)` writes `'A\x80'` raw, which does not read back. -/
theorem refute_show_roundtrip : ¬ ShowCharLiteralRoundTrip := by
  intro h
  obtain ⟨trace, ht, hl⟩ := h (fun _ => true) 0x41800000
  rw [show_4180] at ht
  cases ht
  have hf : flattenWritten [.bytes [0x27], .character 0x41800000, .bytes [0x27]] =
      [0x27, 0x41, 0x80, 0x27] := by
    simp only [flattenWritten, wr_4180]; decide
  exact not_literal_4180 _ _ hl hf rfl

/-! ## Proofs -/

theorem leadingOnes_bounds (c : JChar) :
    0 ≤ (charBitOps.leadingOnes c).val ∧ (charBitOps.leadingOnes c).val ≤ 32 := by
  have h := JuliaLean.Proofs.base.int.leadingZeros_proven .u32 (int.bnot (jUInt32 c))
  exact ⟨h.1, h.2.1⟩

theorem lit_eight_mul (v : Int) (h0 : 0 ≤ v) (h1 : v ≤ 32) :
    (JInt.lit .i64 (8 * v)).val = 8 * v := by
  show wrapInt .i64 (8 * v) = 8 * v
  simp [wrapInt, IntTy.signed, IntTy.bits]
  omega

theorem unsafeCodepointMatches : UnsafeCodepointMatches := by
  intro c hm
  obtain ⟨h0, h1⟩ := leadingOnes_bounds c
  have h8 := lit_eight_mul _ h0 h1
  unfold ismalformed_Char at hm
  unfold codepoint_Char uint32_Char unsafe_codepoint_Char
  by_cases hu : c < 0x80000000
  · simp [hu]; rfl
  · simp only [hu, ite_false]
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, h8] at hm
    obtain ⟨⟨ha, hb⟩, hc⟩ := hm
    have hne : ¬ ((charBitOps.leadingOnes c).val == 1) = true := by
      simp only [beq_iff_eq]; omega
    simp [hne, hb, hc, throw_invalid_char]
    rfl

theorem charTypeExtrema : CharTypeExtrema := by
  intro c
  have h1 : (UInt32.ofNat (int.typemax .u32).val.toNat) = 0xffffffff := by decide
  have h2 : (UInt32.ofNat (int.typemin .u32).val.toNat) = 0 := by decide
  simp only [typemax_Char, typemin_Char, isless_Char, h1, h2, decide_eq_false_iff_not,
    UInt32.lt_iff_toNat_lt]
  have := c.toNat_lt
  constructor <;> simp <;> omega

theorem storedBytes_cases (c : JChar) :
    (storedBytes c = [c.toNat / 16777216 % 256, c.toNat / 65536 % 256, c.toNat / 256 % 256,
        c.toNat % 256] ∧ c.toNat % 256 ≠ 0) ∨
    (storedBytes c = [c.toNat / 16777216 % 256, c.toNat / 65536 % 256, c.toNat / 256 % 256] ∧
        c.toNat % 256 = 0 ∧ c.toNat / 256 % 256 ≠ 0) ∨
    (storedBytes c = [c.toNat / 16777216 % 256, c.toNat / 65536 % 256] ∧
        c.toNat % 256 = 0 ∧ c.toNat / 256 % 256 = 0 ∧ c.toNat / 65536 % 256 ≠ 0) ∨
    (storedBytes c = [c.toNat / 16777216 % 256] ∧
        c.toNat % 256 = 0 ∧ c.toNat / 256 % 256 = 0 ∧ c.toNat / 65536 % 256 = 0) := by
  unfold storedBytes storedCount storageByte
  by_cases h3 : c.toNat % 256 = 0 <;> by_cases h2 : c.toNat / 256 % 256 = 0 <;>
    by_cases h1 : c.toNat / 65536 % 256 = 0 <;>
    simp [h3, h2, h1, List.range_succ]

theorem minimalUtf8Length_cases (u : Nat) :
    (u < 0x80 ∧ minimalUtf8Length u = 1) ∨ (0x80 ≤ u ∧ u < 0x800 ∧ minimalUtf8Length u = 2) ∨
    (0x800 ≤ u ∧ u < 0x10000 ∧ minimalUtf8Length u = 3) ∨
    (0x10000 ≤ u ∧ minimalUtf8Length u = 4) := by
  unfold minimalUtf8Length
  by_cases h1 : u < 0x80
  · simp [h1]
  · by_cases h2 : u < 0x800
    · simp [h1, h2]; omega
    · by_cases h3 : u < 0x10000
      · simp [h1, h2, h3]; omega
      · simp [h1, h2, h3]; omega

/-- The 32-bit storage of the standard UTF-8 encoding of `u < 0x200000`. -/
def encNat (u : Nat) : Nat :=
  if u < 0x80 then u * 16777216
  else if u < 0x800 then (0xc0 + u / 64) * 16777216 + (0x80 + u % 64) * 65536
  else if u < 0x10000 then
    (0xe0 + u / 4096) * 16777216 + (0x80 + u / 64 % 64) * 65536 + (0x80 + u % 64) * 256
  else (0xf0 + u / 262144) * 16777216 + (0x80 + u / 4096 % 64) * 65536 +
    (0x80 + u / 64 % 64) * 256 + (0x80 + u % 64)

theorem lengthEnc_cases (u : Nat) :
    (u < 0x80 ∧ minimalUtf8Length u = 1 ∧ encNat u = u * 16777216) ∨
    (0x80 ≤ u ∧ u < 0x800 ∧ minimalUtf8Length u = 2 ∧
      encNat u = (0xc0 + u / 64) * 16777216 + (0x80 + u % 64) * 65536) ∨
    (0x800 ≤ u ∧ u < 0x10000 ∧ minimalUtf8Length u = 3 ∧
      encNat u = (0xe0 + u / 4096) * 16777216 + (0x80 + u / 64 % 64) * 65536 +
        (0x80 + u % 64) * 256) ∨
    (0x10000 ≤ u ∧ minimalUtf8Length u = 4 ∧
      encNat u = (0xf0 + u / 262144) * 16777216 + (0x80 + u / 4096 % 64) * 65536 +
        (0x80 + u / 64 % 64) * 256 + (0x80 + u % 64)) := by
  unfold minimalUtf8Length encNat
  by_cases h1 : u < 0x80
  · simp [h1]
  · by_cases h2 : u < 0x800
    · simp [h1, h2]; omega
    · by_cases h3 : u < 0x10000
      · simp [h1, h2, h3]; omega
      · simp [h1, h2, h3]; omega

theorem toNat_bytes (c : JChar) :
    c.toNat = c.toNat / 16777216 % 256 * 16777216 + c.toNat / 65536 % 256 * 65536 +
      c.toNat / 256 % 256 * 256 + c.toNat % 256 := by
  have : c.toNat < 4294967296 := c.toNat_lt
  omega

theorem properlyEncoded_toNat {c : JChar} {u : Nat} (h : ProperlyEncoded c u) :
    c.toNat = encNat u ∧ u < 0x200000 := by
  obtain ⟨hs, hl⟩ := h
  have hb := toNat_bytes c
  have l0 : c.toNat / 16777216 % 256 < 256 := Nat.mod_lt _ (by decide)
  have l1 : c.toNat / 65536 % 256 < 256 := Nat.mod_lt _ (by decide)
  have l2 : c.toNat / 256 % 256 < 256 := Nat.mod_lt _ (by decide)
  have l3 : c.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [hb]
  rcases storedBytes_cases c with g | g | g | g <;>
    rcases lengthEnc_cases u with m | m | m | m <;>
    · have g2 := g.2
      simp only [g.1, Utf8Seq, List.length_cons, List.length_nil] at hs hl
      generalize c.toNat / 16777216 % 256 = x0 at hs hl g2 l0 ⊢
      generalize c.toNat / 65536 % 256 = x1 at hs hl g2 l1 ⊢
      generalize c.toNat / 256 % 256 = x2 at hs hl g2 l2 ⊢
      generalize c.toNat % 256 = x3 at hs hl g2 l3 ⊢
      omega

theorem encNat_strictMono {u v : Nat} (huv : u < v) (hv : v < 0x200000) : encNat u < encNat v := by
  simp only [encNat]
  by_cases a1 : u < 0x80 <;> by_cases a2 : u < 0x800 <;> by_cases a3 : u < 0x10000 <;>
    by_cases b1 : v < 0x80 <;> by_cases b2 : v < 0x800 <;> by_cases b3 : v < 0x10000 <;>
    simp only [a1, a2, a3, b1, b2, b3, if_true, if_false] <;> omega

theorem charOrderCodepoint : CharOrderCodepoint := by
  intro c d u v hc hd
  obtain ⟨hc1, hc2⟩ := properlyEncoded_toNat hc
  obtain ⟨hd1, hd2⟩ := properlyEncoded_toNat hd
  have hlt : (c < d) ↔ c.toNat < d.toNat := UInt32.lt_iff_toNat_lt
  have heq : (c = d) ↔ c.toNat = d.toNat := UInt32.toNat_inj.symm
  simp only [isless_Char, eq_Char]
  constructor
  · rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hlt, hc1, hd1]
    constructor
    · intro h
      rcases Nat.lt_or_ge u v with h' | h'
      · exact h'
      · rcases Nat.lt_or_ge v u with h'' | h''
        · have := encNat_strictMono h'' hc2; omega
        · have : v = u := by omega
          subst this; omega
    · intro h; exact encNat_strictMono h hd2
  · rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, heq, hc1, hd1]
    constructor
    · intro h
      rcases Nat.lt_trichotomy u v with h' | h' | h'
      · have := encNat_strictMono h' hd2; omega
      · exact h'
      · have := encNat_strictMono h' hc2; omega
    · intro h; rw [h]

theorem hexCharAt_succ (n : Nat) (hn : n < 16) :
    hexCharAt (n + 1) = .ok (UInt8.ofNat (hexDigitByte n)) := by
  have key : ∀ k : Fin 16, hex_chars[k.val]? = some (UInt8.ofNat (hexDigitByte k.val)) := by
    decide
  have := key ⟨n, hn⟩
  simp only [hexCharAt, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
  simp only at this
  rw [this]

theorem toNat_lt32 (u : JChar) : u.toNat < 4294967296 := u.toNat_lt

theorem hi_nibble (u : JChar) :
    ((ushr32 u 28) &&& 0xf).toNat = u.toNat / 16777216 % 256 / 16 := by
  have := toNat_lt32 u
  simp only [ushr32, show (28 : Nat) < 32 from by decide, if_true, UInt32.toNat_and,
    UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have h15 : (UInt32.toNat 0xf) = 2 ^ 4 - 1 := by decide
  rw [h15, Nat.and_two_pow_sub_one_eq_mod]
  simp
  omega

theorem lo_nibble (u : JChar) :
    ((ushr32 u 24) &&& 0xf).toNat = u.toNat / 16777216 % 256 % 16 := by
  have := toNat_lt32 u
  simp only [ushr32, show (24 : Nat) < 32 from by decide, if_true, UInt32.toNat_and,
    UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have h15 : (UInt32.toNat 0xf) = 2 ^ 4 - 1 := by decide
  rw [h15, Nat.and_two_pow_sub_one_eq_mod]
  simp <;> omega

theorem shl8_toNat (u : JChar) : (shl32 u 8).toNat = u.toNat % 16777216 * 256 := by
  have := toNat_lt32 u
  simp only [shl32, show (8 : Nat) < 32 from by decide, if_true, UInt32.toNat_shiftLeft,
    Nat.shiftLeft_eq]
  simp
  omega

theorem storedCount_pos (u : JChar) : 1 ≤ storedCount u := by
  unfold storedCount; split <;> (try split) <;> (try split) <;> omega

theorem storedBytes_zero_tail (u : JChar) (h : u.toNat % 16777216 = 0) :
    storedBytes u = [u.toNat / 16777216 % 256] ∧ storedCount u = 1 := by
  have hu := toNat_lt32 u
  have hcu : storedCount u = (storedBytes u).length := by simp [storedBytes]
  rw [hcu]
  rcases storedBytes_cases u with g | g | g | g
  · exfalso; have g2 := g.2; generalize u.toNat = n at *; omega
  · exfalso; have g2 := g.2; generalize u.toNat = n at *; omega
  · exfalso; have g2 := g.2; generalize u.toNat = n at *; omega
  · rw [g.1]; simp

theorem storedBytes_shift (u : JChar) (h : u.toNat % 16777216 ≠ 0) :
    storedBytes u = u.toNat / 16777216 % 256 :: storedBytes (shl32 u 8) ∧
      storedCount u = storedCount (shl32 u 8) + 1 := by
  have hu := toNat_lt32 u
  have hs := shl8_toNat u
  have hv := toNat_lt32 (shl32 u 8)
  have hcu : storedCount u = (storedBytes u).length := by simp [storedBytes]
  have hcv : storedCount (shl32 u 8) = (storedBytes (shl32 u 8)).length := by simp [storedBytes]
  rw [hcu, hcv]
  rcases storedBytes_cases u with g | g | g | g <;>
    rcases storedBytes_cases (shl32 u 8) with k | k | k | k <;>
    · have g2 := g.2
      have k2 := k.2
      rw [g.1, k.1, hs]
      rw [hs] at k2
      simp only [List.cons.injEq, List.length_cons, List.length_nil, and_true, true_and]
      omega

def escapeEvents (u : JChar) : List CharOutput :=
  (storedBytes u).map fun b =>
    CharOutput.bytes [0x5c, 0x78, UInt8.ofNat (hexDigitByte (b / 16)), UInt8.ofNat (hexDigitByte (b % 16))]

theorem loop_spec : ∀ (fuel : Nat) (io : List CharOutput) (u : JChar), storedCount u ≤ fuel →
    showInvalidLoop writeBytesTrace fuel io u = .ok (io ++ escapeEvents u) := by
  intro fuel
  induction fuel with
  | zero => intro io u h; have := storedCount_pos u; omega
  | succ fuel ih =>
    intro io u h
    have hb : u.toNat / 16777216 % 256 < 256 := Nat.mod_lt _ (by decide)
    have ha := hexCharAt_succ (u.toNat / 16777216 % 256 / 16) (by omega)
    have hb' := hexCharAt_succ (u.toNat / 16777216 % 256 % 16) (by omega)
    simp only [showInvalidLoop, hi_nibble, lo_nibble, ha, hb', writeBytesTrace, bind, Except.bind,
      pure, Except.pure]
    by_cases hz : u.toNat % 16777216 = 0
    · have hz' : (shl32 u 8 == 0) = true := by
        rw [beq_iff_eq, ← UInt32.toNat_inj, shl8_toNat, hz]; rfl
      rw [if_pos hz']
      obtain ⟨hsb, _⟩ := storedBytes_zero_tail u hz
      simp [escapeEvents, hsb]
    · have hz' : ¬ (shl32 u 8 == 0) = true := by
        rw [beq_iff_eq, ← UInt32.toNat_inj, shl8_toNat]
        simp; omega
      rw [if_neg hz']
      obtain ⟨hsb, hsc⟩ := storedBytes_shift u hz
      rw [ih _ _ (by omega)]
      simp [escapeEvents, hsb]

theorem flattenOutput_append (a b : List CharOutput) :
    flattenOutput (a ++ b) = flattenOutput a ++ flattenOutput b := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp [flattenOutput, ih]

theorem hexDigitByte_lt (n : Nat) (h : n < 16) : hexDigitByte n < 256 := by
  unfold hexDigitByte; split <;> omega

theorem flatten_escapes (u : JChar) :
    flattenOutput (escapeEvents u) = (storedBytes u).flatMap hexByteEscape := by
  have hall : ∀ b ∈ storedBytes u, b < 256 := by
    intro b hb
    simp only [storedBytes, List.mem_map] at hb
    obtain ⟨k, _, rfl⟩ := hb
    exact Nat.mod_lt _ (by decide)
  unfold escapeEvents
  generalize storedBytes u = l at hall ⊢
  induction l with
  | nil => rfl
  | cons b bs ih =>
    have hb : b < 256 := hall b (by simp)
    have h1 := hexDigitByte_lt (b / 16) (by omega)
    have h2 := hexDigitByte_lt (b % 16) (by omega)
    simp only [List.map_cons, flattenOutput, List.flatMap_cons, hexByteEscape]
    rw [ih (fun x hx => hall x (by simp [hx]))]
    simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]

theorem showInvalidEscapesStoredBytes : ShowInvalidEscapesStoredBytes := by
  intro c
  have hc : storedCount c ≤ 4 := by unfold storedCount; split <;> (try split) <;> (try split) <;> omega
  refine ⟨[.bytes [0x27]] ++ escapeEvents c ++ [.bytes [0x27]], JInt.lit .i64 1, ?_, ?_⟩
  · simp only [show_invalid_Char, writeBytesTrace, bind, Except.bind]
    rw [show ([] : List CharOutput) ++ [CharOutput.bytes [0x27]] = [.bytes [0x27]] from rfl,
      loop_spec 4 _ c hc]
    rfl
  · rw [flattenOutput_append, flattenOutput_append, flatten_escapes]
    rfl

/-! ## Bit-level decoding and encoding -/

section BitLevel
open JuliaLean.Promotion

theorem jUInt32_pattern (c : JChar) : JuliaLean.Proofs.base.int.pattern (jUInt32 c) = c.toNat := by
  have hv : (jUInt32 c).val = c.toNat := by
    have hbound : 0 ≤ (c.toNat : Int) ∧ (c.toNat : Int) < 2 ^ 32 := by
      exact ⟨by omega, by exact_mod_cast UInt32.toNat_lt c⟩
    change wrapInt .u32 (c.toNat : Int) = (c.toNat : Int)
    simp only [wrapInt, IntTy.signed, IntTy.bits, if_false]
    exact Int.emod_eq_of_lt hbound.1 hbound.2
  have hu : ((JuliaLean.C.fromJInt (jUInt32 c)).toNat : Int) = c.toNat := by
    rw [JuliaLean.Proofs.base.int.fromJInt_toNat_unsigned _ (by decide), hv]
  rw [JuliaLean.Proofs.base.int.pattern_fromJInt]
  exact_mod_cast hu

theorem charLeadingOnesRange (c : JChar) (k : Nat) (hk : k < 32)
    (h1 : 4294967296 - 2 ^ (32 - k) ≤ c.toNat)
    (h2 : c.toNat < 4294967296 - 2 ^ (31 - k)) :
    (charBitOps.leadingOnes c).val = (k : Int) := by
  have hn : JuliaLean.Proofs.base.int.pattern (int.bnot (jUInt32 c)) =
      4294967295 - c.toNat := by
    rw [JuliaLean.Proofs.base.int.pattern_bnot, jUInt32_pattern,
      show IntTy.u32.bits = 32 by decide]
  have hpow : 2 ^ (32 - k) = 2 ^ (31 - k) * 2 := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hpowpos : 0 < 2 ^ (31 - k) := Nat.two_pow_pos _
  have hlow : 2 ^ (31 - k) ≤ 4294967295 - c.toNat := by omega
  have hhigh : 4294967295 - c.toNat < 2 ^ (32 - k) := by omega
  have hlog : Nat.log2 (4294967295 - c.toNat) = 31 - k := by
    rw [Nat.log2_eq_iff (by omega), show 31 - k + 1 = 32 - k by omega]
    exact ⟨hlow, hhigh⟩
  unfold charBitOps leadingOnesUInt32
  change (int.leading_zeros (int.bnot (jUInt32 c))).val = _
  rw [JuliaLean.Proofs.base.int.leading_zeros_val, hn]
  have hnz : 4294967295 - c.toNat ≠ 0 := by omega
  rw [if_neg hnz, hlog]
  simp only [show IntTy.u32.bits = 32 by decide, Int.toNat_natCast]
  omega
theorem natByteHasBit {b : Nat} (hb : b < 256) (hne : b ≠ 0) :
    ∃ i, i < 8 ∧ b.testBit i = true := by
  apply Classical.byContradiction
  intro h
  have hzero : ∀ i, i < 8 → b.testBit i = false := by
    intro i hi
    cases hbit : b.testBit i with
    | false => rfl
    | true => exact False.elim (h ⟨i, hi, hbit⟩)
  have hz : b = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · rw [hzero i hi]
      simp
    · have hpow : 256 ≤ 2 ^ i := by
        have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 8 ≤ i by omega)
        have h256 : (2 ^ 8 : Nat) = 256 := by decide
        rw [h256] at hp
        exact hp
      have hlt : b < 2 ^ i := by omega
      rw [Nat.testBit_lt_two_pow hlt]
      simp
  exact hne hz
theorem natTestBitSplit (a b k j : Nat) (hb : b < 2 ^ k) :
    (2 ^ k * a + b).testBit j = if j < k then b.testBit j else a.testBit (j - k) := by
  have hm : (2 ^ k * a + b) % 2 ^ k = b := by
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hb
  have hd : (2 ^ k * a + b) / 2 ^ k = a := by
    rw [Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt hb, Nat.add_zero]
  split
  · next h =>
    have ht := Nat.testBit_mod_two_pow (2 ^ k * a + b) k j
    rw [hm] at ht
    rw [ht]
    simp [h]
  · next h =>
    conv => lhs; rw [show j = k + (j - k) by omega]
    rw [← Nat.testBit_shiftRight, Nat.shiftRight_eq_div_pow, hd]

theorem natAndSplit (a b c d k : Nat) (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    (2 ^ k * a + b) &&& (2 ^ k * c + d) = 2 ^ k * (a &&& c) + (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, natTestBitSplit _ _ _ _ hb, natTestBitSplit _ _ _ _ hd,
    natTestBitSplit _ _ _ _ (Nat.and_lt_two_pow _ hd), Nat.testBit_and, Nat.testBit_and]
  split <;> rfl

theorem natAnd7 (x : Nat) : x &&& 7 = x % 8 := by
  rw [show (7 : Nat) = 2 ^ 3 - 1 by decide]
  exact Nat.and_two_pow_sub_one_eq_mod x 3

theorem natAndMask56 (x : Nat) : x &&& 56 = x / 8 % 8 * 8 := by
  have h := natAndSplit (x / 8) (x % 8) 7 0 3
    (Nat.mod_lt _ (by decide)) (Nat.two_pow_pos 3)
  rw [show (2 ^ 3 : Nat) = 8 by decide, show (8 : Nat) * 7 = 56 by decide,
    Nat.div_add_mod, Nat.and_zero, Nat.add_zero, natAnd7] at h
  simpa [Nat.mul_comm] using h
def b4 (a b c d : Nat) : Nat := 256 * (256 * (256 * a + b) + c) + d

theorem natOrSplit (a b c d k : Nat) (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    (2 ^ k * a + b) ||| (2 ^ k * c + d) = 2 ^ k * (a ||| c) + (b ||| d) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, natTestBitSplit _ _ _ _ hb, natTestBitSplit _ _ _ _ hd,
    natTestBitSplit _ _ _ _ (Nat.or_lt_two_pow hb hd), Nat.testBit_or, Nat.testBit_or]
  split <;> rfl

theorem natXorSplit (a b c d k : Nat) (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    (2 ^ k * a + b) ^^^ (2 ^ k * c + d) = 2 ^ k * (a ^^^ c) + (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, natTestBitSplit _ _ _ _ hb, natTestBitSplit _ _ _ _ hd,
    natTestBitSplit _ _ _ _ (Nat.xor_lt_two_pow hb hd), Nat.testBit_xor, Nat.testBit_xor]
  split <;> rfl

theorem natAnd8 (a b c d : Nat) (hb : b < 256) (hd : d < 256) :
    (256 * a + b) &&& (256 * c + d) = 256 * (a &&& c) + (b &&& d) :=
  natAndSplit a b c d 8 (by simpa using hb) (by simpa using hd)

theorem natOr8 (a b c d : Nat) (hb : b < 256) (hd : d < 256) :
    (256 * a + b) ||| (256 * c + d) = 256 * (a ||| c) + (b ||| d) :=
  natOrSplit a b c d 8 (by simpa using hb) (by simpa using hd)

theorem natXor8 (a b c d : Nat) (hb : b < 256) (hd : d < 256) :
    (256 * a + b) ^^^ (256 * c + d) = 256 * (a ^^^ c) + (b ^^^ d) :=
  natXorSplit a b c d 8 (by simpa using hb) (by simpa using hd)

theorem andB4 {a b c d a' b' c' d' : Nat} (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (hb' : b' < 256) (hc' : c' < 256) (hd' : d' < 256) :
    b4 a b c d &&& b4 a' b' c' d' = b4 (a &&& a') (b &&& b') (c &&& c') (d &&& d') := by
  unfold b4
  rw [natAnd8 _ _ _ _ hd hd', natAnd8 _ _ _ _ hc hc', natAnd8 _ _ _ _ hb hb']

theorem orB4 {a b c d a' b' c' d' : Nat} (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (hb' : b' < 256) (hc' : c' < 256) (hd' : d' < 256) :
    b4 a b c d ||| b4 a' b' c' d' = b4 (a ||| a') (b ||| b') (c ||| c') (d ||| d') := by
  unfold b4
  rw [natOr8 _ _ _ _ hd hd', natOr8 _ _ _ _ hc hc', natOr8 _ _ _ _ hb hb']

theorem xorB4 {a b c d a' b' c' d' : Nat} (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (hb' : b' < 256) (hc' : c' < 256) (hd' : d' < 256) :
    b4 a b c d ^^^ b4 a' b' c' d' = b4 (a ^^^ a') (b ^^^ b') (c ^^^ c') (d ^^^ d') := by
  unfold b4
  rw [natXor8 _ _ _ _ hd hd', natXor8 _ _ _ _ hc hc', natXor8 _ _ _ _ hb hb']

theorem natOrAdd (x y k : Nat) (hx : x < 2 ^ k) : x ||| y * 2 ^ k = x + y * 2 ^ k := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hx, Nat.add_comm]

theorem natOrAdd6 (x y : Nat) (hx : x < 64) : x ||| y * 64 = x + y * 64 :=
  natOrAdd x y 6 hx

theorem natOrAdd12 (x y : Nat) (hx : x < 4096) : x ||| y * 4096 = x + y * 4096 :=
  natOrAdd x y 12 hx

theorem natOrAdd18 (x y : Nat) (hx : x < 262144) : x ||| y * 262144 = x + y * 262144 :=
  natOrAdd x y 18 hx

theorem or4lo {p0 p1 p2 p3 a b c d : Nat} (h0 : p0 = b4 0 0 0 d)
    (h1 : p1 = b4 0 0 c 0) (h2 : p2 = b4 0 b 0 0) (h3 : p3 = b4 a 0 0 0)
    (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    p0 ||| p1 ||| p2 ||| p3 = b4 a b c d := by
  subst h0 h1 h2 h3
  simp (disch := omega) only [orB4, Nat.or_zero, Nat.zero_or]

theorem ushr32_toNat (x : JChar) (k : Nat) (hk : k < 32) :
    (ushr32 x k).toNat = x.toNat / 2 ^ k := by
  unfold ushr32
  rw [if_pos hk, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have hkNat : (UInt32.ofNat k).toNat = k := by
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  rw [hkNat, show k % 32 = k from Nat.mod_eq_of_lt hk]

theorem uintShrToNat (x k : UInt32) (hk : k.toNat < 32) :
    (x >>> k).toNat = x.toNat / 2 ^ k.toNat := by
  rw [UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hk]

theorem shr0 (x : UInt32) : (x >>> (0 : UInt32)).toNat = x.toNat := by
  rw [uintShrToNat x _ (by decide), show (0 : UInt32).toNat = 0 by decide]
  simp

theorem shr2 (x : UInt32) : (x >>> (2 : UInt32)).toNat = x.toNat / 4 := by
  rw [uintShrToNat x _ (by decide), show (2 : UInt32).toNat = 2 by decide]

theorem shr4 (x : UInt32) : (x >>> (4 : UInt32)).toNat = x.toNat / 16 := by
  rw [uintShrToNat x _ (by decide), show (4 : UInt32).toNat = 4 by decide]

theorem shr6 (x : UInt32) : (x >>> (6 : UInt32)).toNat = x.toNat / 64 := by
  rw [uintShrToNat x _ (by decide), show (6 : UInt32).toNat = 6 by decide]

theorem natAnd63 (x : Nat) : x &&& 63 = x % 64 :=
  Nat.and_two_pow_sub_one_eq_mod x 6

theorem natAndMask6 (x k : Nat) : x &&& (63 * 2 ^ k) = x / 2 ^ k % 64 * 2 ^ k := by
  have h := natAndSplit (x / 2 ^ k) (x % 2 ^ k) 63 0 k
    (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.two_pow_pos k)
  rw [Nat.div_add_mod, Nat.add_zero, Nat.and_zero, Nat.add_zero, natAnd63] at h
  rw [Nat.mul_comm 63, h, Nat.mul_comm]
theorem natAnd3 (x : Nat) : x &&& 3 = x % 4 :=
  Nat.and_two_pow_sub_one_eq_mod x 2

theorem natAndMask2 (x k : Nat) : x &&& (3 * 2 ^ k) = x / 2 ^ k % 4 * 2 ^ k := by
  have h := natAndSplit (x / 2 ^ k) (x % 2 ^ k) 3 0 k
    (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.two_pow_pos k)
  rw [Nat.div_add_mod, Nat.add_zero, Nat.and_zero, Nat.add_zero, natAnd3] at h
  rw [Nat.mul_comm 3, h, Nat.mul_comm]

theorem cont192 (q : Nat) (hq : q < 64) : (128 + q) &&& 192 = 128 := by
  rw [show (192 : Nat) = 3 * 2 ^ 6 by decide, natAndMask2,
    show (2 ^ 6 : Nat) = 64 by decide]
  omega

theorem natAndM8 (x : Nat) : x &&& 16128 = x / 256 % 64 * 256 := by
  rw [show (16128 : Nat) = 63 * 2 ^ 8 by decide, natAndMask6]

theorem natAndM16 (x : Nat) : x &&& 4128768 = x / 65536 % 64 * 65536 := by
  rw [show (4128768 : Nat) = 63 * 2 ^ 16 by decide, natAndMask6]

theorem natAndM24 (x : Nat) : x &&& 1056964608 = x / 16777216 % 64 * 16777216 := by
  rw [show (1056964608 : Nat) = 63 * 2 ^ 24 by decide, natAndMask6]

theorem natAnd127 (x : Nat) : x &&& 127 = x % 128 :=
  Nat.and_two_pow_sub_one_eq_mod x 7

theorem b4_000 (d : Nat) : b4 0 0 0 d = d := by
  unfold b4
  omega

theorem b4_div4 (c : Nat) : b4 0 0 c 0 / 4 = c * 64 := by
  unfold b4
  omega

theorem b4_div16 (b : Nat) : b4 0 b 0 0 / 16 = b * 4096 := by
  unfold b4
  omega

theorem b4_div64 (a : Nat) : b4 a 0 0 0 / 64 = a * 262144 := by
  unfold b4
  omega
theorem b4_shift16 (a b : Nat) : b4 a b 0 0 / 65536 = b4 0 0 a b := by
  unfold b4
  omega

theorem b4_shift8 (a b c : Nat) : b4 a b c 0 / 256 = b4 0 a b c := by
  unfold b4
  omega

theorem k0c0c0 : (0x00c0c0c0 : UInt32).toNat = b4 0 192 192 192 := rfl
theorem k808080 : (0x00808080 : UInt32).toNat = b4 0 128 128 128 := rfl
theorem k7f : (0x0000007f : UInt32).toNat = b4 0 0 0 127 := rfl
theorem k7f00 : (0x00007f00 : UInt32).toNat = b4 0 0 127 0 := rfl
theorem k7f0000 : (0x007f0000 : UInt32).toNat = b4 0 127 0 0 := rfl
theorem k7f000000 : (0x7f000000 : UInt32).toNat = b4 127 0 0 0 := rfl
theorem kmask2 : (ushr32 0xffffffff 2).toNat = b4 63 255 255 255 := by decide
theorem kmask3 : (ushr32 0xffffffff 3).toNat = b4 31 255 255 255 := by decide
theorem kmask4 : (ushr32 0xffffffff 4).toNat = b4 15 255 255 255 := by decide

theorem decN_toNat (u : UInt32) (a b c d : Nat) (h : u.toNat = b4 a b c d)
    (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (hb' : b % 128 < 64) (hc' : c % 128 < 64) (hd' : d % 128 < 64) :
    (((u &&& 0x0000007f) >>> 0) ||| ((u &&& 0x00007f00) >>> 2) |||
      ((u &&& 0x007f0000) >>> 4) ||| ((u &&& 0x7f000000) >>> 6)).toNat =
    a % 128 * 262144 + b % 128 * 4096 + c % 128 * 64 + d % 128 := by
  simp only [UInt32.toNat_or, UInt32.toNat_and, shr0, shr2, shr4, shr6, h, k7f, k7f00,
    k7f0000, k7f000000]
  simp (disch := omega) only [andB4, Nat.and_zero, natAnd127]
  simp only [b4_000, b4_div4, b4_div16, b4_div64]
  simp (disch := omega) only [natOrAdd6, natOrAdd12, natOrAdd18]
  omega

theorem charTrailingZerosRange (c : JChar) (k y : Nat) (hk : k ≤ 24)
    (hc : c.toNat = 2 ^ k * y) (hy : y % 256 ≠ 0) :
    (k : Int) ≤ (int.trailing_zeros (jUInt32 c)).val ∧
      (int.trailing_zeros (jUInt32 c)).val < (k + 8 : Int) := by
  let r := (int.trailing_zeros (jUInt32 c)).val
  have hbits : IntTy.u32.bits = 32 := by decide
  have htz := JuliaLean.Proofs.base.int.trailingZeros_proven .u32 (jUInt32 c)
  have hr0 : 0 ≤ r := by simpa [r] using htz.1
  have hr32 : r ≤ 32 := by simpa [r, hbits] using htz.2.1
  have hbefore : ∀ i : Nat, (i : Int) < r → c.toNat.testBit i = false := by
    intro i hi
    have h := htz.2.2.1 i (by simpa [r] using hi)
    simpa only [JuliaLean.Proofs.base.int.bitOf_eq, jUInt32_pattern] using h
  have hat : r < 32 → c.toNat.testBit r.toNat = true := by
    intro hr
    have h := htz.2.2.2 (by simpa [r, hbits] using hr)
    simpa only [JuliaLean.Proofs.base.int.bitOf_eq, jUInt32_pattern] using h
  have hmod : c.toNat % 2 ^ k = 0 := by
    rw [hc, Nat.mul_comm (2 ^ k) y]
    exact Nat.mul_mod_left y (2 ^ k)
  have hlow : ∀ i, i < k → c.toNat.testBit i = false := by
    intro i hi
    have h := congrArg (fun n : Nat => n.testBit i) hmod
    simpa [Nat.testBit_mod_two_pow, hi] using h
  have hyrem : y % 256 < 256 := Nat.mod_lt _ (by decide)
  obtain ⟨j, hj, hjbit⟩ := natByteHasBit hyrem hy
  have hybit : y.testBit j = true := by
    have h := Nat.testBit_mod_two_pow y 8 j
    rw [show (2 ^ 8 : Nat) = 256 by decide] at h
    have heq : (y % 256).testBit j = y.testBit j := by simpa [hj] using h
    rw [← heq]
    exact hjbit
  have hbit : c.toNat.testBit (k + j) = true := by
    rw [hc, Nat.mul_comm (2 ^ k) y, show k + j = j + k by omega,
      Nat.testBit_mul_two_pow]
    have hkj : k ≤ j + k := by omega
    simp [hybit, hkj, Nat.add_sub_cancel_right]
  have hlowBound : (k : Int) ≤ r := by
    apply Classical.byContradiction
    intro h
    have hrk : r < k := by omega
    have hrlt : r < 32 := by omega
    have htrue := hat hrlt
    have hi : r.toNat < k := by
      have hr' : (r.toNat : Int) < (k : Int) := by
        rw [Int.toNat_of_nonneg hr0]
        exact hrk
      exact_mod_cast hr'
    have hfalse := hlow r.toNat hi
    rw [htrue] at hfalse
    cases hfalse
  have hhighBound : r < (k + 8 : Int) := by
    apply Classical.byContradiction
    intro h
    have hrk : (k + 8 : Int) ≤ r := by omega
    have hfalse := hbefore (k + j) (by omega)
    rw [hbit] at hfalse
    cases hfalse
  exact ⟨hlowBound, hhighBound⟩
theorem trailingZerosMask56_range (z : JInt .i64) (k : Nat)
    (hk : k = 0 ∨ k = 8 ∨ k = 16 ∨ k = 24)
    (hlo : (k : Int) ≤ z.val) (hhi : z.val < (k + 8 : Int)) :
    (int.band z (JInt.lit .i64 56)).val = (k : Int) := by
  have hz0 : 0 ≤ z.val := by omega
  have hpZ : JuliaLean.Proofs.base.int.pattern z = z.val.toNat :=
    JuliaLean.Proofs.base.int.pattern_of_nonneg z hz0
  have hp56 : JuliaLean.Proofs.base.int.pattern (JInt.lit .i64 56) = 56 := by decide
  have hmask : z.val.toNat &&& 56 = k := by
    rw [natAndMask56]
    have hn : (z.val.toNat : Int) = z.val := Int.toNat_of_nonneg hz0
    rcases hk with hk | hk | hk | hk <;> subst k <;> omega
  have hwrap : wrapInt .i64 (k : Int) = (k : Int) := by
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  rw [JuliaLean.Proofs.base.int.val_eq_wrap_pattern,
    JuliaLean.Proofs.base.int.pattern_band, hpZ, hp56, hmask, hwrap]

theorem eqOfNat {x : UInt32} {n : Nat} (h : x.toNat = n) : x = UInt32.ofNat n := by
  rw [← h, UInt32.ofNat_toNat]

/-! ### Per-length decoding -/

/-- The model's final codepoint assembly (char.jl:168-169). -/
def decOut (u : JChar) : JChar :=
  ((u &&& 0x0000007f) >>> 0) ||| ((u &&& 0x00007f00) >>> 2) |||
    ((u &&& 0x007f0000) >>> 4) ||| ((u &&& 0x7f000000) >>> 6)

theorem wrap64_small (v : Int) (h0 : 0 ≤ v) (h1 : v ≤ 64) : wrapInt .i64 v = v := by
  simp [wrapInt, IntTy.signed, IntTy.bits]; omega

theorem core_flags (c : JChar) (L T : Nat)
    (hl : (charBitOps.leadingOnes c).val = (L : Int))
    (ht : (band (charBitOps.trailingZeros c) (JInt.lit .i64 56)).val = (T : Int))
    (hLT : 8 * L + T ≤ 32) :
    (JInt.lit .i64 (8 * (charBitOps.leadingOnes c).val)).val = 8 * (L : Int) ∧
    (JInt.lit .i64 (8 * (charBitOps.leadingOnes c).val) +
      band (charBitOps.trailingZeros c) (JInt.lit .i64 56)).val = 8 * (L : Int) + T := by
  have h8 : (JInt.lit .i64 (8 * (charBitOps.leadingOnes c).val)).val = 8 * (L : Int) := by
    rw [hl]; exact lit_eight_mul _ (by omega) (by omega)
  refine ⟨h8, ?_⟩
  show wrapInt .i64 ((JInt.lit .i64 (8 * (charBitOps.leadingOnes c).val)).val +
    (band (charBitOps.trailingZeros c) (JInt.lit .i64 56)).val) = _
  rw [h8, ht]
  exact wrap64_small _ (by omega) (by omega)

theorem core_malformed (c : JChar) (L T : Nat)
    (hl : (charBitOps.leadingOnes c).val = (L : Int))
    (ht : (band (charBitOps.trailingZeros c) (JInt.lit .i64 56)).val = (T : Int))
    (hL1 : L ≠ 1) (hLT : 8 * L + T ≤ 32)
    (hx : ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) T = 0) :
    ismalformed_Char charBitOps c = false := by
  obtain ⟨h8, hs⟩ := core_flags c L T hl ht hLT
  have e1 : ¬ (8 * (L : Int) = 8) := by omega
  have e2 : ¬ (8 * (L : Int) + T > 32) := by omega
  unfold ismalformed_Char
  simp only [h8, hs, ht, Int.toNat_natCast, hx]
  simp [e1, e2]

theorem core_uint32 (c : JChar) (L T : Nat) (hfast : ¬ c < 0x80000000)
    (hl : (charBitOps.leadingOnes c).val = (L : Int))
    (ht : (band (charBitOps.trailingZeros c) (JInt.lit .i64 56)).val = (T : Int))
    (hL1 : L ≠ 1) (hLT : 8 * L + T ≤ 32)
    (hx : ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) T = 0) :
    uint32_Char charBitOps c = .ok (decOut (ushr32 (c &&& ushr32 0xffffffff L) T)) := by
  obtain ⟨_, hs⟩ := core_flags c L T hl ht hLT
  have e1 : ¬ ((L : Int) = 1) := by omega
  have e2 : ¬ (8 * (L : Int) + T > 32) := by omega
  unfold uint32_Char
  simp only [hs]
  simp only [hfast, hl, ht, Int.toNat_natCast, hx, if_false]
  simp [e1, e2, decOut, pure, Except.pure]

theorem decOut_toNat (u : UInt32) (hb : u.toNat / 65536 % 256 % 128 < 64)
    (hc : u.toNat / 256 % 256 % 128 < 64) (hd : u.toNat % 256 % 128 < 64) :
    (decOut u).toNat = u.toNat / 16777216 % 256 % 128 * 262144 +
      u.toNat / 65536 % 256 % 128 * 4096 + u.toNat / 256 % 256 % 128 * 64 +
      u.toNat % 256 % 128 :=
  decN_toNat u _ _ _ _ (by have := u.toNat_lt; unfold b4; omega)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hb hc hd

theorem xorMask_toNat (c : JChar) (a b e d : Nat) (hc : c.toNat = b4 a b e d)
    (hb : b < 256) (he : e < 256) (hd : d < 256) :
    ((c &&& 0x00c0c0c0) ^^^ 0x00808080).toNat =
      b4 0 ((b &&& 192) ^^^ 128) ((e &&& 192) ^^^ 128) ((d &&& 192) ^^^ 128) := by
  have m1 : b &&& 192 < 256 := Nat.lt_of_le_of_lt Nat.and_le_left hb
  have m2 : e &&& 192 < 256 := Nat.lt_of_le_of_lt Nat.and_le_left he
  have m3 : d &&& 192 < 256 := Nat.lt_of_le_of_lt Nat.and_le_left hd
  rw [UInt32.toNat_xor, UInt32.toNat_and, hc, k0c0c0, andB4 hb he hd (by decide) (by decide) (by decide),
    k808080, xorB4 m1 m2 m3 (by decide) (by decide) (by decide), Nat.and_zero, Nat.zero_xor]

theorem contXor (p : Nat) (hp : p / 64 = 2) : (p &&& 192) ^^^ 128 = 0 := by
  have h : p = 128 + p % 64 := by omega
  rw [h, cont192 _ (Nat.mod_lt _ (by decide))]
  decide

theorem zeroXor : ((0 : Nat) &&& 192) ^^^ 128 = 128 := by decide

theorem lit80 : (0x80000000 : UInt32).toNat = 2147483648 := by decide

theorem notFast (c : JChar) (h : 2147483648 ≤ c.toNat) : ¬ c < 0x80000000 := by
  intro h'
  have := UInt32.lt_iff_toNat_lt.mp h'
  rw [lit80] at this
  omega

theorem maskShift_toNat (c : JChar) (L T : Nat) (hT : T < 32)
    (hm : (ushr32 0xffffffff L).toNat = 2 ^ (32 - L) - 1) :
    (ushr32 (c &&& ushr32 0xffffffff L) T).toNat = c.toNat % 2 ^ (32 - L) / 2 ^ T := by
  rw [ushr32_toNat _ _ hT, UInt32.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]

theorem dec1 (c : JChar) (a : Nat) (hc : c.toNat = a * 16777216) (ha : a < 128) :
    ismalformed_Char charBitOps c = false ∧ uint32_Char charBitOps c = .ok (UInt32.ofNat a) := by
  by_cases h0 : a = 0
  · subst h0
    have : c = 0 := UInt32.toNat_inj.mp (by rw [hc]; rfl)
    subst this
    exact ⟨by decide, rfl⟩
  · have hfast : c < 0x80000000 := UInt32.lt_iff_toNat_lt.mpr (by rw [lit80]; omega)
    have hl : (charBitOps.leadingOnes c).val = ((0 : Nat) : Int) :=
      charLeadingOnesRange c 0 (by decide) (by omega) (by omega)
    have htr := charTrailingZerosRange c 24 a (by decide) (by rw [hc, Nat.mul_comm])
      (by omega)
    have ht : (band (charBitOps.trailingZeros c) (JInt.lit .i64 56)).val = ((24 : Nat) : Int) :=
      trailingZerosMask56_range _ 24 (by decide) htr.1 htr.2
    have hx : ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) 24 = 0 := by
      apply UInt32.toNat_inj.mp
      rw [ushr32_toNat _ _ (by decide), xorMask_toNat c a 0 0 0 (by rw [hc]; unfold b4; omega)
        (by decide) (by decide) (by decide), zeroXor]
      decide
    refine ⟨core_malformed c 0 24 hl ht (by decide) (by decide) hx, ?_⟩
    unfold uint32_Char
    simp only [hfast, if_true]
    apply congrArg
    apply eqOfNat
    rw [ushr32_toNat _ _ (by decide), hc]
    omega

theorem dec2 (c : JChar) (a b : Nat) (hc : c.toNat = b4 a b 0 0) (ha : a / 32 = 6)
    (hb : b / 64 = 2) :
    ismalformed_Char charBitOps c = false ∧
      uint32_Char charBitOps c = .ok (UInt32.ofNat (a % 32 * 64 + b % 64)) := by
  have hn : c.toNat = a * 16777216 + b * 65536 := by rw [hc]; unfold b4; omega
  have hl : (charBitOps.leadingOnes c).val = ((2 : Nat) : Int) :=
    charLeadingOnesRange c 2 (by decide) (by omega) (by omega)
  have htr := charTrailingZerosRange c 16 (256 * a + b) (by decide) (by rw [hn]; omega)
    (by omega)
  have ht : (band (charBitOps.trailingZeros c) (JInt.lit .i64 56)).val = ((16 : Nat) : Int) :=
    trailingZerosMask56_range _ 16 (by decide) htr.1 htr.2
  have hx : ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) 16 = 0 := by
    apply UInt32.toNat_inj.mp
    rw [ushr32_toNat _ _ (by decide), xorMask_toNat c a b 0 0 hc (by omega) (by decide)
      (by decide), contXor b hb, zeroXor]
    decide
  have hfast := notFast c (by omega)
  refine ⟨core_malformed c 2 16 hl ht (by decide) (by decide) hx, ?_⟩
  rw [core_uint32 c 2 16 hfast hl ht (by decide) (by decide) hx]
  apply congrArg
  apply eqOfNat
  have hv := maskShift_toNat c 2 16 (by decide) (by decide)
  rw [show (2 : Nat) ^ (32 - 2) = 1073741824 by decide,
    show (2 : Nat) ^ 16 = 65536 by decide, hn] at hv
  rw [decOut_toNat _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega), hv]
  omega

theorem dec3 (c : JChar) (a b e : Nat) (hc : c.toNat = b4 a b e 0) (ha : a / 16 = 14)
    (hb : b / 64 = 2) (he : e / 64 = 2) :
    ismalformed_Char charBitOps c = false ∧
      uint32_Char charBitOps c = .ok (UInt32.ofNat (a % 16 * 4096 + b % 64 * 64 + e % 64)) := by
  have hn : c.toNat = a * 16777216 + b * 65536 + e * 256 := by rw [hc]; unfold b4; omega
  have hl : (charBitOps.leadingOnes c).val = ((3 : Nat) : Int) :=
    charLeadingOnesRange c 3 (by decide) (by omega) (by omega)
  have htr := charTrailingZerosRange c 8 (65536 * a + 256 * b + e) (by decide)
    (by rw [hn]; omega) (by omega)
  have ht : (band (charBitOps.trailingZeros c) (JInt.lit .i64 56)).val = ((8 : Nat) : Int) :=
    trailingZerosMask56_range _ 8 (by decide) htr.1 htr.2
  have hx : ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) 8 = 0 := by
    apply UInt32.toNat_inj.mp
    rw [ushr32_toNat _ _ (by decide), xorMask_toNat c a b e 0 hc (by omega) (by omega)
      (by decide), contXor b hb, contXor e he, zeroXor]
    decide
  have hfast := notFast c (by omega)
  refine ⟨core_malformed c 3 8 hl ht (by decide) (by decide) hx, ?_⟩
  rw [core_uint32 c 3 8 hfast hl ht (by decide) (by decide) hx]
  apply congrArg
  apply eqOfNat
  have hv := maskShift_toNat c 3 8 (by decide) (by decide)
  rw [show (2 : Nat) ^ (32 - 3) = 536870912 by decide,
    show (2 : Nat) ^ 8 = 256 by decide, hn] at hv
  rw [decOut_toNat _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega), hv]
  omega

theorem dec4 (c : JChar) (a b e d : Nat) (hc : c.toNat = b4 a b e d) (ha : a / 8 = 30)
    (hb : b / 64 = 2) (he : e / 64 = 2) (hd : d / 64 = 2) :
    ismalformed_Char charBitOps c = false ∧
      uint32_Char charBitOps c =
        .ok (UInt32.ofNat (a % 8 * 262144 + b % 64 * 4096 + e % 64 * 64 + d % 64)) := by
  have hn : c.toNat = a * 16777216 + b * 65536 + e * 256 + d := by rw [hc]; unfold b4; omega
  have hl : (charBitOps.leadingOnes c).val = ((4 : Nat) : Int) :=
    charLeadingOnesRange c 4 (by decide) (by omega) (by omega)
  have htr := charTrailingZerosRange c 0 c.toNat (by decide) (by simp) (by omega)
  have ht : (band (charBitOps.trailingZeros c) (JInt.lit .i64 56)).val = ((0 : Nat) : Int) :=
    trailingZerosMask56_range _ 0 (by decide) htr.1 htr.2
  have hx : ushr32 ((c &&& 0x00c0c0c0) ^^^ 0x00808080) 0 = 0 := by
    apply UInt32.toNat_inj.mp
    rw [ushr32_toNat _ _ (by decide), xorMask_toNat c a b e d hc (by omega) (by omega)
      (by omega), contXor b hb, contXor e he, contXor d hd]
    decide
  have hfast := notFast c (by omega)
  refine ⟨core_malformed c 4 0 hl ht (by decide) (by decide) hx, ?_⟩
  rw [core_uint32 c 4 0 hfast hl ht (by decide) (by decide) hx]
  apply congrArg
  apply eqOfNat
  have hv := maskShift_toNat c 4 0 (by decide) (by decide)
  rw [show (2 : Nat) ^ (32 - 4) = 268435456 by decide,
    show (2 : Nat) ^ 0 = 1 by decide, hn] at hv
  rw [decOut_toNat _ (by rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega), hv]
  omega

theorem byte4 (c : JChar) : c.toNat = b4 (c.toNat / 16777216 % 256) (c.toNat / 65536 % 256)
    (c.toNat / 256 % 256) (c.toNat % 256) := by
  have := c.toNat_lt; unfold b4; omega

theorem codepointDecodesUtf8 : CodepointDecodesUtf8 := by
  intro c u hs
  have hlt := c.toNat_lt
  rcases storedBytes_cases c with g | g | g | g <;> rw [g.1] at hs <;> simp only [Utf8Seq] at hs
  · obtain ⟨h1, h2, h3, h4, rfl⟩ := hs
    have h := dec4 c _ _ _ _ (byte4 c) h1 h2 h3 h4
    exact ⟨h.1, h.2, h.2⟩
  · obtain ⟨h1, h2, h3, rfl⟩ := hs
    have g2 := g.2
    have h := dec3 c _ _ _ (by unfold b4; omega) h1 h2 h3
    exact ⟨h.1, h.2, h.2⟩
  · obtain ⟨h1, h2, rfl⟩ := hs
    have g2 := g.2
    have h := dec2 c _ _ (by unfold b4; omega) h1 h2
    exact ⟨h.1, h.2, h.2⟩
  · obtain ⟨h1, rfl⟩ := hs
    have g2 := g.2
    have h := dec1 c _ (by omega) h1
    exact ⟨h.1, h.2, h.2⟩

/-! ### `Char(u::UInt32)` -/

theorem shl32_toNat (u : JChar) (k : Nat) (hk : k < 32) :
    (shl32 u k).toNat = u.toNat * 2 ^ k % 4294967296 := by
  unfold shl32
  rw [if_pos hk, UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hkNat : (UInt32.ofNat k).toNat = k := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [hkNat, Nat.mod_eq_of_lt hk]

/-- The continuation-bit layout `c` computed by `Char(u::UInt32)` before the lead byte. -/
def encBits (u : JChar) : JChar :=
  ((shl32 u 0) &&& 0x0000003f) ||| ((shl32 u 2) &&& 0x00003f00) |||
    ((shl32 u 4) &&& 0x003f0000) ||| ((shl32 u 6) &&& 0x3f000000)

theorem encBits_toNat (u : JChar) (hn : u.toNat < 2097152) :
    (encBits u).toNat =
      b4 (u.toNat / 262144 % 64) (u.toNat / 4096 % 64) (u.toNat / 64 % 64) (u.toNat % 64) := by
  have p0 : ((shl32 u 0) &&& 0x0000003f).toNat = b4 0 0 0 (u.toNat % 64) := by
    rw [UInt32.toNat_and, shl32_toNat _ _ (by decide), show (0x3f : UInt32).toNat = 63 from rfl,
      natAnd63]
    simp only [Nat.reducePow]; unfold b4; omega
  have p1 : ((shl32 u 2) &&& 0x00003f00).toNat = b4 0 0 (u.toNat / 64 % 64) 0 := by
    rw [UInt32.toNat_and, shl32_toNat _ _ (by decide),
      show (0x00003f00 : UInt32).toNat = 16128 from rfl, natAndM8]
    simp only [Nat.reducePow]; unfold b4; omega
  have p2 : ((shl32 u 4) &&& 0x003f0000).toNat = b4 0 (u.toNat / 4096 % 64) 0 0 := by
    rw [UInt32.toNat_and, shl32_toNat _ _ (by decide),
      show (0x003f0000 : UInt32).toNat = 4128768 from rfl, natAndM16]
    simp only [Nat.reducePow]; unfold b4; omega
  have p3 : ((shl32 u 6) &&& 0x3f000000).toNat = b4 (u.toNat / 262144 % 64) 0 0 0 := by
    rw [UInt32.toNat_and, shl32_toNat _ _ (by decide),
      show (0x3f000000 : UInt32).toNat = 1056964608 from rfl, natAndM24]
    simp only [Nat.reducePow]; unfold b4; omega
  unfold encBits
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or]
  exact or4lo p0 p1 p2 p3 (by omega) (by omega) (by omega)

theorem or192 (x : Nat) (hx : x < 64) : x ||| 192 = x + 192 := natOrAdd x 3 6 hx
theorem or128 (x : Nat) (hx : x < 64) : x ||| 128 = x + 128 := natOrAdd x 2 6 hx
theorem or224 (x : Nat) (hx : x < 32) : x ||| 224 = x + 224 := natOrAdd x 7 5 hx
theorem or240 (x : Nat) (hx : x < 16) : x ||| 240 = x + 240 := natOrAdd x 15 4 hx

theorem litLt (u : JChar) (n : Nat) (h : u.toNat < n) (hn : n < 4294967296) :
    u < UInt32.ofNat n := by
  apply UInt32.lt_iff_toNat_lt.mpr
  rw [UInt32.toNat_ofNat']
  rw [Nat.mod_eq_of_lt hn]
  exact h

theorem litNotLt (u : JChar) (n : Nat) (h : n ≤ u.toNat) : ¬ u < UInt32.ofNat n := by
  intro h'
  have := UInt32.lt_iff_toNat_lt.mp h'
  rw [UInt32.toNat_ofNat'] at this
  have := Nat.mod_le n 4294967296
  omega

theorem charUInt32_ok (u : JChar) (hu : u.toNat < 2097152) :
    ∃ c, char_UInt32 u = .ok c ∧ c.toNat = encNat u.toNat := by
  have hP := encBits_toNat u hu
  have hlt : u < 0x00200000 := litLt u 2097152 hu (by decide)
  by_cases h1 : u.toNat < 128
  · have h1' : u < 0x80 := litLt u 128 h1 (by decide)
    refine ⟨shl32 u 24, by simp [char_UInt32, h1', pure, Except.pure], ?_⟩
    rw [shl32_toNat _ _ (by decide)]
    unfold encNat; rw [if_pos h1]
    simp only [Nat.reducePow]; omega
  · have h1' : ¬ u < 0x80 := litNotLt u 128 (by omega)
    by_cases h2 : u.toNat < 2048
    · have h2' : u < 0x800 := litLt u 2048 h2 (by decide)
      refine ⟨shl32 (encBits u) 16 ||| 0xc0800000,
        by simp [char_UInt32, h1', hlt, h2', encBits, pure, Except.pure], ?_⟩
      have hs : (shl32 (encBits u) 16).toNat = b4 (u.toNat / 64 % 64) (u.toNat % 64) 0 0 := by
        rw [shl32_toNat _ _ (by decide), hP]; simp only [Nat.reducePow]; unfold b4; omega
      rw [UInt32.toNat_or, hs, show (0xc0800000 : UInt32).toNat = b4 192 128 0 0 from rfl,
        orB4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        or192 _ (by omega), or128 _ (by omega), Nat.or_zero]
      unfold encNat; rw [if_neg h1, if_pos h2]; unfold b4; omega
    · have h2' : ¬ u < 0x800 := litNotLt u 2048 (by omega)
      by_cases h3 : u.toNat < 65536
      · have h3' : u < 0x00010000 := litLt u 65536 h3 (by decide)
        refine ⟨shl32 (encBits u) 8 ||| 0xe0808000,
          by simp [char_UInt32, h1', hlt, h2', h3', encBits, pure, Except.pure], ?_⟩
        have hs : (shl32 (encBits u) 8).toNat =
            b4 (u.toNat / 4096 % 64) (u.toNat / 64 % 64) (u.toNat % 64) 0 := by
          rw [shl32_toNat _ _ (by decide), hP]; simp only [Nat.reducePow]; unfold b4; omega
        rw [UInt32.toNat_or, hs, show (0xe0808000 : UInt32).toNat = b4 224 128 128 0 from rfl,
          orB4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          or224 _ (by omega), or128 _ (by omega), or128 _ (by omega), Nat.or_zero]
        unfold encNat; rw [if_neg h1, if_neg h2, if_pos h3]; unfold b4; omega
      · have h3' : ¬ u < 0x00010000 := litNotLt u 65536 (by omega)
        refine ⟨shl32 (encBits u) 0 ||| 0xf0808080,
          by simp [char_UInt32, h1', hlt, h2', h3', encBits, pure, Except.pure], ?_⟩
        have hs : (shl32 (encBits u) 0).toNat =
            b4 (u.toNat / 262144 % 64) (u.toNat / 4096 % 64) (u.toNat / 64 % 64) (u.toNat % 64) := by
          rw [shl32_toNat _ _ (by decide), hP]; simp only [Nat.reducePow]; unfold b4; omega
        rw [UInt32.toNat_or, hs, show (0xf0808080 : UInt32).toNat = b4 240 128 128 128 from rfl,
          orB4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          or240 _ (by omega), or128 _ (by omega), or128 _ (by omega), or128 _ (by omega)]
        unfold encNat; rw [if_neg h1, if_neg h2, if_neg h3]; unfold b4; omega

theorem bytes_of {n A B C D : Nat} (h : n = b4 A B C D) (hA : A < 256) (hB : B < 256)
    (hC : C < 256) (hD : D < 256) :
    n / 16777216 % 256 = A ∧ n / 65536 % 256 = B ∧ n / 256 % 256 = C ∧ n % 256 = D := by
  subst h; unfold b4; omega

theorem encB4_cases (u : Nat) :
    (u < 0x80 ∧ minimalUtf8Length u = 1 ∧ encNat u = b4 u 0 0 0) ∨
    (0x80 ≤ u ∧ u < 0x800 ∧ minimalUtf8Length u = 2 ∧
      encNat u = b4 (0xc0 + u / 64) (0x80 + u % 64) 0 0) ∨
    (0x800 ≤ u ∧ u < 0x10000 ∧ minimalUtf8Length u = 3 ∧
      encNat u = b4 (0xe0 + u / 4096) (0x80 + u / 64 % 64) (0x80 + u % 64) 0) ∨
    (0x10000 ≤ u ∧ minimalUtf8Length u = 4 ∧
      encNat u = b4 (0xf0 + u / 262144) (0x80 + u / 4096 % 64) (0x80 + u / 64 % 64)
        (0x80 + u % 64)) := by
  rcases lengthEnc_cases u with ⟨a1, m1, e1⟩ | ⟨a1, a2, m1, e1⟩ | ⟨a1, a2, m1, e1⟩ | ⟨a1, m1, e1⟩
  · exact Or.inl ⟨a1, m1, by rw [e1]; unfold b4; omega⟩
  · exact Or.inr (Or.inl ⟨a1, a2, m1, by rw [e1]; unfold b4; omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a1, a2, m1, by rw [e1]; unfold b4; omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a1, m1, by rw [e1]; unfold b4; omega⟩))

theorem encDigit_cases (u : Nat) (hu : u < 0x200000) :
    (u < 0x80 ∧ minimalUtf8Length u = 1 ∧ encNat u = b4 u 0 0 0) ∨
    (∃ z w, 2 ≤ z ∧ z < 32 ∧ w < 64 ∧ u = z * 64 + w ∧ minimalUtf8Length u = 2 ∧
      encNat u = b4 (192 + z) (128 + w) 0 0) ∨
    (∃ y z w, y < 16 ∧ z < 64 ∧ w < 64 ∧ 2048 ≤ u ∧ u = y * 4096 + z * 64 + w ∧
      minimalUtf8Length u = 3 ∧ encNat u = b4 (224 + y) (128 + z) (128 + w) 0) ∨
    (∃ x y z w, x < 8 ∧ y < 64 ∧ z < 64 ∧ w < 64 ∧ 65536 ≤ u ∧
      u = x * 262144 + y * 4096 + z * 64 + w ∧
      minimalUtf8Length u = 4 ∧ encNat u = b4 (240 + x) (128 + y) (128 + z) (128 + w)) := by
  rcases encB4_cases u with ⟨a1, m1, e1⟩ | ⟨a1, a2, m1, e1⟩ | ⟨a1, a2, m1, e1⟩ | ⟨a1, m1, e1⟩
  · exact Or.inl ⟨a1, m1, e1⟩
  · exact Or.inr (Or.inl ⟨u / 64, u % 64, by omega, by omega, by omega, by omega, m1, e1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨u / 4096, u / 64 % 64, u % 64, by omega, by omega, by omega,
      a1, by omega, m1, e1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨u / 262144, u / 4096 % 64, u / 64 % 64, u % 64, by omega,
      by omega, by omega, by omega, a1, by omega, m1, e1⟩))

theorem properlyEncoded_of_toNat (c : JChar) (u : Nat) (h : c.toNat = encNat u)
    (hu : u < 0x200000) : ProperlyEncoded c u := by
  rcases storedBytes_cases c with g | g | g | g <;>
    rcases encDigit_cases u hu with ⟨a1, m1, e1⟩ | ⟨z, w, hz, hz', hw, rfl, m1, e1⟩ |
      ⟨y, z, w, hy, hz, hw, a1, rfl, m1, e1⟩ | ⟨x, y, z, w, hx, hy, hz, hw, a1, rfl, m1, e1⟩ <;>
    · have g2 := g.2
      rw [e1] at h
      obtain ⟨q0, q1, q2, q3⟩ := bytes_of h (by omega) (by omega) (by omega) (by omega)
      simp only [ProperlyEncoded, g.1, Utf8Seq, List.length_cons, List.length_nil, m1]
      simp only [q0, q1, q2, q3] at g2 ⊢
      clear q0 q1 q2 q3 h e1 g
      try simp only [and_true]
      omega

theorem isoverlong_enc_false (c : JChar) (u : Nat) (h : c.toNat = encNat u)
    (hu : u < 0x200000) : isoverlong_Char c = false := by
  have h25 : (ushr32 c 25).toNat = c.toNat / 33554432 := by
    rw [ushr32_toNat _ _ (by decide)]
  have h21 : (ushr32 c 21).toNat = c.toNat / 2097152 := by
    rw [ushr32_toNat _ _ (by decide)]
  have h20 : (ushr32 c 20).toNat = c.toNat / 1048576 := by
    rw [ushr32_toNat _ _ (by decide)]
  have key : c.toNat / 33554432 ≠ 96 ∧ c.toNat / 2097152 ≠ 1796 ∧ c.toNat / 1048576 ≠ 3848 := by
    rcases encDigit_cases u hu with ⟨a1, m1, e1⟩ | ⟨z, w, hz, hz', hw, rfl, m1, e1⟩ |
      ⟨y, z, w, hy, hz, hw, a1, rfl, m1, e1⟩ | ⟨x, y, z, w, hx, hy, hz, hw, a1, rfl, m1, e1⟩ <;>
    · rw [e1] at h
      rw [h]
      unfold b4
      omega
  have k1 : ¬ (ushr32 c 25 = 0x60) := by
    intro e; have := congrArg UInt32.toNat e; rw [h25] at this; exact key.1 this
  have k2 : ¬ (ushr32 c 21 = 0x0704) := by
    intro e; have := congrArg UInt32.toNat e; rw [h21] at this; exact key.2.1 this
  have k3 : ¬ (ushr32 c 20 = 0x0f08) := by
    intro e; have := congrArg UInt32.toNat e; rw [h20] at this; exact key.2.2 this
  unfold isoverlong_Char is_overlong_enc
  simp [k1, k2, k3]

theorem charFromUInt32 : CharFromUInt32 := by
  intro u
  constructor
  · intro h
    have hn : 2097152 ≤ u.toNat := by
      have := UInt32.le_iff_toNat_le.mp h; exact this
    have a1 : ¬ u < 0x80 := litNotLt u 128 (by omega)
    have a2 : ¬ u < 0x00200000 := litNotLt u 2097152 hn
    exact ⟨.codePointError u, by simp [char_UInt32, a1, a2, throw_code_point_err, Functor.map, Except.map]⟩
  · intro h
    have hn : u.toNat < 2097152 := UInt32.lt_iff_toNat_lt.mp h
    obtain ⟨c, hc, he⟩ := charUInt32_ok u hn
    have hp := properlyEncoded_of_toNat c u.toNat he hn
    have hd := codepointDecodesUtf8 c u.toNat hp.1
    rw [UInt32.ofNat_toNat] at hd
    exact ⟨c, hc, hp, hd.2.1, hd.1, isoverlong_enc_false c u.toNat he hn⟩

/-! ### `ncodeunits(c)` and `write(io, c)` -/

theorem shrK (x : UInt32) (k : Nat) (hk : k < 32) :
    (x >>> (UInt32.ofNat k)).toNat = x.toNat / 2 ^ k := by
  rw [uintShrToNat x _ (by rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; exact hk),
    UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem shr8 (x : UInt32) : (x >>> (8 : UInt32)).toNat = x.toNat / 256 := shrK x 8 (by decide)

theorem shlK (x : UInt32) (k : Nat) (hk : k < 32) :
    (x <<< (UInt32.ofNat k)).toNat = x.toNat * 2 ^ k % 4294967296 := by
  rw [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (show k < 4294967296 by omega), Nat.mod_eq_of_lt hk]

theorem shlU (x k : UInt32) (hk : k.toNat < 32) :
    (x <<< k).toNat = x.toNat * 2 ^ k.toNat % 4294967296 := by
  rw [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hk]

theorem andFF (x : UInt32) : (x &&& 0xff).toNat = x.toNat % 256 := by
  rw [UInt32.toNat_and, show (0xff : UInt32).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem bswap_toNat (c : JChar) :
    (strings.basic.bswap32 c).toNat =
      b4 (c.toNat % 256) (c.toNat / 256 % 256) (c.toNat / 65536 % 256) (c.toNat / 16777216) := by
  have hlt := c.toNat_lt
  have p0 : ((c &&& 0xff) <<< (24 : UInt32)).toNat = b4 (c.toNat % 256) 0 0 0 := by
    rw [shlU _ _ (by decide), andFF, show (24 : UInt32).toNat = 24 from rfl]; simp only [Nat.reducePow]; unfold b4; omega
  have p1 : (((c >>> (8 : UInt32)) &&& 0xff) <<< (16 : UInt32)).toNat =
      b4 0 (c.toNat / 256 % 256) 0 0 := by
    rw [shlU _ _ (by decide), andFF, shr8, show (16 : UInt32).toNat = 16 from rfl]; simp only [Nat.reducePow]; unfold b4; omega
  have p2 : (((c >>> (16 : UInt32)) &&& 0xff) <<< (8 : UInt32)).toNat =
      b4 0 0 (c.toNat / 65536 % 256) 0 := by
    rw [shlU _ _ (by decide), andFF, uintShrToNat _ _ (by decide),
      show (8 : UInt32).toNat = 8 from rfl, show (16 : UInt32).toNat = 16 from rfl]; simp only [Nat.reducePow]
    unfold b4; omega
  have p3 : (c >>> (24 : UInt32)).toNat = b4 0 0 0 (c.toNat / 16777216) := by
    rw [uintShrToNat _ _ (by decide), show (24 : UInt32).toNat = 24 from rfl]; simp only [Nat.reducePow]; unfold b4; omega
  unfold strings.basic.bswap32
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or, p0, p1, p2, p3]
  simp (disch := omega) only [orB4, Nat.or_zero, Nat.zero_or]

theorem loop_small (f : Nat) (u : UInt32) (h : u.toNat < 256) :
    (strings.io.charUtf8BytesLoop (f + 1) u).length = 1 := by
  have hz : (u >>> 8 == 0) = true := by
    rw [beq_iff_eq, ← UInt32.toNat_inj, shr8]; change u.toNat / 256 = 0; omega
  simp [strings.io.charUtf8BytesLoop, hz]

theorem loop_big (f : Nat) (u : UInt32) (h : 256 ≤ u.toNat) :
    (strings.io.charUtf8BytesLoop (f + 1) u).length =
      (strings.io.charUtf8BytesLoop f (u >>> 8)).length + 1 := by
  have hz : ¬ (u >>> 8 == 0) = true := by
    rw [beq_iff_eq, ← UInt32.toNat_inj, shr8]; change ¬ u.toNat / 256 = 0; omega
  simp [strings.io.charUtf8BytesLoop, hz]

theorem loop4_len (B : UInt32) (x0 x1 x2 x3 : Nat) (hB : B.toNat = b4 x3 x2 x1 x0)
    (h0 : x0 < 256) (h1 : x1 < 256) (h2 : x2 < 256) (h3 : x3 < 256) :
    (strings.io.charUtf8BytesLoop 4 B).length =
      if x3 ≠ 0 then 4 else if x2 ≠ 0 then 3 else if x1 ≠ 0 then 2 else 1 := by
  have s1 : (B >>> 8).toNat = x3 * 65536 + x2 * 256 + x1 := by rw [shr8, hB]; unfold b4; omega
  have s2 : (B >>> 8 >>> 8).toNat = x3 * 256 + x2 := by rw [shr8, s1]; omega
  have s3 : (B >>> 8 >>> 8 >>> 8).toNat = x3 := by rw [shr8, s2]; omega
  have hB' : B.toNat = x3 * 16777216 + x2 * 65536 + x1 * 256 + x0 := by rw [hB]; unfold b4; omega
  by_cases a3 : x3 = 0
  · by_cases a2 : x2 = 0
    · by_cases a1 : x1 = 0
      · rw [loop_small 3 B (by omega)]; simp [a1, a2, a3]
      · rw [loop_big 3 B (by omega), loop_small 2 _ (by omega)]; simp [a1, a2, a3]
    · rw [loop_big 3 B (by omega), loop_big 2 _ (by omega), loop_small 1 _ (by omega)]
      simp [a2, a3]
  · rw [loop_big 3 B (by omega), loop_big 2 _ (by omega), loop_big 1 _ (by omega),
      loop_small 0 _ (by omega)]
    simp [a3]

theorem charUtf8Bytes_length (c : JChar) :
    (strings.io.charUtf8Bytes c).length = storedCount c := by
  have hlt := c.toNat_lt
  unfold strings.io.charUtf8Bytes
  rw [loop4_len _ _ _ _ _ (bswap_toNat c) (by omega) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
  simp only [storedCount, storageByte, Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.div_one]
  by_cases a : c.toNat % 256 = 0 <;> by_cases b : c.toNat / 256 % 256 = 0 <;>
    by_cases d : c.toNat / 65536 % 256 = 0 <;> simp [a, b, d]

theorem litArith (a b : Int) (ha0 : 0 ≤ b) (hab : b ≤ a) (ha : a ≤ 64) :
    JInt.lit .i64 a - JInt.lit .i64 b + JInt.lit .i64 0 = JInt.lit .i64 (a - b) := by
  show JInt.wrap .i64 ((JInt.wrap .i64 ((JInt.wrap .i64 a).val - (JInt.wrap .i64 b).val)).val +
    (JInt.wrap .i64 0).val) = JInt.wrap .i64 (a - b)
  have e1 : (JInt.wrap .i64 a).val = a := wrap64_small a (by omega) ha
  have e2 : (JInt.wrap .i64 b).val = b := wrap64_small b ha0 (by omega)
  have e0 : (JInt.wrap .i64 0).val = 0 := wrap64_small 0 (by omega) (by omega)
  rw [e1, e2, e0, Int.add_zero]
  have e3 : (JInt.wrap .i64 (a - b)).val = a - b := wrap64_small _ (by omega) (by omega)
  rw [e3]

theorem lit8_val : (JInt.lit .i64 8).val = 8 := wrap64_small 8 (by omega) (by omega)

theorem ncodeunits_div (c : JChar) (k : Nat) (hk8 : k % 8 = 0) (hk : k ≤ 24)
    (h1 : (k : Int) ≤ (charBitOps.trailingZeros c).val)
    (h2 : (charBitOps.trailingZeros c).val < (k + 8 : Int)) :
    divInt64 (charBitOps.trailingZeros c) (JInt.lit .i64 8) =
      .ok (JInt.lit .i64 ((k / 8 : Nat) : Int)) := by
  unfold divInt64
  generalize hL : JInt.lit .i64 8 = L
  have hLv : L.val = 8 := by rw [← hL]; exact lit8_val
  generalize hT : charBitOps.trailingZeros c = T at h1 h2 ⊢
  have hq : T.val.tdiv L.val = ((k / 8 : Nat) : Int) := by
    rw [hLv, Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  unfold JInt.div
  rw [if_neg (by omega), if_neg (by intro h; have := h.2.2; omega), hq]
  rfl

theorem ncu_abstract (sz : JInt64) (dv : JInt64 → JInt64 → CharResult JInt64) (ops : CharBitOps)
    (iz : JChar → Bool) (c : JChar) (q : JInt64)
    (hd : dv (ops.trailingZeros c) (JInt.lit .i64 8) = .ok q) (hz : iz c = false) :
    ncodeunits_Char sz dv ops iz c = .ok (sz - q + JInt.lit .i64 0) := by
  unfold ncodeunits_Char
  dsimp only
  rw [hd, hz]
  rfl

theorem iszero_ne (c : JChar) (hc : c ≠ 0) : iszeroUInt32 c = false := by
  simp [iszeroUInt32, hc]

theorem sz4 : ((int.sizeofT .u32 : Nat) : Int) = 4 := rfl

theorem ncodeunits_tz (c : JChar) (hc : c ≠ 0) (k n : Nat) (hk8 : k % 8 = 0) (hk : k ≤ 24)
    (hn : n = 4 - k / 8)
    (h1 : (k : Int) ≤ (charBitOps.trailingZeros c).val)
    (h2 : (charBitOps.trailingZeros c).val < (k + 8 : Int)) :
    ncodeunits_Char (JInt.lit .i64 (int.sizeofT .u32)) divInt64 charBitOps iszeroUInt32 c =
      .ok (JInt.lit .i64 n) := by
  rw [ncu_abstract _ _ _ _ c _ (ncodeunits_div c k hk8 hk h1 h2) (iszero_ne c hc),
    litArith _ _ (by omega) (by rw [sz4]; omega) (by rw [sz4]; omega), sz4]
  subst hn
  rw [show (4 : Int) - ((k / 8 : Nat) : Int) = ((4 - k / 8 : Nat) : Int) by omega]

theorem ncodeunits_count (c : JChar) :
    ncodeunits_Char (JInt.lit .i64 (int.sizeofT .u32)) divInt64 charBitOps iszeroUInt32 c =
      .ok (JInt.lit .i64 (storedCount c)) := by
  by_cases hc0 : c = 0
  · subst hc0; rfl
  · have hlt := c.toNat_lt
    have hne : c.toNat ≠ 0 := fun h => hc0 (UInt32.toNat_inj.mp (by rw [h]; rfl))
    have hs : storedCount c = (storedBytes c).length := by simp [storedBytes]
    rcases storedBytes_cases c with g | g | g | g <;> have g2 := g.2 <;> rw [hs, g.1] <;>
      simp only [List.length_cons, List.length_nil]
    · have htr := charTrailingZerosRange c 0 c.toNat (by decide) (by simp) g2
      exact ncodeunits_tz c hc0 0 _ (by decide) (by decide) rfl htr.1 htr.2
    · have htr := charTrailingZerosRange c 8 (c.toNat / 256) (by decide)
        (by simp only [Nat.reducePow]; omega) (by omega)
      exact ncodeunits_tz c hc0 8 _ (by decide) (by decide) rfl htr.1 htr.2
    · have htr := charTrailingZerosRange c 16 (c.toNat / 65536) (by decide)
        (by simp only [Nat.reducePow]; omega) (by omega)
      exact ncodeunits_tz c hc0 16 _ (by decide) (by decide) rfl htr.1 htr.2
    · have htr := charTrailingZerosRange c 24 (c.toNat / 16777216) (by decide)
        (by simp only [Nat.reducePow]; omega) (by omega)
      exact ncodeunits_tz c hc0 24 _ (by decide) (by decide) rfl htr.1 htr.2

theorem ncodeunitsCountsWrittenBytes : NcodeunitsCountsWrittenBytes := by
  intro c
  have hs : (storedBytes c).length = storedCount c := by simp [storedBytes]
  rw [charUtf8Bytes_length, hs]
  exact ⟨ncodeunits_count c, ncodeunits_count c⟩

/-! ### Numbers to `Char` -/

theorem routes_eq {N : Type} (f : N → CharResult JChar) (x : N) :
    ∀ r ∈ numberToCharRoutes f x, r = f x := by
  intro r hr
  simp only [numberToCharRoutes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> rfl

theorem charUInt32_err (u : JChar) (h : 2097152 ≤ u.toNat) : ∃ e, char_UInt32 u = .error e := by
  have a1 : ¬ u < 0x80 := litNotLt u 128 (by omega)
  have a2 : ¬ u < 0x00200000 := litNotLt u 2097152 h
  exact ⟨.codePointError u,
    by simp [char_UInt32, a1, a2, throw_code_point_err, Functor.map, Except.map]⟩

theorem charOfNat (n : Nat) (hn : n < 4294967296) :
    (n < 0x200000 → ∃ c, char_UInt32 (UInt32.ofNat n) = .ok c ∧ ProperlyEncoded c n) ∧
    (¬ n < 0x200000 → ∃ e, char_UInt32 (UInt32.ofNat n) = .error e) := by
  have ht : (UInt32.ofNat n).toNat = n := by rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt hn]
  constructor
  · intro h
    obtain ⟨c, hc, he⟩ := charUInt32_ok (UInt32.ofNat n) (by rw [ht]; exact h)
    rw [ht] at he
    exact ⟨c, hc, properlyEncoded_of_toNat c n he h⟩
  · intro h
    exact charUInt32_err _ (by rw [ht]; omega)

theorem u32_min : IntTy.u32.min = 0 := rfl
theorem u32_max : IntTy.u32.max = 4294967295 := rfl

theorem exactUInt32_ok (z : Int) (h0 : 0 ≤ z) (h1 : z < 4294967296) :
    exactUInt32 z = .ok (UInt32.ofNat z.toNat) := by
  have hr : IntTy.u32.min ≤ z ∧ z ≤ IntTy.u32.max := by rw [u32_min, u32_max]; omega
  unfold exactUInt32 JInt.convert
  rw [dif_pos hr]

theorem exactUInt32_err (z : Int) (h : z < 0 ∨ 4294967296 ≤ z) :
    ∃ e, exactUInt32 z = .error e := by
  have hr : ¬ (IntTy.u32.min ≤ z ∧ z ≤ IntTy.u32.max) := by rw [u32_min, u32_max]; omega
  unfold exactUInt32 JInt.convert
  rw [dif_neg hr]
  exact ⟨_, rfl⟩

theorem intRoute {t : IntTy} (x : JInt t) :
    (0 ≤ x.val ∧ x.val < 0x200000 →
      ∃ c, constructor_Number_AbstractChar uint32OfInteger char_UInt32 x = .ok c ∧
        ProperlyEncoded c x.val.toNat) ∧
    (¬ (0 ≤ x.val ∧ x.val < 0x200000) →
      ∃ e, constructor_Number_AbstractChar uint32OfInteger char_UInt32 x = .error e) := by
  by_cases h0 : 0 ≤ x.val ∧ x.val < 4294967296
  · have he : constructor_Number_AbstractChar uint32OfInteger char_UInt32 x =
        char_UInt32 (UInt32.ofNat x.val.toNat) := by
      unfold constructor_Number_AbstractChar uint32OfInteger
      rw [exactUInt32_ok _ h0.1 h0.2]
      rfl
    rw [he]
    have hs := charOfNat x.val.toNat (by omega)
    exact ⟨fun h => hs.1 (by omega), fun h => hs.2 (by omega)⟩
  · obtain ⟨e, he⟩ := exactUInt32_err x.val (by omega)
    have hr : constructor_Number_AbstractChar uint32OfInteger char_UInt32 x = .error e := by
      unfold constructor_Number_AbstractChar uint32OfInteger
      rw [he]
      rfl
    exact ⟨fun h => absurd ⟨h.1, by omega⟩ h0, fun _ => ⟨e, hr⟩⟩

theorem u32Route (x : JInt .u32) :
    (0 ≤ x.val ∧ x.val < 0x200000 →
      ∃ c, char_UInt32 (UInt32.ofNat x.val.toNat) = .ok c ∧ ProperlyEncoded c x.val.toNat) ∧
    (¬ (0 ≤ x.val ∧ x.val < 0x200000) →
      ∃ e, char_UInt32 (UInt32.ofNat x.val.toNat) = .error e) := by
  have hx1 : 0 ≤ x.val := Int.le_trans (Int.le_of_eq u32_min.symm) x.property.1
  have hx2 : x.val ≤ 4294967295 := Int.le_trans x.property.2 (Int.le_of_eq u32_max)
  have hs := charOfNat x.val.toNat (by omega)
  exact ⟨fun h => hs.1 (by omega), fun h => hs.2 (by omega)⟩

theorem u8_min : IntTy.u8.min = 0 := rfl
theorem u8_max : IntTy.u8.max = 255 := rfl
theorem i8_min : IntTy.i8.min = -128 := rfl
theorem i8_max : IntTy.i8.max = 127 := rfl

theorem isAscii_eq (t : IntTy) (ht : t = .u8 ∨ t = .i8) (b : JInt t) :
    isAsciiSmall b = decide (0 ≤ b.val ∧ b.val ≤ 127) := by
  rcases ht with rfl | rfl
  · have hb1 : 0 ≤ b.val := Int.le_trans (Int.le_of_eq u8_min.symm) b.property.1
    have hb2 : b.val ≤ 255 := Int.le_trans b.property.2 (Int.le_of_eq u8_max)
    simp only [isAsciiSmall, lePromote, promoteSameSign, JuliaLean.Proofs.base.int.leSame_eq,
      JuliaLean.Proofs.base.int.widenTo_val]
    simp [IntTy.promote, IntTy.signed, IntTy.bits, wrapInt, JInt.lit, JInt.wrap]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  · have hb1 : -128 ≤ b.val := Int.le_trans (Int.le_of_eq i8_min.symm) b.property.1
    have hb2 : b.val ≤ 127 := Int.le_trans b.property.2 (Int.le_of_eq i8_max)
    simp only [isAsciiSmall, lePromote, promoteSameSign, JuliaLean.Proofs.base.int.leSame_eq,
      JuliaLean.Proofs.base.int.widenTo_val]
    simp [IntTy.promote, IntTy.signed, IntTy.bits, wrapInt, JInt.lit, JInt.wrap]
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega

theorem smallRoute (t : IntTy) (ht : t = .u8 ∨ t = .i8) (x : JInt t) :
    (0 ≤ x.val ∧ x.val < 0x200000 →
      ∃ c, char_SmallInteger isAsciiSmall smallBitsUInt32 uint32OfInteger x = .ok c ∧
        ProperlyEncoded c x.val.toNat) ∧
    (¬ (0 ≤ x.val ∧ x.val < 0x200000) →
      ∃ e, char_SmallInteger isAsciiSmall smallBitsUInt32 uint32OfInteger x = .error e) := by
  by_cases ha : 0 ≤ x.val ∧ x.val ≤ 127
  · have hA : isAsciiSmall x = true := by rw [isAscii_eq t ht x]; exact decide_eq_true ha
    have hw : wrapInt .u32 x.val = x.val := by
      simp only [wrapInt, IntTy.signed, IntTy.bits]; simp; omega
    have hsb : (smallBitsUInt32 x).toNat = x.val.toNat := by
      unfold smallBitsUInt32
      rw [JuliaLean.Proofs.base.int.remT_val, hw, UInt32.toNat_ofNat']
      omega
    have hr : char_SmallInteger isAsciiSmall smallBitsUInt32 uint32OfInteger x =
        .ok (shl32 (smallBitsUInt32 x) 24) := by
      simp only [char_SmallInteger, hA, if_true]
    refine ⟨fun _ => ⟨_, hr, properlyEncoded_of_toNat _ _ ?_ (by omega)⟩,
      fun h => absurd ⟨ha.1, by omega⟩ h⟩
    rw [shl32_toNat _ _ (by decide), hsb]
    unfold encNat
    rw [if_pos (by omega)]
    simp only [Nat.reducePow]
    omega
  · have hA : isAsciiSmall x = false := by rw [isAscii_eq t ht x]; exact decide_eq_false ha
    have hr : char_SmallInteger isAsciiSmall smallBitsUInt32 uint32OfInteger x =
        constructor_Number_AbstractChar uint32OfInteger char_UInt32 x := by
      simp only [char_SmallInteger, hA, Bool.false_eq_true, if_false]
      rfl
    rw [hr]
    exact intRoute x

theorem boolRoute (b : Bool) :
    ∃ c, constructor_Number_AbstractChar uint32OfBool char_UInt32 b = .ok c ∧
      ProperlyEncoded c (if b then 1 else 0) := by
  have hv : UInt32.ofNat (int.ofBool .u32 b).val.toNat = UInt32.ofNat (if b then 1 else 0) := by
    cases b <;> rfl
  obtain ⟨c, hc, hp⟩ := (charOfNat (if b then 1 else 0) (by split <;> omega)).1
    (by split <;> omega)
  refine ⟨c, ?_, hp⟩
  unfold constructor_Number_AbstractChar uint32OfBool
  rw [hv]
  exact hc

theorem toRat_den_pos {T : float.FTy} (x : float.FV T) (h : x.isfinite = true) :
    0 < x.toRat.2 := by
  unfold Fl.toRat
  simp only [h, Bool.not_true, Bool.false_eq_true, if_false]
  split <;> split <;> simp [Nat.two_pow_pos]

theorem exact_iff {T : float.FTy} (x : float.FV T) (n : Int) :
    (x.isfinite = true ∧ x.toRat.1 = n * (x.toRat.2 : Int)) ↔
      (x.isinteger = true ∧ x.truncVal = n) := by
  constructor
  · rintro ⟨hf, he⟩
    have hd := toRat_den_pos x hf
    refine ⟨?_, ?_⟩
    · simp only [Fl.isinteger, hf, Bool.true_and, beq_iff_eq]
      rw [he]
      exact Int.mul_emod_left _ _
    · simp only [Fl.truncVal]
      rw [he]
      exact Int.mul_tdiv_cancel _ (by omega)
  · rintro ⟨hi, ht⟩
    simp only [Fl.isinteger, Bool.and_eq_true, beq_iff_eq] at hi
    refine ⟨hi.1, ?_⟩
    have hdv := Int.dvd_of_emod_eq_zero hi.2
    simp only [Fl.truncVal] at ht
    rw [Int.tdiv_eq_ediv_of_dvd hdv] at ht
    rw [← ht, Int.ediv_mul_cancel hdv]

theorem floatRoute {Tf : float.FTy} (x : float.FV Tf) :
    (∀ n : Int, (x.isfinite = true ∧ x.toRat.1 = n * (x.toRat.2 : Int)) → 0 ≤ n → n < 0x200000 →
      ∃ c, constructor_Number_AbstractChar uint32OfFloat char_UInt32 x = .ok c ∧
        ProperlyEncoded c n.toNat) ∧
    ((¬ ∃ n : Int, (x.isfinite = true ∧ x.toRat.1 = n * (x.toRat.2 : Int)) ∧ 0 ≤ n ∧
        n < 0x200000) →
      ∃ e, constructor_Number_AbstractChar uint32OfFloat char_UInt32 x = .error e) := by
  have hI := JuliaLean.Proofs.base.float.TruncProofs.intOfFloat_eq Tf .u32 x
  by_cases hc : (x.isinteger && decide (IntTy.u32.min ≤ x.truncVal ∧ x.truncVal ≤ IntTy.u32.max))
      = true
  · rw [if_pos hc] at hI
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hc : x.isinteger = true ∧ 0 ≤ x.truncVal ∧ x.truncVal ≤ 4294967295 :=
      ⟨hc.1, Int.le_trans (Int.le_of_eq u32_min.symm) hc.2.1, Int.le_trans hc.2.2 (Int.le_of_eq u32_max)⟩
    have hw : wrapInt .u32 x.truncVal = x.truncVal := by
      simp only [wrapInt, IntTy.signed, IntTy.bits]; simp; omega
    have hr : constructor_Number_AbstractChar uint32OfFloat char_UInt32 x =
        char_UInt32 (UInt32.ofNat x.truncVal.toNat) := by
      unfold constructor_Number_AbstractChar uint32OfFloat
      rw [hI]
      show char_UInt32 (UInt32.ofNat (wrapInt .u32 x.truncVal).toNat) = _
      rw [hw]
    rw [hr]
    have hs := charOfNat x.truncVal.toNat (by omega)
    constructor
    · intro n hn h0 h1
      have ht := ((exact_iff x n).mp hn).2
      subst ht
      exact hs.1 (by omega)
    · intro hno
      apply hs.2
      intro hlt
      exact hno ⟨x.truncVal, (exact_iff x _).mpr ⟨hc.1, rfl⟩, hc.2.1, by omega⟩
  · rw [if_neg hc] at hI
    have hr : constructor_Number_AbstractChar uint32OfFloat char_UInt32 x =
        .error (.foreign (.inexactError IntTy.u32.name)) := by
      unfold constructor_Number_AbstractChar uint32OfFloat
      rw [hI]
      rfl
    rw [hr]
    refine ⟨?_, fun _ => ⟨_, rfl⟩⟩
    intro n hn h0 h1
    have hx := (exact_iff x n).mp hn
    exfalso
    apply hc
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hx.1, by rw [u32_min, hx.2]; exact h0, by rw [u32_max, hx.2]; omega⟩

theorem genericRoute {N : Type} (toU : N → CharResult JChar) (x : N) :
    (∀ u, toU x = .ok u →
      (u < 0x00200000 → ∃ c, constructor_Number_AbstractChar toU char_UInt32 x = .ok c ∧
        ProperlyEncoded c u.toNat) ∧
      (0x00200000 ≤ u → ∃ e, constructor_Number_AbstractChar toU char_UInt32 x = .error e)) ∧
    (∀ e, toU x = .error e → constructor_Number_AbstractChar toU char_UInt32 x = .error e) := by
  constructor
  · intro u hu
    have hr : constructor_Number_AbstractChar toU char_UInt32 x = char_UInt32 u := by
      unfold constructor_Number_AbstractChar; rw [hu]; rfl
    rw [hr]
    have hs := charOfNat u.toNat u.toNat_lt
    rw [UInt32.ofNat_toNat] at hs
    constructor
    · intro h
      exact hs.1 (UInt32.lt_iff_toNat_lt.mp h)
    · intro h
      exact hs.2 (by have := UInt32.le_iff_toNat_le.mp h; change 2097152 ≤ u.toNat at this; omega)
  · intro e he
    unfold constructor_Number_AbstractChar; rw [he]; rfl

theorem abstractRoute {C : Type} (cp : C → CharResult JChar) (x : C) :
    (∀ u, cp x = .ok u →
      (u < 0x00200000 → ∃ c, constructor_AbstractChar_AbstractChar cp char_UInt32 x = .ok c ∧
        ProperlyEncoded c u.toNat) ∧
      (0x00200000 ≤ u → ∃ e, constructor_AbstractChar_AbstractChar cp char_UInt32 x = .error e)) ∧
    (∀ e, cp x = .error e → constructor_AbstractChar_AbstractChar cp char_UInt32 x = .error e) :=
  genericRoute cp x

theorem numberToChar : NumberToChar := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t x r hr
    rw [routes_eq _ x r hr]
    cases t <;> first
      | exact u32Route x
      | exact smallRoute _ (Or.inl rfl) x
      | exact smallRoute _ (Or.inr rfl) x
      | exact intRoute x
  · intro b r hr
    rw [routes_eq _ b r hr]
    exact boolRoute b
  · intro Tf x r hr
    rw [routes_eq _ x r hr]
    exact floatRoute x
  · intro N toU x r hr
    rw [routes_eq _ x r hr]
    exact genericRoute toU x
  · intro C cp x
    exact abstractRoute cp x

end BitLevel

end JuliaLean.Proofs.base.char

/-! Proofs for the unchanged batch 4 group 14 character properties. -/

namespace JuliaLean.ChatGPT.Batch4.Group14
open JuliaLean JuliaLean.base.char JuliaLean.Proofs.base.char

/-- Fallback comparisons use the successfully converted character values. -/
theorem CharAbstractComparisons_proven : JuliaLean.Proofs.base.char.CharAbstractComparison := by
  intro C toChar x y c d hx hy
  simp only [isless_AbstractChar, eq_AbstractChar, hx, hy, bind, Except.bind,
    pure, Except.pure, and_self]

/-- Equality of raw character storage implies equality of every seeded hash. -/
theorem CharHashEquality_proven : JuliaLean.Proofs.base.char.CharHashRespectsEquality := by
  constructor
  · intro finalize x y h he
    have hxy : x = y := by simpa only [eq_Char, beq_iff_eq] using he
    cases hxy
    rfl
  · intro C toChar finalize x h c hx
    simp only [hash_AbstractChar, hx, bind, Except.bind, pure, Except.pure]

/-- The abstract fallback converts before calling the character printer. -/
theorem CharAbstractPrint_proven : JuliaLean.Proofs.base.char.AbstractCharPrintUsesChar := by
  intro C IO toChar printChar io c value io' hc hp
  simp only [print_AbstractChar, hc, bind, Except.bind, hp]

/-- Printing a concrete character preserves the updated IO state. -/
theorem charPrintWrites : JuliaLean.Proofs.base.char.CharPrintWritesChar := by
  intro IO writeChar io c io' count hw
  simp only [print_Char, hw, bind, Except.bind, pure, Except.pure]

/-- The documented malformed-codepoint guarantee fails at two ordinary stored bytes. -/
theorem IntfuncscovCharEncoding_refuted : ¬ JuliaLean.Proofs.base.char.CharEncodingBehavior := by
  intro h
  obtain ⟨e, he⟩ := h.1 (0x61620000 : JChar) mal_6162
  rw [cp_6162] at he
  cases he

/-- The finite short-escape table takes precedence over the generic display paths. -/
theorem CharShowControlEscapes_proven : JuliaLean.Proofs.base.char.ShowControlEscapes := by
  intro isPrint c escape h
  by_cases h0 : c = 0x00000000
  · subst c
    have he : (0x30 : UInt8) = escape := by simpa [controlEscapeSpec] using h
    subst escape
    rfl
  by_cases h1 : c = 0x07000000
  · subst c
    have he : (0x61 : UInt8) = escape := by simpa [controlEscapeSpec] using h
    subst escape
    rfl
  by_cases h2 : c = 0x08000000
  · subst c
    have he : (0x62 : UInt8) = escape := by simpa [controlEscapeSpec] using h
    subst escape
    rfl
  by_cases h3 : c = 0x09000000
  · subst c
    have he : (0x74 : UInt8) = escape := by simpa [controlEscapeSpec] using h
    subst escape
    rfl
  by_cases h4 : c = 0x0a000000
  · subst c
    have he : (0x6e : UInt8) = escape := by simpa [controlEscapeSpec] using h
    subst escape
    rfl
  by_cases h5 : c = 0x0b000000
  · subst c
    have he : (0x76 : UInt8) = escape := by simpa [controlEscapeSpec] using h
    subst escape
    rfl
  by_cases h6 : c = 0x0c000000
  · subst c
    have he : (0x66 : UInt8) = escape := by simpa [controlEscapeSpec] using h
    subst escape
    rfl
  by_cases h7 : c = 0x0d000000
  · subst c
    have he : (0x72 : UInt8) = escape := by simpa [controlEscapeSpec] using h
    subst escape
    rfl
  by_cases h8 : c = 0x1b000000
  · subst c
    have he : (0x65 : UInt8) = escape := by simpa [controlEscapeSpec] using h
    subst escape
    rfl
  by_cases h9 : c = 0x27000000
  · subst c
    have he : (0x27 : UInt8) = escape := by simpa [controlEscapeSpec] using h
    subst escape
    rfl
  by_cases h10 : c = 0x5c000000
  · subst c
    have he : (0x5c : UInt8) = escape := by simpa [controlEscapeSpec] using h
    subst escape
    rfl
  simp [controlEscapeSpec, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] at h

/-- A generic reduction for the printable path, kept separate from concrete character adapters. -/
theorem charPrintablePath {C IO N : Type} (ops : CharShowOps C IO N)
    (io io1 io2 io3 : IO) (c : C) (b : Bool)
    (hlt : ops.lessEqualBackslash c = .ok b)
    (he0 : ops.equalChar c 0x00000000 = .ok false)
    (he1 : ops.equalChar c 0x07000000 = .ok false)
    (he2 : ops.equalChar c 0x08000000 = .ok false)
    (he3 : ops.equalChar c 0x09000000 = .ok false)
    (he4 : ops.equalChar c 0x0a000000 = .ok false)
    (he5 : ops.equalChar c 0x0b000000 = .ok false)
    (he6 : ops.equalChar c 0x0c000000 = .ok false)
    (he7 : ops.equalChar c 0x0d000000 = .ok false)
    (he8 : ops.equalChar c 0x1b000000 = .ok false)
    (he9 : ops.equalChar c 0x27000000 = .ok false)
    (he10 : ops.equalChar c 0x5c000000 = .ok false)
    (ho : ops.isOverlong c = .ok false) (hm : ops.isMalformed c = .ok false)
    (hp : ops.isPrint c = .ok true)
    (n1 n3 : JInt64)
    (hw1 : ops.writeBytes io [0x27] = .ok (io1, n1))
    (hprint : ops.printChar io1 c = .ok (io2, ()))
    (hw3 : ops.writeBytes io2 [0x27] = .ok (io3, n3)) :
    show_AbstractChar ops io c = .ok (io3, ()) := by
  have hb : ((0xff : UInt8) != 0xff) = false := by decide
  cases b <;>
    simp only [show_AbstractChar, hlt, he0, he1, he2, he3, he4, he5, he6, he7, he8, he9, he10,
      ho, hm, hp, hw1, hprint, hw3, hb, bind, Except.bind, pure, Except.pure,
      Bool.false_eq_true, ite_false, ite_true]

/-- Printable ordinary characters follow the quoted character-output path. -/
theorem CharShowPrintable_proven : JuliaLean.Proofs.base.char.ShowPrintableChars := by
  intro isPrint c hc hp hm ho
  have h0 : c ≠ 0x00000000 := by
    intro h
    subst c
    simp [controlEscapeSpec] at hc
  have h1 : c ≠ 0x07000000 := by
    intro h
    subst c
    simp [controlEscapeSpec] at hc
  have h2 : c ≠ 0x08000000 := by
    intro h
    subst c
    simp [controlEscapeSpec] at hc
  have h3 : c ≠ 0x09000000 := by
    intro h
    subst c
    simp [controlEscapeSpec] at hc
  have h4 : c ≠ 0x0a000000 := by
    intro h
    subst c
    simp [controlEscapeSpec] at hc
  have h5 : c ≠ 0x0b000000 := by
    intro h
    subst c
    simp [controlEscapeSpec] at hc
  have h6 : c ≠ 0x0c000000 := by
    intro h
    subst c
    simp [controlEscapeSpec] at hc
  have h7 : c ≠ 0x0d000000 := by
    intro h
    subst c
    simp [controlEscapeSpec] at hc
  have h8 : c ≠ 0x1b000000 := by
    intro h
    subst c
    simp [controlEscapeSpec] at hc
  have h9 : c ≠ 0x27000000 := by
    intro h
    subst c
    simp [controlEscapeSpec] at hc
  have h10 : c ≠ 0x5c000000 := by
    intro h
    subst c
    simp [controlEscapeSpec] at hc
  have hle : (charShowOps isPrint).lessEqualBackslash c = .ok (decide (c ≤ 0x5c000000)) := rfl
  have heq (d : JChar) : (charShowOps isPrint).equalChar c d = .ok (c == d) := rfl
  have hp' : (charShowOps isPrint).isPrint c = .ok true := by
    change Except.ok (isPrint c) = Except.ok true
    rw [hp]
  have hm' : (charShowOps isPrint).isMalformed c = .ok false := by
    change Except.ok (ismalformed_Char charBitOps c) = Except.ok false
    rw [hm]
  have ho' : (charShowOps isPrint).isOverlong c = .ok false := by
    change Except.ok (isoverlong_Char c) = Except.ok false
    rw [ho]
  have hw (io : List CharOutput) (bs : List UInt8) :
      (charShowOps isPrint).writeBytes io bs =
      .ok (io ++ [.bytes bs], JInt.lit .i64 bs.length) := rfl
  have hprint (io : List CharOutput) : (charShowOps isPrint).printChar io c =
      .ok (io ++ [.character c], ()) := rfl
  apply charPrintablePath (charShowOps isPrint) [] [.bytes [0x27]]
    [.bytes [0x27], .character c] [.bytes [0x27], .character c, .bytes [0x27]]
    c (decide (c ≤ 0x5c000000)) hle
    (n1 := JInt.lit .i64 1) (n3 := JInt.lit .i64 1)
  · simp only [heq, beq_eq_false_iff_ne.mpr h0]
  · simp only [heq, beq_eq_false_iff_ne.mpr h1]
  · simp only [heq, beq_eq_false_iff_ne.mpr h2]
  · simp only [heq, beq_eq_false_iff_ne.mpr h3]
  · simp only [heq, beq_eq_false_iff_ne.mpr h4]
  · simp only [heq, beq_eq_false_iff_ne.mpr h5]
  · simp only [heq, beq_eq_false_iff_ne.mpr h6]
  · simp only [heq, beq_eq_false_iff_ne.mpr h7]
  · simp only [heq, beq_eq_false_iff_ne.mpr h8]
  · simp only [heq, beq_eq_false_iff_ne.mpr h9]
  · simp only [heq, beq_eq_false_iff_ne.mpr h10]
  · exact ho'
  · exact hm'
  · exact hp'
  · rfl
  · rfl
  · rfl




/-- Every successful non-compact plain display records the selected state branch. -/
theorem CharShowPlainState_proven : JuliaLean.Proofs.base.char.PlainDisplayReportsState := by
  intro ops c initial trace hp hs hc ht
  constructor
  · intro hm
    cases ha : ops.categoryAbbrev c <;> cases hd : ops.categoryString c <;>
      simp [show_MIMETextPlain, hp, hs, hc, hm, printStringsTrace, ha, hd, bind, Except.bind, pure, Except.pure] at ht
    cases ht
    simp [List.mem_append]
  constructor
  · intro u converted padded hm ho hu hv hpadded
    cases ha : ops.categoryAbbrev converted <;> cases hd : ops.categoryString converted <;>
      simp [show_MIMETextPlain, hp, hs, hc, hm, ho, hu, hv, hpadded,
        printStringsTrace, ha, hd, bind, Except.bind, pure, Except.pure] at ht
    cases ht
    simp [List.mem_append]
  · intro u padded hm ho hu hpadded
    cases ha : ops.categoryAbbrev c <;> cases hd : ops.categoryString c <;>
      simp [show_MIMETextPlain, hp, hs, hc, hm, ho, hu, hpadded,
        printStringsTrace, ha, hd, bind, Except.bind, pure, Except.pure] at ht
    cases ht
    simp [List.mem_append]

end JuliaLean.ChatGPT.Batch4.Group14

namespace JuliaLean.Proofs.base.char

open JuliaLean.Registry

/-! ## Registry entries -/

def entries : List JuliaLean.Registry.Entry := [
  { id := "missingchar-codepoint-malformed", juliaFile := "base/char.jl",
    juliaFns := ["codepoint(::Char)", "UInt32(::Char)", "ismalformed(::Char)"],
    statement := "For every Char c, codepoint(c) and UInt32(c) throw exactly when ismalformed(c) is true.",
    source := "base/char.jl:46-48,83-92,135-142", status := .refuted,
    prop := ``CodepointThrowsExactlyMalformed, thm := some ``refute_codepoint_malformed,
    issue := "none found (JuliaLang/julia issues and PRs searched for: ismalformed; isoverlong; decode_overlong; \"malformed Char codepoint\"; \"Char arithmetic malformed\"; \"overlong char\"). Related, not duplicates: PR #55152 (codepoint for overlong chars), PR #25559 (overlong !isvalid), PR #54393 (hascodepoint, closed), PR #61625 (nothrow effects on Char predicates), issue #25072",
    notes := "Bug A, root cause: an ASCII lead byte with trailing junk skips the malformed check (char.jl:161, 225, 279, 289). Primary entry. reinterpret(Char, 0x61620000) (also 0x41c00000) is ismalformed, yet codepoint and UInt32 return 0x61 instead of throwing. Reproduced on 1.13.2 and nightly." },
  { id := "missingchar-codepoint-wellformed", juliaFile := "base/char.jl",
    juliaFns := ["codepoint(::Char)", "UInt32(::Char)", "ismalformed(::Char)"],
    statement := "A Char storing exactly one UTF-8 sequence (shortest or overlong) for u is not malformed, and codepoint(c) and UInt32(c) return u.",
    source := "base/char.jl:80-92,135-142", status := .proven,
    prop := ``CodepointDecodesUtf8, thm := some ``codepointDecodesUtf8 },
  { id := "char-ismalformed-exact-sequence", juliaFile := "base/char.jl",
    juliaFns := ["ismalformed(::Char)"],
    statement := "Every Char for which ismalformed is false stores exactly one UTF-8 sequence.",
    source := "base/char.jl:129-142", status := .refuted,
    prop := ``NonMalformedIsOneSequence, thm := some ``refute_exact_sequence,
    issue := "none found (JuliaLang/julia issues and PRs searched for: ismalformed; isoverlong; decode_overlong; \"malformed Char codepoint\"; \"Char arithmetic malformed\"; \"overlong char\"). Related, not duplicates: PR #55152 (codepoint for overlong chars), PR #25559 (overlong !isvalid), PR #54393 (hascodepoint, closed), PR #61625 (nothrow effects on Char predicates), issue #25072",
    notes := "Bug B: an ASCII lead byte followed by a continuation byte is not flagged malformed (char.jl:111-117). Primary entry. reinterpret(Char, 0x41800000) stores bytes 0x41 0x80, which decode to two characters, yet ismalformed is false. Reproduced on 1.13.2 and nightly." },
  { id := "missingchar-char-codepoint-roundtrip", juliaFile := "base/char.jl",
    juliaFns := ["Char(::UInt32)", "codepoint(::Char)", "ismalformed(::Char)", "isoverlong(::Char)",
      "throw_code_point_err(::Integer)"],
    statement := "Char(u::UInt32) throws for u >= 0x200000; otherwise it is the standard UTF-8 encoding of u, not malformed, not overlong, and codepoint(Char(u)) == u.",
    source := "base/char.jl:9-22,39-51", status := .proven,
    prop := ``CharFromUInt32, thm := some ``charFromUInt32 },
  { id := "missingchar-char-order-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["isless(::Char, ::Char)", "==(::Char, ::Char)"],
    statement := "For every pair of standard UTF-8 encoded Chars, isless and == agree with codepoint order and equality.",
    source := "base/char.jl:10-12", status := .proven,
    prop := ``CharOrderCodepoint, thm := some ``charOrderCodepoint },
  { id := "missingchar-char-add-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["+(::Char, ::Integer)", "+%(::Char, ::Integer)",
      "+%(::Integer, ::AbstractChar)", "+(::Integer, ::AbstractChar)"],
    statement := "Char with Int (Int64 component; other Integer types await model R2): in either order, + and +% give the standard encoding of codepoint(c) + n when it lies in [0, 0x200000), and throw otherwise or for a malformed Char.",
    source := "invariant; base/char.jl:9-12,80-92,276-300", status := .refuted,
    prop := ``CharAddInt64, thm := some ``refute_add,
    issue := "none found (JuliaLang/julia issues and PRs searched for: ismalformed; isoverlong; decode_overlong; \"malformed Char codepoint\"; \"Char arithmetic malformed\"; \"overlong char\"). Related, not duplicates: PR #55152 (codepoint for overlong chars), PR #25559 (overlong !isvalid), PR #54393 (hascodepoint, closed), PR #61625 (nothrow effects on Char predicates), issue #25072",
    notes := "Bug A, root cause: an ASCII lead byte with trailing junk skips the malformed check (char.jl:161, 225, 279, 289). Covered by missingchar-codepoint-malformed. reinterpret(Char, 0x41c00000) + 1 == 'B' (fast path char.jl:289) for a malformed Char. Reproduced on 1.13.2 and nightly." },
  { id := "char-sub-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["-(::Char, ::Integer)", "-%(::Char, ::Integer)"],
    statement := "Char minus Int (Int64 component; other Integer types await model R2): - and -% give the standard encoding of codepoint(c) - n when it lies in [0, 0x200000), and throw otherwise or for a malformed Char.",
    source := "invariant; base/char.jl:9-12,80-92,276-298", status := .refuted,
    prop := ``CharSubInt64, thm := some ``refute_sub,
    issue := "none found (JuliaLang/julia issues and PRs searched for: ismalformed; isoverlong; decode_overlong; \"malformed Char codepoint\"; \"Char arithmetic malformed\"; \"overlong char\"). Related, not duplicates: PR #55152 (codepoint for overlong chars), PR #25559 (overlong !isvalid), PR #54393 (hascodepoint, closed), PR #61625 (nothrow effects on Char predicates), issue #25072",
    notes := "Bug A, root cause: an ASCII lead byte with trailing junk skips the malformed check (char.jl:161, 225, 279, 289). Covered by missingchar-codepoint-malformed. reinterpret(Char, 0x41c00000) - 1 == '@' (fast path char.jl:279) for a malformed Char. Reproduced on 1.13.2 and nightly." },
  { id := "missingchar-ncodeunits-write", juliaFile := "base/char.jl",
    juliaFns := ["ncodeunits(::Char)", "write(::IO, ::Char)"],
    statement := "ncodeunits(c) is the number of bytes write(io, c) emits (installed charUtf8Bytes), which is the number of stored UTF-8 bytes, '\\0' counting one.",
    source := "base/char.jl:60-78", status := .proven,
    prop := ``NcodeunitsCountsWrittenBytes, thm := some ``ncodeunitsCountsWrittenBytes },
  { id := "missingchar-show-char-roundtrip", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::AbstractChar)", "write(::IO, ::Char)"],
    statement := "For every Char and every isprint answer, show(io, c) does not throw and its output, with characters written by the installed write(io, ::Char) model, reads back as c under Julia's character-literal syntax.",
    source := "base/show.jl show contract; base/char.jl:325-370", status := .refuted,
    prop := ``ShowCharLiteralRoundTrip, thm := some ``refute_show_roundtrip,
    issue := "none found (JuliaLang/julia issues and PRs searched for: ismalformed; isoverlong; decode_overlong; \"malformed Char codepoint\"; \"Char arithmetic malformed\"; \"overlong char\"). Related, not duplicates: PR #55152 (codepoint for overlong chars), PR #25559 (overlong !isvalid), PR #54393 (hascodepoint, closed), PR #61625 (nothrow effects on Char predicates), issue #25072",
    notes := "Bug B: an ASCII lead byte followed by a continuation byte is not flagged malformed (char.jl:111-117). Covered by char-ismalformed-exact-sequence. show(reinterpret(Char, 0x41800000)) writes 'A\\x80' raw, which Meta.parse rejects (invalid UTF-8). The repro also keeps the older case Char(0x110000): repr '\\U110000' does not parse. Reproduced on 1.13.2 and nightly." },
  { id := "intfuncscov-char-encoding", juliaFile := "base/char.jl",
    juliaFns := ["AbstractChar", "Char", "codepoint", "ismalformed", "isoverlong",
      "unsafe_codepoint", "decode_overlong", "UInt32", "UInt32_cold", "Char_cold", "convert", "rem"],
    statement := "Char construction, decoding, malformed and overlong checks, unsafe decoding, and numeric conversion preserve the documented codepoint behavior.",
    source := "base/char.jl:54-239", status := .refuted,
    prop := ``CharEncodingBehavior, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.IntfuncscovCharEncoding_refuted,
    issue := "documentation mismatch for reinterpret-only representation; related JuliaLang/julia#59800 (open), #48283 (open), #44989 (merged), #29192 (merged)" },
  { id := "intfuncscov-char-scalar", juliaFile := "base/char.jl",
    juliaFns := ["typemax(::Type{Char})", "typemin(::Type{Char})", "isless(::Char, ::Char)"],
    statement := "typemax(Char) and typemin(Char) are the largest and smallest Char under isless.",
    source := "base/char.jl:241-242; typemax/typemin docstrings", status := .proven,
    prop := ``CharTypeExtrema, thm := some ``charTypeExtrema },
  { id := "intfuncscov-char-display", juliaFile := "base/char.jl",
    juliaFns := ["print", "show_invalid", "show", "show(::MIME\"text/plain\")"],
    statement := "Char print preserves the result of write and returns nothing; show_invalid escapes stored bytes, show quotes printable characters, and plain display reports malformed, overlong, and codepoint state.",
    source := "base/char.jl:302-392", status := .todo,
    prop := ``CharDisplayBehavior },
  { id := "char-unsafe-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["unsafe_codepoint(::Char)", "codepoint(::Char)"],
    statement := "For every non-malformed Char, unsafe_codepoint(c) equals codepoint(c).",
    source := "base/char.jl:173-181", status := .proven,
    prop := ``UnsafeCodepointMatches, thm := some ``unsafeCodepointMatches },
  { id := "char-overlong-decode", juliaFile := "base/char.jl",
    juliaFns := ["decode_overlong(::AbstractChar)", "codepoint(::Char)", "isoverlong(::Char)"],
    statement := "Whenever isoverlong(c) is true, decode_overlong(c) returns the codepoint of the UTF-8 sequence c stores.",
    source := "base/char.jl:194-206", status := .refuted,
    prop := ``DecodeOverlongCodepoint, thm := some ``refute_overlong_decode,
    issue := "none found (JuliaLang/julia issues and PRs searched for: ismalformed; isoverlong; decode_overlong; \"malformed Char codepoint\"; \"Char arithmetic malformed\"; \"overlong char\"). Related, not duplicates: PR #55152 (codepoint for overlong chars), PR #25559 (overlong !isvalid), PR #54393 (hascodepoint, closed), PR #61625 (nothrow effects on Char predicates), issue #25072",
    notes := "Bug C (low priority): a lone 0xc0 lead byte is classified overlong (char.jl:119-124). Covered by char-overlong-encoding. For reinterpret(Char, 0xc0000000), isoverlong is true but decode_overlong throws InvalidCharError on nightly. Nightly-only regression: 1.13.2 returns 0x00000000." },
  { id := "char-overlong-encoding", juliaFile := "base/char.jl",
    juliaFns := ["is_overlong_enc(::UInt32)", "isoverlong(::Char)"],
    statement := "For every Char, isoverlong is true exactly when it stores one UTF-8 sequence longer than the shortest one for its value.",
    source := "base/char.jl:16-22,148-152", status := .refuted,
    prop := ``IsoverlongExactlyOverlong, thm := some ``refute_overlong_encoding,
    issue := "none found (JuliaLang/julia issues and PRs searched for: ismalformed; isoverlong; decode_overlong; \"malformed Char codepoint\"; \"Char arithmetic malformed\"; \"overlong char\"). Related, not duplicates: PR #55152 (codepoint for overlong chars), PR #25559 (overlong !isvalid), PR #54393 (hascodepoint, closed), PR #61625 (nothrow effects on Char predicates), issue #25072",
    notes := "Bug C (low priority): a lone 0xc0 lead byte is classified overlong (char.jl:119-124). Primary entry. Base.isoverlong(reinterpret(Char, 0xc0000000)) is true although the Char stores a single byte, not an overlong sequence (it is also malformed). Reproduced on 1.13.2 and nightly." },
  { id := "char-abstract-comparisons", juliaFile := "base/char.jl",
    juliaFns := ["isless(::AbstractChar, ::AbstractChar)", "==(::AbstractChar, ::AbstractChar)"],
    statement := "Fallback AbstractChar comparisons agree with comparisons of the corresponding Char conversions.",
    source := "base/char.jl:268-270", status := .proven,
    prop := ``CharAbstractComparison, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.CharAbstractComparisons_proven },
  { id := "char-integer-conversions", juliaFile := "base/char.jl",
    juliaFns := ["(::Type{T})(::Number) where T<:AbstractChar", "AbstractChar(::Number)",
      "Char(::UInt32)", "Char(::Union{Int8,UInt8})", "convert(::Type{AbstractChar}, ::Number)",
      "convert(::Type{T}, ::Number) where T<:AbstractChar",
      "(::Type{T})(::AbstractChar) where T<:Union{Number,AbstractChar}"],
    statement := "With Julia's dispatch, Char(x), AbstractChar(x), convert(AbstractChar, x) and convert(Char, x) turn every number equal to an integer n with 0 <= n < 0x200000 (every BitInteger type, Bool, IEEE floats, other Numbers through their UInt32 conversion) into the standard UTF-8 encoding of n and throw for every other number; Char of another AbstractChar encodes its UInt32 codepoint.",
    source := "base/char.jl:9-10,16-18,39-56,211-234", status := .proven,
    prop := ``NumberToChar, thm := some ``numberToChar },
  { id := "char-numeric-from-char", juliaFile := "base/char.jl",
    juliaFns := ["(::Type{T})(::AbstractChar) where T<:Union{Number,AbstractChar}",
      "(::Type{T})(::AbstractChar) where T<:Union{Int32,Int64}",
      "convert(::Type{T}, ::AbstractChar) where T<:Number"],
    statement := "Converting a Char to a number gives its codepoint: exactly for Int32/Int64 and IEEE floats, exactly or InexactError for the other integer types served by char.jl:56, and through UInt32(c) for convert(UInt32, c); a malformed Char throws.",
    source := "base/char.jl:9-10,26-28,46-48,56-57,80-92,235", status := .refuted,
    prop := ``NumericFromChar, thm := some ``refute_numeric_from_char,
    issue := "none found (JuliaLang/julia issues and PRs searched for: ismalformed; isoverlong; decode_overlong; \"malformed Char codepoint\"; \"Char arithmetic malformed\"; \"overlong char\"). Related, not duplicates: PR #55152 (codepoint for overlong chars), PR #25559 (overlong !isvalid), PR #54393 (hascodepoint, closed), PR #61625 (nothrow effects on Char predicates), issue #25072",
    notes := "Bug A, root cause: an ASCII lead byte with trailing junk skips the malformed check (char.jl:161, 225, 279, 289). Covered by missingchar-codepoint-malformed. Int32(reinterpret(Char, 0x41c00000)) == 65 and Int(c) == 65 for a malformed Char. Reproduced on 1.13.2 and nightly." },
  { id := "char-smallinteger-conversions", juliaFile := "base/char.jl",
    juliaFns := ["(T::Union{Type{Int8},Type{UInt8}})(c::Char)", "Char(b::Union{Int8,UInt8})"],
    statement := "Char(b) for Int8/UInt8 b is the standard encoding of b when b >= 0 and throws when b < 0; Int8(c)/UInt8(c) return the codepoint when it fits, and throw when it does not or when c is malformed.",
    source := "base/char.jl:9-10,39-51,80-92,223-231", status := .refuted,
    prop := ``SmallIntegerConversions, thm := some ``refute_smallinteger,
    issue := "none found (JuliaLang/julia issues and PRs searched for: ismalformed; isoverlong; decode_overlong; \"malformed Char codepoint\"; \"Char arithmetic malformed\"; \"overlong char\"). Related, not duplicates: PR #55152 (codepoint for overlong chars), PR #25559 (overlong !isvalid), PR #54393 (hascodepoint, closed), PR #61625 (nothrow effects on Char predicates), issue #25072",
    notes := "Bug A, root cause: an ASCII lead byte with trailing junk skips the malformed check (char.jl:161, 225, 279, 289). Covered by missingchar-codepoint-malformed. UInt8(reinterpret(Char, 0x41c00000)) == 0x41 (i >= 0 fast path, char.jl:225) for a malformed Char. Reproduced on 1.13.2 and nightly." },
  { id := "char-remainder-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["rem(::AbstractChar, ::Type{<:Number})"],
    statement := "rem(c, T) for every integer type T is the codepoint of c reduced to T; a malformed Char throws.",
    source := "base/char.jl:80-92,239", status := .refuted,
    prop := ``RemainderCodepoint, thm := some ``refute_remainder,
    issue := "none found (JuliaLang/julia issues and PRs searched for: ismalformed; isoverlong; decode_overlong; \"malformed Char codepoint\"; \"Char arithmetic malformed\"; \"overlong char\"). Related, not duplicates: PR #55152 (codepoint for overlong chars), PR #25559 (overlong !isvalid), PR #54393 (hascodepoint, closed), PR #61625 (nothrow effects on Char predicates), issue #25072",
    notes := "Bug A, root cause: an ASCII lead byte with trailing junk skips the malformed check (char.jl:161, 225, 279, 289). Covered by missingchar-codepoint-malformed. reinterpret(Char, 0x41c00000) % UInt8 == 0x41 for a malformed Char. Reproduced on 1.13.2 and nightly." },
  { id := "char-difference-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["-%(::AbstractChar, ::AbstractChar)", "-(::AbstractChar, ::AbstractChar)"],
    statement := "For two Chars, c - d and c -% d return the Int difference of their codepoints; a malformed operand throws.",
    source := "base/char.jl:9-12,80-92,274-275", status := .refuted,
    prop := ``CharDifferenceCodepoint, thm := some ``refute_difference,
    issue := "none found (JuliaLang/julia issues and PRs searched for: ismalformed; isoverlong; decode_overlong; \"malformed Char codepoint\"; \"Char arithmetic malformed\"; \"overlong char\"). Related, not duplicates: PR #55152 (codepoint for overlong chars), PR #25559 (overlong !isvalid), PR #54393 (hascodepoint, closed), PR #61625 (nothrow effects on Char predicates), issue #25072",
    notes := "Bug A, root cause: an ASCII lead byte with trailing junk skips the malformed check (char.jl:161, 225, 279, 289). Covered by missingchar-codepoint-malformed. reinterpret(Char, 0x41c00000) - 'A' == 0 for a malformed Char. Reproduced on 1.13.2 and nightly." },
  { id := "char-hash-equality", juliaFile := "base/char.jl",
    juliaFns := ["hash(::Char, ::UInt)", "hash(::AbstractChar, ::UInt)", "==(::Char, ::Char)"],
    statement := "Equal Char values have equal hashes for every seed, including through the AbstractChar fallback.",
    source := "base/char.jl:263,265-271", status := .proven,
    prop := ``CharHashRespectsEquality, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.CharHashEquality_proven },
  { id := "char-show-invalid-bytes", juliaFile := "base/char.jl",
    juliaFns := ["show_invalid(::IO, ::Char)"],
    statement := "show_invalid writes the Char as a quoted sequence of lowercase \\xHH escapes, one per stored byte, and nothing else.",
    source := "base/char.jl:46-48,308-331", status := .proven,
    prop := ``ShowInvalidEscapesStoredBytes, thm := some ``showInvalidEscapesStoredBytes },
  { id := "char-show-control-escapes", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::AbstractChar)"],
    statement := "show uses Julia's short escapes for NUL, ASCII controls, apostrophe, and backslash.",
    source := "base/char.jl:336-353", status := .proven,
    prop := ``ShowControlEscapes, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.CharShowControlEscapes_proven },
  { id := "char-show-printable", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::AbstractChar)", "print(::IO, ::AbstractChar)"],
    statement := "show surrounds printable, well-formed, non-overlong characters with single quotes and prints the character between them.",
    source := "base/char.jl:354-370", status := .proven,
    prop := ``ShowPrintableChars, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.CharShowPrintable_proven },
  { id := "char-show-plain-compact", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::MIME\"text/plain\", ::AbstractChar)"],
    statement := "When the IO context is compact, plain-text show emits only the ordinary character display.",
    source := "base/char.jl:372-392", status := .todo,
    prop := ``PlainDisplayCompact },
  { id := "char-abstract-print", juliaFile := "base/char.jl",
    juliaFns := ["print(::IO, ::AbstractChar)"],
    statement := "The AbstractChar print fallback converts to Char and prints that Char.",
    source := "base/char.jl:302-306", status := .proven,
    prop := ``AbstractCharPrintUsesChar, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.CharAbstractPrint_proven },
  { id := "char-show-plain-state", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::MIME\"text/plain\", ::AbstractChar)"],
    statement := "Non-compact plain-text display reports malformed UTF-8, overlong encoding, or the decoded Unicode codepoint.",
    source := "base/char.jl:372-392", status := .proven,
    prop := ``PlainDisplayReportsState, thm := some ``JuliaLean.ChatGPT.Batch4.Group14.CharShowPlainState_proven },
  { id := "char-show-plain-category", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::MIME\"text/plain\", ::AbstractChar)"],
    statement := "For non-compact plain-text display, the output ends with the character's Unicode category abbreviation and description.",
    source := "base/char.jl:372-392", status := .todo,
    prop := ``PlainDisplayReportsCategory, notes := "Frozen assumptions constrain initial compactness and original-character categories, while display uses post-show compactness and reconstructed categories." },
]
end JuliaLean.Proofs.base.char

namespace JuliaLean.ChatGPT.Batch8.Group3
open JuliaLean JuliaLean.base.char JuliaLean.Proofs.base.char

/-- Plain display propagates failure of the ordinary character display. -/
theorem charPlainShowFailure {C IO N : Type} (ops : CharPlainShowOps C IO N)
    (io : IO) (c : C) (e : CharError)
    (hshow : ops.showValue io c = .error e) :
    show_MIMETextPlain ops io c = .error e := by
  simp only [show_MIMETextPlain, hshow, bind, Except.bind]

/-- Compactness is queried on the state returned by ordinary character display. -/
theorem charPlainCompactAfterShow {C IO N : Type} (ops : CharPlainShowOps C IO N)
    (io shown : IO) (c : C)
    (hshow : ops.showValue io c = .ok (shown, ()))
    (hcompact : ops.compact shown = .ok true) :
    show_MIMETextPlain ops io c = .ok (shown, ()) := by
  simp only [show_MIMETextPlain, hshow, hcompact, bind, Except.bind,
    pure, Except.pure, ite_true]

/-- A stability law transfers the frozen statement's initial compactness assumption. -/
theorem charPlainCompactWithStability {C IO N : Type} (ops : CharPlainShowOps C IO N)
    (io : IO) (c : C)
    (hstable : ∀ shown, ops.showValue io c = .ok (shown, ()) →
      ops.compact shown = ops.compact io)
    (hcompact : ops.compact io = .ok true) :
    show_MIMETextPlain ops io c = (do
      let (out, _) ← ops.showValue io c
      pure (out, ())) := by
  cases hshow : ops.showValue io c with
  | error e =>
      simp only [show_MIMETextPlain, hshow, bind, Except.bind]
  | ok result =>
      rcases result with ⟨shown, unitValue⟩
      cases unitValue
      have hc : ops.compact shown = .ok true := (hstable shown hshow).trans hcompact
      simp only [show_MIMETextPlain, hshow, hc, bind, Except.bind,
        pure, Except.pure, ite_true]

/-- Failure of the post-display compact query is propagated directly. -/
theorem charPlainCompactFailure {C IO N : Type} (ops : CharPlainShowOps C IO N)
    (io shown : IO) (c : C) (e : CharError)
    (hshow : ops.showValue io c = .ok (shown, ()))
    (hcompact : ops.compact shown = .error e) :
    show_MIMETextPlain ops io c = .error e := by
  simp only [show_MIMETextPlain, hshow, hcompact, bind, Except.bind]

/-- The complete malformed branch, including the final category event. -/
theorem charPlainMalformedTrace
    (ops : CharPlainShowOps JChar (List CharOutput) JChar)
    (io shown : List CharOutput) (c : JChar) (abbreviation description : String)
    (hshow : ops.showValue io c = .ok (shown, ()))
    (hcompact : ops.compact shown = .ok false)
    (hmalformed : ops.isMalformed c = true)
    (hprint : ops.printStrings = printStringsTrace)
    (habbreviation : ops.categoryAbbrev c = .ok abbreviation)
    (hdescription : ops.categoryString c = .ok description) :
    show_MIMETextPlain ops io c =
      .ok ((shown ++ [.text [": Malformed UTF-8"]]) ++
        [.text [" (category ", abbreviation, ": ", description, ")"]], ()) := by
  simp only [show_MIMETextPlain, hshow, hcompact, hmalformed, hprint,
    habbreviation, hdescription, printStringsTrace, bind, Except.bind,
    pure, Except.pure, Bool.not_true, Bool.false_eq_true, ite_false]

/-- The ordinary branch records the original character's codepoint and category. -/
theorem charPlainOrdinaryTrace
    (ops : CharPlainShowOps JChar (List CharOutput) JChar)
    (io shown : List CharOutput) (c u : JChar)
    (padded abbreviation description : String)
    (hshow : ops.showValue io c = .ok (shown, ()))
    (hcompact : ops.compact shown = .ok false)
    (hmalformed : ops.isMalformed c = false)
    (hoverlong : ops.isOverlong c = false)
    (hcodepoint : ops.codepoint c = .ok u)
    (hpadded : ops.stringBase16Pad4 u = .ok padded)
    (hprint : ops.printStrings = printStringsTrace)
    (habbreviation : ops.categoryAbbrev c = .ok abbreviation)
    (hdescription : ops.categoryString c = .ok description) :
    show_MIMETextPlain ops io c =
      .ok (((shown ++ [.text [": "]]) ++
        [.text [if ops.isAscii c then "ASCII/" else "", "Unicode U+", ops.uppercase padded]]) ++
        [.text [" (category ", abbreviation, ": ", description, ")"]], ()) := by
  simp only [show_MIMETextPlain, hshow, hcompact, hmalformed, hoverlong,
    hcodepoint, hpadded, hprint, habbreviation, hdescription, printStringsTrace,
    bind, Except.bind, pure, Except.pure, Bool.not_false, Bool.false_eq_true,
    ite_true, ite_false]

/-- The overlong branch uses the reconstructed character for ASCII and category queries. -/
theorem charPlainOverlongTrace
    (ops : CharPlainShowOps JChar (List CharOutput) JChar)
    (io shown : List CharOutput) (c u converted : JChar)
    (padded abbreviation description : String)
    (hshow : ops.showValue io c = .ok (shown, ()))
    (hcompact : ops.compact shown = .ok false)
    (hmalformed : ops.isMalformed c = false)
    (hoverlong : ops.isOverlong c = true)
    (hdecode : ops.decodeOverlong c = .ok u)
    (hconstruct : ops.constructFromNumber u = .ok converted)
    (hpadded : ops.stringBase16Pad4 u = .ok padded)
    (hprint : ops.printStrings = printStringsTrace)
    (habbreviation : ops.categoryAbbrev converted = .ok abbreviation)
    (hdescription : ops.categoryString converted = .ok description) :
    show_MIMETextPlain ops io c =
      .ok ((((shown ++ [.text [": "]]) ++ [.text ["[overlong] "]]) ++
        [.text [if ops.isAscii converted then "ASCII/" else "", "Unicode U+", ops.uppercase padded]]) ++
        [.text [" (category ", abbreviation, ": ", description, ")"]], ()) := by
  simp only [show_MIMETextPlain, hshow, hcompact, hmalformed, hoverlong,
    hdecode, hconstruct, hpadded, hprint, habbreviation, hdescription,
    printStringsTrace, bind, Except.bind, pure, Except.pure,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false]

/-- The raw-literal parser assumption suffices on the printable, non-escape branch. -/
theorem charPrintableParserRoundtrip
    (isPrint : JChar → Bool) (parse : List CharOutput → Option JChar)
    (hparse : ∀ c, parse [.bytes [0x27], .character c, .bytes [0x27]] = some c)
    (c : JChar) (trace : List CharOutput)
    (hcontrol : controlEscapeSpec c = none) (hprint : isPrint c = true)
    (hmalformed : ismalformed_Char charBitOps c = false)
    (hoverlong : isoverlong_Char c = false)
    (hshow : show_AbstractChar (charShowOps isPrint) [] c = .ok (trace, ())) :
    parse trace = some c := by
  have hquoted := JuliaLean.ChatGPT.Batch4.Group14.CharShowPrintable_proven
    isPrint c hcontrol hprint hmalformed hoverlong
  rw [hquoted] at hshow
  cases hshow
  exact hparse c

/-- An additional short-escape parser law suffices on the control-character branch. -/
theorem charControlParserRoundtrip
    (isPrint : JChar → Bool) (parse : List CharOutput → Option JChar)
    (hparse : ∀ c escape, controlEscapeSpec c = some escape →
      parse [.bytes [0x27, 0x5c, escape, 0x27]] = some c)
    (c : JChar) (escape : UInt8) (trace : List CharOutput)
    (hcontrol : controlEscapeSpec c = some escape)
    (hshow : show_AbstractChar (charShowOps isPrint) [] c = .ok (trace, ())) :
    parse trace = some c := by
  have hescaped := JuliaLean.ChatGPT.Batch4.Group14.CharShowControlEscapes_proven
    isPrint c escape hcontrol
  rw [hescaped] at hshow
  cases hshow
  exact hparse c escape hcontrol


/-- The frozen category conclusion follows from explicit state and reconstruction laws. -/
theorem charPlainCategoryWithContracts
    (ops : CharPlainShowOps JChar (List CharOutput) JChar)
    (c : JChar) (trace : List CharOutput) (abbreviation description : String)
    (hcompact : ops.compact [] = .ok false)
    (habbreviation : ops.categoryAbbrev c = .ok abbreviation)
    (hdescription : ops.categoryString c = .ok description)
    (hprint : ops.printStrings = printStringsTrace)
    (hstable : ∀ shown, ops.showValue [] c = .ok (shown, ()) →
      ops.compact shown = ops.compact [])
    (hconverted : ∀ u converted,
      ops.decodeOverlong c = .ok u → ops.constructFromNumber u = .ok converted →
      ops.categoryAbbrev converted = .ok abbreviation ∧
      ops.categoryString converted = .ok description)
    (hresult : show_MIMETextPlain ops [] c = .ok (trace, ())) :
    trace.getLast? = some (.text [" (category ", abbreviation, ": ", description, ")"]) := by
  cases hshow : ops.showValue [] c with
  | error e =>
      rw [charPlainShowFailure ops [] c e hshow] at hresult
      cases hresult
  | ok shownResult =>
      rcases shownResult with ⟨shown, unitValue⟩
      cases unitValue
      have hc : ops.compact shown = .ok false := (hstable shown hshow).trans hcompact
      cases hm : ops.isMalformed c with
      | true =>
          rw [charPlainMalformedTrace ops [] shown c abbreviation description
            hshow hc hm hprint habbreviation hdescription] at hresult
          cases hresult
          exact List.getLast?_concat
      | false =>
          cases ho : ops.isOverlong c with
          | false =>
              cases hcp : ops.codepoint c with
              | error e =>
                  simp only [show_MIMETextPlain, hshow, hc, hm, ho, hcp, hprint,
                    printStringsTrace, bind, Except.bind, pure, Except.pure,
                    Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hresult
                  cases hresult
              | ok u =>
                  cases hp : ops.stringBase16Pad4 u with
                  | error e =>
                      simp only [show_MIMETextPlain, hshow, hc, hm, ho, hcp, hp, hprint,
                        printStringsTrace, bind, Except.bind, pure, Except.pure,
                        Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hresult
                      cases hresult
                  | ok padded =>
                      rw [charPlainOrdinaryTrace ops [] shown c u padded abbreviation description
                        hshow hc hm ho hcp hp hprint habbreviation hdescription] at hresult
                      cases hresult
                      exact List.getLast?_concat
          | true =>
              cases hd : ops.decodeOverlong c with
              | error e =>
                  simp only [show_MIMETextPlain, hshow, hc, hm, ho, hd, hprint,
                    printStringsTrace, bind, Except.bind, pure, Except.pure,
                    Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hresult
                  cases hresult
              | ok u =>
                  cases hk : ops.constructFromNumber u with
                  | error e =>
                      simp only [show_MIMETextPlain, hshow, hc, hm, ho, hd, hk, hprint,
                        printStringsTrace, bind, Except.bind, pure, Except.pure,
                        Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hresult
                      cases hresult
                  | ok converted =>
                      cases hp : ops.stringBase16Pad4 u with
                      | error e =>
                          simp only [show_MIMETextPlain, hshow, hc, hm, ho, hd, hk, hp, hprint,
                            printStringsTrace, bind, Except.bind, pure, Except.pure,
                            Bool.not_false, Bool.false_eq_true, ite_false, ite_true] at hresult
                          cases hresult
                      | ok padded =>
                          obtain ⟨ha, hs⟩ := hconverted u converted hd hk
                          rw [charPlainOverlongTrace ops [] shown c u converted padded
                            abbreviation description hshow hc hm ho hd hk hp hprint ha hs] at hresult
                          cases hresult
                          exact List.getLast?_concat


/-- The independent byte formula agrees with the existing finite hexadecimal table. -/
theorem charHexDigitSpec (n : Nat) :
    UInt8.ofNat (hexDigitByte n) = specHexDigit n := by
  by_cases hn : n < 10
  · simp only [hexDigitByte, specHexDigit, ite_eq_left hn]
  · simp only [hexDigitByte, specHexDigit, ite_eq_right hn]
    congr 1
    omega

/-- The invalid-character loop realizes the frozen event specification for every fuel. -/
theorem charInvalidLoopTrace (fuel : Nat) (io : List CharOutput) (u : JChar) :
    showInvalidLoop writeBytesTrace fuel io u =
      .ok (io ++ showInvalidTraceLoopSpec fuel u) := by
  induction fuel generalizing io u with
  | zero =>
      simp only [showInvalidLoop, showInvalidTraceLoopSpec, List.append_nil]
  | succ fuel ih =>
      have highBound : ((ushr32 u 28) &&& 0xf).toNat < 16 := by
        rw [hi_nibble]
        have hbyte : u.toNat / 16777216 % 256 < 256 := Nat.mod_lt _ (by decide)
        omega
      have lowBound : ((ushr32 u 24) &&& 0xf).toNat < 16 := by
        rw [lo_nibble]
        exact Nat.mod_lt _ (by decide)
      have hhigh := hexCharAt_succ ((ushr32 u 28) &&& 0xf).toNat highBound
      have hlow := hexCharAt_succ ((ushr32 u 24) &&& 0xf).toNat lowBound
      simp only [showInvalidLoop, showInvalidTraceLoopSpec, hhigh, hlow,
        charHexDigitSpec, writeBytesTrace, bind, Except.bind, pure, Except.pure]
      cases hz : shl32 u 8 == 0 with
      | false =>
          simp only [Bool.false_eq_true, ite_false, ih, List.append_assoc]
      | true =>
          simp only [ite_true, List.append_nil]

/-- The invalid-byte component of the display aggregate holds without added contracts. -/
theorem charDisplayInvalidEscapes : JuliaLean.Proofs.base.char.ShowInvalidEscapes := by
  intro c
  simp only [show_invalid_Char, writeBytesTrace, bind, Except.bind,
    charInvalidLoopTrace, showInvalidTraceSpec, List.nil_append]
  rfl

end JuliaLean.ChatGPT.Batch8.Group3

namespace JuliaLean.ChatGPT.Batch8.Group2

open JuliaLean JuliaLean.base.char

/-- The three source branches determine the character passed to category lookup. -/
def PlainCategoryArgument {C N : Type}
    (ops : CharPlainShowOps C (List CharOutput) N) (original selected : C) : Prop :=
  (ops.isMalformed original = true ∧ selected = original) ∨
  (ops.isMalformed original = false ∧ ops.isOverlong original = false ∧
    selected = original) ∨
  (ops.isMalformed original = false ∧ ops.isOverlong original = true ∧
    ∃ value, ops.decodeOverlong original = .ok value ∧
      ops.constructFromNumber value = .ok selected)

/-- A successful display, known non-compact at the actual post-show state,
finishes with a category lookup on exactly the character selected by the source.
No success assumption for decoding, reconstruction, formatting, or category
lookup is needed: success of the entire call supplies those facts. -/
theorem plainDisplayCategoryExecution {C N : Type}
    (ops : CharPlainShowOps C (List CharOutput) N)
    (initial shown trace : List CharOutput) (c : C)
    (hshow : ops.showValue initial c = .ok (shown, ()))
    (hcompact : ops.compact shown = .ok false)
    (hprint : ops.printStrings = printStringsTrace)
    (hsuccess : show_MIMETextPlain ops initial c = .ok (trace, ())) :
    ∃ selected abbreviation description preceding,
      PlainCategoryArgument ops c selected ∧
      ops.categoryAbbrev selected = .ok abbreviation ∧
      ops.categoryString selected = .ok description ∧
      trace = preceding ++ [.text [" (category ", abbreviation, ": ", description, ")"]] := by
  cases hm : ops.isMalformed c with
  | true =>
    cases ha : ops.categoryAbbrev c with
    | error e =>
      simp only [show_MIMETextPlain, hshow, hcompact, hm, hprint, ha,
        printStringsTrace, bind, Except.bind, pure, Except.pure,
        Bool.not, Bool.false_eq_true, ite_false] at hsuccess
      cases hsuccess
    | ok abbreviation =>
      cases hd : ops.categoryString c with
      | error e =>
        simp only [show_MIMETextPlain, hshow, hcompact, hm, hprint, ha, hd,
          printStringsTrace, bind, Except.bind, pure, Except.pure,
          Bool.not, Bool.false_eq_true, ite_false] at hsuccess
        cases hsuccess
      | ok description =>
        refine ⟨c, abbreviation, description, shown ++ [.text [": Malformed UTF-8"]],
          Or.inl ⟨hm, rfl⟩, ha, hd, ?_⟩
        simpa only [show_MIMETextPlain, hshow, hcompact, hm, hprint, ha, hd,
          printStringsTrace, bind, Except.bind, pure, Except.pure,
          Bool.not, Bool.false_eq_true, ite_false,
          Except.ok.injEq, Prod.mk.injEq, and_true] using hsuccess.symm
  | false =>
    cases ho : ops.isOverlong c with
    | false =>
      cases hu : ops.codepoint c with
      | error e =>
        simp only [show_MIMETextPlain, hshow, hcompact, hm, ho, hprint, hu,
          printStringsTrace, bind, Except.bind, pure, Except.pure,
          Bool.not, Bool.false_eq_true, ite_true, ite_false] at hsuccess
        cases hsuccess
      | ok value =>
        cases hf : ops.stringBase16Pad4 value with
        | error e =>
          simp only [show_MIMETextPlain, hshow, hcompact, hm, ho, hprint, hu, hf,
            printStringsTrace, bind, Except.bind, pure, Except.pure,
            Bool.not, Bool.false_eq_true, ite_true, ite_false] at hsuccess
          cases hsuccess
        | ok padded =>
          cases ha : ops.categoryAbbrev c with
          | error e =>
            simp only [show_MIMETextPlain, hshow, hcompact, hm, ho, hprint, hu, hf, ha,
              printStringsTrace, bind, Except.bind, pure, Except.pure,
              Bool.not, Bool.false_eq_true, ite_true, ite_false] at hsuccess
            cases hsuccess
          | ok abbreviation =>
            cases hd : ops.categoryString c with
            | error e =>
              simp only [show_MIMETextPlain, hshow, hcompact, hm, ho, hprint, hu, hf, ha, hd,
                printStringsTrace, bind, Except.bind, pure, Except.pure,
                Bool.not, Bool.false_eq_true, ite_true, ite_false] at hsuccess
              cases hsuccess
            | ok description =>
              refine ⟨c, abbreviation, description,
                (shown ++ [.text [": "]]) ++
                  [.text [if ops.isAscii c then "ASCII/" else "", "Unicode U+", ops.uppercase padded]],
                Or.inr (Or.inl ⟨hm, ho, rfl⟩), ha, hd, ?_⟩
              simpa only [show_MIMETextPlain, hshow, hcompact, hm, ho, hprint, hu, hf, ha, hd,
                printStringsTrace, bind, Except.bind, pure, Except.pure,
                Bool.not, Bool.false_eq_true, ite_true, ite_false,
                Except.ok.injEq, Prod.mk.injEq, and_true] using hsuccess.symm
    | true =>
      cases hu : ops.decodeOverlong c with
      | error e =>
        simp only [show_MIMETextPlain, hshow, hcompact, hm, ho, hprint, hu,
          printStringsTrace, bind, Except.bind, pure, Except.pure,
          Bool.not, Bool.false_eq_true, ite_true, ite_false] at hsuccess
        cases hsuccess
      | ok value =>
        cases hr : ops.constructFromNumber value with
        | error e =>
          simp only [show_MIMETextPlain, hshow, hcompact, hm, ho, hprint, hu, hr,
            printStringsTrace, bind, Except.bind, pure, Except.pure,
            Bool.not, Bool.false_eq_true, ite_true, ite_false] at hsuccess
          cases hsuccess
        | ok selected =>
          cases hf : ops.stringBase16Pad4 value with
          | error e =>
            simp only [show_MIMETextPlain, hshow, hcompact, hm, ho, hprint, hu, hr, hf,
              printStringsTrace, bind, Except.bind, pure, Except.pure,
              Bool.not, Bool.false_eq_true, ite_true, ite_false] at hsuccess
            cases hsuccess
          | ok padded =>
            cases ha : ops.categoryAbbrev selected with
            | error e =>
              simp only [show_MIMETextPlain, hshow, hcompact, hm, ho, hprint, hu, hr, hf, ha,
                printStringsTrace, bind, Except.bind, pure, Except.pure,
                Bool.not, Bool.false_eq_true, ite_true, ite_false] at hsuccess
              cases hsuccess
            | ok abbreviation =>
              cases hd : ops.categoryString selected with
              | error e =>
                simp only [show_MIMETextPlain, hshow, hcompact, hm, ho, hprint, hu, hr, hf, ha, hd,
                  printStringsTrace, bind, Except.bind, pure, Except.pure,
                  Bool.not, Bool.false_eq_true, ite_true, ite_false] at hsuccess
                cases hsuccess
              | ok description =>
                refine ⟨selected, abbreviation, description,
                  ((shown ++ [.text [": "]]) ++ [.text ["[overlong] "]]) ++
                    [.text [if ops.isAscii selected then "ASCII/" else "", "Unicode U+", ops.uppercase padded]],
                  Or.inr (Or.inr ⟨hm, ho, value, hu, hr⟩), ha, hd, ?_⟩
                simpa only [show_MIMETextPlain, hshow, hcompact, hm, ho, hprint, hu, hr, hf, ha, hd,
                  printStringsTrace, bind, Except.bind, pure, Except.pure,
                  Bool.not, Bool.false_eq_true, ite_true, ite_false,
                  Except.ok.injEq, Prod.mk.injEq, and_true] using hsuccess.symm

/-- The final event from the preceding execution theorem is the category event. -/
theorem plainDisplayCategoryLast {C N : Type}
    (ops : CharPlainShowOps C (List CharOutput) N)
    (initial shown trace : List CharOutput) (c : C)
    (hshow : ops.showValue initial c = .ok (shown, ()))
    (hcompact : ops.compact shown = .ok false)
    (hprint : ops.printStrings = printStringsTrace)
    (hsuccess : show_MIMETextPlain ops initial c = .ok (trace, ())) :
    ∃ selected abbreviation description,
      PlainCategoryArgument ops c selected ∧
      ops.categoryAbbrev selected = .ok abbreviation ∧
      ops.categoryString selected = .ok description ∧
      trace.getLast? = some (.text [" (category ", abbreviation, ": ", description, ")"]) := by
  obtain ⟨selected, abbreviation, description, preceding, harg, ha, hd, htrace⟩ :=
    plainDisplayCategoryExecution ops initial shown trace c hshow hcompact hprint hsuccess
  refine ⟨selected, abbreviation, description, harg, ha, hd, ?_⟩
  rw [htrace]
  exact List.getLast?_concat


/-- If all category arguments reachable in the source branches have the expected
category, the final event reports that expected category. This separates the
verified display control flow from the external Unicode callback contracts. -/
theorem plainDisplayExpectedCategory {C N : Type}
    (ops : CharPlainShowOps C (List CharOutput) N)
    (initial shown trace : List CharOutput) (c : C) (abbreviation description : String)
    (hshow : ops.showValue initial c = .ok (shown, ()))
    (hcompact : ops.compact shown = .ok false)
    (hprint : ops.printStrings = printStringsTrace)
    (hcategories : ∀ selected, PlainCategoryArgument ops c selected →
      ops.categoryAbbrev selected = .ok abbreviation ∧
      ops.categoryString selected = .ok description)
    (hsuccess : show_MIMETextPlain ops initial c = .ok (trace, ())) :
    trace.getLast? = some (.text [" (category ", abbreviation, ": ", description, ")"]) := by
  obtain ⟨selected, foundAbbrev, foundDescription, harg, ha, hd, hlast⟩ :=
    plainDisplayCategoryLast ops initial shown trace c hshow hcompact hprint hsuccess
  obtain ⟨haExpected, hdExpected⟩ := hcategories selected harg
  have hae : foundAbbrev = abbreviation := Except.ok.inj (ha.symm.trans haExpected)
  have hde : foundDescription = description := Except.ok.inj (hd.symm.trans hdExpected)
  cases hae
  cases hde
  exact hlast

end JuliaLean.ChatGPT.Batch8.Group2

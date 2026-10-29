import JuliaLean.base.char
import JuliaLean.base.int
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
    isless_AbstractChar toChar isless_Char x y = .ok (isless_Char c d) ∧
    eq_AbstractChar toChar eq_Char x y = .ok (eq_Char c d)

/- The codepoint/validity methods in this file distinguish overlong UTF-8 sequences by their encoded byte count. -/
def minimumUtf8Bytes (u : JChar) : Nat :=
  if u ≤ 0x7f then 1 else if u ≤ 0x7ff then 2 else if u ≤ 0xffff then 3 else 4

def CharOverlongEncoding : Prop :=
  ∀ c u, ismalformed_Char charBitOps c = false →
    codepoint_Char charBitOps c = .ok u →
    isoverlong_Char c = decide (rawCharByteCount c > minimumUtf8Bytes u)

/- The Char order and equality preserve every codepoint accepted by the Char constructor. -/
def CharOrderCodepoint : Prop :=
  ∀ (u v c d : JChar), char_UInt32 u = .ok c → char_UInt32 v = .ok d →
    (isless_Char c d = decide (u < v)) ∧ (eq_Char c d = decide (u = v))

/- Addition in either operand order, with wrapping methods, returns the constructible codepoint sum. -/
def CharAddCodepoint : Prop :=
  ∀ u c (n : JInt64), char_UInt32 u = .ok c →
    0 ≤ (u.toNat : Int) + n.val → (u.toNat : Int) + n.val < 0x00200000 →
    let result := char_UInt32 (UInt32.ofNat ((u.toNat : Int) + n.val).toNat)
    addWrap_AbstractChar_Integer charIntegerOps c n = result ∧
    addWrap_Integer_AbstractChar charIntegerOps n c = result ∧
    add_AbstractChar_Integer charIntegerOps c n = result ∧
    add_Integer_AbstractChar charIntegerOps n c = result
def CharSubCodepoint : Prop :=
  ∀ u c (n : JInt64), char_UInt32 u = .ok c →
    0 ≤ (u.toNat : Int) - n.val → (u.toNat : Int) - n.val < 0x00200000 →
    sub_AbstractChar_Integer charIntegerOps c n =
      char_UInt32 (UInt32.ofNat ((u.toNat : Int) - n.val).toNat)


def CharDifferenceExact : Prop :=
  (∀ u v c d, char_UInt32 u = .ok c → char_UInt32 v = .ok d →
    sub_AbstractChar_AbstractChar codepointInt64 sub c d =
      .ok (JInt.lit .i64 ((u.toNat : Int) - v.toNat))) ∧
  (∀ u v c d, char_UInt32 u = .ok c → char_UInt32 v = .ok d →
    subWrap_AbstractChar_AbstractChar codepointInt64 subWrap c d =
      .ok (JInt.lit .i64 ((u.toNat : Int) - v.toNat)))

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
/-! Every scalar collection operation treats an AbstractChar as a one-element, zero-dimensional collection. -/
def CharScalarBehavior : Prop :=
  (∀ {C : Type} (c : C), size_AbstractChar c = ()) ∧
  (∀ {C I : Type} (less : I → I → Bool) (one : I) (c : C) (d : I),
    size_AbstractChar_Dimension less one c d =
      if less d one then .error .boundsError else .ok (JInt.lit .i64 1)) ∧
  (∀ {C : Type} (c : C), ndims_AbstractChar c = JInt.lit .i64 0) ∧
  (∀ {C : Type}, ndims_TypeAbstractChar (C := C) = JInt.lit .i64 0) ∧
  (∀ {C : Type} (c : C), length_AbstractChar c = JInt.lit .i64 1) ∧
  (∀ {C : Type}, iteratorSize_AbstractChar (C := C) = .hasShape 0) ∧
  (∀ {C : Type} (c : C), firstindex_AbstractChar c = JInt.lit .i64 1 ∧
    lastindex_AbstractChar c = JInt.lit .i64 1) ∧
  (∀ {C : Type} (c : C), getindex_AbstractChar c = c ∧
    first_AbstractChar c = c ∧ last_AbstractChar c = c) ∧
  (∀ {C I : Type} (equal : I → I → Bool) (one : I) (c : C) (i : I),
    getindex_AbstractChar_Integer equal one c i =
      if equal i one then .ok c else .error .boundsError) ∧
  (∀ {C I : Type} (equal : I → I → Bool) (one : I) (c : C) (indices : List I),
    getindex_AbstractChar_Vararg equal one c indices =
      if indices.all (fun x => equal x one) then .ok c else .error .boundsError) ∧
  (∀ {C : Type}, eltype_AbstractChar (C := C) = C) ∧
  (∀ {C : Type} (c : C) (done : Bool),
    iterate_AbstractChar c done = if done then none else some (c, true)) ∧
  (∀ {C : Type} (c : C), isempty_AbstractChar c = false) ∧
  (∀ {C : Type} (equal : C → C → Bool) (x y : C),
    in_AbstractChar equal x y = equal x y) ∧
  (∀ {C : Type}, widen_AbstractChar (C := C) = C) ∧
  CharOrderCodepoint ∧ CharAddCodepoint ∧ CharSubCodepoint ∧
  CharDifferenceExact ∧ CharAbstractComparison ∧ CharHashRespectsEquality ∧
  CharAbstractDefaults ∧ CharIntegerConversions ∧ CharSmallIntegerConstruction ∧
  CharRemainderCodepoint ∧ CharOverlongEncoding ∧
  typemin_Char 0 = 0 ∧ typemax_Char 0xffffffff = 0xffffffff

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

/-! ## Registry entries -/

def entries : List JuliaLean.Registry.Entry := [
  { id := "missingchar-codepoint-malformed", juliaFile := "base/char.jl",
    juliaFns := ["codepoint(::Char)", "UInt32(::Char)"],
    statement := "codepoint(c) throws for every malformed Char c.",
    source := "base/char.jl:83-85,141-142", status := .todo,
    prop := ``CodepointThrowsMalformed },
  { id := "missingchar-codepoint-wellformed", juliaFile := "base/char.jl",
    juliaFns := ["codepoint(::Char)", "ismalformed(::Char)"],
    statement := "codepoint(c) succeeds for every non-malformed Char, including overlong encodings.",
    source := "base/char.jl:89-92", status := .todo,
    prop := ``CodepointWellFormed },
  { id := "missingchar-char-codepoint-roundtrip", juliaFile := "base/char.jl",
    juliaFns := ["Char(::UInt32)", "codepoint(::Char)", "ismalformed(::Char)", "isoverlong(::Char)"],
    statement := "Char(u) throws CodePointError exactly for u >= 0x200000; otherwise it is well-formed, not overlong, and codepoint(Char(u)) == u.",
    source := "base/char.jl:39-51,135-140,211-220", status := .todo,
    prop := ``CharCodepointRoundTrip },
  { id := "missingchar-char-order-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["isless(::Char, ::Char)", "==(::Char, ::Char)"],
    statement := "For every pair of constructible Char values, isless and == agree with their codepoint order and equality.",
    source := "base/char.jl:10-12,263-264", status := .todo,
    prop := ``CharOrderCodepoint },
  { id := "missingchar-char-add-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["+(::Char, ::Integer)", "+%(::Char, ::Integer)",
      "+%(::Integer, ::AbstractChar)", "+(::Integer, ::AbstractChar)"],
    statement := "Adding an Int on either side of a constructible Char gives the Char for the summed codepoint whenever that sum is constructible.",
    source := "invariant; base/char.jl:286-300", status := .todo,
    prop := ``CharAddCodepoint },
  { id := "char-sub-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["-(::Char, ::Integer)", "-%(::Char, ::Integer)"],
    statement := "Subtracting an integer from a Char moves backward by that amount in codepoint space whenever the result is constructible.",
    source := "invariant; base/char.jl:276-285,298", status := .todo,
    prop := ``CharSubCodepoint },
  { id := "missingchar-ncodeunits-write", juliaFile := "base/char.jl",
    juliaFns := ["ncodeunits(::Char)", "write(::IO, ::Char)"],
    statement := "ncodeunits(c) is the number of UTF-8 bytes emitted when a Char is written.",
    source := "base/char.jl:60-78", status := .todo,
    prop := ``NcodeunitsWrite },
  { id := "missingchar-show-char-roundtrip", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::AbstractChar)"],
    statement := "For every well-formed, non-overlong Char, the literal repr(c) parses back to c.",
    source := "base/show.jl show contract; base/char.jl:336-370", status := .todo,
    prop := ``ShowCharParses },
  { id := "intfuncscov-char-encoding", juliaFile := "base/char.jl",
    juliaFns := ["AbstractChar", "Char", "codepoint", "ismalformed", "isoverlong",
      "unsafe_codepoint", "decode_overlong", "UInt32", "UInt32_cold", "Char_cold", "convert", "rem"],
    statement := "Char construction, decoding, malformed and overlong checks, unsafe decoding, and numeric conversion preserve the documented codepoint behavior.",
    source := "base/char.jl:54-239", status := .todo,
    prop := ``CharEncodingBehavior },
  { id := "intfuncscov-char-scalar", juliaFile := "base/char.jl",
    juliaFns := ["typemin", "typemax", "size", "ndims", "length", "IteratorSize",
      "firstindex", "lastindex", "getindex", "first", "last", "eltype", "iterate",
      "isempty", "in", "==", "isless", "hash", "widen", "-%", "-", "+%", "+"],
    statement := "AbstractChar has one element, zero dimensions, scalar indexing, and codepoint-based comparison and arithmetic.",
    source := "base/char.jl:241-300", status := .todo,
    prop := ``CharScalarBehavior },
  { id := "intfuncscov-char-display", juliaFile := "base/char.jl",
    juliaFns := ["print", "show_invalid", "show", "show(::MIME\"text/plain\")"],
    statement := "Char print preserves the result of write and returns nothing; show_invalid escapes stored bytes, show quotes printable characters, and plain display reports malformed, overlong, and codepoint state.",
    source := "base/char.jl:302-392", status := .todo,
    prop := ``CharDisplayBehavior },
  { id := "char-unsafe-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["unsafe_codepoint(::AbstractChar)", "unsafe_codepoint(::Char)"],
    statement := "For every non-malformed Char, unsafe_codepoint returns the same UInt32 value as codepoint.",
    source := "base/char.jl:174-192", status := .todo,
    prop := ``UnsafeCodepointAgrees },
  { id := "char-overlong-decode", juliaFile := "base/char.jl",
    juliaFns := ["decode_overlong(::AbstractChar)", "codepoint(::Char)"],
    statement := "decode_overlong(c) returns codepoint(c) for every overlong Char that codepoint can decode.",
    source := "base/char.jl:194-209", status := .todo,
    prop := ``OverlongDecodeCodepoint },
  { id := "char-overlong-encoding", juliaFile := "base/char.jl",
    juliaFns := ["is_overlong_enc(::UInt32)", "isoverlong(::Char)"],
    statement := "For a non-malformed Char, isoverlong is true exactly when its stored UTF-8 sequence uses more bytes than the decoded codepoint requires.",
    source := "base/char.jl:119-124,149-152", status := .todo,
    prop := ``CharOverlongEncoding },
  { id := "char-abstract-comparisons", juliaFile := "base/char.jl",
    juliaFns := ["isless(::AbstractChar, ::AbstractChar)", "==(::AbstractChar, ::AbstractChar)"],
    statement := "Fallback AbstractChar comparisons agree with comparisons of the corresponding Char conversions.",
    source := "base/char.jl:268-270", status := .todo,
    prop := ``CharAbstractComparison },
  { id := "char-integer-conversions", juliaFile := "base/char.jl",
    juliaFns := ["(::Type{T})(::Number) where T<:AbstractChar",
      "(::Type{T})(::AbstractChar) where T<:Union{Number,AbstractChar}",
      "(::Type{T})(::AbstractChar) where T<:Union{Int32,Int64}"],
    statement := "Char constructors convert the numeric input to UInt32 before encoding it, and AbstractChar constructors preserve the decoded codepoint.",
    source := "base/char.jl:54,56-57,211-220", status := .todo,
    prop := ``CharIntegerConversions },
  { id := "char-smallinteger-conversions", juliaFile := "base/char.jl",
    juliaFns := ["(T::Union{Type{Int8},Type{UInt8}})(c::Char)", "Char(b::Union{Int8,UInt8})"],
    statement := "Char construction from Int8 and UInt8 uses the same codepoint as the general UInt32 constructor, with the ASCII fast path preserving its byte.",
    source := "base/char.jl:223-231", status := .todo,
    prop := ``CharSmallIntegerConstruction },
  { id := "char-remainder-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["rem(::AbstractChar, ::Type{<:Number})"],
    statement := "Remainder of an AbstractChar by a numeric type is the remainder of its codepoint by that type.",
    source := "base/char.jl:239", status := .todo,
    prop := ``CharRemainderCodepoint },
  { id := "char-difference-codepoint", juliaFile := "base/char.jl",
    juliaFns := ["-%(::AbstractChar, ::AbstractChar)", "-(::AbstractChar, ::AbstractChar)"],
    statement := "Subtracting AbstractChars returns their Int codepoint difference, with wraparound for -%.",
    source := "base/char.jl:274-275", status := .todo,
    prop := ``CharDifferenceExact },
  { id := "char-hash-equality", juliaFile := "base/char.jl",
    juliaFns := ["hash(::Char, ::UInt)", "hash(::AbstractChar, ::UInt)", "==(::Char, ::Char)"],
    statement := "Equal Char values have equal hashes for every seed, including through the AbstractChar fallback.",
    source := "base/char.jl:263,265-271", status := .todo,
    prop := ``CharHashRespectsEquality },
  { id := "char-show-invalid-bytes", juliaFile := "base/char.jl",
    juliaFns := ["show_invalid(::IO, ::Char)"],
    statement := "show_invalid writes a quoted lowercase hex escape for each stored leading byte.",
    source := "base/char.jl:308-323", status := .todo,
    prop := ``ShowInvalidEscapes },
  { id := "char-show-control-escapes", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::AbstractChar)"],
    statement := "show uses Julia's short escapes for NUL, ASCII controls, apostrophe, and backslash.",
    source := "base/char.jl:336-353", status := .todo,
    prop := ``ShowControlEscapes },
  { id := "char-show-printable", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::AbstractChar)", "print(::IO, ::AbstractChar)"],
    statement := "show surrounds printable, well-formed, non-overlong characters with single quotes and prints the character between them.",
    source := "base/char.jl:354-370", status := .todo,
    prop := ``ShowPrintableChars },
  { id := "char-show-plain-compact", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::MIME\"text/plain\", ::AbstractChar)"],
    statement := "When the IO context is compact, plain-text show emits only the ordinary character display.",
    source := "base/char.jl:372-392", status := .todo,
    prop := ``PlainDisplayCompact },
  { id := "char-abstract-print", juliaFile := "base/char.jl",
    juliaFns := ["print(::IO, ::AbstractChar)"],
    statement := "The AbstractChar print fallback converts to Char and prints that Char.",
    source := "base/char.jl:302-306", status := .todo,
    prop := ``AbstractCharPrintUsesChar },
  { id := "char-show-plain-state", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::MIME\"text/plain\", ::AbstractChar)"],
    statement := "Non-compact plain-text display reports malformed UTF-8, overlong encoding, or the decoded Unicode codepoint.",
    source := "base/char.jl:372-392", status := .todo,
    prop := ``PlainDisplayReportsState },
  { id := "char-show-plain-category", juliaFile := "base/char.jl",
    juliaFns := ["show(::IO, ::MIME\"text/plain\", ::AbstractChar)"],
    statement := "For non-compact plain-text display, the output ends with the character's Unicode category abbreviation and description.",
    source := "base/char.jl:372-392", status := .todo,
    prop := ``PlainDisplayReportsCategory },
]
end JuliaLean.Proofs.base.char

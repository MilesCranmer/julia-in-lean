import JuliaLean.Registry.Types
import JuliaLean.Transcode.Valid
import JuliaLean.base.strings.cstring
import JuliaLean.base.char

namespace JuliaLean.Proofs.base.strings.cstring

open JuliaLean.Registry
open JuliaLean.base.strings.cstring

/-! Statements for the source-mirrored Cstring model. -/
/-! Nothing to promise: Cstring@31: re-tags the same address; no behaviour. -/
/-! Nothing to promise: Cwstring@32: re-tags the same address; no behaviour. -/
/-! Nothing to promise: Ptr{T}@33: re-tags the same address; no behaviour. -/
/-! Nothing to promise: convert@36: re-tags the same address; no behaviour. -/
/-! Nothing to promise: convert@37: re-tags the same address; no behaviour. -/
/-! Nothing to promise: convert@38: re-tags the same address; no behaviour. -/
/-! Nothing to promise: convert@39: re-tags the same address; no behaviour. -/
/-! Nothing to promise: pointer@55: re-tags the same address; no behaviour. -/
/-! Nothing to promise: pointer@56: re-tags the same address; no behaviour. -/
/-! Nothing to promise: cconvert@65: identity conversion; no additional behaviour. -/
/-! Nothing to promise: cconvert@66: pure forwarding wrapper; no independent behaviour. -/
/-! Nothing to promise: eltype@75: constant element type; no behaviour. -/
/-! Nothing to promise: eltype@76: constant element type; no behaviour. -/
/-! Nothing to promise: unsafe_convert@90: re-tags the same address; no behaviour. -/
/-! Nothing to promise: unsafe_convert@101: pointer conversion wrapper; no independent behaviour. -/
/-! Nothing to promise: unsafe_convert@102: identity conversion; no additional behaviour. -/
/-! Nothing to promise: cconvert@105: identity conversion; no additional behaviour. -/
/-! Nothing to promise: unsafe_convert@106: re-tags the same address; no behaviour. -/
/-! Nothing to promise: transcode@163: same-code-unit identity; no additional behaviour. -/
/-! Nothing to promise: transcode@165: copy-and-forward wrapper; no independent behaviour. -/
/-! Nothing to promise: transcode@167: pure forwarding wrapper; no independent behaviour. -/
/-! Nothing to promise: transcode@177: identity conversion; no additional behaviour. -/
/-! Nothing to promise: transcode@178: pure forwarding wrapper; no independent behaviour. -/
/-! Nothing to promise: transcode@183: pure forwarding wrapper; no independent behaviour. -/
/-! Nothing to promise: unsafe_string@331: pure forwarding wrapper; no independent behaviour. -/



def CwstringPointerTargetSpec : Prop :=
  ∀ {T : Type} [CwstringTarget T] (p : Cwstring),
    Ptr Cwchar_t = Ptr T ∧ (ptrCwstring (T := T) p).address = p.address

def readCStringBytes : List UInt8 → List UInt8
  | [] => []
  | 0 :: _ => []
  | byte :: rest => byte :: readCStringBytes rest

def PointerOperationsSpec : Prop :=
  (∀ {U : Type}
      (sameAddress : ∀ {α β : Type}, Ptr α → Ptr β → Bool)
      (x : CstringOrCwstring) (y : Ptr U),
      (∀ {α β : Type} (a : Ptr α) (b : Ptr β),
        sameAddress a b = (a.address == b.address)) →
      eqCptr sameAddress x y =
        match x with
        | .cstring value => value.address == y.address
        | .cwstring value => value.address == y.address) ∧
  (∀ {T : Type}
      (sameAddress : ∀ {α β : Type}, Ptr α → Ptr β → Bool)
      (x : Ptr T) (y : CstringOrCwstring),
      (∀ {α β : Type} (a : Ptr α) (b : Ptr β),
        sameAddress a b = (a.address == b.address)) →
      eqPtrC sameAddress x y =
        match y with
        | .cstring value => x.address == value.address
        | .cwstring value => x.address == value.address) ∧
  (∀ (read : Ptr UInt8 → StringResult JString)
      (memory : PointerAccess UInt8)
      (stringFromBytes : List UInt8 → StringResult JString) (s : Cstring),
      let p := convertPtrCstring (T := UInt8) s
      (memory.cells p).contains 0 = true →
      (∀ q, (memory.cells q).contains 0 = true →
        read q = stringFromBytes (readCStringBytes (memory.cells q))) →
      unsafeStringCstring read s =
        stringFromBytes (readCStringBytes (memory.cells p)))

def ContainsnulSpec : Prop :=
  (∀ {T : Type} (cast : Ptr T → Ptr Int8)
      (memchrZero : Ptr Int8 → Nat → Bool)
      (pointerBytes : Ptr Int8 → List UInt8) (p : Ptr T) (n : Nat),
      (∀ q length, memchrZero q length = ((pointerBytes q).take length).contains 0) →
      containsnulPtr cast memchrZero p n =
        ((pointerBytes (cast p)).take n).contains 0) ∧
  (∀ (unsafeConvert : JString → Ptr Int8) (sizeof : JString → Nat)
      (memchrZero : Ptr Int8 → Nat → Bool)
      (pointerBytes : Ptr Int8 → List UInt8)
      (containsNulChar : JString → StringResult Bool) (s : JString),
      (∀ p length, memchrZero p length = ((pointerBytes p).take length).contains 0) →
      pointerBytes (unsafeConvert s) = s.bytes →
      sizeof s = s.bytes.length →
      (∀ text, ∃ value, containsNulChar text = .ok value ∧
        (value = true ↔ text.bytes.contains 0 = true) ∧
        (value = false ↔ text.bytes.contains 0 = false)) →
      containsnulString unsafeConvert sizeof memchrZero s = s.bytes.contains 0 ∧
      ∃ value, containsnulAbstract containsNulChar s = .ok value ∧
        value = containsnulString unsafeConvert sizeof memchrZero s ∧
        (value = true ↔ s.bytes.contains 0 = true) ∧
        (value = false ↔ s.bytes.contains 0 = false))

def CStringConversionWrappersSpec : Prop :=
  ContainsnulSpec

def CStringNulSpec : Prop :=
  ∀ (unsafeConvert : JString → Ptr Int8)
    (memchrZero : Ptr Int8 → Nat → Bool)
    (sizeof : JString → Nat) (pointerBytes : Ptr Int8 → List UInt8)
    (repr : JString → String) (s : JString),
    (∀ p length, memchrZero p length = ((pointerBytes p).take length).contains 0) →
    (pointerBytes (unsafeConvert s)).take (s.bytes.length + 1) = s.bytes ++ [0] →
    sizeof s = s.bytes.length →
    let p := unsafeConvert s
    ((s.bytes.contains 0 = true →
        unsafeConvertCstring unsafeConvert memchrZero sizeof repr s =
          .error (.jl (.argumentError s!"embedded NULs are not allowed in C strings: {repr s}"))) ∧
     (s.bytes.contains 0 = false →
        unsafeConvertCstring unsafeConvert memchrZero sizeof repr s =
          .ok (cstringCtor p) ∧
        (pointerBytes p).take s.bytes.length = s.bytes ∧
        (pointerBytes p)[s.bytes.length]? = some 0))

def CwstringVectorSpec : Prop :=
  ∀ (zero : Cwchar_t) (eq : Cwchar_t → Cwchar_t → Bool)
    (repr : List Cwchar_t → String)
    (toPtr : List Cwchar_t → StringResult (Ptr Cwchar_t)),
    (∀ value, eq value zero = true ↔ value = zero) →
    (∀ (prior : List Cwchar_t) (p : Ptr Cwchar_t),
      prior.any (fun x => eq x zero) = false →
      toPtr (prior ++ [zero]) = .ok p →
      cconvertCwstringVector zero eq repr toPtr (prior ++ [zero]) = .ok p) ∧
    (∀ (prior : List Cwchar_t),
      prior.any (fun x => eq x zero) = true →
      ∃ message, cconvertCwstringVector zero eq repr toPtr (prior ++ [zero]) =
        .error (.jl (.argumentError message))) ∧
    cconvertCwstringVector zero eq repr toPtr [] =
      .error JuliaLean.Strings.boundsErr ∧
    (∀ (prior : List Cwchar_t) (last : Cwchar_t),
      prior.any (fun x => eq x zero) = false → eq last zero = false →
      ∃ message, cconvertCwstringVector zero eq repr toPtr (prior ++ [last]) =
        .error (.jl (.argumentError message)))

def CwstringVectorTerminatorTotalSpec : Prop :=
  ∀ (zero : Cwchar_t) (eq : Cwchar_t → Cwchar_t → Bool)
    (repr : List Cwchar_t → String)
    (toPtr : List Cwchar_t → StringResult (Ptr Cwchar_t))
    (values : List Cwchar_t),
    (∀ value, eq value zero = true ↔ value = zero) →
    (values = [] ∨ ∃ prior last, values = prior ++ [last] ∧ eq last zero = false) →
    ∃ message, cconvertCwstringVector zero eq repr toPtr values =
      .error (.jl (.argumentError message))

def CwstringAbstractSpec : Prop :=
  ∀ {S : Type} [CwcharPlatform]
    (toString : S → StringResult JString)
    (zero : Cwchar_t) (eq : Cwchar_t → Cwchar_t → Bool)
    (repr : List Cwchar_t → String)
    (cconvertPtr : List Cwchar_t → StringResult (Ptr Cwchar_t)) (s : S),
    (∀ value, eq value zero = true ↔ value = zero) →
    (∀ result, cconvertCwstringAbstract toString zero eq repr cconvertPtr s = .ok result →
      ∃ (concrete : JString) (units : List Cwchar_t), toString s = .ok concrete ∧
        transcode (T := Cwchar_t) concrete = .ok units ∧
        units.any (fun unit => eq unit zero) = false ∧
        cconvertPtr (units ++ [zero]) = .ok result) ∧
    (∀ (concrete : JString) (units : List Cwchar_t), toString s = .ok concrete →
      transcode (T := Cwchar_t) concrete = .ok units →
      units.any (fun unit => eq unit zero) = true →
      ∃ message, cconvertCwstringAbstract toString zero eq repr cconvertPtr s =
        .error (.jl (.argumentError message)))

def CwstringWindowsSpec : Prop :=
  ∀ {S : Type}
    (toString : S → StringResult JString)
    (codeunits : JString → List UInt8)
    (repr : JString → String) (s : S) (concrete : JString)
    (bytes : List UInt8) (units : List UInt16),
    toString s = .ok concrete → codeunits concrete = bytes →
    bytes.contains 0 = false → transcode (T := UInt16) bytes = .ok units →
    cwstringWindows toString codeunits repr s = .ok (units ++ [0])

def CwstringWindowsNulSpec : Prop :=
  ∀ {S : Type}
    (toString : S → StringResult JString)
    (codeunits : JString → List UInt8)
    (repr : JString → String) (s : S) (concrete : JString)
    (bytes : List UInt8) (units result : List UInt16),
    toString s = .ok concrete → codeunits concrete = bytes →
    bytes.contains 0 = false → transcode (T := UInt16) bytes = .ok units →
    cwstringWindows toString codeunits repr s = .ok result →
    result.getLast? = some 0 ∧ result.dropLast.contains 0 = false

def Utf8ToUtf16TotalSpec : Prop :=
  (∀ bytes : List UInt8, ∃ units : List UInt16,
    transcode (T := UInt16) (Output := List UInt16) bytes = .ok units) ∧
  (∀ s : JString, ∃ units : List UInt16,
    transcode (T := UInt16) (Output := List UInt16) s = .ok units)

def Utf16ToUtf8RuntimeLaw (runtime : Utf16ToUtf8Runtime) : Prop :=
  (∀ units, runtime.requireOneBased units = .ok ()) ∧
  (∀ units, runtime.length units = ix units.length) ∧
  (∀ units (i : Nat) (value : UInt16),
    1 ≤ i → i ≤ units.length →
    units[i - 1]? = some value →
    runtime.read units (ix i) = .ok value) ∧
  runtime.empty.capacity.val = 0 ∧ runtime.empty.written = [] ∧
  (∀ requested, 0 ≤ requested.val → requested.val < (2 ^ 62 : Int) →
    ∃ result, runtime.allocate requested = .ok result ∧
      result.capacity = requested ∧ result.written = []) ∧
  (∀ requested result, runtime.allocate requested = .ok result →
    result.capacity = requested ∧ result.written = []) ∧
  (∀ (dst : StringVector) (i : Index) (byte : UInt8),
    1 ≤ i.val →
    i.val = (dst.written.length : Int) + 1 →
    i.val ≤ dst.capacity.val →
    runtime.setByte dst i byte =
      .ok {dst with written := dst.written ++ [byte]})

def StringFromBytesRuntimeLaw (runtime : StringFromBytesRuntime) : Prop :=
  (∀ bytes, bytes.length < 2 ^ 62 →
    ∃ result, runtime.fromBytes bytes = .ok result ∧ result.bytes = bytes)

def utf16OutputSize (runtime : Utf16ToUtf8Runtime) (units : List UInt16) :
    StringResult Index := do
  let _ ← runtime.requireOneBased units
  let n := runtime.length units
  if n.val == 0 then
    pure (ix 0)
  else do
    let first ← runtime.read units (ix 1)
    utf16CountLoop runtime.read runtime.length units n n.val.toNat (ix 1) first (ix 0)

def Utf16ToUtf8TotalSpec : Prop :=
  ∀ [runtime : Utf16ToUtf8Runtime] (units : List UInt16) (requested : Index),
    Utf16ToUtf8RuntimeLaw runtime →
    units.length < 2 ^ 62 →
    utf16OutputSize runtime units = .ok requested →
    0 ≤ requested.val →
    requested.val < (2 ^ 62 : Int) →
    ∃ result : StringVector,
      transcodeUtf16ToUtf8 runtime.requireOneBased runtime.length runtime.read
        runtime.empty runtime.allocate runtime.setByte units = .ok result ∧
      result.capacity = requested ∧
      result.written.length = requested.val.toNat

def Utf16RoundtripSpec : Prop :=
  ∀ [runtime : Utf16ToUtf8Runtime] [bytesRuntime : StringFromBytesRuntime]
    (s : JString) (units : List UInt16) (requested : Index),
    Utf16ToUtf8RuntimeLaw runtime →
    StringFromBytesRuntimeLaw bytesRuntime →
    JuliaLean.Transcode.ValidUtf8 s.bytes →
    transcode (T := UInt16) (Output := List UInt16) s = .ok units →
    units.length < 2 ^ 62 →
    utf16OutputSize runtime units = .ok requested →
    0 ≤ requested.val →
    requested.val < (2 ^ 62 : Int) →
    ∃ (result : StringVector) (bytes : List UInt8),
      transcodeUtf16ToUtf8 runtime.requireOneBased runtime.length runtime.read
        runtime.empty runtime.allocate runtime.setByte units = .ok result ∧
      result.capacity = requested ∧
      result.written.length = requested.val.toNat ∧
      transcode (T := UInt8) (Output := List UInt8) units = .ok bytes ∧
      bytes = result.written ∧
      transcode (T := JString) (Output := JString) units = .ok s ∧
      requested.val = (s.bytes.length : Int) ∧
      bytes.length = s.bytes.length
def Utf16WellformedSpec : Prop :=
  ∀ (s : JString) (units : List UInt16),
    JuliaLean.Transcode.ValidUtf8 s.bytes →
    transcode (T := UInt16) (Output := List UInt16) s = .ok units →
    JuliaLean.Transcode.wf16 units = true

def Utf16LengthSpec : Prop :=
  ∀ (s : JString) (units : List UInt16),
    JuliaLean.Transcode.ValidUtf8 s.bytes →
    transcode (T := UInt16) (Output := List UInt16) s = .ok units →
    (units.length : Int) = (JuliaLean.base.strings.string.stringLength s).val +
      ((s.bytes.filter (fun b => decide (0xf0 ≤ b))).length : Int)

def CharErrorAgrees : JuliaLean.base.char.CharError → JuliaLean.Strings.SErr → Prop
  | .invalidChar bits, .invalidChar actual => HEq bits actual
  | .codePointError value, .codePointError actual => HEq value actual
  | .boundsError, .jl .boundsError => True
  | .foreign error, .jl actual => error = actual
  | _, _ => False

def CharResultAgrees {α β : Type} (project : α → β)
    (source : JuliaLean.base.char.CharResult α) (actual : StringResult β) : Prop :=
  match source, actual with
  | .ok value, .ok result => result = project value
  | .error error, .error result => CharErrorAgrees error result
  | _, _ => False

def Utf32CharacterConversionLaw
    (conversion : Utf32CharacterConversion UInt32) : Prop :=
  ∀ bits, CharResultAgrees id
    (JuliaLean.base.char.codepoint_Char JuliaLean.base.char.charBitOps bits)
    (conversion.convertChar bits)

def Int32CharacterConversionLaw
    (conversion : Utf32CharacterConversion Int32) : Prop :=
  ∀ bits, CharResultAgrees id (JuliaLean.base.char.charToInt32 bits)
    (conversion.convertChar bits)

def Utf32StringLengthSpec : Prop :=
  (∀ [Utf32CodeUnit UInt32] [conversion : Utf32CharacterConversion UInt32]
      (s : JString) (units : List UInt32),
      Utf32CharacterConversionLaw conversion →
      transcode (T := UInt32) (Output := List UInt32) s = .ok units →
      (units.length : Int) = (JuliaLean.base.strings.string.stringLength s).val) ∧
  (∀ [Utf32CodeUnit Int32] [conversion : Utf32CharacterConversion Int32]
      (s : JString) (units : List Int32),
      Int32CharacterConversionLaw conversion →
      transcode (T := Int32) (Output := List Int32) s = .ok units →
      (units.length : Int) = (JuliaLean.base.strings.string.stringLength s).val)


def Utf32StringTotalSpec : Prop :=
  ∀ [Utf32CodeUnit UInt32] [conversion : Utf32CharacterConversion UInt32]
    (s : JString),
    Utf32CharacterConversionLaw conversion →
    ∃ units : List UInt32,
      transcode (T := UInt32) (Output := List UInt32) s = .ok units

def Char32ToUtf8RuntimeLaw (runtime : Char32ToUtf8Runtime UInt32) : Prop :=
  ∀ value, CharResultAgrees JuliaChar.mk
    (JuliaLean.base.char.char_UInt32 value) (runtime.toChar value)

def Int32ToUtf8RuntimeLaw (runtime : Char32ToUtf8Runtime Int32) : Prop :=
  ∀ value, CharResultAgrees JuliaChar.mk
    (JuliaLean.base.char.constructor_Number_AbstractChar
      (fun input : Int32 => JuliaLean.base.char.exactUInt32 input.toInt)
      JuliaLean.base.char.char_UInt32 value)
    (runtime.toChar value)

def Utf32ToUtf8TotalSpec : Prop :=
  ∀ [Char32Value UInt32] [runtime : Char32ToUtf8Runtime UInt32]
    (units : List UInt32),
    Char32ToUtf8RuntimeLaw runtime →
    ∃ bytes : List UInt8,
      transcode (T := UInt8) (Output := List UInt8) units = .ok bytes

def cstringStringPrefix (s : JString) : List UInt32 → Index → Index → Prop
  | [], start, finish => start = finish
  | character :: rest, start, finish =>
      ∃ next, iterateCstringString s start = some (character, next) ∧
        cstringStringPrefix s rest next finish

def Utf32StringErrorSpec : Prop :=
  (∀ [conversion : Utf32CharacterConversion UInt32]
      (s : JString) (priorChars : List UInt32) (cursor : Index)
      (bad : UInt32) (next : Index) (sourceError : JuliaLean.base.char.CharError)
      (error : JuliaLean.Strings.SErr),
      Utf32CharacterConversionLaw conversion →
      cstringStringPrefix s priorChars (ix 1) cursor →
      (∀ character, character ∈ priorChars →
        ∃ value, JuliaLean.base.char.codepoint_Char
          JuliaLean.base.char.charBitOps character = .ok value) →
      iterateCstringString s cursor = some (bad, next) →
      JuliaLean.base.char.codepoint_Char JuliaLean.base.char.charBitOps bad =
        .error sourceError →
      CharErrorAgrees sourceError error →
      transcode (T := UInt32) (Output := List UInt32) s = .error error) ∧
  (∀ [conversion : Utf32CharacterConversion Int32]
      (s : JString) (priorChars : List UInt32) (cursor : Index)
      (bad : UInt32) (next : Index) (sourceError : JuliaLean.base.char.CharError)
      (error : JuliaLean.Strings.SErr),
      Int32CharacterConversionLaw conversion →
      cstringStringPrefix s priorChars (ix 1) cursor →
      (∀ character, character ∈ priorChars →
        ∃ value, JuliaLean.base.char.charToInt32 character = .ok value) →
      iterateCstringString s cursor = some (bad, next) →
      JuliaLean.base.char.charToInt32 bad = .error sourceError →
      CharErrorAgrees sourceError error →
      transcode (T := Int32) (Output := List Int32) s = .error error)


def Utf32ToUtf8ErrorSpec : Prop :=
  (∀ [Char32Value UInt32] [runtime : Char32ToUtf8Runtime UInt32]
      (prior suffix : List UInt32) (bad : UInt32),
      Char32ToUtf8RuntimeLaw runtime →
      prior.all (fun value => decide (value < (0x00200000 : UInt32))) = true →
      (0x00200000 : UInt32) ≤ bad →
      transcode (T := UInt8) (Output := List UInt8) (prior ++ bad :: suffix) =
        .error (.codePointError bad)) ∧
  (∀ [Char32Value Int32] [runtime : Char32ToUtf8Runtime Int32]
      (prior suffix : List Int32) (bad : Int32)
      (sourceError : JuliaLean.base.char.CharError) (error : JuliaLean.Strings.SErr),
      Int32ToUtf8RuntimeLaw runtime →
      (∀ value, value ∈ prior →
        ∃ bits, JuliaLean.base.char.constructor_Number_AbstractChar
          (fun input : Int32 => JuliaLean.base.char.exactUInt32 input.toInt)
          JuliaLean.base.char.char_UInt32 value = .ok bits) →
      JuliaLean.base.char.constructor_Number_AbstractChar
        (fun input : Int32 => JuliaLean.base.char.exactUInt32 input.toInt)
        JuliaLean.base.char.char_UInt32 bad = .error sourceError →
      CharErrorAgrees sourceError error →
      transcode (T := UInt8) (Output := List UInt8) (prior ++ bad :: suffix) =
        .error error)

def TranscodeVectorStringSpec : Prop :=
  ∀ [runtime : StringViewRuntime] (src : List UInt8) (result : JString),
    (∀ bytes, runtime.viewBytes (runtime.viewAll bytes) = bytes) →
    (∀ (view : runtime.View) (value : JString),
      runtime.stringFromView view = .ok value →
      value.bytes = runtime.viewBytes view) →
    transcode (T := JString) (Output := JString) src = .ok result →
    result.bytes = src

def UnsafeWideSpec : Prop :=
  (∀ {T N : Type} [WideCodeUnit T] [JuliaIntegerArgument N]
      [TranscodeOverload UInt8 (List T) (List UInt8)]
      (pointer : PointerAccess T)
      (stringFromBytes : List UInt8 → StringResult JString)
      (p : Ptr T) (len : N) (units : List T) (bytes : List UInt8) (result : JString),
      let n := JuliaIntegerArgument.toInt len
      0 ≤ n →
      n.toNat ≤ (pointer.cells p).length →
      pointer.unsafeWrap p n = .ok units →
      units = (pointer.cells p).take n.toNat →
      transcode (T := UInt8) (Output := List UInt8) units = .ok bytes →
      stringFromBytes bytes = .ok result →
      unsafeStringWideLength pointer stringFromBytes p len = .ok result ∧
        units.length = n.toNat) ∧
  (∀ {T : Type} [WideCodeUnit T]
      [TranscodeOverload UInt8 (List T) (List UInt8)]
      (pointer : PointerAccess T) (zero : T) (eq : T → T → Bool)
      (stringFromBytes : List UInt8 → StringResult JString)
      (p : Ptr T) (count : Nat),
      (∀ value, eq value zero = true ↔ value = zero) →
      (∀ i, 1 ≤ i → i ≤ count → eq (pointer.load p i) zero = false) →
      eq (pointer.load p (count + 1)) zero = true →
      count + 1 ≤ (pointer.cells p).length →
      ∀ (bytes : List UInt8) (result : JString),
        transcode (T := UInt8) (Output := List UInt8)
          ((pointer.cells p).take count) = .ok bytes →
        stringFromBytes bytes = .ok result →
        unsafeStringWide pointer zero eq stringFromBytes p = .ok result
)
def entry (id : String) (juliaFns : List String) (statement source : String)
    (property : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/strings/cstring.jl", juliaFns := juliaFns,
    statement := statement, source := source, status := .todo,
    prop := property, thm := none }

def entries : List Entry := [
  entry "transcode-utf8-utf16-total" ["transcode(::Type{UInt16}, ::AbstractVector{UInt8})", "transcode(::Type{UInt16}, ::String)"] "transcode(UInt16, src) returns for every byte vector, valid UTF-8 or not (overlong forms, surrogates, truncated sequences, stray continuation bytes, bytes F5-FF), and never reads past the end of src." "base/strings/cstring.jl:140-142: \"it always succeeds for conversions between UTF-XX encodings, even for invalid Unicode data.\"" ``Utf8ToUtf16TotalSpec,
  entry "transcode-utf16-utf8-complete" ["transcode(::Type{UInt8}, ::AbstractVector{UInt16})", "transcode(::Type{String}, ::Vector{UInt16})"] "For every UTF-16 vector whose precomputed UTF-8 size fits Julia's string limit, transcoding succeeds, allocates capacity exactly equal to the byte count, and writes every allocated byte." "base/strings/cstring.jl:140-142 (always succeeds); cstring.jl:241-246 (sizes are precomputed so that dst is never grown); invariant" ``Utf16ToUtf8TotalSpec,
  entry "transcode-utf32-invalid" ["transcode(::Type{UInt32}, ::String)"] "transcode(UInt32, s) returns for every String s, including malformed UTF-8." "base/strings/cstring.jl:140-142: \"it always succeeds for conversions between UTF-XX encodings, even for invalid Unicode data.\"" ``Utf32StringTotalSpec,
  entry "transcode-utf32-out-of-range" ["transcode(::Type{UInt8}, ::Vector{UInt32})"] "transcode(UInt8, v::Vector{UInt32}) returns for every vector v, including one containing 0x00200000." "base/strings/cstring.jl:140-142: \"it always succeeds for conversions between UTF-XX encodings, even for invalid Unicode data.\"" ``Utf32ToUtf8TotalSpec,
  entry "transcode-utf16-roundtrip" ["transcode(::Type{UInt16}, ::String)", "transcode(::Type{String}, ::Vector{UInt16})"] "For valid UTF-8 strings, UTF-16 transcoding round-trips to the original String and allocates a UTF-8 byte buffer with capacity exactly ncodeunits(s)." "base/strings/cstring.jl:157-158 (doctest transcode(String, transcode(UInt16, str)) == str); invariant" ``Utf16RoundtripSpec,
  entry "transcode-utf16-wellformed" ["transcode(::Type{UInt16}, ::String)"] "For a valid string s, transcode(UInt16, s) is well-formed UTF-16: every high surrogate is immediately followed by a low surrogate, and every low surrogate immediately follows a high surrogate." "invariant (UTF-16 output of valid input; Unicode D91)" ``Utf16WellformedSpec,
  entry "transcode-utf16-length" ["transcode(::Type{UInt16}, ::String)", "length(::String)"] "For a valid string s, length(transcode(UInt16, s)) == length(s) + count(>=(0xf0), codeunits(s)): one code unit per character and two for characters outside the BMP." "invariant" ``Utf16LengthSpec,
  entry "transcode-utf32-length" ["transcode(::Type{UInt32}, ::String)", "transcode(::Type{Int32}, ::String)", "length(::String)"] "Whenever transcode(T, s) returns for T equal to Int32 or UInt32, its length equals length(s), for any byte string s." "invariant (one UTF-32 code unit per character)" ``Utf32StringLengthSpec,
  entry "transcode-containsnul-agree" ["containsnul(::String)", "containsnul(::AbstractString)"] "The String and AbstractString forms agree both ways for every byte string, return false exactly when no NUL occurs, and the AbstractString form does not error." "base/strings/cstring.jl:78-81; invariant" ``ContainsnulSpec,
  entry "transcode-cstring-nul-check" ["unsafe_convert(::Type{Cstring}, ::String)", "ccall with Cstring arguments"] "unsafe_convert(Cstring, s::String) throws ArgumentError exactly when '\\0' in s; otherwise the C function receives all of s's bytes followed by one NUL terminator, with no embedded NUL." "base/strings/cstring.jl:83-88; Cstring docstring (cstring.jl:21-22): \"Cstrings are NUL-terminated\"" ``CStringNulSpec,
  entry "transcode-cwstring-nul-terminated" ["cconvert(::Type{Cwstring}, ::AbstractString)", "cconvert(::Type{Cwstring}, ::Vector{Cwchar_t})"] "cconvert(Cwstring, s) passes NUL-terminated data without an embedded NUL to C, both on Windows (Cwchar_t = UInt16) and on Linux/macOS (Cwchar_t = Int32)." "Cwstring docstring (base/strings/cstring.jl:8-9): \"Cwstrings are NUL-terminated\"; cstring.jl:92-100" ``CwstringAbstractSpec,
  entry "transcode-cwstring-overlong-nul" ["Base.cwstring(::AbstractString)"] "Base.cwstring(s) returns UTF-16 data whose only NUL is the terminator." "base/strings/cstring.jl:112-113: \"Convert a string s to a NUL-terminated Vector{Cwchar_t}, suitable for passing to C functions\"; the embedded-NUL check at :121" ``CwstringWindowsNulSpec,
  entry "transcode-cwstring-empty-vector" ["cconvert(::Type{Cwstring}, ::Vector{Cwchar_t})"] "cconvert(Cwstring, v::Vector{Cwchar_t}) throws ArgumentError for every v that is not NUL-terminated." "base/strings/cstring.jl:97-98: v[end] == 0 || throw(ArgumentError(\"C string data must be NUL terminated: ...\"))" ``CwstringVectorTerminatorTotalSpec,
  entry "transcode-unsafe-string-nul" ["unsafe_string(::Ptr{UInt16})", "unsafe_string(::Ptr{UInt16}, ::Integer)"] "unsafe_string(p::Ptr{UInt16}) reads the code units up to and including the first NUL and nothing after it, and returns transcode(String, ...) of the units before the NUL." "base/strings/cstring.jl:309-319 (unsafe_string docstring: C-style NUL-terminated data)" ``UnsafeWideSpec,
  entry "stringscova-cwstring-pointer-type" ["Ptr{T}(::Cwstring)"] "Ptr{T}(Cwstring) returns a value of the requested Ptr{T} type and preserves the original pointer address." "constructor and conversion invariant; base/strings/cstring.jl:34,39" ``CwstringPointerTargetSpec,
  entry "stringscova-cstring-pointer-operations" ["==(::Union{Cstring,Cwstring}, ::Ptr)", "==(::Ptr, ::Union{Cstring,Cwstring})", "unsafe_string(::Cstring)"] "C-string pointer equality compares converted addresses, and unsafe_string reads bytes through the first NUL." "base/strings/cstring.jl:59-62" ``PointerOperationsSpec,
  entry "stringscova-cstring-conversion-wrappers" ["containsnul(::Ptr, len)", "containsnul(::String)", "containsnul(::AbstractString)"] "Pointer containsnul reports NUL exactly within the requested prefix; String and AbstractString forms agree both ways, return false exactly when no NUL occurs, and AbstractString does not error." "base/strings/cstring.jl:78-81" ``CStringConversionWrappersSpec,
  entry "stringscova-transcode-wrappers" ["transcode(::Type{String}, ::Vector{UInt8})"] "Vector{UInt8} to String transcode returns a String whose bytes equal the source vector's bytes." "base/strings/cstring.jl:182; String(view(src, :))" ``TranscodeVectorStringSpec,
  entry "stringscova-unsafe-wide-strings" ["unsafe_string(::Ptr{T}, ::Integer)", "unsafe_string(::Ptr{T})"] "Wide unsafe_string with a length transcodes exactly the requested code-unit prefix; the NUL-terminated form transcodes exactly the prefix before the first zero." "base/strings/cstring.jl:321-330" ``UnsafeWideSpec,
  entry "stringscova-cstring-eq-ptr-faithful" ["==(::Union{Cstring,Cwstring}, ::Ptr)"] "C-string equality with a pointer compares the converted address." "base/strings/cstring.jl:59" ``PointerOperationsSpec,
  entry "stringscova-ptr-eq-cstring-faithful" ["==(::Ptr, ::Union{Cstring,Cwstring})"] "Pointer equality with a C string compares against the converted address." "base/strings/cstring.jl:60" ``PointerOperationsSpec,
  entry "stringscova-cstring-unsafe-string-faithful" ["unsafe_string(::Cstring)"] "unsafe_string(Cstring) converts to Ptr{UInt8} and copies through the first NUL." "base/strings/cstring.jl:62" ``PointerOperationsSpec,
  entry "stringscova-cwstring-cconvert-abstract-faithful" ["cconvert(::Type{Cwstring}, ::AbstractString)"] "cconvert(Cwstring,AbstractString) first constructs a String, transcodes to the platform wide type, appends NUL, and applies the wide-vector checks in order." "base/strings/cstring.jl:69-73" ``CwstringAbstractSpec,
  entry "stringscova-containsnul-ptr-faithful" ["containsnul(::Ptr, len)"] "containsnul calls memchr for zero over exactly len bytes." "base/strings/cstring.jl:78-79" ``ContainsnulSpec,
  entry "stringscova-containsnul-string-faithful" ["containsnul(::String)"] "String NUL detection converts the storage pointer and scans exactly sizeof(s) bytes, excluding the trailing terminator." "base/strings/cstring.jl:80" ``ContainsnulSpec,
  entry "stringscova-cstring-unsafe-string-convert-faithful" ["unsafe_convert(::Type{Cstring}, ::String)"] "String-to-Cstring conversion scans exactly the String bytes for embedded NUL, throws when one is present, and otherwise preserves the address and all bytes followed by the terminating NUL." "base/strings/cstring.jl:83-88" ``CStringNulSpec,
  entry "stringscova-cwstring-cconvert-vector-faithful" ["cconvert(::Type{Cwstring}, ::Vector{Cwchar_t})"] "Wide-vector conversion rejects embedded NULs before the last element, requires a final NUL, and preserves every accepted vector." "base/strings/cstring.jl:92-100" ``CwstringVectorSpec,
  entry "stringscova-cwstring-windows-faithful" ["cwstring(::AbstractString)"] "Windows cwstring first constructs a String, rejects zero bytes, transcodes its bytes to UInt16, and appends one terminating NUL." "base/strings/cstring.jl:119-123" ``CwstringWindowsSpec,
  entry "stringscova-transcode-string32-faithful" ["transcode(::Type{UInt32}, ::String)", "transcode(::Type{Int32}, ::String)"] "String-to-Int32 or UInt32 transcode returns the first character-conversion error after any successfully converted prefix." "base/strings/cstring.jl:164" ``Utf32StringErrorSpec,
  entry "stringscova-transcode-32-to-bytes-faithful" ["transcode(::Type{UInt8}, ::Vector{UInt32})", "transcode(::Type{UInt8}, ::Vector{Int32})"] "Int32 or UInt32 to UTF-8 transcode returns the first Char-construction error after any valid prefix; a UInt32 value at or above 0x00200000 raises CodePointError." "base/strings/cstring.jl:170-176" ``Utf32ToUtf8ErrorSpec,
  entry "stringscova-transcode-vector-string-faithful" ["transcode(::Type{String}, ::Vector{UInt8})"] "Vector{UInt8} to String transcode returns a String whose bytes equal the source vector's bytes." "base/strings/cstring.jl:182; String(view(src, :))" ``TranscodeVectorStringSpec,
  entry "stringscova-unsafe-wide-length-faithful" ["unsafe_string(::Ptr{T}, ::Integer)"] "For every valid pointer and nonnegative Integer length, wide unsafe_string wraps exactly that many units without ownership and transcodes them to String." "base/strings/cstring.jl:321-323" ``UnsafeWideSpec,
  entry "stringscova-unsafe-wide-nul-faithful" ["unsafe_string(::Ptr{T})"] "For every documented valid NUL-terminated pointer, wide unsafe_string loads consecutive units from index one, excludes the first zero, and calls the length-qualified method." "base/strings/cstring.jl:324-330" ``UnsafeWideSpec,
]

end JuliaLean.Proofs.base.strings.cstring

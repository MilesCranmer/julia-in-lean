import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.strings.cstring.encoding
import JuliaLean.base.strings.cstring
import JuliaLean.base.char
import JuliaLean.Proofs.base.strings.cstring.wrappers

namespace JuliaLean.Proofs.base.strings.cstring

open JuliaLean.Registry
open JuliaLean.base.strings.cstring
open JuliaLean.Transcode (wfChar isC isHigh isLow wf16 ValidUtf8)

/-! Statements for the source-mirrored Cstring model. -/



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
  | .showError error, .showError actual => error = actual
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
theorem pointerOperations_proven : PointerOperationsSpec := by
  constructor
  · intro U sameAddress x y haddr
    cases x with
    | cstring p =>
        simp [eqCptr, pointerCstringOrCwstring, pointerCstring, convertPtrCstring,
          ptrCstring, cstringCtor, haddr]
    | cwstring p =>
        simp [eqCptr, pointerCstringOrCwstring, pointerCwstring, convertPtrCwstring,
          ptrCwstring, cwstringCtor, haddr]
  constructor
  · intro T sameAddress x y haddr
    cases y with
    | cstring p =>
        simp [eqPtrC, pointerCstringOrCwstring, pointerCstring, convertPtrCstring,
          ptrCstring, cstringCtor, haddr]
    | cwstring p =>
        simp [eqPtrC, pointerCstringOrCwstring, pointerCwstring, convertPtrCwstring,
          ptrCwstring, cwstringCtor, haddr]
  · intro read memory stringFromBytes s p hzero hread
    change (memory.cells ({ address := s.address } : Ptr UInt8)).contains 0 = true at hzero
    simpa [unsafeStringCstring, convertPtrCstring, ptrCstring, cstringCtor, p] using
      hread _ hzero
theorem containsnul_proven : ContainsnulSpec := by
  constructor
  · intro T cast memchrZero pointerBytes p n hmem
    exact hmem _ _
  · intro unsafeConvert sizeof memchrZero pointerBytes containsNulChar s hmem hbytes hsizeof hcontains
    have hstring : containsnulString unsafeConvert sizeof memchrZero s = s.bytes.contains 0 := by
      simpa [containsnulString, containsnulPtr, hbytes, hsizeof] using hmem (unsafeConvert s) (sizeof s)
    obtain ⟨value, hvalue, htrue, hfalse⟩ := hcontains s
    have hvalue' : value = s.bytes.contains 0 := by
      cases hbytesZero : s.bytes.contains 0 with
      | false => exact hfalse.mpr hbytesZero
      | true => exact htrue.mpr hbytesZero
    exact ⟨hstring, ⟨value, by simpa [containsnulAbstract] using hvalue,
      by rw [hstring]; exact hvalue', htrue, hfalse⟩⟩
theorem cstringConversionWrappers_proven : CStringConversionWrappersSpec :=
  containsnul_proven
theorem transcodeVectorString_proven : TranscodeVectorStringSpec := by
  intro runtime src result hview hbytes htrans
  change transcodeVectorString runtime.viewAll runtime.stringFromView src = .ok result at htrans
  have hresult := hbytes (runtime.viewAll src) result htrans
  simpa [hview] using hresult

theorem cstringNul_proven : CStringNulSpec := by
  intro unsafeConvert memchrZero sizeof pointerBytes repr s hmem hbytes hsizeof
  let p := unsafeConvert s
  have hpref : (pointerBytes p).take (s.bytes.length + 1) = s.bytes ++ [0] := by
    simpa [p] using hbytes
  have hbefore : (pointerBytes p).take s.bytes.length = s.bytes := by
    have hh := congrArg (fun xs : List UInt8 => xs.take s.bytes.length) hpref
    rw [List.take_take, Nat.min_eq_left (by omega)] at hh
    simpa [List.take_append] using hh
  have hzero : (pointerBytes p)[s.bytes.length]? = some 0 := by
    have hh := congrArg (fun xs : List UInt8 => xs[s.bytes.length]?) hpref
    simpa using hh
  have hscan : containsnulPtr (fun q => q) memchrZero p (sizeof s) =
      s.bytes.contains 0 := by
    change memchrZero p (sizeof s) = s.bytes.contains 0
    rw [hmem p (sizeof s), hsizeof, hbefore]
  constructor
  · intro hcontains
    have hscanTrue : containsnulPtr (fun q => q) memchrZero p (sizeof s) = true := by
      rw [hscan]
      exact hcontains
    simpa [unsafeConvertCstring, p, hscanTrue]
  · intro hnoNul
    have hscanFalse : containsnulPtr (fun q => q) memchrZero p (sizeof s) = false := by
      rw [hscan, hnoNul]
    have hresult : unsafeConvertCstring unsafeConvert memchrZero sizeof repr s =
        .ok (cstringCtor p) := by
      simp [unsafeConvertCstring, p, hscanFalse] <;> rfl
    exact ⟨hresult, hbefore, hzero⟩


def utf32CharOutput (value : _root_.UInt32) : StringResult JuliaChar :=
  match JuliaLean.base.char.char_UInt32 value with
  | .ok bits => .ok (JuliaChar.mk bits)
  | .error (.codePointError _) =>
      .error (JuliaLean.Strings.SErr.codePointError value)
  | .error _ => .error .assertion

private theorem charUInt32_ok (value : UInt32) (h : value < 0x00200000) :
    ∃ bits, JuliaLean.base.char.char_UInt32 value = .ok bits := by
  let payload :=
    ((JuliaLean.base.char.shl32 value 0) &&& 0x0000003f) |||
      ((JuliaLean.base.char.shl32 value 2) &&& 0x00003f00) |||
      ((JuliaLean.base.char.shl32 value 4) &&& 0x003f0000) |||
      ((JuliaLean.base.char.shl32 value 6) &&& 0x3f000000)
  let encoded : UInt32 :=
    if value < 0x00000800 then
      (JuliaLean.base.char.shl32 payload 16) ||| 0xc0800000
    else if value < 0x00010000 then
      (JuliaLean.base.char.shl32 payload 8) ||| 0xe0808000
    else
      (JuliaLean.base.char.shl32 payload 0) ||| 0xf0808080
  let bits : UInt32 := if value < 0x80 then JuliaLean.base.char.shl32 value 24 else encoded
  refine ⟨bits, ?_⟩
  by_cases hsmall : value < 0x80
  · simp [JuliaLean.base.char.char_UInt32, payload, encoded, bits, hsmall, h] <;> rfl
  · by_cases hshort : value < 0x00000800
    · simp [JuliaLean.base.char.char_UInt32, payload, encoded, bits, hsmall, hshort, h] <;> rfl
    · by_cases hmedium : value < 0x00010000
      · simp [JuliaLean.base.char.char_UInt32, payload, encoded, bits, hsmall, hshort, hmedium, h] <;> rfl
      · simp [JuliaLean.base.char.char_UInt32, payload, encoded, bits, hsmall, hshort, hmedium, h] <;> rfl

private theorem charUInt32_error (value : UInt32) (h : 0x00200000 ≤ value) :
    JuliaLean.base.char.char_UInt32 value = .error (.codePointError value) := by
  have hval : 2097152 ≤ value.toNat := by
    rw [UInt32.le_iff_toNat_le] at h
    have hbound : (0x00200000 : UInt32).toNat = 2097152 := rfl
    rw [hbound] at h
    exact h
  have hsmall : ¬ value < 0x80 := by
    rw [UInt32.lt_iff_toNat_lt]
    have hbound : (0x80 : UInt32).toNat = 128 := rfl
    rw [hbound]
    omega
  have hlimit : ¬ value < 0x00200000 := by
    rw [UInt32.lt_iff_toNat_lt]
    have hbound : (0x00200000 : UInt32).toNat = 2097152 := rfl
    rw [hbound]
    omega
  simp [JuliaLean.base.char.char_UInt32, hsmall, hlimit,
    JuliaLean.base.char.throw_code_point_err, bind, Except.bind, pure, Except.pure]

theorem utf32ToUtf8Total_refuted : ¬ Utf32ToUtf8TotalSpec := by
  intro h
  let runtime : Char32ToUtf8Runtime UInt32 :=
    { Buffer := Unit, initialBuffer := (), toChar := utf32CharOutput,
      printChar := fun _ _ => (), takeBuffer := fun _ => [] }
  letI : Char32ToUtf8Runtime UInt32 := runtime
  have hlaw : Char32ToUtf8RuntimeLaw runtime := by
    intro value
    change CharResultAgrees JuliaChar.mk
      (JuliaLean.base.char.char_UInt32 value) (utf32CharOutput value)
    by_cases hvalid : value < 0x00200000
    · obtain ⟨bits, hsource⟩ := charUInt32_ok value hvalid
      simp [CharResultAgrees, utf32CharOutput, hsource]
    · have hnot : ¬ value.toNat < 2097152 := by
        intro hlt
        apply hvalid
        rw [UInt32.lt_iff_toNat_lt]
        have hbound : (0x00200000 : UInt32).toNat = 2097152 := rfl
        rw [hbound]
        exact hlt
      have hge : 2097152 ≤ value.toNat := by omega
      have hbound : 0x00200000 ≤ value := by
        rw [UInt32.le_iff_toNat_le]
        have hvalue : (0x00200000 : UInt32).toNat = 2097152 := rfl
        rw [hvalue]
        exact hge
      have hsource := charUInt32_error value hbound
      simp [CharResultAgrees, CharErrorAgrees, utf32CharOutput, hsource]
  have hcharSource : JuliaLean.base.char.char_UInt32 (0x00200000 : UInt32) =
      .error (.codePointError (0x00200000 : UInt32)) :=
    charUInt32_error _ (by decide)
  have hchar : utf32CharOutput (0x00200000 : UInt32) =
      .error (.codePointError (0x00200000 : UInt32)) := by
    simp [utf32CharOutput, hcharSource]
  have hbad : transcode (T := UInt8) (Output := List UInt8)
      ([0x00200000] : List UInt32) = .error (.codePointError 0x00200000) := by
    change transcode32To8 () utf32CharOutput (fun _ _ => ()) (fun _ => [])
      ([0x00200000] : List UInt32) = .error (.codePointError 0x00200000)
    simp [transcode32To8, hchar, bind, Except.bind, pure, Except.pure]
  obtain ⟨bytes, hbytes⟩ := h (runtime := runtime) [0x00200000] hlaw
  rw [hbytes] at hbad
  cases hbad

private def overlongNulString : JString :=
  ⟨[0xc0, 0x80], by decide⟩

private def overlongNulBytes : List UInt8 := [0xc0, 0x80]

private theorem overlongNulTranscode :
    transcode (T := UInt16) overlongNulBytes = .ok ([0] : List UInt16) := by
  change transcodeUtf8ToUtf16List overlongNulBytes = .ok ([0] : List UInt16)
  rfl
private theorem stringResultThrow {α : Type} (error : JuliaLean.Strings.SErr) :
    (throw error : StringResult α) = .error error := rfl

theorem cwstringVector_proven : CwstringVectorSpec := by
  intro zero eq repr toPtr heq
  have loopOk : ∀ (message : String) (xs : List Cwchar_t),
      (∀ x ∈ xs, eq x zero = false) →
      (forIn xs PUnit.unit (fun x _ =>
        if eq x zero then
          (Except.error (.jl (.argumentError message)) : StringResult (ForInStep PUnit))
        else .ok (ForInStep.yield PUnit.unit)) : StringResult PUnit) = .ok PUnit.unit := by
    intro message xs
    induction xs with
    | nil =>
        intro _
        simp [List.forIn_nil, pure, Except.pure]
    | cons x xs ih =>
        intro h
        have hx := h x (by simp)
        have htail : ∀ y ∈ xs, eq y zero = false := by
          intro y hy
          exact h y (by simp [hy])
        simpa [List.forIn_cons, hx, bind, Except.bind, pure, Except.pure] using ih htail
  have loopBad : ∀ (message : String) (xs : List Cwchar_t),
      (∃ x, x ∈ xs ∧ eq x zero = true) →
      (forIn xs PUnit.unit (fun x _ =>
        if eq x zero then
          (Except.error (.jl (.argumentError message)) : StringResult (ForInStep PUnit))
        else .ok (ForInStep.yield PUnit.unit)) : StringResult PUnit) =
          .error (.jl (.argumentError message)) := by
    intro message xs
    induction xs with
    | nil =>
        intro ⟨x, hx, _⟩
        simp at hx
    | cons x xs ih =>
        intro ⟨y, hy, hyzero⟩
        rcases List.mem_cons.mp hy with hxy | hy
        · subst y
          simp [List.forIn_cons, hyzero, bind, Except.bind, pure, Except.pure]
        · cases hzero : eq x zero with
          | true =>
              simp [List.forIn_cons, hzero, bind, Except.bind, pure, Except.pure]
          | false =>
              have htail : ∃ y, y ∈ xs ∧ eq y zero = true := ⟨y, hy, hyzero⟩
              simpa [List.forIn_cons, hzero, bind, Except.bind, pure, Except.pure] using ih htail
  constructor
  · intro prior p hprior hptr
    have hno : ∀ x ∈ prior, eq x zero = false := by
      intro x hx
      cases hvalue : eq x zero with
      | false => rfl
      | true =>
          have hbad : prior.any (fun y => eq y zero) = true :=
            List.any_eq_true.mpr ⟨x, hx, hvalue⟩
          rw [hprior] at hbad
          cases hbad
    let values := prior ++ [zero]
    let message := s!"embedded NULs are not allowed in C strings: {repr values}"
    have hloop := loopOk message prior hno
    have hdrop : values.dropLast = prior := by simp [values]
    have hlast : values.getLast? = some zero := by simp [values]
    have hzero : eq zero zero = true := (heq zero).2 rfl
    simpa [cconvertCwstringVector, values, message, hdrop, hlast, hzero, hptr,
      hloop, Functor.map, Except.map, stringResultThrow, pure, Except.pure,
      bind, Except.bind]
  constructor
  · intro prior hcontains
    rcases List.any_eq_true.mp hcontains with ⟨x, hx, hzero⟩
    let values := prior ++ [zero]
    let message := s!"embedded NULs are not allowed in C strings: {repr values}"
    refine ⟨message, ?_⟩
    have hzero0 : eq zero zero = true := (heq zero).2 rfl
    have hloop := loopBad message prior ⟨x, hx, hzero⟩
    simp [cconvertCwstringVector, values, message, hzero0, hloop, Functor.map,
      Except.map, stringResultThrow, pure, Except.pure, bind, Except.bind]
  constructor
  · rfl
  · intro prior last hprior hlastValue
    have hno : ∀ x ∈ prior, eq x zero = false := by
      intro x hx
      cases hvalue : eq x zero with
      | false => rfl
      | true =>
          have hbad : prior.any (fun y => eq y zero) = true :=
            List.any_eq_true.mpr ⟨x, hx, hvalue⟩
          rw [hprior] at hbad
          cases hbad
    let values := prior ++ [last]
    let message := s!"C string data must be NUL terminated: {repr values}"
    have hloop := loopOk (s!"embedded NULs are not allowed in C strings: {repr values}") prior hno
    have hdrop : values.dropLast = prior := by simp [values]
    have hlast : values.getLast? = some last := by simp [values]
    refine ⟨message, ?_⟩
    simp [cconvertCwstringVector, values, message, hdrop, hlast, hlastValue, hloop,
      Functor.map, Except.map, stringResultThrow, pure, Except.pure, bind, Except.bind]

theorem cwstringAbstract_proven : CwstringAbstractSpec := by
  intro S platform toString zero eq repr cconvertPtr s heq
  rcases cwstringVector_proven zero eq repr cconvertPtr heq with
    ⟨_, hvectorBad, _, _⟩
  have loopOk : ∀ (message : String) (xs : List Cwchar_t),
      (∀ x ∈ xs, eq x zero = false) →
      ((forIn xs PUnit.unit (fun x _ =>
        if eq x zero then
          match (throw (.jl (.argumentError message)) : StringResult (ForInStep PUnit)) with
          | .error err => .error err
          | .ok _ => .ok (ForInStep.yield PUnit.unit)
        else .ok (ForInStep.yield PUnit.unit))) : StringResult PUnit) = .ok PUnit.unit := by
    intro message xs
    induction xs with
    | nil =>
        intro _
        simp [List.forIn_nil, pure, Except.pure]
    | cons x xs ih =>
        intro h
        have hx := h x (by simp)
        have htail : ∀ y ∈ xs, eq y zero = false := by
          intro y hy
          exact h y (by simp [hy])
        simpa [List.forIn_cons, hx, bind, Except.bind, pure, Except.pure, Except.map] using ih htail
  constructor
  · intro result hresult
    cases hto : toString s with
    | error e => simp [cconvertCwstringAbstract, hto, bind, Except.bind, pure, Except.pure] at hresult
    | ok concrete =>
        cases ht : transcode (T := Cwchar_t) (Output := List Cwchar_t) concrete with
        | error e => simp [cconvertCwstringAbstract, hto, ht, bind, Except.bind, pure, Except.pure] at hresult
        | ok units =>
            have hvector : cconvertCwstringVector zero eq repr cconvertPtr
                (units ++ [zero]) = .ok result := by
              simpa [cconvertCwstringAbstract, hto, ht, bind, Except.bind, pure, Except.pure] using hresult
            have hno : units.any (fun unit => eq unit zero) = false := by
              cases hzero : units.any (fun unit => eq unit zero) with
              | false => rfl
              | true =>
                  obtain ⟨message, hbad⟩ := hvectorBad units hzero
                  rw [hvector] at hbad
                  cases hbad
            have hpoint : ∀ unit ∈ units, eq unit zero = false := by
              intro unit hunit
              cases hvalue : eq unit zero with
              | false => rfl
              | true =>
                  have hany : units.any (fun value => eq value zero) = true :=
                    List.any_eq_true.mpr ⟨unit, hunit, hvalue⟩
                  rw [hno] at hany
                  cases hany
            have hzero : eq zero zero = true := (heq zero).2 rfl
            have hloop := loopOk
              (s!"embedded NULs are not allowed in C strings: {repr (units ++ [zero])}")
              units hpoint
            have hptr : cconvertPtr (units ++ [zero]) = .ok result := by
              have hdrop : (units ++ [zero]).dropLast = units := by simp
              have hlast : (units ++ [zero]).getLast? = some zero := by simp
              simp only [cconvertCwstringVector, hdrop, hlast] at hvector
              change Except.bind
                (forIn units PUnit.unit (fun x _ =>
                  if eq x zero then
                    match (throw (Strings.SErr.jl (.argumentError
                      s!"embedded NULs are not allowed in C strings: {repr (units ++ [zero])}"))
                      : StringResult (ForInStep PUnit)) with
                    | .error err => .error err
                    | .ok _ => .ok (ForInStep.yield PUnit.unit)
                  else .ok (ForInStep.yield PUnit.unit)))
                (fun (_ : PUnit) =>
                  if eq zero zero then cconvertPtr (units ++ [zero]) else
                    throw (Strings.SErr.jl (.argumentError
                      s!"C string data must be NUL terminated: {repr (units ++ [zero])}"))) =
                  .ok result at hvector
              rw [hloop] at hvector
              simp [hzero, bind, Except.bind, pure, Except.pure] at hvector
              exact hvector
            exact ⟨concrete, units, rfl, ht, hno, hptr⟩
  · intro concrete units hstring htrans hcontains
    obtain ⟨message, hbad⟩ := hvectorBad units hcontains
    refine ⟨message, ?_⟩
    simp [cconvertCwstringAbstract, hstring, htrans, hbad, bind, Except.bind, pure, Except.pure] <;> rfl

theorem cwstringWindowsNul_refuted : ¬ CwstringWindowsNulSpec := by
  intro hspec
  let toString : JString → StringResult JString := fun value => .ok value
  let codeunits : JString → List UInt8 := fun value => value.bytes
  let repr : JString → String := fun _ => "overlong NUL"
  have hbytes : codeunits overlongNulString = overlongNulBytes := rfl
  have hno : overlongNulBytes.contains 0 = false := by decide
  have hwindow :
      cwstringWindows toString codeunits repr overlongNulString = .ok [0, 0] := by
    simp only [cwstringWindows, toString, codeunits, overlongNulString,
      bind, Except.bind, hno, if_false]
    change (do
      let wide ← transcode (T := UInt16) overlongNulBytes
      pure (wide ++ [0])) = .ok ([0, 0] : List UInt16)
    rw [overlongNulTranscode]
    rfl
  have hresult := hspec toString codeunits repr overlongNulString
    overlongNulString overlongNulBytes [0] [0, 0] rfl hbytes hno
    overlongNulTranscode hwindow
  have hzero : ([0, 0] : List UInt16).dropLast.contains 0 = true := by decide
  simp [hzero] at hresult
theorem unsafeWideLengthCase_proven :
    ∀ {T N : Type} [WideCodeUnit T] [JuliaIntegerArgument N]
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
        units.length = n.toNat := by
  intro T N wideCodeUnit integerArgument overload pointer stringFromBytes p len units bytes result
  dsimp only
  intro hnonnegative hlength hwrap hunits htrans hstring
  constructor
  · simp only [unsafeStringWideLength, hwrap, bind, Except.bind, transcodeToString,
      htrans, hstring]
  · rw [hunits, List.length_take, Nat.min_eq_left hlength]

private def unsafeWideScan {T : Type} [WideCodeUnit T]
    [TranscodeOverload UInt8 (List T) (List UInt8)]
    (pointer : PointerAccess T) (zero : T) (eq : T → T → Bool)
    (stringFromBytes : List UInt8 → StringResult JString) (p : Ptr T) :
    Nat → Nat → StringResult JString
  | 0, _ => .error JuliaLean.Strings.boundsErr
  | fuel + 1, n =>
      if eq (pointer.load p n) zero then
        unsafeStringWideLength pointer stringFromBytes p (Int.ofNat (n - 1))
      else unsafeWideScan pointer zero eq stringFromBytes p fuel (n + 1)

private theorem unsafeStringWide_scan {T : Type} [WideCodeUnit T]
    [TranscodeOverload UInt8 (List T) (List UInt8)]
    (pointer : PointerAccess T) (zero : T) (eq : T → T → Bool)
    (stringFromBytes : List UInt8 → StringResult JString) (p : Ptr T) :
    unsafeStringWide pointer zero eq stringFromBytes p =
      unsafeWideScan pointer zero eq stringFromBytes p (pointer.cells p).length 1 := by
  change unsafeStringWide.scan pointer zero eq stringFromBytes p
    (pointer.cells p).length 1 =
    unsafeWideScan pointer zero eq stringFromBytes p (pointer.cells p).length 1
  have hscan : ∀ fuel n,
      unsafeStringWide.scan pointer zero eq stringFromBytes p fuel n =
        unsafeWideScan pointer zero eq stringFromBytes p fuel n := by
    intro fuel
    induction fuel with
    | zero =>
        intro n
        rfl
    | succ fuel ih =>
        intro n
        simp only [unsafeStringWide.scan, unsafeWideScan]
        split
        · rfl
        · exact ih (n + 1)
  exact hscan _ _

private theorem unsafeWideScan_firstZero {T : Type} [WideCodeUnit T]
    [TranscodeOverload UInt8 (List T) (List UInt8)]
    (pointer : PointerAccess T) (zero : T) (eq : T → T → Bool)
    (stringFromBytes : List UInt8 → StringResult JString) (p : Ptr T)
    (result : JString) (fuel start count stop : Nat)
    (hstop : stop = start + count)
    (hfuel : count + 1 ≤ fuel)
    (hno : ∀ i, start ≤ i → i < stop → eq (pointer.load p i) zero = false)
    (hzero : eq (pointer.load p stop) zero = true)
    (hresult : unsafeStringWideLength pointer stringFromBytes p
      (Int.ofNat (stop - 1)) = .ok result) :
    unsafeWideScan pointer zero eq stringFromBytes p fuel start = .ok result := by
  induction count generalizing fuel start with
  | zero =>
      have hstop' : stop = start := by omega
      have hzero' : eq (pointer.load p start) zero = true := by
        simpa [hstop'] using hzero
      have hresult' : unsafeStringWideLength pointer stringFromBytes p
          (Int.ofNat (start - 1)) = .ok result := by
        simpa [hstop'] using hresult
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp [unsafeWideScan, hzero']
          exact hresult'
  | succ count ih =>
      have hfirst : eq (pointer.load p start) zero = false :=
        hno start (Nat.le_refl _) (by omega)
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hfuel' : count + 1 ≤ fuel := by omega
          have hstop' : stop = (start + 1) + count := by omega
          have hno' : ∀ i, start + 1 ≤ i → i < stop →
              eq (pointer.load p i) zero = false := by
            intro i hstart hbound
            exact hno i (by omega) hbound
          simp [unsafeWideScan, hfirst]
          exact ih fuel (start + 1) hstop' hfuel' hno'

theorem unsafeWide_proven : UnsafeWideSpec := by
  constructor
  · exact unsafeWideLengthCase_proven
  · intro T wideCodeUnit overload pointer zero eq stringFromBytes p count heq hno hzero hbound
      bytes result htrans hstring
    have hcount : count ≤ (pointer.cells p).length := by omega
    have hwrap : pointer.unsafeWrap p (Int.ofNat count) =
        .ok ((pointer.cells p).take count) := by
      apply pointer.wrapLaw
      · exact Int.natCast_nonneg _
      · simpa using hcount
    have hlength : unsafeStringWideLength pointer stringFromBytes p
        (Int.ofNat count) = .ok result := by
      change (do
        let units ← pointer.unsafeWrap p (Int.ofNat count)
        let bytes ← transcode (T := UInt8) units
        stringFromBytes bytes) = .ok result
      simp only [hwrap, bind, Except.bind, transcodeToString, htrans, hstring]
    have hno' : ∀ i, 1 ≤ i → i < count + 1 →
        eq (pointer.load p i) zero = false := by
      intro i hpos hlt
      exact hno i hpos (by omega)
    have hresult : unsafeStringWideLength pointer stringFromBytes p
        (Int.ofNat (count + 1 - 1)) = .ok result := by
      have hnat : count + 1 - 1 = count := by omega
      simpa [hnat] using hlength
    have hscan := unsafeWideScan_firstZero pointer zero eq stringFromBytes p result
      (pointer.cells p).length 1 count (count + 1) (by omega) (by omega)
      hno' hzero hresult
    rw [unsafeStringWide_scan]
    exact hscan
private theorem utf32CharUInt32BelowLimit (value : UInt32) (h : value < 0x00200000) :
    ∃ bits, JuliaLean.base.char.char_UInt32 value = .ok bits := by
  let payload :=
    ((JuliaLean.base.char.shl32 value 0) &&& 0x0000003f) |||
      ((JuliaLean.base.char.shl32 value 2) &&& 0x00003f00) |||
      ((JuliaLean.base.char.shl32 value 4) &&& 0x003f0000) |||
      ((JuliaLean.base.char.shl32 value 6) &&& 0x3f000000)
  let encoded : UInt32 :=
    if value < 0x00000800 then
      (JuliaLean.base.char.shl32 payload 16) ||| 0xc0800000
    else if value < 0x00010000 then
      (JuliaLean.base.char.shl32 payload 8) ||| 0xe0808000
    else
      (JuliaLean.base.char.shl32 payload 0) ||| 0xf0808080
  let bits : UInt32 := if value < 0x80 then JuliaLean.base.char.shl32 value 24 else encoded
  refine ⟨bits, ?_⟩
  by_cases hsmall : value < 0x80
  · simp [JuliaLean.base.char.char_UInt32, payload, encoded, bits, hsmall, h] <;> rfl
  · by_cases hshort : value < 0x00000800
    · simp [JuliaLean.base.char.char_UInt32, payload, encoded, bits, hsmall, hshort, h] <;> rfl
    · by_cases hmedium : value < 0x00010000
      · simp [JuliaLean.base.char.char_UInt32, payload, encoded, bits, hsmall, hshort, hmedium, h] <;> rfl
      · simp [JuliaLean.base.char.char_UInt32, payload, encoded, bits, hsmall, hshort, hmedium, h] <;> rfl

private theorem utf32CharUInt32AtOrAboveLimit (value : UInt32)
    (h : 0x00200000 ≤ value) :
    JuliaLean.base.char.char_UInt32 value = .error (.codePointError value) := by
  have hval : 2097152 ≤ value.toNat := by
    rw [UInt32.le_iff_toNat_le] at h
    have hbound : (0x00200000 : UInt32).toNat = 2097152 := rfl
    rw [hbound] at h
    exact h
  have hsmall : ¬ value < 0x80 := by
    rw [UInt32.lt_iff_toNat_lt]
    have hbound : (0x80 : UInt32).toNat = 128 := rfl
    rw [hbound]
    omega
  have hlimit : ¬ value < 0x00200000 := by
    rw [UInt32.lt_iff_toNat_lt]
    have hbound : (0x00200000 : UInt32).toNat = 2097152 := rfl
    rw [hbound]
    omega
  simp [JuliaLean.base.char.char_UInt32, hsmall, hlimit,
    JuliaLean.base.char.throw_code_point_err, bind, Except.bind, pure, Except.pure]

private theorem utf32CharErrorAgreesUnique
    (source : JuliaLean.base.char.CharError) (left right : JuliaLean.Strings.SErr)
    (hl : CharErrorAgrees source left) (hr : CharErrorAgrees source right) :
    left = right := by
  cases source with
  | invalidChar sourceValue =>
      cases left with
      | invalidChar leftValue =>
          cases right with
          | invalidChar rightValue =>
              simp only [CharErrorAgrees] at hl hr
              have h : HEq leftValue rightValue := HEq.trans (HEq.symm hl) hr
              exact congrArg JuliaLean.Strings.SErr.invalidChar (eq_of_heq h)
          | _ => simp [CharErrorAgrees] at hr
      | _ => simp [CharErrorAgrees] at hl
  | codePointError sourceValue =>
      cases left with
      | codePointError leftValue =>
          cases right with
          | codePointError rightValue =>
              simp only [CharErrorAgrees] at hl hr
              have h : HEq leftValue rightValue := HEq.trans (HEq.symm hl) hr
              exact congrArg JuliaLean.Strings.SErr.codePointError (eq_of_heq h)
          | _ => simp [CharErrorAgrees] at hr
      | _ => simp [CharErrorAgrees] at hl
  | unicodeError _ => cases left <;> simp [CharErrorAgrees] at hl
  | boundsError =>
      cases left with
      | jl leftError =>
          cases leftError with
          | boundsError =>
              cases right with
              | jl rightError =>
                  cases rightError with
                  | boundsError => rfl
                  | _ => simp [CharErrorAgrees] at hr
              | _ => simp [CharErrorAgrees] at hr
          | _ => simp [CharErrorAgrees] at hl
      | _ => simp [CharErrorAgrees] at hl
  | foreign sourceError =>
      cases left with
      | jl leftError =>
          cases right with
          | jl rightError =>
              simp only [CharErrorAgrees] at hl hr
              exact congrArg JuliaLean.Strings.SErr.jl (hl.symm.trans hr)
          | _ => simp [CharErrorAgrees] at hr
      | _ => simp [CharErrorAgrees] at hl
  | showError sourceError =>
      cases left with
      | showError leftError =>
          cases right with
          | showError rightError =>
              simp only [CharErrorAgrees] at hl hr
              exact congrArg JuliaLean.Strings.SErr.showError (hl.symm.trans hr)
          | _ => simp [CharErrorAgrees] at hr
      | _ => simp [CharErrorAgrees] at hl

private theorem utf32Runtime32ToCharOk {T : Type} (runtime : Char32ToUtf8Runtime T)
    (source : T → JuliaLean.base.char.CharResult UInt32)
    (law : ∀ value, CharResultAgrees JuliaChar.mk (source value) (runtime.toChar value))
    (value : T) (bits : UInt32) (hsource : source value = .ok bits) :
    runtime.toChar value = .ok (JuliaChar.mk bits) := by
  have hrel := law value
  rw [hsource] at hrel
  cases hrun : runtime.toChar value with
  | error error => simp [CharResultAgrees, hrun] at hrel
  | ok result =>
      simp [CharResultAgrees, hrun] at hrel
      subst result
      rfl

private theorem utf32Runtime32ToCharError {T : Type} (runtime : Char32ToUtf8Runtime T)
    (source : T → JuliaLean.base.char.CharResult UInt32)
    (law : ∀ value, CharResultAgrees JuliaChar.mk (source value) (runtime.toChar value))
    (value : T) (sourceError : JuliaLean.base.char.CharError)
    (error : JuliaLean.Strings.SErr)
    (hsource : source value = .error sourceError)
    (hagrees : CharErrorAgrees sourceError error) :
    runtime.toChar value = .error error := by
  have hrel := law value
  rw [hsource] at hrel
  cases hrun : runtime.toChar value with
  | ok result => simp [CharResultAgrees, hrun] at hrel
  | error actual =>
      have hagrees' : CharErrorAgrees sourceError actual := by
        simpa [CharResultAgrees, hrun] using hrel
      have heq := utf32CharErrorAgreesUnique sourceError actual error hagrees' hagrees
      exact congrArg Except.error heq

private theorem utf32ListFoldlMErrorAt {α β ε : Type}
    (step : β → α → Except ε β) (initial : β) (prior suffix : List α)
    (bad : α) (error : ε)
    (hgood : ∀ accumulator value, value ∈ prior →
      ∃ next, step accumulator value = .ok next)
    (hbad : ∀ accumulator, step accumulator bad = .error error) :
    List.foldlM step initial (prior ++ bad :: suffix) = .error error := by
  induction prior generalizing initial with
  | nil =>
      simp only [List.nil_append, List.foldlM_cons]
      rw [hbad initial]
      rfl
  | cons value rest ih =>
      obtain ⟨next, hnext⟩ := hgood initial value (by simp)
      have htail : ∀ accumulator item, item ∈ rest →
          ∃ next, step accumulator item = .ok next := by
        intro accumulator item hitem
        exact hgood accumulator item (by simp [hitem])
      simp only [List.cons_append, List.foldlM_cons]
      rw [hnext]
      simpa only [bind, Except.bind] using ih next htail

theorem transcode32To8Error_proven : Utf32ToUtf8ErrorSpec := by
  constructor
  · intro _ runtime prior suffix bad hlaw hprior hbad
    let source : UInt32 → JuliaLean.base.char.CharResult UInt32 :=
      JuliaLean.base.char.char_UInt32
    have law : ∀ value, CharResultAgrees JuliaChar.mk (source value) (runtime.toChar value) := by
      intro value
      exact hlaw value
    let step : runtime.Buffer → UInt32 → StringResult runtime.Buffer :=
      fun buffer value => do
        let character ← runtime.toChar value
        pure (runtime.printChar buffer character)
    have hgood : ∀ accumulator value, value ∈ prior →
        ∃ next, step accumulator value = .ok next := by
      intro accumulator value hvalue
      have hlt : value < 0x00200000 := by
        have htest := (List.all_eq_true.mp hprior) value hvalue
        exact of_decide_eq_true htest
      obtain ⟨bits, hchar⟩ := utf32CharUInt32BelowLimit value hlt
      have hconvert := utf32Runtime32ToCharOk runtime source law value bits hchar
      exact ⟨runtime.printChar accumulator (JuliaChar.mk bits), by
        simp [step, hconvert, bind, Except.bind, pure, Except.pure]⟩
    have hconvert : runtime.toChar bad = .error (.codePointError bad) :=
      utf32Runtime32ToCharError runtime source law bad (.codePointError bad)
        (.codePointError bad) (utf32CharUInt32AtOrAboveLimit bad hbad)
        (by simp [CharErrorAgrees])
    have hbadStep : ∀ accumulator, step accumulator bad = .error (.codePointError bad) := by
      intro accumulator
      simp [step, hconvert, bind, Except.bind, pure, Except.pure]
    have hfold := utf32ListFoldlMErrorAt step runtime.initialBuffer prior suffix bad
      (.codePointError bad) hgood hbadStep
    change transcode32To8 runtime.initialBuffer runtime.toChar runtime.printChar
      runtime.takeBuffer (prior ++ bad :: suffix) = .error (.codePointError bad)
    change (do
      let buffer ← List.foldlM step runtime.initialBuffer (prior ++ bad :: suffix)
      pure (runtime.takeBuffer buffer)) = .error (.codePointError bad)
    simp only [hfold, bind, Except.bind, pure, Except.pure]
  · intro _ runtime prior suffix bad sourceError error hlaw hprior hbad hagrees
    let source : Int32 → JuliaLean.base.char.CharResult UInt32 := fun value =>
      JuliaLean.base.char.constructor_Number_AbstractChar
        (fun input : Int32 => JuliaLean.base.char.exactUInt32 input.toInt)
        JuliaLean.base.char.char_UInt32 value
    have law : ∀ value, CharResultAgrees JuliaChar.mk (source value) (runtime.toChar value) := by
      intro value
      exact hlaw value
    let step : runtime.Buffer → Int32 → StringResult runtime.Buffer :=
      fun buffer value => do
        let character ← runtime.toChar value
        pure (runtime.printChar buffer character)
    have hgood : ∀ accumulator value, value ∈ prior →
        ∃ next, step accumulator value = .ok next := by
      intro accumulator value hvalue
      obtain ⟨bits, hchar⟩ := hprior value hvalue
      have hconvert := utf32Runtime32ToCharOk runtime source law value bits hchar
      exact ⟨runtime.printChar accumulator (JuliaChar.mk bits), by
        simp [step, hconvert, bind, Except.bind, pure, Except.pure]⟩
    have hconvert := utf32Runtime32ToCharError runtime source law bad sourceError error hbad hagrees
    have hbadStep : ∀ accumulator, step accumulator bad = .error error := by
      intro accumulator
      simp [step, hconvert, bind, Except.bind, pure, Except.pure]
    have hfold := utf32ListFoldlMErrorAt step runtime.initialBuffer prior suffix bad error
      hgood hbadStep
    change transcode32To8 runtime.initialBuffer runtime.toChar runtime.printChar
      runtime.takeBuffer (prior ++ bad :: suffix) = .error error
    change (do
      let buffer ← List.foldlM step runtime.initialBuffer (prior ++ bad :: suffix)
      pure (runtime.takeBuffer buffer)) = .error error
    simp only [hfold, bind, Except.bind, pure, Except.pure]




theorem cstringUnsafeConvertFaithful_proven : CStringNulSpec := cstringNul_proven

/-! ## Small `Except` steps

Proofs below rewrite one `do` step at a time with these lemmas instead of unfolding
`bind`: `simp only [bind, Except.bind]` also rewrites the error-message branches, and the
kernel then recurses deeply on the interpolated message strings. -/

theorem exceptBindOk {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Except.ok x >>= f) = f x := rfl

theorem exceptBindError {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = Except.error e := rfl

theorem cwstringWindows_proven : CwstringWindowsSpec := by
  intro S toString codeunits repr s concrete bytes units hstring hbytes hno htrans
  unfold cwstringWindows
  rw [hstring, exceptBindOk]
  dsimp only
  rw [hbytes, hno, ite_cond_eq_false _ _ (eq_false Bool.false_ne_true)]
  rw [htrans, exceptBindOk]
  rfl

/-! ## Index arithmetic -/

theorem ixVal (k : Int) (h1 : -(2 ^ 63) ≤ k) (h2 : k < 2 ^ 63) : (ix k).val = k := by
  show wrapInt .i64 k = k
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  constructor <;> simp <;> omega

theorem indexAddVal (a b : Index) (h1 : -(2 ^ 63) ≤ a.val + b.val)
    (h2 : a.val + b.val < 2 ^ 63) : (a + b).val = a.val + b.val := by
  show wrapInt .i64 (a.val + b.val) = a.val + b.val
  apply wrapInt_of_inRange
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
  constructor <;> simp <;> omega

theorem indexAddOne (i : Index) (h0 : 0 ≤ i.val) (h : i.val + 1 < 2 ^ 63) :
    (i + ix 1).val = i.val + 1 := by
  rw [indexAddVal i (ix 1) (by rw [ixVal 1 (by omega) (by omega)]; omega)
    (by rw [ixVal 1 (by omega) (by omega)]; omega), ixVal 1 (by omega) (by omega)]

/-- `indexAddOne` stated with `JuliaLean.Strings.ix`, the spelling the string model uses. -/
theorem indexAddOneS (i : Index) (h0 : 0 ≤ i.val) (h : i.val + 1 < 2 ^ 63) :
    (i + JuliaLean.Strings.ix 1).val = i.val + 1 :=
  indexAddOne i h0 h

theorem idPureSnd {α β : Type} (a : α) (b : β) : (pure (a, b) : Id (α × β)).snd = b := rfl

/-! ## `transcode` through an overload instance

`transcode src` and an overload body such as `transcodeString32 conv src` are definitionally
equal, but a kernel check of that equality unfolds the body first and then evaluates string
iteration or index wrapping on a symbolic input until it recurses too deeply. These two
lemmas only ever unfold the instance constant to its constructor. -/

theorem transcode_mk {T S Output : Type} (f : S → StringResult Output) (s : S) :
    @transcode T S Output ⟨f⟩ s = f s := rfl

theorem transcode_of_run {T S Output : Type} (inst : TranscodeOverload T S Output)
    (f : S → StringResult Output) (hinst : inst = ⟨f⟩) (s : S) (r : StringResult Output)
    (h : f s = r) : @transcode T S Output inst s = r := by
  rw [hinst, transcode_mk]
  exact h

/-! ## String iteration advances the index -/

theorem iterateContinued_index (nc : JString → Index) (cu : JString → Index → UInt8)
    (s : JString) (i : Index) (u : UInt32) (h0 : 0 ≤ i.val) (h : i.val < 2 ^ 62) :
    i.val + 1 ≤ (JuliaLean.base.strings.string.iterateContinued nc cu s i u).2.val := by
  have e1 := indexAddOneS i h0 (by omega)
  have e2 := indexAddOneS (i + JuliaLean.Strings.ix 1) (by omega) (by omega)
  have e3 := indexAddOneS (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)
    (by omega) (by omega)
  have e4 := indexAddOneS
    (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)
    (by omega) (by omega)
  unfold JuliaLean.base.strings.string.iterateContinued
  simp only [Id.run]
  repeat' split
  all_goals (rw [idPureSnd]; omega)

theorem remU64Val (i : Index) : (JInt.rem .u64 i).val = wrapInt .u64 i.val := rfl
theorem subU64Val (a b : JInt .u64) : (a - b).val = wrapInt .u64 (a.val - b.val) := rfl
theorem litU64One : (JInt.lit .u64 1).val = 1 := by
  simp [JInt.lit, JInt.wrap, wrapInt, IntTy.signed, IntTy.bits]

/-- A successful `iterate(s, i)` starts at a valid byte position and moves forward. -/
theorem iterateCstring_some (s : JString) (i : Index) (c : UInt32) (j : Index)
    (h : iterateCstringString s i = some (c, j)) :
    1 ≤ i.val ∧ i.val ≤ s.bytes.length ∧ i.val + 1 ≤ j.val := by
  have hs := s.small
  have hL : (ix (s.bytes.length : Int)).val = s.bytes.length := ixVal _ (by omega) (by omega)
  have hi := i.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hi
  unfold iterateCstringString JuliaLean.base.strings.string.iterateString at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hcond
    have hc : (JInt.rem .u64 i - JInt.lit .u64 1).val < (ix (s.bytes.length : Int)).val := by
      simpa using hcond
    rw [subU64Val, remU64Val, litU64One, hL] at hc
    simp [wrapInt, IntTy.signed, IntTy.bits] at hc
    have hb : 1 ≤ i.val ∧ i.val ≤ s.bytes.length := by
      simp at hi
      omega
    refine ⟨hb.1, hb.2, ?_⟩
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [indexAddOne i (by omega) (by omega)]
      omega
    · simp only [Option.some.injEq] at h
      have hj := congrArg Prod.snd h
      simp only at hj
      rw [← hj]
      exact iterateContinued_index _ _ s i _ (by omega) (by omega)

theorem cstringPrefix_advance (s : JString) : ∀ (cs : List UInt32) (i cursor : Index),
    cstringStringPrefix s cs i cursor → i.val + cs.length ≤ cursor.val := by
  intro cs
  induction cs with
  | nil =>
    intro i cursor h
    simp only [cstringStringPrefix] at h
    subst h
    simp
  | cons c cs ih =>
    intro i cursor h
    simp only [cstringStringPrefix] at h
    obtain ⟨next, hit, hrest⟩ := h
    have h1 := (iterateCstring_some s i c next hit).2.2
    have h2 := ih next cursor hrest
    simp only [List.length_cons]
    omega

/-! ## The UTF-32 loop with the iteration function as a parameter

The equation lemmas of `transcodeString32Loop` cannot be generated: their proof whnf's
`iterateCstringString src i` on a symbolic string. `loop32With` takes the iteration as a
parameter, so its equations are cheap, and it agrees with the model loop definitionally. -/

def loop32With {T : Type} (g : Index → Option (UInt32 × Index))
    (conv : UInt32 → StringResult T) : Nat → Index → List T → StringResult (List T)
  | 0, _, _ => .error .assertion
  | fuel + 1, i, out =>
      match g i with
      | none => .ok out.reverse
      | some (c, next) => do
          let v ← conv c
          loop32With g conv fuel next (v :: out)

section
attribute [local irreducible] iterateCstringString
set_option smartUnfolding false in
theorem transcodeString32Loop_eq_with {T : Type} (conv : UInt32 → StringResult T)
    (src : JString) (k : Nat) (i : Index) (out : List T) :
    transcodeString32Loop conv src k i out =
      loop32With (iterateCstringString src) conv k i out :=
  rfl
end

theorem loop32With_none {T : Type} (g : Index → Option (UInt32 × Index))
    (conv : UInt32 → StringResult T) (k : Nat) (i : Index) (out : List T)
    (h : g i = none) : loop32With g conv (k + 1) i out = .ok out.reverse := by
  simp only [loop32With, h]

theorem loop32With_some {T : Type} (g : Index → Option (UInt32 × Index))
    (conv : UInt32 → StringResult T) (k : Nat) (i : Index) (out : List T)
    (c : UInt32) (j : Index) (h : g i = some (c, j)) :
    loop32With g conv (k + 1) i out =
      (conv c >>= fun v => loop32With g conv k j (v :: out)) := by
  simp only [loop32With, h]

/-- Invariant of the UTF-32 loop: after a converted prefix `cs` it stops at the first
conversion error. -/
theorem string32Loop_prefixError {T : Type} (s : JString) (conv : UInt32 → StringResult T)
    (bad : UInt32) (next : Index) (e : JuliaLean.Strings.SErr) (cursor : Index)
    (hbad : conv bad = .error e) (hcur : iterateCstringString s cursor = some (bad, next)) :
    ∀ (cs : List UInt32) (i : Index) (fuel : Nat) (out : List T),
      cstringStringPrefix s cs i cursor → (∀ c ∈ cs, ∃ v, conv c = .ok v) →
      cs.length < fuel →
      loop32With (iterateCstringString s) conv fuel i out = .error e := by
  intro cs
  induction cs with
  | nil =>
    intro i fuel out hp _ hf
    simp only [cstringStringPrefix] at hp
    subst hp
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    rw [loop32With_some _ _ _ _ _ _ _ hcur, hbad, exceptBindError]
  | cons c cs ih =>
    intro i fuel out hp hok hf
    simp only [cstringStringPrefix] at hp
    obtain ⟨next', hit, hrest⟩ := hp
    obtain ⟨v, hv⟩ := hok c (by simp)
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    rw [loop32With_some _ _ _ _ _ _ _ hit, hv, exceptBindOk]
    exact ih next' k (v :: out) hrest (fun c' hc' => hok c' (by simp [hc']))
      (by simp at hf; omega)

/-! ## Character-conversion agreement -/

theorem charErrorAgrees_bounds {e : JuliaLean.Strings.SErr}
    (h : CharErrorAgrees .boundsError e) : e = .jl .boundsError := by
  cases e with
  | jl x => cases x <;> first | rfl | exact False.elim h
  | _ => exact False.elim h

/-- Each base `CharError` agrees with at most one runtime error. -/
theorem charErrorAgrees_unique {se : JuliaLean.base.char.CharError}
    {e1 e2 : JuliaLean.Strings.SErr}
    (h1 : CharErrorAgrees se e1) (h2 : CharErrorAgrees se e2) : e1 = e2 := by
  cases se with
  | invalidChar c =>
    cases e1 <;> try exact False.elim h1
    cases e2 <;> try exact False.elim h2
    exact congrArg _ (eq_of_heq (HEq.trans (HEq.symm h1) h2))
  | codePointError c =>
    cases e1 <;> try exact False.elim h1
    cases e2 <;> try exact False.elim h2
    exact congrArg _ (eq_of_heq (HEq.trans (HEq.symm h1) h2))
  | unicodeError u => exact False.elim h1
  | boundsError => rw [charErrorAgrees_bounds h1, charErrorAgrees_bounds h2]
  | foreign x =>
    cases e1 <;> try exact False.elim h1
    cases e2 <;> try exact False.elim h2
    have h1' : x = _ := h1
    have h2' : x = _ := h2
    rw [← h1', ← h2']
  | showError sourceError =>
    cases e1 with
    | showError leftError =>
      cases e2 with
      | showError rightError =>
        simp only [CharErrorAgrees] at h1 h2
        exact congrArg JuliaLean.Strings.SErr.showError (h1.symm.trans h2)
      | _ => exact False.elim h2
    | _ => exact False.elim h1

theorem charResultAgrees_ok {T : Type} {src : JuliaLean.base.char.CharResult T}
    {act : StringResult T} {v : T}
    (h : CharResultAgrees id src act) (hs : src = .ok v) : act = .ok v := by
  subst hs
  cases act with
  | ok r => exact congrArg Except.ok h
  | error e => exact False.elim h

theorem charResultAgrees_error {T : Type} {src : JuliaLean.base.char.CharResult T}
    {act : StringResult T} {se : JuliaLean.base.char.CharError} {e : JuliaLean.Strings.SErr}
    (h : CharResultAgrees id src act) (hs : src = .error se) (he : CharErrorAgrees se e) :
    act = .error e := by
  subst hs
  cases act with
  | ok r => exact False.elim h
  | error e' => exact congrArg Except.error (charErrorAgrees_unique h he)

/-- `transcode(T, s)` for `T` in `Int32, UInt32` returns the first conversion error after
a converted prefix, for any conversion that agrees with a base `Char` conversion. -/
theorem transcodeString32_error {T : Type} [Utf32CodeUnit T]
    (source : UInt32 → JuliaLean.base.char.CharResult T) (conv : UInt32 → StringResult T)
    (hlaw : ∀ bits, CharResultAgrees id (source bits) (conv bits))
    (s : JString) (cs : List UInt32) (cursor : Index) (bad : UInt32) (next : Index)
    (se : JuliaLean.base.char.CharError) (e : JuliaLean.Strings.SErr)
    (hp : cstringStringPrefix s cs (ix 1) cursor)
    (hok : ∀ c ∈ cs, ∃ v, source c = .ok v)
    (hit : iterateCstringString s cursor = some (bad, next))
    (hbad : source bad = .error se) (he : CharErrorAgrees se e) :
    transcodeString32 conv s = .error e := by
  have hadv := cstringPrefix_advance s cs (ix 1) cursor hp
  have hcur := iterateCstring_some s cursor bad next hit
  rw [ixVal 1 (by omega) (by omega)] at hadv
  unfold transcodeString32
  rw [transcodeString32Loop_eq_with]
  exact string32Loop_prefixError s conv bad next e cursor
    (charResultAgrees_error (hlaw bad) hbad he) hit cs (ix 1) _ [] hp
    (fun c hc => by
      obtain ⟨v, hv⟩ := hok c hc
      exact ⟨v, charResultAgrees_ok (hlaw c) hv⟩)
    (by omega)

theorem transcodeString32Error_proven : Utf32StringErrorSpec := by
  constructor
  · intro conversion s cs cursor bad next se e hlaw hp hok hit hbad he
    exact transcode_of_run _ (transcodeString32 conversion.convertChar) rfl s _
      (transcodeString32_error _ conversion.convertChar hlaw s cs cursor bad next se e
        hp hok hit hbad he)
  · intro conversion s cs cursor bad next se e hlaw hp hok hit hbad he
    exact transcode_of_run _ (transcodeString32 conversion.convertChar) rfl s _
      (transcodeString32_error _ conversion.convertChar hlaw s cs cursor bad next se e
        hp hok hit hbad he)

/-! ## `transcode(UInt32, "a\xffb")` throws -/

theorem codepointChar_error (bits : UInt32) (se : JuliaLean.base.char.CharError)
    (h : JuliaLean.base.char.codepoint_Char JuliaLean.base.char.charBitOps bits = .error se) :
    se = .invalidChar bits := by
  revert h
  unfold JuliaLean.base.char.codepoint_Char JuliaLean.base.char.uint32_Char
  dsimp only
  split
  · intro h; cases h
  · split
    · intro h
      simp only [JuliaLean.base.char.throw_invalid_char] at h
      cases h
      rfl
    · intro h; cases h

/-- A conversion that agrees with `codepoint(::Char)` on every bit pattern. -/
def codepointStringConversion (bits : UInt32) : StringResult UInt32 :=
  match JuliaLean.base.char.codepoint_Char JuliaLean.base.char.charBitOps bits with
  | .ok v => .ok v
  | .error _ => .error (.invalidChar bits)

theorem codepointStringConversion_law :
    Utf32CharacterConversionLaw ⟨codepointStringConversion⟩ := by
  intro bits
  show CharResultAgrees id
    (JuliaLean.base.char.codepoint_Char JuliaLean.base.char.charBitOps bits)
    (codepointStringConversion bits)
  unfold codepointStringConversion
  cases h : JuliaLean.base.char.codepoint_Char JuliaLean.base.char.charBitOps bits with
  | ok v => exact rfl
  | error se =>
    obtain rfl := codepointChar_error bits se h
    exact HEq.rfl

/-- `"a\xffb"`. -/
def strAFFB : JString := ⟨[0x61, 0xff, 0x62], by decide⟩

theorem utf32StringTotal_refuted : ¬ Utf32StringTotalSpec := by
  intro h
  obtain ⟨units, hunits⟩ :=
    @h inferInstance ⟨codepointStringConversion⟩ strAFFB codepointStringConversion_law
  have h1 : iterateCstringString strAFFB (ix 1) = some (0x61000000, ix 2) := by decide
  have h2 : iterateCstringString strAFFB (ix 2) = some (0xff000000, ix 3) := by decide
  have hsrc1 : JuliaLean.base.char.codepoint_Char JuliaLean.base.char.charBitOps
      (0x61000000 : UInt32) = .ok 0x61 := rfl
  have hsrc2 : JuliaLean.base.char.codepoint_Char JuliaLean.base.char.charBitOps
      (0xff000000 : UInt32) = .error (.invalidChar (0xff000000 : UInt32)) := rfl
  have herr := transcodeString32_error
    (JuliaLean.base.char.codepoint_Char JuliaLean.base.char.charBitOps)
    codepointStringConversion codepointStringConversion_law strAFFB [0x61000000] (ix 2)
    0xff000000 (ix 3) (.invalidChar (0xff000000 : UInt32)) (.invalidChar 0xff000000)
    ⟨ix 2, h1, rfl⟩
    (fun c hc => by
      simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨_, hsrc1⟩)
    h2 hsrc2 HEq.rfl
  have key : (Except.ok units : StringResult (List UInt32)) =
      .error (.invalidChar 0xff000000) :=
    hunits.symm.trans (transcode_of_run _ (transcodeString32 codepointStringConversion) rfl
      strAFFB _ herr)
  cases key

/-! ## UTF-8 to UTF-16: every input returns -/

theorem indexVal_lt (i : Index) : i.val < 2 ^ 63 := by
  have := i.property.2
  simp only [IntTy.max, IntTy.signed, IntTy.bits] at this
  simp at this
  omega

theorem okBind {ε α β : Type} {x : Except ε α} {f : α → Except ε β}
    (hx : ∃ v, x = .ok v) (hf : ∀ v, ∃ r, f v = .ok r) : ∃ r, (x >>= f) = .ok r := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨r, hr⟩ := hf v
  exact ⟨r, by rw [hv, exceptBindOk, hr]⟩

/-- Case split on an `if` without `split`, whose internal `simp` exceeds its step limit on
the loop bodies below. -/
theorem iteOk {ε α : Type} {c : Prop} [Decidable c] {t e : Except ε α}
    (ht : c → ∃ r, t = .ok r) (he : ¬c → ∃ r, e = .ok r) :
    ∃ r, (if c then t else e) = .ok r := by
  by_cases h : c
  · rw [if_pos h]; exact ht h
  · rw [if_neg h]; exact he h

/-- One iteration of `utf8ToUtf16Loop` (the model body verbatim), with the next iteration
as the parameter `next`. Generating the model loop's own equation lemmas exceeds `simp`'s
step limit; `utf8Loop_succ` unfolds one iteration by `rfl` instead. -/
def utf8Step {V : Type}
    (read : V → Index → StringResult UInt8)
    (push : List UInt16 → List UInt16 → StringResult (List UInt16))
    (src : V) (n : Index)
    (next : Index → UInt8 → List UInt16 → StringResult (List UInt16))
    (i : Index) (a : UInt8) (dst : List UInt16) : StringResult (List UInt16) := do
      if decide (i < n) && utf8Lead a then
        let b ← read src (i + ix 1)
        let i := i + ix 1
        if decide (-64 ≤ signedByte b) || (a == 0xf4 && 0x8f < b) then
          next i b (← push dst [a.toUInt16])
        else if a < 0xe0 then
          let dst ← push dst [utf8Two a b]
          if i < n then
            let nextByte ← read src (i + ix 1)
            next (i + ix 1) nextByte dst
          else pure dst
        else if i < n then
          let c ← read src (i + ix 1)
          let i := i + ix 1
          if decide (-64 ≤ signedByte c) then
            next i c (← push dst [a.toUInt16, b.toUInt16])
          else if a < 0xf0 then
            let dst ← push dst [utf8Three a b c]
            if i < n then
              let nextByte ← read src (i + ix 1)
              next (i + ix 1) nextByte dst
            else pure dst
          else if i < n then
            let d ← read src (i + ix 1)
            let i := i + ix 1
            if decide (-64 ≤ signedByte d) then
              next i d (← push dst [a.toUInt16, b.toUInt16, c.toUInt16])
            else if a == 0xf0 && b < 0x90 then
              let dst ← push dst [utf8Three b c d]
              if i < n then
                let nextByte ← read src (i + ix 1)
                next (i + ix 1) nextByte dst
              else pure dst
            else
              let dst ← push dst [utf8FourHigh a b c, utf8FourLow c d]
              if i < n then
                let nextByte ← read src (i + ix 1)
                next (i + ix 1) nextByte dst
              else pure dst
          else
            push dst [a.toUInt16, b.toUInt16, c.toUInt16]
        else
          push dst [a.toUInt16, b.toUInt16]
      else
        let dst ← push dst [a.toUInt16]
        if i < n then
          let nextByte ← read src (i + ix 1)
          next (i + ix 1) nextByte dst
        else pure dst

theorem utf8Loop_succ {V : Type} (read : V → Index → StringResult UInt8)
    (push : List UInt16 → List UInt16 → StringResult (List UInt16)) (src : V) (n : Index)
    (fuel : Nat) (i : Index) (a : UInt8) (dst : List UInt16) :
    utf8ToUtf16Loop read push src n (fuel + 1) i a dst =
      utf8Step read push src n (utf8ToUtf16Loop read push src n fuel) i a dst := rfl

/-- Invariant of the UTF-8 to UTF-16 loop: it returns whenever every in-bounds read and
every push returns. Each iteration consumes at least one byte, so `n - i + 1` fuel
suffices, and every read index lies in `1..n`. -/
theorem utf8ToUtf16Loop_ok {V : Type} (read : V → Index → StringResult UInt8)
    (push : List UInt16 → List UInt16 → StringResult (List UInt16)) (src : V) (n : Index)
    (hread : ∀ k : Index, 1 ≤ k.val → k.val ≤ n.val → ∃ b, read src k = .ok b)
    (hpush : ∀ d m, ∃ r, push d m = .ok r) :
    ∀ (fuel : Nat) (i : Index) (a : UInt8) (dst : List UInt16),
      1 ≤ i.val → i.val ≤ n.val → n.val + 1 ≤ i.val + fuel →
      ∃ r, utf8ToUtf16Loop read push src n fuel i a dst = .ok r := by
  have hn := indexVal_lt n
  intro fuel
  induction fuel with
  | zero => intro i a dst h1 h2 h3; omega
  | succ fuel ih =>
    intro i a dst h1 h2 h3
    have step : ∀ (j : Index) (b : UInt8) (d : List UInt16), i.val < j.val → j.val ≤ n.val →
        ∃ r, utf8ToUtf16Loop read push src n fuel j b d = .ok r :=
      fun j b d hj1 hj2 => ih j b d (by omega) hj2 (by omega)
    have cont : ∀ (j : Index) (d : List UInt16), i.val ≤ j.val → j.val ≤ n.val →
        ∃ r, (if j < n then (read src (j + ix 1) >>= fun next =>
          utf8ToUtf16Loop read push src n fuel (j + ix 1) next d) else pure d) = .ok r := by
      intro j d hj1 hj2
      refine iteOk (fun hlt => ?_) (fun _ => ⟨d, rfl⟩)
      have hlt' : j.val < n.val := hlt
      have e := indexAddOne j (by omega) (by omega)
      exact okBind (hread _ (by omega) (by omega)) (fun b => step _ _ _ (by omega) (by omega))
    rw [utf8Loop_succ]
    delta utf8Step
    dsimp only
    refine iteOk (fun hlead => ?_)
      (fun _ => okBind (hpush _ _) (fun d => cont _ d (by omega) (by omega)))
    have hi : i.val < n.val := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hlead
      exact hlead.1
    have e1 := indexAddOne i (by omega) (by omega)
    refine okBind (hread _ (by omega) (by omega)) (fun b => ?_)
    try dsimp only
    refine iteOk (fun _ => okBind (hpush _ _) (fun d => step _ _ _ (by omega) (by omega)))
      (fun _ => ?_)
    refine iteOk (fun _ => okBind (hpush _ _) (fun d => cont _ d (by omega) (by omega)))
      (fun _ => ?_)
    refine iteOk (fun hlt1 => ?_) (fun _ => hpush _ _)
    have h1' : (i + ix 1).val < n.val := hlt1
    have e2 := indexAddOne (i + ix 1) (by omega) (by omega)
    refine okBind (hread _ (by omega) (by omega)) (fun c => ?_)
    try dsimp only
    refine iteOk (fun _ => okBind (hpush _ _) (fun d => step _ _ _ (by omega) (by omega)))
      (fun _ => ?_)
    refine iteOk (fun _ => okBind (hpush _ _) (fun d => cont _ d (by omega) (by omega)))
      (fun _ => ?_)
    refine iteOk (fun hlt2 => ?_) (fun _ => hpush _ _)
    have h2' : (i + ix 1 + ix 1).val < n.val := hlt2
    have e3 := indexAddOne (i + ix 1 + ix 1) (by omega) (by omega)
    refine okBind (hread _ (by omega) (by omega)) (fun d0 => ?_)
    try dsimp only
    refine iteOk (fun _ => okBind (hpush _ _) (fun d => step _ _ _ (by omega) (by omega)))
      (fun _ => ?_)
    refine iteOk (fun _ => okBind (hpush _ _) (fun d => cont _ d (by omega) (by omega)))
      (fun _ => okBind (hpush _ _) (fun d => cont _ d (by omega) (by omega)))

/-- `length(src)` as an `Int` wraps for lists longer than `typemax(Int)`; a positive
wrapped value never exceeds the true length, so every read stays in bounds. -/
theorem wrapLength_le (L : Nat) (h : 0 < (ix (L : Int)).val) : (ix (L : Int)).val ≤ L := by
  have e : (ix (L : Int)).val = wrapInt .i64 L := rfl
  rw [e] at h ⊢
  simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢
  simp at h ⊢
  omega

theorem transcodeUtf8ToUtf16List_ok (src : List UInt8) :
    ∃ units, transcodeUtf8ToUtf16List src = .ok units := by
  unfold transcodeUtf8ToUtf16List transcodeUtf8ToUtf16
  dsimp only
  rw [exceptBindOk]
  split
  · rename_i hpos
    have hle := wrapLength_le src.length hpos
    rw [exceptBindOk]
    have hread : ∀ k : Index, 1 ≤ k.val → k.val ≤ (ix (src.length : Int)).val →
        ∃ b, (match src[(k.val - 1).toNat]? with
          | some byte => (Except.ok byte : StringResult UInt8)
          | none => .error JuliaLean.Strings.boundsErr) = .ok b := by
      intro k hk1 hk2
      rw [List.getElem?_eq_getElem (by omega)]
      exact ⟨_, rfl⟩
    refine okBind (hread (ix 1) (by rw [ixVal 1 (by omega) (by omega)]; omega)
      (by rw [ixVal 1 (by omega) (by omega)]; omega)) (fun a => ?_)
    exact utf8ToUtf16Loop_ok _ _ src _ hread (fun d m => ⟨_, rfl⟩) _ _ _ _
      (by rw [ixVal 1 (by omega) (by omega)]; omega)
      (by rw [ixVal 1 (by omega) (by omega)]; omega)
      (by rw [ixVal 1 (by omega) (by omega), Int.toNat_of_nonneg (by omega)]; omega)
  · exact ⟨_, rfl⟩

/-! ## The UTF-8 loop on well-formed characters -/

theorem iteBoolFalse {α : Type} {b : Bool} (h : b = false) (t e : α) :
    (if b = true then t else e) = e := by
  rw [h]; rfl

theorem iteBoolTrue {α : Type} {b : Bool} (h : b = true) (t e : α) :
    (if b = true then t else e) = t := by
  rw [h]; rfl

/-- The loop tail `if i < n; a = src[i += 1]; continue`, with the next iteration's fuel. -/
def cont8 {V : Type} (read : V → Index → StringResult UInt8)
    (push : List UInt16 → List UInt16 → StringResult (List UInt16)) (src : V) (n : Index)
    (fuel : Nat) (j : Index) (d : List UInt16) : StringResult (List UInt16) :=
  if j < n then (read src (j + ix 1) >>= fun next =>
    utf8ToUtf16Loop read push src n fuel (j + ix 1) next d) else pure d

/-- The UTF-16 code units `transcode(UInt16, ...)` produces for one well-formed character. -/
def units16 : List UInt8 → List UInt16
  | [a] => [a.toUInt16]
  | [a, b] => [utf8Two a b]
  | [a, b, c] => [utf8Three a b c]
  | [a, b, c, d] => [utf8FourHigh a b c, utf8FourLow c d]
  | _ => []

theorem getD_of_drop {α : Type} (src rest : List α) (k j : Nat) (d : α)
    (h : src.drop k = rest) : src.getD (k + j) d = rest.getD j d := by
  rw [← h]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem lt_of_drop {α : Type} (src rest : List α) (k j : Nat)
    (h : src.drop k = rest) (hj : j < rest.length) : k + j < src.length := by
  have := congrArg List.length h
  simp only [List.length_drop] at this
  omega

section Chunks
variable {V : Type} (read : V → Index → StringResult UInt8)
  (push : List UInt16 → List UInt16 → StringResult (List UInt16)) (src : V) (n : Index)
  (hpush : ∀ d m, push d m = .ok (d ++ m))
include hpush

theorem chunk1 (fuel : Nat) (i : Index) (a : UInt8) (dst : List UInt16)
    (hlead : utf8Lead a = false) :
    utf8ToUtf16Loop read push src n (fuel + 1) i a dst =
      cont8 read push src n fuel i (dst ++ [a.toUInt16]) := by
  rw [utf8Loop_succ]
  delta utf8Step
  rw [iteBoolFalse (by rw [hlead, Bool.and_false]), hpush, exceptBindOk]
  rfl

theorem chunk2 (fuel : Nat) (i : Index) (a b : UInt8) (dst : List UInt16)
    (hi : i < n) (hb : read src (i + ix 1) = .ok b)
    (c1 : utf8Lead a = true)
    (c2 : (decide (-64 ≤ signedByte b) || (a == 0xf4 && 0x8f < b)) = false)
    (c3 : a < 0xe0) :
    utf8ToUtf16Loop read push src n (fuel + 1) i a dst =
      cont8 read push src n fuel (i + ix 1) (dst ++ [utf8Two a b]) := by
  rw [utf8Loop_succ]
  delta utf8Step
  rw [iteBoolTrue (by rw [c1, Bool.and_true]; exact decide_eq_true hi), hb, exceptBindOk]
  try dsimp only
  rw [iteBoolFalse c2, if_pos c3, hpush, exceptBindOk]
  rfl

theorem chunk3 (fuel : Nat) (i : Index) (a b c : UInt8) (dst : List UInt16)
    (hi : i < n) (hb : read src (i + ix 1) = .ok b)
    (hi1 : i + ix 1 < n) (hc : read src (i + ix 1 + ix 1) = .ok c)
    (c1 : utf8Lead a = true)
    (c2 : (decide (-64 ≤ signedByte b) || (a == 0xf4 && 0x8f < b)) = false)
    (c3 : ¬ a < 0xe0) (c4 : decide (-64 ≤ signedByte c) = false) (c5 : a < 0xf0) :
    utf8ToUtf16Loop read push src n (fuel + 1) i a dst =
      cont8 read push src n fuel (i + ix 1 + ix 1) (dst ++ [utf8Three a b c]) := by
  rw [utf8Loop_succ]
  delta utf8Step
  rw [iteBoolTrue (by rw [c1, Bool.and_true]; exact decide_eq_true hi), hb, exceptBindOk]
  try dsimp only
  rw [iteBoolFalse c2, if_neg c3, if_pos hi1, hc, exceptBindOk]
  try dsimp only
  rw [iteBoolFalse c4, if_pos c5, hpush, exceptBindOk]
  rfl

theorem chunk4 (fuel : Nat) (i : Index) (a b c d : UInt8) (dst : List UInt16)
    (hi : i < n) (hb : read src (i + ix 1) = .ok b)
    (hi1 : i + ix 1 < n) (hc : read src (i + ix 1 + ix 1) = .ok c)
    (hi2 : i + ix 1 + ix 1 < n) (hd : read src (i + ix 1 + ix 1 + ix 1) = .ok d)
    (c1 : utf8Lead a = true)
    (c2 : (decide (-64 ≤ signedByte b) || (a == 0xf4 && 0x8f < b)) = false)
    (c3 : ¬ a < 0xe0) (c4 : decide (-64 ≤ signedByte c) = false) (c5 : ¬ a < 0xf0)
    (c6 : decide (-64 ≤ signedByte d) = false) (c7 : (a == 0xf0 && b < 0x90) = false) :
    utf8ToUtf16Loop read push src n (fuel + 1) i a dst =
      cont8 read push src n fuel (i + ix 1 + ix 1 + ix 1)
        (dst ++ [utf8FourHigh a b c, utf8FourLow c d]) := by
  rw [utf8Loop_succ]
  delta utf8Step
  rw [iteBoolTrue (by rw [c1, Bool.and_true]; exact decide_eq_true hi), hb, exceptBindOk]
  try dsimp only
  rw [iteBoolFalse c2, if_neg c3, if_pos hi1, hc, exceptBindOk]
  try dsimp only
  rw [iteBoolFalse c4, if_neg c5, if_pos hi2, hd, exceptBindOk]
  try dsimp only
  rw [iteBoolFalse c6, iteBoolFalse c7, hpush, exceptBindOk]
  rfl

end Chunks
def wr16Enc2 (a : UInt16) : List UInt8 :=
  [(0xc0 : UInt8) ||| (a >>> 6).toUInt8, (0x80 : UInt8) ||| (a.toUInt8 &&& (0x3f : UInt8))]

def wr16Enc3 (a : UInt16) : List UInt8 :=
  [(0xe0 : UInt8) ||| (a >>> 12).toUInt8,
    (0x80 : UInt8) ||| ((a >>> 6).toUInt8 &&& (0x3f : UInt8)),
    (0x80 : UInt8) ||| (a.toUInt8 &&& (0x3f : UInt8))]

def wr16Enc4 (a b : UInt16) : List UInt8 :=
  [(0xf0 : UInt8) ||| ((a + 0x2840) >>> 8).toUInt8,
    (0x80 : UInt8) ||| ((a + 0x2840).toUInt8 >>> 2),
    (0xf0 : UInt8) ^^^ (((a + 0x2840).toUInt8 <<< 4) &&& (0x3f : UInt8)) ^^^ (b >>> 6).toUInt8,
    (0x80 : UInt8) ||| (b.toUInt8 &&& (0x3f : UInt8))]
/-! ## Byte tables for well-formed UTF-8 characters

Moved from `JuliaLean/Transcode/Tables.lean:17-195`, restated for the live decoder
(`utf8Lead`, `signedByte`, `utf8Two`, ...) and the write-loop encoders `wr16Enc2/3/4`.
Each fact is checked exhaustively by the kernel (`decide +kernel`). -/

/-- Facts for a 1-byte character. -/
abbrev P1 (a : UInt8) : Prop :=
  wfChar [a] = true →
    utf8Lead a = false ∧ a.toUInt16 < 0x80 ∧
    a.toUInt16.toUInt8 = a ∧ isHigh a.toUInt16 = false ∧ isLow a.toUInt16 = false ∧
    decide (0xf0 ≤ a) = false

/-- Facts for a 2-byte character. -/
abbrev P2 (a b : UInt8) : Prop :=
  wfChar [a, b] = true →
    utf8Lead a = true ∧
    (decide (-64 ≤ signedByte b) || (a == 0xf4 && 0x8f < b)) = false ∧ a < 0xe0 ∧
    ¬ utf8Two a b < 0x80 ∧ utf8Two a b < 0x800 ∧ wr16Enc2 (utf8Two a b) = [a, b] ∧
    isHigh (utf8Two a b) = false ∧ isLow (utf8Two a b) = false ∧
    decide (0xf0 ≤ a) = false ∧ decide (0xf0 ≤ b) = false

/-- The part of `wfChar [a, b, c]` that depends on `a` and `b`. -/
def pre3 (a b : UInt8) : Bool :=
  if a == 0xe0 then 0xa0 ≤ b && b ≤ 0xbf
  else if a == 0xed then 0x80 ≤ b && b ≤ 0x9f
  else 0xe1 ≤ a && a ≤ 0xef && isC b

theorem wfChar3 (a b c : UInt8) : wfChar [a, b, c] = (isC c && pre3 a b) := rfl

/-- Facts for a 3-byte character. -/
abbrev P3 (a b c : UInt8) : Prop :=
  wfChar [a, b, c] = true →
    utf8Lead a = true ∧
    (decide (-64 ≤ signedByte b) || (a == 0xf4 && 0x8f < b)) = false ∧ ¬ a < 0xe0 ∧
    decide (-64 ≤ signedByte c) = false ∧ a < 0xf0 ∧
    ¬ utf8Three a b c < 0x80 ∧ ¬ utf8Three a b c < 0x800 ∧
    ((utf8Three a b c &&& 0xfc00) == 0xd800) = false ∧
    isLow (utf8Three a b c) = false ∧ wr16Enc3 (utf8Three a b c) = [a, b, c] ∧
    decide (0xf0 ≤ a) = false ∧ decide (0xf0 ≤ b) = false ∧ decide (0xf0 ≤ c) = false

/-- The part of `wfChar [a, b, c, d]` that depends on `a` and `b`. -/
def pre4 (a b : UInt8) : Bool :=
  if a == 0xf0 then 0x90 ≤ b && b ≤ 0xbf
  else if a == 0xf4 then 0x80 ≤ b && b ≤ 0x8f
  else 0xf1 ≤ a && a ≤ 0xf3 && isC b

theorem wfChar4 (a b c d : UInt8) : wfChar [a, b, c, d] = (isC c && isC d && pre4 a b) := rfl

/-- Facts for the first three bytes of a 4-byte character. -/
abbrev P4a (a b c : UInt8) : Prop :=
  (isC c && pre4 a b) = true →
    utf8Lead a = true ∧
    (decide (-64 ≤ signedByte b) || (a == 0xf4 && 0x8f < b)) = false ∧ ¬ a < 0xe0 ∧
    decide (-64 ≤ signedByte c) = false ∧ ¬ a < 0xf0 ∧ (a == 0xf0 && b < 0x90) = false ∧
    ¬ utf8FourHigh a b c < 0x80 ∧ ¬ utf8FourHigh a b c < 0x800 ∧
    ((utf8FourHigh a b c &&& 0xfc00) == 0xd800) = true ∧
    (0xf0 : UInt8) ||| ((utf8FourHigh a b c + 0x2840) >>> 8).toUInt8 = a ∧
    (0x80 : UInt8) ||| ((utf8FourHigh a b c + 0x2840).toUInt8 >>> 2) = b ∧
    (((utf8FourHigh a b c + 0x2840).toUInt8 <<< 4) &&& (0x3f : UInt8)) =
      ((c >>> 4) &&& 3) <<< 4 ∧
    decide (0xf0 ≤ a) = true ∧ decide (0xf0 ≤ b) = false ∧ decide (0xf0 ≤ c) = false

/-- Facts for the last two bytes of a 4-byte character. -/
abbrev P4b (c d : UInt8) : Prop :=
  (isC c && isC d) = true →
    decide (-64 ≤ signedByte d) = false ∧ ((utf8FourLow c d &&& 0xfc00) == 0xdc00) = true ∧
    (0x80 : UInt8) ||| ((utf8FourLow c d).toUInt8 &&& (0x3f : UInt8)) = d ∧
    (utf8FourLow c d >>> 6).toUInt8 = (0x70 : UInt8) ^^^ (c &&& 0xf) ∧
    (0xf0 : UInt8) ^^^ (((c >>> 4) &&& 3) <<< 4) ^^^ ((0x70 : UInt8) ^^^ (c &&& 0xf)) = c ∧
    decide (0xf0 ≤ d) = false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab1 : ∀ x, x < 256 → P1 (UInt8.ofNat x) := by decide +kernel

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab2 : ∀ x, x < 256 → ∀ y, y < 256 → P2 (UInt8.ofNat x) (UInt8.ofNat y) := by
  decide +kernel

/-- `f lo && f (lo + 1) && ... && f (lo + n - 1)`. -/
def allFrom (lo : Nat) : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f (lo + n) && allFrom lo n f

theorem allFrom_spec (lo : Nat) : ∀ (n : Nat) (f : Nat → Bool), allFrom lo n f = true →
    ∀ i, lo ≤ i → i < lo + n → f i = true := by
  intro n
  induction n with
  | zero => intro f _ i h1 h2; omega
  | succ n ih =>
    intro f h i h1 h2
    simp only [allFrom, Bool.and_eq_true] at h
    by_cases hi : i = lo + n
    · subst hi; exact h.1
    · exact ih f h.2 i h1 (by omega)

/-- The 3-byte table for lead bytes `lo, ..., lo + n - 1`. -/
def table3Row (x : Nat) : Bool :=
  allFrom 0 256 fun y =>
    !pre3 (UInt8.ofNat x) (UInt8.ofNat y) ||
      allFrom 0 256 fun z => decide (P3 (UInt8.ofNat x) (UInt8.ofNat y) (UInt8.ofNat z))

def table3 (lo n : Nat) : Bool := allFrom lo n table3Row

/-- The 4-byte table for lead bytes `lo, ..., lo + n - 1`. -/
def table4 (lo n : Nat) : Bool :=
  allFrom lo n fun x => allFrom 0 256 fun y =>
    !pre4 (UInt8.ofNat x) (UInt8.ofNat y) ||
      allFrom 0 256 fun z => decide (P4a (UInt8.ofNat x) (UInt8.ofNat y) (UInt8.ofNat z))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lead3_range : allFrom 0 256 (fun x => allFrom 0 256 fun y =>
    !pre3 (UInt8.ofNat x) (UInt8.ofNat y) || (decide (0xe0 ≤ x) && decide (x < 0xf0))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lead4_range : allFrom 0 256 (fun x => allFrom 0 256 fun y =>
    !pre4 (UInt8.ofNat x) (UInt8.ofNat y) || (decide (0xf0 ≤ x) && decide (x < 0xf5))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3e0 : table3Row 0xe0 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3e1 : table3Row 0xe1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3e2 : table3Row 0xe2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3e3 : table3Row 0xe3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3e4 : table3Row 0xe4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3e5 : table3Row 0xe5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3e6 : table3Row 0xe6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3e7 : table3Row 0xe7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3e8 : table3Row 0xe8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3e9 : table3Row 0xe9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3ea : table3Row 0xea = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3eb : table3Row 0xeb = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3ec : table3Row 0xec = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3ed : table3Row 0xed = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3ee : table3Row 0xee = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab3ef : table3Row 0xef = true := by decide +kernel

theorem tab3a : table3 0xe0 4 = true := by
  simp [table3, allFrom, tab3e0, tab3e1, tab3e2, tab3e3]
theorem tab3b : table3 0xe4 4 = true := by
  simp [table3, allFrom, tab3e4, tab3e5, tab3e6, tab3e7]
theorem tab3c : table3 0xe8 4 = true := by
  simp [table3, allFrom, tab3e8, tab3e9, tab3ea, tab3eb]
theorem tab3d : table3 0xec 4 = true := by
  simp [table3, allFrom, tab3ec, tab3ed, tab3ee, tab3ef]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab4a1 : table4 0xf0 2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab4a2 : table4 0xf2 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem tab4b : ∀ x, x < 256 → ∀ y, y < 256 → P4b (UInt8.ofNat x) (UInt8.ofNat y) := by
  decide +kernel

theorem facts1 (a : UInt8) : P1 a := by
  have := tab1 a.toNat (UInt8.toNat_lt a); simpa [UInt8.ofNat_toNat] using this

theorem facts2 (a b : UInt8) : P2 a b := by
  have := tab2 a.toNat (UInt8.toNat_lt a) b.toNat (UInt8.toNat_lt b)
  simpa only [UInt8.ofNat_toNat] using this

/-- Look up `a, b, c` in a 3- or 4-byte table whose lead bytes include `a`. -/
theorem chunk_at {lo n : Nat} {pre : UInt8 → UInt8 → Bool} {P : UInt8 → UInt8 → UInt8 → Prop}
    [∀ a b c, Decidable (P a b c)]
    (ht : (allFrom lo n fun x => allFrom 0 256 fun y =>
      !pre (UInt8.ofNat x) (UInt8.ofNat y) ||
        allFrom 0 256 fun z => decide (P (UInt8.ofNat x) (UInt8.ofNat y) (UInt8.ofNat z))) = true)
    (a b c : UInt8) (hp : pre a b = true) (h1 : lo ≤ a.toNat) (h2 : a.toNat < lo + n) :
    P a b c := by
  have hx := allFrom_spec lo n _ ht a.toNat h1 h2
  have hy := allFrom_spec 0 256 _ hx b.toNat (Nat.zero_le _) (UInt8.toNat_lt b)
  simp only [UInt8.ofNat_toNat, hp, Bool.not_true, Bool.false_or] at hy
  have hz := allFrom_spec 0 256 _ hy c.toNat (Nat.zero_le _) (UInt8.toNat_lt c)
  simp only [UInt8.ofNat_toNat] at hz
  exact of_decide_eq_true hz

theorem lead_at {pre : UInt8 → UInt8 → Bool} {lo hi : Nat}
    (ht : allFrom 0 256 (fun x => allFrom 0 256 fun y =>
      !pre (UInt8.ofNat x) (UInt8.ofNat y) || (decide (lo ≤ x) && decide (x < hi))) = true)
    (a b : UInt8) (hp : pre a b = true) : lo ≤ a.toNat ∧ a.toNat < hi := by
  have hx := allFrom_spec 0 256 _ ht a.toNat (Nat.zero_le _) (UInt8.toNat_lt a)
  have hy := allFrom_spec 0 256 _ hx b.toNat (Nat.zero_le _) (UInt8.toNat_lt b)
  simp only [UInt8.ofNat_toNat, hp, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq] at hy
  exact hy

theorem facts3 (a b c : UInt8) : P3 a b c := by
  intro h
  have hp : pre3 a b = true := by rw [wfChar3] at h; simp only [Bool.and_eq_true] at h; exact h.2
  have hr := lead_at lead3_range a b hp
  have : P3 a b c := by
    by_cases h1 : a.toNat < 0xe4
    · exact chunk_at (pre := pre3) (P := P3) tab3a a b c hp hr.1 (by omega)
    by_cases h2 : a.toNat < 0xe8
    · exact chunk_at (pre := pre3) (P := P3) tab3b a b c hp (by omega) (by omega)
    by_cases h3 : a.toNat < 0xec
    · exact chunk_at (pre := pre3) (P := P3) tab3c a b c hp (by omega) (by omega)
    · exact chunk_at (pre := pre3) (P := P3) tab3d a b c hp (by omega) (by omega)
  exact this h

theorem facts4a (a b c : UInt8) : P4a a b c := by
  intro h
  have hp : pre4 a b = true := by simp only [Bool.and_eq_true] at h; exact h.2
  have hr := lead_at lead4_range a b hp
  have : P4a a b c := by
    by_cases h1 : a.toNat < 0xf2
    · exact chunk_at (pre := pre4) (P := P4a) tab4a1 a b c hp hr.1 (by omega)
    · exact chunk_at (pre := pre4) (P := P4a) tab4a2 a b c hp (by omega) (by omega)
  exact this h

theorem facts4b (c d : UInt8) : P4b c d := by
  have := tab4b c.toNat (UInt8.toNat_lt c) d.toNat (UInt8.toNat_lt d)
  simpa only [UInt8.ofNat_toNat] using this

def read8List (src : List UInt8) (i : Index) : StringResult UInt8 :=
  match src[(i.val - 1).toNat]? with
  | some byte => .ok byte
  | none => .error JuliaLean.Strings.boundsErr

def push16List (dst more : List UInt16) : StringResult (List UInt16) :=
  .ok (dst ++ more)

theorem listDropLength {α : Type} (src rest : List α) (k : Nat)
    (h : src.drop k = rest) (hk : k ≤ src.length) :
    src.length = k + rest.length := by
  have hl := congrArg List.length h
  simp only [List.length_drop] at hl
  omega

theorem listDropAfterAppend {α : Type} (src pref rest : List α) (k : Nat)
    (h : src.drop k = pref ++ rest) :
    src.drop (k + pref.length) = rest := by
  rw [← List.drop_drop, h]
  simp

theorem read8List_drop (src rest : List UInt8) (p j : Nat) (i : Index)
    (hdrop : src.drop p = rest) (hj : j < rest.length)
    (hi : i.val = (p + j + 1 : Nat)) :
    read8List src i = .ok (rest.getD j 0) := by
  have hp : p ≤ src.length := by
    have hl := congrArg List.length hdrop
    simp only [List.length_drop] at hl
    omega
  have hlen := listDropLength src rest p hdrop hp
  have hidx : p + j < src.length := by omega
  have hget : src[p + j] = rest[j] := by
    have hgetD := getD_of_drop src rest p j (0 : UInt8) hdrop
    simpa [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hj] using hgetD
  unfold read8List
  rw [show (i.val - 1).toNat = p + j by omega]
  rw [List.getElem?_eq_getElem hidx, hget]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem indexAddOneExact (i : Index) (p : Nat)
    (hi : i.val = (p : Int)) (hb : p + 1 < 2 ^ 63) :
    (i + ix 1).val = (p + 1 : Nat) := by
  rw [indexAddOne i (by omega) (by omega)]
  omega

theorem utf8WfCases (ch : List UInt8) (hw : wfChar ch = true) :
    (∃ a, ch = [a]) ∨ (∃ a b, ch = [a, b]) ∨ (∃ a b c, ch = [a, b, c]) ∨
      (∃ a b c d, ch = [a, b, c, d]) := by
  match ch, hw with
  | [a], _ => exact .inl ⟨a, rfl⟩
  | [a, b], _ => exact .inr (.inl ⟨a, b, rfl⟩)
  | [a, b, c], _ => exact .inr (.inr (.inl ⟨a, b, c, rfl⟩))
  | [a, b, c, d], _ => exact .inr (.inr (.inr ⟨a, b, c, d, rfl⟩))
  | [], hw => simp [wfChar] at hw
  | _ :: _ :: _ :: _ :: _ :: _, hw => simp [wfChar] at hw

theorem utf8WfNeNil {ch : List UInt8} (hw : wfChar ch = true) : ch ≠ [] := by
  rcases utf8WfCases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ |
    ⟨a, b, c, d, rfl⟩ <;> simp

theorem flatten_nil_of_wf : ∀ (cs : List (List UInt8)),
    (∀ c ∈ cs, wfChar c = true) → cs.flatten = [] → cs = [] := by
  intro cs h
  cases cs with
  | nil => intro _; rfl
  | cons ch cs =>
    intro e
    have hne := utf8WfNeNil (h ch (by simp))
    have hch : ch = [] := by
      cases ch <;> simp_all [List.flatten_cons]
    exact absurd hch hne

theorem chars_le_flatten_length : ∀ (cs : List (List UInt8)),
    (∀ c ∈ cs, wfChar c = true) → cs.length ≤ cs.flatten.length := by
  intro cs
  induction cs with
  | nil => intro _; simp
  | cons ch cs ih =>
    intro h
    have hne := utf8WfNeNil (h ch (by simp))
    have hi := ih (fun c hc => h c (by simp [hc]))
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    have hpos : 0 < ch.length := List.length_pos_iff.mpr hne
    omega

theorem utf8Loop_chars (src : List UInt8) (n : Index)
    (hn : n.val = src.length) (hsmall : src.length < 2 ^ 62) :
    ∀ (cs : List (List UInt8)), (∀ c ∈ cs, wfChar c = true) →
      ∀ (fuel k : Nat) (dst : List UInt16) (i : Index) (a : UInt8)
        (rest : List UInt8),
        cs.length ≤ fuel →
        src.drop k = cs.flatten →
        i.val = (k + 1 : Nat) →
        cs.flatten = a :: rest →
        utf8ToUtf16Loop read8List push16List src n fuel i a dst =
          .ok (dst ++ cs.flatMap units16) := by
  intro cs
  induction cs with
  | nil =>
    intro _ fuel k dst i a rest _ _ _ hhead
    simp at hhead
  | cons ch cs ih =>
    intro hcs fuel k dst i a rest hfuel hdrop hi hhead
    have hw := hcs ch (by simp)
    have hchpos : 0 < ch.length := List.length_pos_iff.mpr (utf8WfNeNil hw)
    have hcs' : ∀ c ∈ cs, wfChar c = true := fun c hc => hcs c (by simp [hc])
    have hfuelPos : 0 < fuel := by
      cases fuel with
      | zero => simp at hfuel
      | succ fuel => omega
    obtain ⟨fuel0, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [List.flatten_cons] at hdrop hhead
    have hdropApp : src.drop k = ch ++ cs.flatten := hdrop
    have hk : k ≤ src.length := by
      have hl := congrArg List.length hdropApp
      simp only [List.length_drop, List.length_append] at hl
      have hpos : 0 < ch.length := List.length_pos_iff.mpr (utf8WfNeNil hw)
      omega
    have hsourceLen : src.length = k + ch.length + cs.flatten.length := by
      have hl := listDropLength src (ch ++ cs.flatten) k hdropApp hk
      simpa [List.length_append, Nat.add_assoc] using hl
    have hdropTail : src.drop (k + ch.length) = cs.flatten :=
      listDropAfterAppend src ch cs.flatten k hdropApp
    have hpush : ∀ d m, push16List d m = .ok (d ++ m) := by
      intro d m
      rfl
    have finish (consumed : Nat) (last : Index) (out : List UInt16)
        (hval : last.val = (consumed : Int)) (hle : consumed ≤ src.length)
        (hdrop' : src.drop consumed = cs.flatten) :
        cont8 read8List push16List src n fuel0 last out =
          .ok (out ++ cs.flatMap units16) := by
      cases htail : cs.flatten with
      | nil =>
        have hnil := flatten_nil_of_wf cs hcs' htail
        subst cs
        have hlen := congrArg List.length hdrop'
        simp at hlen
        have hconsumed : consumed = src.length := by omega
        unfold cont8
        rw [if_neg (by change ¬ last.val < n.val; rw [hval, hn]; omega)]
        rw [List.flatMap_nil, List.append_nil]
        rfl
      | cons y ys =>
        have hdropOrig := hdrop'
        rw [htail] at hdrop'
        have hlen := listDropLength src (y :: ys) consumed hdrop' hle
        simp at hlen
        have hlt : last < n := by
          change last.val < n.val
          rw [hval, hn]
          omega
        have hnext := indexAddOneExact last consumed hval (by omega)
        have hread := read8List_drop src (y :: ys) consumed 0 (last + ix 1)
          hdrop' (by simp) (by omega)
        unfold cont8
        rw [if_pos hlt, hread, exceptBindOk]
        exact ih hcs' fuel0 consumed out (last + ix 1) y ys
          (by
            have hfuel' := hfuel
            simp only [List.length_cons] at hfuel'
            omega) hdropOrig hnext htail
    rcases utf8WfCases ch hw with ⟨x, rfl⟩ | ⟨x, y, rfl⟩ |
      ⟨x, y, z, rfl⟩ | ⟨x, y, z, w, rfl⟩
    · have hhead' := hhead
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hhead'
      rcases hhead' with ⟨rfl, rfl⟩
      simp only [List.length_cons, List.length_nil] at hsourceLen hdropTail
      obtain ⟨c1, -, -, -, -, -⟩ := facts1 x hw
      have hchunk := chunk1 read8List push16List src n hpush
        fuel0 i x dst c1
      have hfinish := finish (k + 1) i (dst ++ [x.toUInt16])
        (by omega) (by omega) (by simpa using hdropTail)
      rw [hchunk, hfinish]
      simp [List.flatMap_cons, units16, List.append_assoc]
    · have hhead' := hhead
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hhead'
      rcases hhead' with ⟨rfl, rfl⟩
      simp only [List.length_cons, List.length_nil] at hsourceLen hdropTail
      have hdropFull : src.drop k = x :: y :: cs.flatten := by
        simpa only [List.cons_append, List.nil_append] using hdropApp
      have hlen1 : i < n := by
        change i.val < n.val
        rw [hi, hn]
        omega
      have hi1 := indexAddOneExact i (k + 1) hi (by omega)
      have hb : read8List src (i + ix 1) = .ok y := by
        have hr := read8List_drop src (x :: y :: cs.flatten) k 1
          (i + ix 1) hdropFull (by simp) (by omega)
        simpa using hr
      obtain ⟨c1, c2, c3, -, -, -, -, -, -, -⟩ := facts2 x y hw
      have hchunk := chunk2 read8List push16List src n hpush
        fuel0 i x y dst hlen1 hb c1 c2 c3
      have hfinish := finish (k + 2) (i + ix 1)
        (dst ++ [utf8Two x y]) (by omega) (by omega)
        (by simpa using hdropTail)
      rw [hchunk, hfinish]
      simp [List.flatMap_cons, units16, List.append_assoc]
    · have hhead' := hhead
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hhead'
      rcases hhead' with ⟨rfl, rfl⟩
      simp only [List.length_cons, List.length_nil] at hsourceLen hdropTail
      have hdropFull : src.drop k = x :: y :: z :: cs.flatten := by
        simpa only [List.cons_append, List.nil_append] using hdropApp
      have hlen1 : i < n := by
        change i.val < n.val
        rw [hi, hn]
        omega
      have hi1 := indexAddOneExact i (k + 1) hi (by omega)
      have hlen2 : i + ix 1 < n := by
        change (i + ix 1).val < n.val
        rw [hi1, hn]
        omega
      have hi2 := indexAddOneExact (i + ix 1) (k + 2) hi1 (by omega)
      have hb : read8List src (i + ix 1) = .ok y := by
        have hr := read8List_drop src (x :: y :: z :: cs.flatten) k 1
          (i + ix 1) hdropFull (by simp) (by omega)
        simpa using hr
      have hc : read8List src (i + ix 1 + ix 1) = .ok z := by
        have hr := read8List_drop src (x :: y :: z :: cs.flatten) k 2
          (i + ix 1 + ix 1) hdropFull (by simp) (by omega)
        simpa using hr
      obtain ⟨c1, c2, c3, c4, c5, _, _, _, _, _, _, _, _⟩ :=
        facts3 x y z hw
      have hchunk := chunk3 read8List push16List src n hpush
        fuel0 i x y z dst hlen1 hb hlen2 hc c1 c2 c3 c4 c5
      have hfinish := finish (k + 3) (i + ix 1 + ix 1)
        (dst ++ [utf8Three x y z]) (by omega) (by omega)
        (by simpa using hdropTail)
      rw [hchunk, hfinish]
      simp [List.flatMap_cons, units16, List.append_assoc]
    · have hhead' := hhead
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hhead'
      rcases hhead' with ⟨rfl, rfl⟩
      simp only [List.length_cons, List.length_nil] at hsourceLen hdropTail
      have hdropFull : src.drop k = x :: y :: z :: w :: cs.flatten := by
        simpa only [List.cons_append, List.nil_append] using hdropApp
      have hlen1 : i < n := by
        change i.val < n.val
        rw [hi, hn]
        omega
      have hi1 := indexAddOneExact i (k + 1) hi (by omega)
      have hlen2 : i + ix 1 < n := by
        change (i + ix 1).val < n.val
        rw [hi1, hn]
        omega
      have hi2 := indexAddOneExact (i + ix 1) (k + 2) hi1 (by omega)
      have hlen3 : i + ix 1 + ix 1 < n := by
        change (i + ix 1 + ix 1).val < n.val
        rw [hi2, hn]
        omega
      have hi3 := indexAddOneExact (i + ix 1 + ix 1) (k + 3) hi2 (by omega)
      have hb : read8List src (i + ix 1) = .ok y := by
        have hr := read8List_drop src (x :: y :: z :: w :: cs.flatten) k 1
          (i + ix 1) hdropFull (by simp) (by omega)
        simpa using hr
      have hc : read8List src (i + ix 1 + ix 1) = .ok z := by
        have hr := read8List_drop src (x :: y :: z :: w :: cs.flatten) k 2
          (i + ix 1 + ix 1) hdropFull (by simp) (by omega)
        simpa using hr
      have hd : read8List src (i + ix 1 + ix 1 + ix 1) = .ok w := by
        have hr := read8List_drop src (x :: y :: z :: w :: cs.flatten) k 3
          (i + ix 1 + ix 1 + ix 1) hdropFull (by simp) (by omega)
        simpa using hr
      rw [wfChar4] at hw
      have hab : (isC z && pre4 x y) = true := by
        simp only [Bool.and_eq_true] at hw ⊢
        exact ⟨hw.1.1, hw.2⟩
      have hcd : (isC z && isC w) = true := by
        simp only [Bool.and_eq_true] at hw ⊢
        exact hw.1
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, _, _, _, _, _, _, _, _⟩ :=
        facts4a x y z hab
      obtain ⟨g1, _, _, _, _, _⟩ := facts4b z w hcd
      have hchunk := chunk4 read8List push16List src n hpush
        fuel0 i x y z w dst hlen1 hb hlen2 hc hlen3 hd c1 c2 c3 c4 c5 g1 c6
      have hfinish := finish (k + 4) (i + ix 1 + ix 1 + ix 1)
        (dst ++ [utf8FourHigh x y z, utf8FourLow z w])
        (by omega) (by omega) (by simpa using hdropTail)
      rw [hchunk, hfinish]
      simp [List.flatMap_cons, units16, List.append_assoc]

theorem transcodeUtf8ToUtf16List_chars (cs : List (List UInt8))
    (hcs : ∀ c ∈ cs, wfChar c = true)
    (hsmall : cs.flatten.length < 2 ^ 62) :
    transcodeUtf8ToUtf16List cs.flatten = .ok (cs.flatMap units16) := by
  cases hflat : cs.flatten with
  | nil =>
    have hnil := flatten_nil_of_wf cs hcs hflat
    subst cs
    have hz : (ix 0).val = 0 := ixVal 0 (by omega) (by omega)
    simp [transcodeUtf8ToUtf16List, transcodeUtf8ToUtf16, hz]
    rfl
  | cons a rest =>
    have hsmall' : (a :: rest).length < 2 ^ 62 := by simpa [hflat] using hsmall
    have hnval : (ix ((a :: rest).length : Int)).val = (a :: rest).length := by
      rw [ixVal _ (by omega) (by omega)]
    have hpos : 0 < (ix ((a :: rest).length : Int)).val := by
      rw [hnval]
      simp
    have hi : (ix 1).val = 1 := ixVal 1 (by omega) (by omega)
    have hread :
        (match (a :: rest)[((ix 1).val - 1).toNat]? with
          | some byte => (Except.ok byte : StringResult UInt8)
          | none => .error JuliaLean.Strings.boundsErr) = .ok a := by
      simp [hi]
    have hchars : cs.length ≤ (a :: rest).length := by
      have h := chars_le_flatten_length cs hcs
      rw [hflat] at h
      exact h
    unfold transcodeUtf8ToUtf16List transcodeUtf8ToUtf16
    dsimp only
    rw [exceptBindOk]
    rw [if_pos hpos]
    rw [exceptBindOk]
    change ((match (a :: rest)[((ix 1).val - 1).toNat]? with
      | some byte => (Except.ok byte : StringResult UInt8)
      | none => .error JuliaLean.Strings.boundsErr) >>= fun nextByte =>
      utf8ToUtf16Loop read8List push16List (a :: rest)
        (ix ((a :: rest).length : Int))
        ((ix ((a :: rest).length : Int)).val.toNat) (ix 1) nextByte []) =
      .ok (cs.flatMap units16)
    rw [hread, exceptBindOk]
    have hfuel : (ix ((a :: rest).length : Int)).val.toNat = (a :: rest).length := by
      rw [hnval]
      simp
    rw [hfuel]
    exact utf8Loop_chars (a :: rest) (ix ((a :: rest).length : Int)) hnval
      hsmall' cs hcs (a :: rest).length 0 [] (ix 1) a rest
      (by simpa using hchars) (by simpa using hflat.symm) (by rw [hi]; omega) hflat


theorem transcodeUtf16String_chars (s : JString) (cs : List (List UInt8))
    (hcs : ∀ c ∈ cs, wfChar c = true) (hbytes : s.bytes = cs.flatten) :
    transcode (T := UInt16) (Output := List UInt16) s = .ok (cs.flatMap units16) := by
  have hsmall : cs.flatten.length < 2 ^ 62 := by
    rw [← hbytes]
    exact s.small
  have hlist : transcodeUtf8ToUtf16List (codeunitsString s).bytes =
      .ok (cs.flatMap units16) := by
    change transcodeUtf8ToUtf16List s.bytes = .ok (cs.flatMap units16)
    rw [hbytes]
    exact transcodeUtf8ToUtf16List_chars cs hcs hsmall
  refine transcode_of_run _
    (fun src => transcodeStringCodeUnits (T := UInt16) (R := CodeUnits)
      (α := List UInt16) codeunitsString src)
    rfl s _ ?_
  show transcodeStringCodeUnits (T := UInt16) (R := CodeUnits) (α := List UInt16)
    codeunitsString s = _
  unfold transcodeStringCodeUnits
  exact transcode_of_run _ (fun src : CodeUnits => transcodeUtf8ToUtf16List src.bytes)
    rfl (codeunitsString s) _ hlist

theorem utf8ToUtf16Total_proven : Utf8ToUtf16TotalSpec := by
  constructor
  · intro bytes
    obtain ⟨units, h⟩ := transcodeUtf8ToUtf16List_ok bytes
    exact ⟨units, transcode_of_run _ transcodeUtf8ToUtf16List rfl bytes _ h⟩
  · intro s
    obtain ⟨units, h⟩ := transcodeUtf8ToUtf16List_ok (codeunitsString s).bytes
    refine ⟨units, transcode_of_run _
      (fun src => transcodeStringCodeUnits (T := UInt16) (R := CodeUnits)
        (α := List UInt16) codeunitsString src) rfl s _ ?_⟩
    show transcodeStringCodeUnits (T := UInt16) (R := CodeUnits) (α := List UInt16)
      codeunitsString s = _
    unfold transcodeStringCodeUnits
    exact transcode_of_run _ (fun src : CodeUnits => transcodeUtf8ToUtf16List src.bytes) rfl
      (codeunitsString s) _ h


/-! ## UTF-16 to UTF-8: the size loop counts exactly the bytes the write loop writes -/

/-- Wrapped `Int` accumulation: adding to a wrapped value and wrapping again is wrapping
the exact sum. -/
theorem ix_add_wrap (m : Index) (c d : Int) : ix ((m + ix c).val + d) = ix (m.val + (c + d)) := by
  apply Subtype.ext
  show wrapInt .i64 (wrapInt .i64 (m.val + wrapInt .i64 c) + d) = wrapInt .i64 (m.val + (c + d))
  simp only [wrapInt, IntTy.signed, IntTy.bits]
  simp
  omega

/-! ## The bytes `transcode(UInt8, ::AbstractVector{UInt16})` writes -/

def wr16Next (f : UInt16 → List UInt16 → List UInt8) : List UInt16 → List UInt8
  | [] => []
  | x :: r => f x r


/-- The bytes the write loop produces from the current unit `a` and the unread units
`rest`, with the same branches and without capacity checks. -/
def wr16Spec : Nat → UInt16 → List UInt16 → List UInt8
  | 0, _, _ => []
  | k + 1, a, rest =>
    if a < 0x80 then [a.toUInt8] ++ wr16Next (wr16Spec k) rest
    else if a < 0x800 then wr16Enc2 a ++ wr16Next (wr16Spec k) rest
    else if (a &&& 0xfc00) == 0xd800 then
      match rest with
      | b :: r =>
          if (b &&& 0xfc00) == 0xdc00 then wr16Enc4 a b ++ wr16Next (wr16Spec k) r
          else wr16Enc3 a ++ wr16Spec k b r
      | [] => wr16Enc3 a
    else wr16Enc3 a ++ wr16Next (wr16Spec k) rest

theorem wr16Spec_length : ∀ (k : Nat) (a : UInt16) (rest : List UInt16),
    (wr16Spec k a rest).length ≤ 3 * (rest.length + 1) := by
  intro k
  induction k with
  | zero => intro a rest; simp [wr16Spec]
  | succ k ih =>
    intro a rest
    have N : ∀ r : List UInt16, (wr16Next (wr16Spec k) r).length ≤ 3 * r.length := by
      intro r
      cases r with
      | nil => simp [wr16Next]
      | cons x r => have := ih x r; simp [wr16Next] at this ⊢; omega
    rcases rest with _ | ⟨b, r⟩
    · simp only [wr16Spec]
      repeat' split
      all_goals simp [wr16Next, wr16Enc2, wr16Enc3]
    · have N1 := N r
      have N2 := N (b :: r)
      have I1 := ih b r
      simp only [wr16Spec]
      repeat' split
      all_goals (simp only [List.length_append, List.length_cons, List.length_nil,
        wr16Enc2, wr16Enc3, wr16Enc4, List.length_singleton] at N1 N2 I1 ⊢)
      all_goals omega


theorem headBangCons {α : Type} [Inhabited α] (a : α) (l : List α) :
    (a :: l).head! = a := rfl

theorem units16_length {ch : List UInt8} (hw : wfChar ch = true) :
    1 ≤ (units16 ch).length ∧ (units16 ch).length ≤ ch.length := by
  rcases utf8WfCases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ |
    ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩ <;> simp [units16]

theorem chars_le_units16 : ∀ (cs : List (List UInt8)),
    (∀ c ∈ cs, wfChar c = true) → cs.length ≤ (cs.flatMap units16).length := by
  intro cs
  induction cs with
  | nil => intro _; simp
  | cons ch cs ih =>
    intro h
    have hlen := (units16_length (h ch (by simp))).1
    have hi := ih (fun c hc => h c (by simp [hc]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem flatMap_nil_of_wf (cs : List (List UInt8))
    (h : ∀ c ∈ cs, wfChar c = true) (e : cs.flatMap units16 = []) : cs = [] := by
  have hlen := chars_le_units16 cs h
  rw [e] at hlen
  cases cs with
  | nil => rfl
  | cons _ _ => simp at hlen

theorem wf16_units : ∀ (cs : List (List UInt8)),
    (∀ c ∈ cs, wfChar c = true) → wf16 (cs.flatMap units16) = true := by
  intro cs h
  induction cs with
  | nil => rfl
  | cons ch cs ih =>
    have hw := h ch (by simp)
    have hcs : ∀ c ∈ cs, wfChar c = true := fun c hc => h c (List.mem_cons_of_mem _ hc)
    have ih := ih hcs
    simp only [List.flatMap_cons]
    rcases utf8WfCases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ |
      ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩
    · obtain ⟨-, -, -, e1, e2, -⟩ := facts1 a hw
      simp only [units16, List.cons_append, List.nil_append]
      cases hr : List.flatMap units16 cs <;> simp [wf16, e1, e2] <;> simp_all
    · obtain ⟨-, -, -, -, -, -, e1, e2, -, -⟩ := facts2 a b hw
      simp only [units16, List.cons_append, List.nil_append]
      cases hr : List.flatMap units16 cs <;> simp [wf16, e1, e2] <;> simp_all
    · obtain ⟨-, -, -, -, -, -, -, e1, e2, -, _, _, _⟩ := facts3 a b c hw
      have e1' : isHigh (utf8Three a b c) = false := e1
      simp only [units16, List.cons_append, List.nil_append]
      cases hr : List.flatMap units16 cs <;> simp [wf16, e1', e2] <;> simp_all
    · rw [wfChar4] at hw
      have hab : (isC c && pre4 a b) = true := by
        simp only [Bool.and_eq_true] at hw ⊢
        exact ⟨hw.1.1, hw.2⟩
      have hcd : (isC c && isC d) = true := by
        simp only [Bool.and_eq_true] at hw ⊢
        exact hw.1
      obtain ⟨_, _, _, _, _, _, _, _, e1, _, _, _, _, _, _⟩ := facts4a a b c hab
      obtain ⟨_, e2, _, _, _, _⟩ := facts4b c d hcd
      have h1 : isHigh (utf8FourHigh a b c) = true := e1
      have h2 : isLow (utf8FourLow c d) = true := e2
      simp only [units16, List.cons_append, List.nil_append, wf16, h1, h2,
        ↓reduceIte, Bool.true_and]
      exact ih

theorem wr16_chunk (ch : List UInt8) (hw : wfChar ch = true)
    (k : Nat) (r : List UInt16) :
    wr16Spec (k + 1) (units16 ch).head! ((units16 ch).tail ++ r) =
      ch ++ wr16Next (wr16Spec k) r := by
  rcases utf8WfCases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ |
    ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩
  · obtain ⟨-, e1, e2, -, -, -⟩ := facts1 a hw
    simp [units16, headBangCons, wr16Spec, e1, e2]
  · obtain ⟨-, -, -, e1, e2, e3, -, -, -, -⟩ := facts2 a b hw
    simp [units16, headBangCons, wr16Spec, e1, e2, e3]
  · obtain ⟨-, -, -, -, -, e1, e2, e3, -, e4, -, -, -⟩ := facts3 a b c hw
    simp [units16, headBangCons, wr16Spec, e1, e2, e3, e4]
  · rw [wfChar4] at hw
    have hab : (isC c && pre4 a b) = true := by
      simp only [Bool.and_eq_true] at hw ⊢
      exact ⟨hw.1.1, hw.2⟩
    have hcd : (isC c && isC d) = true := by
      simp only [Bool.and_eq_true] at hw ⊢
      exact hw.1
    obtain ⟨_, _, _, _, _, _, e1, e2, e3, f1, f2, f3, _, _, _⟩ :=
      facts4a a b c hab
    obtain ⟨_, g2, g3, g4, g5, _⟩ := facts4b c d hcd
    have henc : wr16Enc4 (utf8FourHigh a b c) (utf8FourLow c d) = [a, b, c, d] := by
      simp only [wr16Enc4, f1, f2, f3, g3, g4, g5]
    simp [units16, headBangCons, wr16Spec, e1, e2, e3, g2, henc]

theorem wr16Spec_chars : ∀ (cs : List (List UInt8)),
    (∀ c ∈ cs, wfChar c = true) →
    ∀ (k : Nat) (u : UInt16) (us : List UInt16),
      cs.length ≤ k →
      cs.flatMap units16 = u :: us →
      wr16Spec k u us = cs.flatten := by
  intro cs h
  induction cs with
  | nil => intro k u us _ e; simp at e
  | cons ch cs ih =>
    intro k u us hk e
    have hw := h ch (by simp)
    have hcs : ∀ c ∈ cs, wfChar c = true := fun c hc => h c (List.mem_cons_of_mem _ hc)
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    obtain ⟨x, vs, hx⟩ : ∃ x vs, units16 ch = x :: vs := by
      have hlen := (units16_length hw).1
      cases hu : units16 ch with
      | nil => rw [hu] at hlen; simp at hlen
      | cons x vs => exact ⟨x, vs, rfl⟩
    simp only [List.flatMap_cons, hx, List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have hchunk := wr16_chunk ch hw k (cs.flatMap units16)
    rw [hx] at hchunk
    simp only [headBangCons, List.tail_cons] at hchunk
    rw [hchunk, List.flatten_cons]
    congr 1
    cases htail : cs.flatMap units16 with
    | nil =>
      have hnil := flatMap_nil_of_wf cs hcs htail
      subst cs
      simp [wr16Next]
    | cons y ys =>
      simp only [wr16Next]
      exact ih hcs k y ys (by simp only [List.length_cons] at hk; omega) htail

/-! ## List reads -/

theorem drop_getD_cons {α : Type} (src : List α) (p : Nat) (h : p < src.length) (d : α) :
    src.drop p = src.getD p d :: src.drop (p + 1) := by
  rw [show src.getD p d = src[p] by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]]
  exact List.drop_eq_getElem_cons h

/-! ## The size loop -/

theorem countContinue_some (read : List UInt16 → Index → StringResult UInt16)
    (src : List UInt16) (n i m : Index) (p : Nat)
    (hread : ∀ (k : Index) (q : Nat), q < src.length → k.val = q + 1 →
      read src k = .ok (src.getD q 0))
    (hi : i.val = p + 1) (hp : p + 1 < src.length) (hn : n.val = src.length)
    (hsmall : src.length < 2 ^ 62) :
    u16CountContinue read src n i m = .ok (some (i + ix 1, src.getD (p + 1) 0, m)) := by
  have e := indexAddOne i (by omega) (by omega)
  unfold u16CountContinue
  rw [if_pos (show i < n from (show i.val < n.val by omega)), hread (i + ix 1) (p + 1) hp
    (by omega), exceptBindOk]
  rfl

theorem countContinue_none (read : List UInt16 → Index → StringResult UInt16)
    (src : List UInt16) (n i m : Index) (p : Nat)
    (hi : i.val = p + 1) (hp : src.length ≤ p + 1) (hn : n.val = src.length) :
    u16CountContinue read src n i m = .ok none := by
  unfold u16CountContinue
  rw [if_neg (show ¬ i < n from (show ¬ i.val < n.val by omega))]
  rfl

/-! ## One iteration of each UTF-16 loop, with the next iteration as a parameter -/

def countCont {V : Type} (read : V → Index → StringResult UInt16) (src : V) (n : Index)
    (next : Index → UInt16 → Index → StringResult Index) (i m : Index) :
    StringResult Index := do
  match ← u16CountContinue read src n i m with
  | none => pure m
  | some (nextI, nextA, nextM) => next nextI nextA nextM

def utf16CountStep {V : Type} (read : V → Index → StringResult UInt16)
    (length : V → Index) (src : V) (n : Index)
    (next : Index → UInt16 → Index → StringResult Index)
    (i : Index) (a : UInt16) (m : Index) : StringResult Index := do
  if a < 0x80 then
    countCont read src n next i (m + ix 1)
  else if a < 0x800 then
    countCont read src n next i (m + ix 2)
  else if (a &&& 0xfc00) == 0xd800 && decide (i < length src) then
    let b ← read src (i + ix 1)
    if (b &&& 0xfc00) == 0xdc00 then
      countCont read src n next (i + ix 1) (m + ix 4)
    else
      next (i + ix 1) b (m + ix 3)
  else
    countCont read src n next i (m + ix 3)

theorem utf16CountLoop_succ {V : Type} (read : V → Index → StringResult UInt16)
    (length : V → Index) (src : V) (n : Index) (fuel : Nat) (i : Index) (a : UInt16)
    (m : Index) :
    utf16CountLoop read length src n (fuel + 1) i a m =
      utf16CountStep read length src n (utf16CountLoop read length src n fuel) i a m := rfl

def writeCont {V : Type} (read : V → Index → StringResult UInt16) (src : V) (n : Index)
    (next : Index → UInt16 → Index → StringVector → StringResult StringVector)
    (i j : Index) (dst : StringVector) : StringResult StringVector := do
  match ← u16WriteContinue read src n i j dst with
  | none => pure dst
  | some (nextI, nextA, nextJ, nextDst) => next nextI nextA nextJ nextDst

def putThen (setByte : StringVector → Index → UInt8 → StringResult StringVector)
    (dst : StringVector) (j : Index) (bytes : List UInt8)
    (k : StringVector → Index → StringResult StringVector) : StringResult StringVector := do
  let (dst, j) ← putStringBytes setByte dst j bytes
  k dst j

def utf16WriteStep {V : Type} (read : V → Index → StringResult UInt16)
    (setByte : StringVector → Index → UInt8 → StringResult StringVector)
    (src : V) (n : Index)
    (next : Index → UInt16 → Index → StringVector → StringResult StringVector)
    (i : Index) (a : UInt16) (j : Index) (dst : StringVector) : StringResult StringVector := do
  if a < 0x80 then
    putThen setByte dst j [a.toUInt8] (fun dst j => writeCont read src n next i j dst)
  else if a < 0x800 then
    putThen setByte dst j (wr16Enc2 a) (fun dst j => writeCont read src n next i j dst)
  else if (a &&& 0xfc00) == 0xd800 && decide (i < n) then
    let b ← read src (i + ix 1)
    if (b &&& 0xfc00) == 0xdc00 then
      putThen setByte dst j (wr16Enc4 a b)
        (fun dst j => writeCont read src n next (i + ix 1) j dst)
    else
      putThen setByte dst j (wr16Enc3 a) (fun dst j => next (i + ix 1) b j dst)
  else
    putThen setByte dst j (wr16Enc3 a) (fun dst j => writeCont read src n next i j dst)

theorem utf16WriteLoop_succ {V : Type} (read : V → Index → StringResult UInt16)
    (setByte : StringVector → Index → UInt8 → StringResult StringVector)
    (src : V) (n : Index) (fuel : Nat) (i : Index) (a : UInt16) (j : Index)
    (dst : StringVector) :
    utf16ToUtf8WriteLoop read setByte src n (fuel + 1) i a j dst =
      utf16WriteStep read setByte src n (utf16ToUtf8WriteLoop read setByte src n fuel)
        i a j dst := rfl

theorem add_ix_eq (m : Index) (c : Int) (hc0 : 0 ≤ c) (hc : c ≤ 4) : m + ix c = ix (m.val + c) := by
  apply Subtype.ext
  show wrapInt .i64 (m.val + (ix c).val) = wrapInt .i64 (m.val + c)
  rw [ixVal c (by omega) (by omega)]

theorem countCont_some {V : Type} (read : V → Index → StringResult UInt16) (src : V)
    (n : Index) (next : Index → UInt16 → Index → StringResult Index) (i m : Index)
    (b : UInt16) (hc : u16CountContinue read src n i m = .ok (some (i + ix 1, b, m))) :
    countCont read src n next i m = next (i + ix 1) b m := by
  unfold countCont
  rw [hc, exceptBindOk]

theorem countCont_none {V : Type} (read : V → Index → StringResult UInt16) (src : V)
    (n : Index) (next : Index → UInt16 → Index → StringResult Index) (i m : Index)
    (hc : u16CountContinue read src n i m = .ok none) :
    countCont read src n next i m = .ok m := by
  unfold countCont
  rw [hc, exceptBindOk]
  rfl

/-- The size loop returns the number of bytes `wr16Spec` produces from its state (with
the same wrapping `Int` accumulation as Julia's `m`). -/
theorem utf16CountLoop_spec (read : List UInt16 → Index → StringResult UInt16)
    (length : List UInt16 → Index) (src : List UInt16) (n : Index)
    (hread : ∀ (k : Index) (q : Nat), q < src.length → k.val = q + 1 →
      read src k = .ok (src.getD q 0))
    (hlen : length src = n) (hn : n.val = src.length) (hsmall : src.length < 2 ^ 62) :
    ∀ (fuel p : Nat) (i m : Index), p < src.length → i.val = p + 1 →
      src.length ≤ p + fuel →
      utf16CountLoop read length src n fuel i (src.getD p 0) m =
        .ok (ix (m.val + (wr16Spec fuel (src.getD p 0) (src.drop (p + 1))).length)) := by
  intro fuel
  induction fuel with
  | zero => intro p i m hp hi hf; omega
  | succ fuel ih =>
    intro p i m hp hi hf
    have cont : ∀ (q : Nat) (i' : Index) (c : Nat) (bytes : List UInt8),
        i'.val = q + 1 → p ≤ q → q < src.length → bytes.length = c → c ≤ 4 →
        countCont read src n (utf16CountLoop read length src n fuel) i' (m + ix c) =
          .ok (ix (m.val + (bytes ++ wr16Next (wr16Spec fuel) (src.drop (q + 1))).length)) := by
      intro q i' c bytes hi' hq hqL hb hc4
      by_cases hlt : q + 1 < src.length
      · have e := indexAddOne i' (by omega) (by omega)
        rw [countCont_some _ _ _ _ _ _ _ (countContinue_some read src n i' _ q hread hi' hlt hn
          hsmall), ih (q + 1) (i' + ix 1) _ hlt (by omega) (by omega),
          drop_getD_cons src (q + 1) hlt 0, ix_add_wrap]
        simp only [wr16Next, List.length_append]
        congr 2
        omega
      · rw [countCont_none _ _ _ _ _ _ (countContinue_none read src n i' _ q hi' (by omega) hn),
          List.drop_eq_nil_of_le (by omega), add_ix_eq m c (by omega) (by omega)]
        simp only [wr16Next, List.append_nil]
        rw [hb]
    have e1 := indexAddOne i (by omega) (by omega)
    rw [utf16CountLoop_succ]
    delta utf16CountStep
    try dsimp only
    conv => rhs; simp only [wr16Spec]
    by_cases h1 : src.getD p 0 < 0x80
    · rw [if_pos h1, if_pos h1]
      exact cont p i 1 _ hi (Nat.le_refl _) hp rfl (by omega)
    rw [if_neg h1, if_neg h1]
    by_cases h2 : src.getD p 0 < 0x800
    · rw [if_pos h2, if_pos h2]
      exact cont p i 2 _ hi (Nat.le_refl _) hp rfl (by omega)
    rw [if_neg h2, if_neg h2]
    by_cases h3 : ((src.getD p 0 &&& 0xfc00) == 0xd800) = true
    · rw [if_pos h3]
      by_cases hlt : p + 1 < src.length
      · have hlt' : i < n := show i.val < n.val by omega
        have hc : ((src.getD p 0 &&& 0xfc00) == 0xd800 && decide (i < length src)) = true := by
          rw [h3, hlen, Bool.true_and]
          exact decide_eq_true hlt'
        rw [if_pos hc, hread (i + ix 1) (p + 1) hlt (by omega), exceptBindOk,
          drop_getD_cons src (p + 1) hlt 0]
        try dsimp only
        by_cases h4 : ((src.getD (p + 1) 0 &&& 0xfc00) == 0xdc00) = true
        · rw [if_pos h4, if_pos h4]
          exact cont (p + 1) (i + ix 1) 4 _ (by omega) (by omega) hlt rfl (by omega)
        · rw [if_neg h4, if_neg h4, ih (p + 1) (i + ix 1) _ hlt (by omega) (by omega), ix_add_wrap]
          simp only [List.length_append]
          congr 2
      · have hlt' : ¬ i < n := show ¬ i.val < n.val by omega
        have hc : ((src.getD p 0 &&& 0xfc00) == 0xd800 && decide (i < length src)) = false := by
          rw [h3, hlen, Bool.true_and]
          exact decide_eq_false hlt'
        rw [hc, if_neg Bool.false_ne_true,
          List.drop_eq_nil_of_le (show src.length ≤ p + 1 by omega)]
        have := cont p i 3 (wr16Enc3 (src.getD p 0)) hi (Nat.le_refl _) hp rfl (by omega)
        rw [List.drop_eq_nil_of_le (show src.length ≤ p + 1 by omega)] at this
        simpa [wr16Next] using this
    · have hc : ((src.getD p 0 &&& 0xfc00) == 0xd800 && decide (i < length src)) = false := by
        have h3' : ((src.getD p 0 &&& 0xfc00) == 0xd800) = false := by simpa using h3
        rw [h3', Bool.false_and]
      rw [if_neg h3, hc, if_neg Bool.false_ne_true]
      exact cont p i 3 _ hi (Nat.le_refl _) hp rfl (by omega)

/-! ## The write loop -/

theorem putStringBytes_cons (setByte : StringVector → Index → UInt8 → StringResult StringVector)
    (dst : StringVector) (j : Index) (b : UInt8) (bs : List UInt8) :
    putStringBytes setByte dst j (b :: bs) =
      (setByte dst (j + ix 1) b >>= fun d => putStringBytes setByte d (j + ix 1) bs) := by
  unfold putStringBytes
  rw [List.foldlM_cons]
  dsimp only
  cases setByte dst (j + ix 1) b <;> rfl

/-- Every byte write of `putStringBytes` lands at `written.length + 1 ≤ capacity`. -/
theorem putStringBytes_ok (setByte : StringVector → Index → UInt8 → StringResult StringVector)
    (hset : ∀ (dst : StringVector) (i : Index) (byte : UInt8), 1 ≤ i.val →
      i.val = (dst.written.length : Int) + 1 → i.val ≤ dst.capacity.val →
      setByte dst i byte = .ok {dst with written := dst.written ++ [byte]}) :
    ∀ (bytes : List UInt8) (dst : StringVector) (j : Index),
      (dst.written.length : Int) = j.val → 0 ≤ j.val →
      j.val + bytes.length ≤ dst.capacity.val → dst.capacity.val < 2 ^ 62 →
      ∃ j' : Index, j'.val = j.val + bytes.length ∧
        putStringBytes setByte dst j bytes = .ok ({dst with written := dst.written ++ bytes}, j') := by
  intro bytes
  induction bytes with
  | nil =>
    intro dst j _ _ _ _
    exact ⟨j, by simp, by simp; rfl⟩
  | cons b bs ih =>
    intro dst j hj h0 hc hcap
    simp only [List.length_cons] at hc
    have e := indexAddOne j h0 (by omega)
    rw [putStringBytes_cons, hset dst (j + ix 1) b (by omega) (by omega) (by omega), exceptBindOk]
    obtain ⟨j', hj', h⟩ := ih {dst with written := dst.written ++ [b]} (j + ix 1)
      (by simp; omega) (by omega) (by simp; omega) (by simpa using hcap)
    refine ⟨j', by simp only [List.length_cons]; omega, ?_⟩
    rw [h]
    simp [List.append_assoc]

theorem putThen_ok (setByte : StringVector → Index → UInt8 → StringResult StringVector)
    (hset : ∀ (dst : StringVector) (i : Index) (byte : UInt8), 1 ≤ i.val →
      i.val = (dst.written.length : Int) + 1 → i.val ≤ dst.capacity.val →
      setByte dst i byte = .ok {dst with written := dst.written ++ [byte]})
    (dst : StringVector) (j : Index) (bytes : List UInt8)
    (k : StringVector → Index → StringResult StringVector)
    (hj : (dst.written.length : Int) = j.val) (h0 : 0 ≤ j.val)
    (hc : j.val + bytes.length ≤ dst.capacity.val) (hcap : dst.capacity.val < 2 ^ 62) :
    ∃ j' : Index, j'.val = j.val + bytes.length ∧
      putThen setByte dst j bytes k = k {dst with written := dst.written ++ bytes} j' := by
  obtain ⟨j', hj', h⟩ := putStringBytes_ok setByte hset bytes dst j hj h0 hc hcap
  refine ⟨j', hj', ?_⟩
  unfold putThen
  rw [h, exceptBindOk]

theorem writeContinue_some (read : List UInt16 → Index → StringResult UInt16)
    (src : List UInt16) (n i j : Index) (dst : StringVector) (p : Nat)
    (hread : ∀ (k : Index) (q : Nat), q < src.length → k.val = q + 1 →
      read src k = .ok (src.getD q 0))
    (hi : i.val = p + 1) (hp : p + 1 < src.length) (hn : n.val = src.length)
    (hsmall : src.length < 2 ^ 62) :
    u16WriteContinue read src n i j dst =
      .ok (some (i + ix 1, src.getD (p + 1) 0, j, dst)) := by
  have e := indexAddOne i (by omega) (by omega)
  unfold u16WriteContinue
  rw [if_pos (show i < n from (show i.val < n.val by omega)), hread (i + ix 1) (p + 1) hp
    (by omega), exceptBindOk]
  rfl

theorem writeContinue_none (read : List UInt16 → Index → StringResult UInt16)
    (src : List UInt16) (n i j : Index) (dst : StringVector) (p : Nat)
    (hi : i.val = p + 1) (hp : src.length ≤ p + 1) (hn : n.val = src.length) :
    u16WriteContinue read src n i j dst = .ok none := by
  unfold u16WriteContinue
  rw [if_neg (show ¬ i < n from (show ¬ i.val < n.val by omega))]
  rfl

theorem writeCont_some {V : Type} (read : V → Index → StringResult UInt16) (src : V)
    (n : Index) (next : Index → UInt16 → Index → StringVector → StringResult StringVector)
    (i j : Index) (dst : StringVector) (b : UInt16)
    (hc : u16WriteContinue read src n i j dst = .ok (some (i + ix 1, b, j, dst))) :
    writeCont read src n next i j dst = next (i + ix 1) b j dst := by
  unfold writeCont
  rw [hc, exceptBindOk]

theorem writeCont_none {V : Type} (read : V → Index → StringResult UInt16) (src : V)
    (n : Index) (next : Index → UInt16 → Index → StringVector → StringResult StringVector)
    (i j : Index) (dst : StringVector)
    (hc : u16WriteContinue read src n i j dst = .ok none) :
    writeCont read src n next i j dst = .ok dst := by
  unfold writeCont
  rw [hc, exceptBindOk]
  rfl

/-- The write loop writes exactly the bytes of `wr16Spec`, each within capacity. -/
theorem utf16WriteLoop_spec (read : List UInt16 → Index → StringResult UInt16)
    (setByte : StringVector → Index → UInt8 → StringResult StringVector)
    (src : List UInt16) (n : Index)
    (hread : ∀ (k : Index) (q : Nat), q < src.length → k.val = q + 1 →
      read src k = .ok (src.getD q 0))
    (hset : ∀ (dst : StringVector) (i : Index) (byte : UInt8), 1 ≤ i.val →
      i.val = (dst.written.length : Int) + 1 → i.val ≤ dst.capacity.val →
      setByte dst i byte = .ok {dst with written := dst.written ++ [byte]})
    (hn : n.val = src.length) (hsmall : src.length < 2 ^ 62) :
    ∀ (fuel p : Nat) (i j : Index) (dst : StringVector), p < src.length → i.val = p + 1 →
      src.length ≤ p + fuel → (dst.written.length : Int) = j.val → 0 ≤ j.val →
      j.val + (wr16Spec fuel (src.getD p 0) (src.drop (p + 1))).length ≤ dst.capacity.val →
      dst.capacity.val < 2 ^ 62 →
      utf16ToUtf8WriteLoop read setByte src n fuel i (src.getD p 0) j dst =
        .ok {dst with written := dst.written ++ wr16Spec fuel (src.getD p 0) (src.drop (p + 1))} := by
  intro fuel
  induction fuel with
  | zero => intro p i j dst hp hi hf; omega
  | succ fuel ih =>
    intro p i j dst hp hi hf hj h0 hc hcap
    have cont : ∀ (q : Nat) (i' j' : Index) (bytes : List UInt8),
        i'.val = q + 1 → p ≤ q → q < src.length →
        ((dst.written ++ bytes).length : Int) = j'.val → 0 ≤ j'.val →
        j'.val + (wr16Next (wr16Spec fuel) (src.drop (q + 1))).length ≤ dst.capacity.val →
        writeCont read src n (utf16ToUtf8WriteLoop read setByte src n fuel) i' j'
            {dst with written := dst.written ++ bytes} =
          .ok {dst with written :=
            dst.written ++ (bytes ++ wr16Next (wr16Spec fuel) (src.drop (q + 1)))} := by
      intro q i' j' bytes hi' hq hqL hj' h0' hc'
      by_cases hlt : q + 1 < src.length
      · rw [writeCont_some _ _ _ _ _ _ _ _ (writeContinue_some read src n i' j' _ q hread hi' hlt
          hn hsmall)]
        rw [drop_getD_cons src (q + 1) hlt 0] at hc' ⊢
        simp only [wr16Next] at hc' ⊢
        rw [ih (q + 1) (i' + ix 1) j' _ hlt (by have := indexAddOne i' (by omega) (by omega); omega)
          (by omega) (by simpa using hj') h0' (by simpa using hc') (by simpa using hcap)]
        simp [List.append_assoc]
      · rw [writeCont_none _ _ _ _ _ _ _ (writeContinue_none read src n i' j' _ q hi' (by omega) hn),
          List.drop_eq_nil_of_le (show src.length ≤ q + 1 by omega)]
        simp [wr16Next]
    have e1 := indexAddOne i (by omega) (by omega)
    rw [utf16WriteLoop_succ]
    delta utf16WriteStep
    try dsimp only
    conv => rhs; simp only [wr16Spec]
    simp only [wr16Spec] at hc
    by_cases h1 : src.getD p 0 < 0x80
    · rw [if_pos h1, if_pos h1]
      rw [if_pos h1] at hc
      simp only [List.length_append] at hc
      obtain ⟨j', hj', hput⟩ := putThen_ok setByte hset dst j [(src.getD p 0).toUInt8] _ hj h0
        (by simp at hc ⊢; omega) hcap
      rw [hput]
      exact cont p i j' _ hi (Nat.le_refl _) hp (by simp at hj' ⊢; omega) (by omega)
        (by simp at hj' hc ⊢; omega)
    rw [if_neg h1, if_neg h1]
    rw [if_neg h1] at hc
    by_cases h2 : src.getD p 0 < 0x800
    · rw [if_pos h2, if_pos h2]
      rw [if_pos h2] at hc
      simp only [List.length_append] at hc
      obtain ⟨j', hj', hput⟩ := putThen_ok setByte hset dst j (wr16Enc2 (src.getD p 0)) _ hj h0
        (by simp [wr16Enc2] at hc ⊢; omega) hcap
      rw [hput]
      exact cont p i j' _ hi (Nat.le_refl _) hp (by simp [wr16Enc2] at hj' ⊢; omega) (by omega)
        (by simp [wr16Enc2] at hj' hc ⊢; omega)
    rw [if_neg h2, if_neg h2]
    rw [if_neg h2] at hc
    by_cases h3 : ((src.getD p 0 &&& 0xfc00) == 0xd800) = true
    · rw [if_pos h3]
      rw [if_pos h3] at hc
      by_cases hlt : p + 1 < src.length
      · have hlt' : i < n := show i.val < n.val by omega
        have hc3 : ((src.getD p 0 &&& 0xfc00) == 0xd800 && decide (i < n)) = true := by
          rw [h3, Bool.true_and]
          exact decide_eq_true hlt'
        rw [if_pos hc3, hread (i + ix 1) (p + 1) hlt (by omega), exceptBindOk,
          drop_getD_cons src (p + 1) hlt 0]
        rw [drop_getD_cons src (p + 1) hlt 0] at hc
        try dsimp only
        try dsimp only at hc
        by_cases h4 : ((src.getD (p + 1) 0 &&& 0xfc00) == 0xdc00) = true
        · rw [if_pos h4, if_pos h4]
          rw [if_pos h4] at hc
          simp only [List.length_append] at hc
          obtain ⟨j', hj', hput⟩ := putThen_ok setByte hset dst j
            (wr16Enc4 (src.getD p 0) (src.getD (p + 1) 0)) _ hj h0
            (by simp [wr16Enc4] at hc ⊢; omega) hcap
          rw [hput]
          exact cont (p + 1) (i + ix 1) j' _ (by omega) (by omega) hlt
            (by simp [wr16Enc4] at hj' ⊢; omega) (by omega)
            (by simp [wr16Enc4] at hj' hc ⊢; omega)
        · rw [if_neg h4, if_neg h4]
          rw [if_neg h4] at hc
          simp only [List.length_append] at hc
          obtain ⟨j', hj', hput⟩ := putThen_ok setByte hset dst j (wr16Enc3 (src.getD p 0)) _ hj h0
            (by simp [wr16Enc3] at hc ⊢; omega) hcap
          rw [hput]
          try dsimp only
          rw [ih (p + 1) (i + ix 1) j' {dst with written := dst.written ++ wr16Enc3 (src.getD p 0)}
            hlt (by omega) (by omega)
            (by simp [wr16Enc3] at hj' ⊢; omega) (by omega)
            (by simp [wr16Enc3] at hj' hc ⊢; omega) hcap]
          simp [List.append_assoc]
      · have hlt' : ¬ i < n := show ¬ i.val < n.val by omega
        have hc3 : ((src.getD p 0 &&& 0xfc00) == 0xd800 && decide (i < n)) = false := by
          rw [h3, Bool.true_and]
          exact decide_eq_false hlt'
        have hnil : src.drop (p + 1) = [] := List.drop_eq_nil_of_le (by omega)
        rw [hc3, if_neg Bool.false_ne_true, hnil]
        rw [hnil] at hc
        try dsimp only
        try dsimp only at hc
        obtain ⟨j', hj', hput⟩ := putThen_ok setByte hset dst j (wr16Enc3 (src.getD p 0)) _ hj h0
          (by simp [wr16Enc3] at hc ⊢; omega) hcap
        rw [hput]
        have := cont p i j' (wr16Enc3 (src.getD p 0)) hi (Nat.le_refl _) hp
          (by simp [wr16Enc3] at hj' ⊢; omega) (by omega)
          (by rw [hnil]; simp [wr16Next, wr16Enc3] at hj' hc ⊢; omega)
        rw [this, hnil]
        simp [wr16Next]
    · have h3' : ((src.getD p 0 &&& 0xfc00) == 0xd800) = false := by simpa using h3
      have hc3 : ((src.getD p 0 &&& 0xfc00) == 0xd800 && decide (i < n)) = false := by
        rw [h3', Bool.false_and]
      rw [if_neg h3, hc3, if_neg Bool.false_ne_true]
      rw [if_neg h3] at hc
      simp only [List.length_append] at hc
      obtain ⟨j', hj', hput⟩ := putThen_ok setByte hset dst j (wr16Enc3 (src.getD p 0)) _ hj h0
        (by simp [wr16Enc3] at hc ⊢; omega) hcap
      rw [hput]
      exact cont p i j' _ hi (Nat.le_refl _) hp (by simp [wr16Enc3] at hj' ⊢; omega) (by omega)
        (by simp [wr16Enc3] at hj' hc ⊢; omega)

/-! ## `transcode(UInt8, ::AbstractVector{UInt16})` end to end -/

theorem utf16ReadOfLaw (runtime : Utf16ToUtf8Runtime) (hlaw : Utf16ToUtf8RuntimeLaw runtime)
    (units : List UInt16) (hsmall : units.length < 2 ^ 62) :
    ∀ (k : Index) (q : Nat), q < units.length → k.val = q + 1 →
      runtime.read units k = .ok (units.getD q 0) := by
  intro k q hq hk
  obtain ⟨_, _, hread, _⟩ := hlaw
  have hkix : k = ix ((q + 1 : Nat) : Int) := by
    apply Subtype.ext
    rw [ixVal _ (by omega) (by omega), hk]
    simp
  rw [hkix]
  exact hread units (q + 1) _ (by omega) (by omega)
    (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq])

/-- A wrapped `Int` built from a natural number below `2^64` that is nonnegative is the
number itself: values in `[2^63, 2^64)` wrap to negative ones. -/
theorem ixNatVal_of_nonneg (L : Nat) (hL : L < 2 ^ 64) (h : 0 ≤ (ix (L : Int)).val) :
    (ix (L : Int)).val = L := by
  have e : (ix (L : Int)).val = wrapInt .i64 L := rfl
  rw [e] at h ⊢
  simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢
  simp at h ⊢
  omega

theorem utf16ToUtf8WrittenExact (runtime : Utf16ToUtf8Runtime)
    (units : List UInt16) (requested : Index)
    (hlaw : Utf16ToUtf8RuntimeLaw runtime) (hsmall : units.length < 2 ^ 62)
    (hsize : utf16OutputSize runtime units = .ok requested)
    (h0 : 0 ≤ requested.val) (hlt : requested.val < 2 ^ 62) :
    ∃ result : StringVector,
      transcodeUtf16ToUtf8 runtime.requireOneBased runtime.length runtime.read
        runtime.empty runtime.allocate runtime.setByte units = .ok result ∧
      result.capacity = requested ∧
      result.written = wr16Spec units.length (units.getD 0 0) (units.drop (0 + 1)) ∧
      requested.val =
        (wr16Spec units.length (units.getD 0 0) (units.drop (0 + 1))).length := by
  have hread := utf16ReadOfLaw runtime hlaw units hsmall
  obtain ⟨hreq, hlen, _, hempty1, hempty2, halloc, _, hset⟩ := hlaw
  have hn : (runtime.length units).val = units.length := by
    rw [hlen units, ixVal _ (by omega) (by omega)]
  unfold utf16OutputSize at hsize
  unfold transcodeUtf16ToUtf8
  rw [hreq units, exceptBindOk] at hsize ⊢
  try dsimp only at hsize ⊢
  by_cases hz : units.length = 0
  · have hz' : ((runtime.length units).val == 0) = true := by rw [hn, hz]; decide
    rw [if_pos hz'] at hsize ⊢
    have hreqv : requested = ix 0 := by injection hsize with h; exact h.symm
    have hix0 : (ix 0).val = 0 := ixVal 0 (by omega) (by omega)
    refine ⟨runtime.empty, rfl, ?_, ?_, ?_⟩
    · apply Subtype.ext
      rw [hempty1, hreqv]
      rfl
    · rw [hempty2]
      simp [wr16Spec, hz]
    · rw [hreqv, hix0]
      simp [wr16Spec, hz]
  · have hz' : ¬ (((runtime.length units).val == 0) = true) := by
      rw [hn]
      simpa using hz
    rw [if_neg hz'] at hsize ⊢
    have hfuel : (runtime.length units).val.toNat = units.length := by rw [hn]; simp
    have h1 : (ix 1).val = ((0 : Nat) : Int) + 1 := by rw [ixVal 1 (by omega) (by omega)]; simp
    rw [hread (ix 1) 0 (by omega) h1, exceptBindOk, hfuel] at hsize
    rw [hread (ix 1) 0 (by omega) h1, exceptBindOk, hfuel]
    have hcount := utf16CountLoop_spec runtime.read runtime.length units (runtime.length units)
      hread rfl hn hsmall units.length 0 (ix 1) (ix 0) (by omega) h1 (by omega)
    rw [hcount] at hsize
    rw [hcount, exceptBindOk]
    have hreqEq : requested = ix ((ix 0).val +
        (wr16Spec units.length (units.getD 0 0) (units.drop (0 + 1))).length) := by
      exact (Except.ok.inj hsize).symm
    have hL := wr16Spec_length units.length (units.getD 0 0) (units.drop (0 + 1))
    simp only [List.length_drop] at hL
    have hL' : (wr16Spec units.length (units.getD 0 0) (units.drop (0 + 1))).length <
        2 ^ 64 := by omega
    have hix0 : (ix 0).val = 0 := ixVal 0 (by omega) (by omega)
    have hreqEq' : requested = ix ((wr16Spec units.length (units.getD 0 0)
        (units.drop (0 + 1))).length : Int) := by
      rw [hreqEq, hix0, Int.zero_add]
    have hreqVal : requested.val =
        (wr16Spec units.length (units.getD 0 0) (units.drop (0 + 1))).length := by
      have h0' := h0
      rw [hreqEq'] at h0' ⊢
      exact ixNatVal_of_nonneg _ hL' h0'
    rw [← hreqEq]
    obtain ⟨result, hres, hcapEq, hw⟩ := halloc requested h0 hlt
    rw [hres, exceptBindOk, exceptBindOk]
    have hwrite := utf16WriteLoop_spec runtime.read runtime.setByte units (runtime.length units)
      hread hset hn hsmall units.length 0 (ix 1) (ix 0) result (by omega) h1 (by omega)
      (by rw [hw, hix0]; rfl) (by rw [hix0]; omega)
      (by rw [hix0, hcapEq, hreqVal]; omega) (by rw [hcapEq]; exact hlt)
    rw [hwrite]
    refine ⟨_, rfl, hcapEq, ?_, hreqVal⟩
    simp only [hw, List.nil_append]

theorem utf16ToUtf8Total_proven : Utf16ToUtf8TotalSpec := by
  intro runtime units requested hlaw hsmall hsize h0 hlt
  obtain ⟨result, hres, hcap, hwritten, hreqVal⟩ :=
    utf16ToUtf8WrittenExact runtime units requested hlaw hsmall hsize h0 hlt
  refine ⟨result, hres, hcap, ?_⟩
  simp [hwritten, hreqVal]


theorem utf16Wellformed_proven : Utf16WellformedSpec := by
  intro s units hvalid htrans
  rcases hvalid with ⟨cs, hcs, hbytes⟩
  rw [transcodeUtf16String_chars s cs hcs hbytes] at htrans
  injection htrans with hunits
  subst units
  exact wf16_units cs hcs

theorem utf16Roundtrip_proven : Utf16RoundtripSpec := by
  intro runtime bytesRuntime s units requested hlaw hbytesLaw hvalid htrans hsmall hsize h0 hlt
  rcases hvalid with ⟨cs, hcs, hbytes⟩
  rw [transcodeUtf16String_chars s cs hcs hbytes] at htrans
  injection htrans with hunits
  subst units
  have hwr : wr16Spec (cs.flatMap units16).length
      ((cs.flatMap units16).getD 0 0)
      ((cs.flatMap units16).drop (0 + 1)) = s.bytes := by
    cases hflat : cs.flatMap units16 with
    | nil =>
      have hnil := flatMap_nil_of_wf cs hcs hflat
      subst cs
      have hbytesNil : s.bytes = [] := by simpa using hbytes
      rw [hbytesNil]
      simp [wr16Spec]
    | cons u us =>
      have hlen := chars_le_units16 cs hcs
      rw [hflat] at hlen
      have hspec := wr16Spec_chars cs hcs (us.length + 1) u us
        (by simpa using hlen) hflat
      calc
        wr16Spec (u :: us).length ((u :: us).getD 0 0) ((u :: us).drop (0 + 1)) =
          wr16Spec (us.length + 1) u us := by simp
        _ = cs.flatten := hspec
        _ = s.bytes := hbytes.symm
  obtain ⟨result, hres, hcap, hwritten, hreqVal⟩ :=
    utf16ToUtf8WrittenExact runtime (cs.flatMap units16) requested
      hlaw hsmall hsize h0 hlt
  have hresultBytes : result.written = s.bytes := by
    rw [hwritten, hwr]
  have hreqBytes : requested.val = (s.bytes.length : Int) := by
    calc
      requested.val =
          (wr16Spec (cs.flatMap units16).length
            ((cs.flatMap units16).getD 0 0)
            ((cs.flatMap units16).drop (0 + 1))).length := hreqVal
      _ = (s.bytes.length : Int) := by rw [hwr]
  have hrequestedNat : requested.val.toNat = s.bytes.length := by
    rw [hreqBytes]
    simp
  have h8 : transcode (T := UInt8) (Output := List UInt8) (cs.flatMap units16) =
      .ok s.bytes := by
    change (transcodeUtf16ToUtf8 runtime.requireOneBased runtime.length runtime.read
      runtime.empty runtime.allocate runtime.setByte (cs.flatMap units16) >>= fun result =>
        pure result.written) = .ok s.bytes
    rw [hres, exceptBindOk, hresultBytes]
    rfl
  have hfrom : bytesRuntime.fromBytes s.bytes = .ok s := by
    obtain ⟨decoded, hdecoded, hdecodedBytes⟩ := hbytesLaw s.bytes s.small
    have hdecodedEq : decoded = s := by
      cases decoded with
      | mk decodedBytes decodedSmall =>
        cases s with
        | mk sourceBytes sourceSmall =>
          simp_all
    rw [hdecoded, hdecodedEq]
  have hstring : transcode (T := JString) (Output := JString) (cs.flatMap units16) =
      .ok s := by
    change (transcode (T := UInt8) (Output := List UInt8) (cs.flatMap units16) >>=
      bytesRuntime.fromBytes) = .ok s
    rw [h8, exceptBindOk, hfrom]
  refine ⟨result, s.bytes, hres, hcap, ?_, h8, ?_, hstring, hreqBytes, rfl⟩
  · rw [hresultBytes]
    exact hrequestedNat.symm
  · exact hresultBytes.symm

def entry (id : String) (juliaFns : List String) (statement source : String)
    (property : Lean.Name) : Entry :=
  { id := id, juliaFile := "base/strings/cstring.jl", juliaFns := juliaFns,
    statement := statement, source := source, status := .todo,
    prop := property, thm := none }
def provenEntry (value : Entry) (thmName : Lean.Name) : Entry :=
  { value with status := .proven, thm := some thmName }
def refutedEntry (value : Entry) (thmName : Lean.Name) (issue : String) : Entry :=
  { value with status := .refuted, thm := some thmName, issue := issue }

end JuliaLean.Proofs.base.strings.cstring

namespace JuliaLean.ChatGPT.Batch4.Group17
open JuliaLean.Proofs.base.strings.cstring
open JuliaLean.base.strings.cstring

theorem StringscovaCstringUnsafeStringConvertFaithful_proven : JuliaLean.Proofs.base.strings.cstring.CStringNulSpec :=
  cstringNul_proven

theorem group17CwstringAddress {T : Type} [CwstringTarget T] (p : Cwstring) :
    (ptrCwstring (T := T) p).address = p.address := rfl

theorem group17CwstringTarget_iff : CwstringPointerTargetSpec ↔
    ∀ {T : Type} [CwstringTarget T], Ptr Cwchar_t = Ptr T := by
  constructor
  · intro h T inst
    exact (h (T := T) (⟨0⟩ : Cwstring)).1
  · intro h T inst p
    exact ⟨h, group17CwstringAddress p⟩

theorem group17CwstringEmpty (zero : Cwchar_t)
    (eq : Cwchar_t → Cwchar_t → Bool) (repr : List Cwchar_t → String)
    (toPtr : List Cwchar_t → StringResult (Ptr Cwchar_t)) :
    cconvertCwstringVector zero eq repr toPtr [] =
      .error JuliaLean.Strings.boundsErr := by
  rfl

theorem group17CwstringEmpty_contradiction (zero : Cwchar_t) :
    ¬ CwstringVectorTerminatorTotalSpec := by
  classical
  intro h
  obtain ⟨message, bad⟩ := h zero (fun x y => decide (x = y)) (fun _ => "")
    (fun _ => .ok ⟨0⟩) [] (by intro value; simp only [decide_eq_true_eq]) (Or.inl rfl)
  rw [group17CwstringEmpty] at bad
  cases bad

theorem group17CwstringTerminator_iff : CwstringVectorTerminatorTotalSpec ↔
    ¬ Nonempty Cwchar_t := by
  constructor
  · intro h ⟨zero⟩
    exact group17CwstringEmpty_contradiction zero h
  · intro h zero
    exact False.elim (h ⟨zero⟩)

end JuliaLean.ChatGPT.Batch4.Group17

namespace JuliaLean.ChatGPT.Batch4.Group17
open JuliaLean
open JuliaLean.Proofs.base.strings.cstring
open JuliaLean.base.strings.cstring

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

local macro "g17OriginalSeek" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JuliaLean.base.strings.string
    `JuliaLean.base.strings.string.lengthSeekLead))
local macro "g17OriginalCount" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JuliaLean.base.strings.string
    `JuliaLean.base.strings.string.lengthCountLoop))

abbrev group17LengthSeek (s : JString) (n : Index) (fuel : Nat) (i : Index) (b : UInt8) :=
  g17OriginalSeek JuliaLean.base.strings.string.stringByteAt s n fuel i b
abbrev group17LengthCount (s : JString) (n : Index) (fuel : Nat)
    (i : Index) (b : UInt8) (c : Index) :=
  g17OriginalCount JuliaLean.base.strings.string.stringByteAt s n fuel i b c

abbrev group17IsLead (b : UInt8) : Bool := 0xc0 ≤ b && b ≤ 0xf7
abbrev group17IsCont (b : UInt8) : Bool :=
  JuliaLean.base.strings.string.isValidContinuation b

def group17Absorbed : List UInt8 → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
      if group17IsLead a then
        if group17IsCont b then
          if a ≥ 0xe0 then
            match rest with
            | [] => 1
            | c :: cs =>
                if group17IsCont c then
                  if a ≥ 0xf0 then
                    match cs with
                    | [] => 2
                    | d :: ds =>
                        (if group17IsCont d then 3 else 2) + group17Absorbed (d :: ds)
                  else 2 + group17Absorbed (c :: cs)
                else 1 + group17Absorbed (c :: cs)
          else 1 + group17Absorbed (b :: rest)
        else group17Absorbed (b :: rest)
      else group17Absorbed (b :: rest)

theorem group17Absorbed_nil : group17Absorbed [] = 0 := rfl

theorem group17Absorbed_single (a : UInt8) : group17Absorbed [a] = 0 := rfl

theorem group17Absorbed_cons_cons (a b : UInt8) (rest : List UInt8) :
    group17Absorbed (a :: b :: rest) =
      (if group17IsLead a then
        if group17IsCont b then
          if a ≥ 0xe0 then
            match rest with
            | [] => 1
            | c :: cs =>
                if group17IsCont c then
                  if a ≥ 0xf0 then
                    match cs with
                    | [] => 2
                    | d :: ds =>
                        (if group17IsCont d then 3 else 2) + group17Absorbed (d :: ds)
                  else 2 + group17Absorbed (c :: cs)
                else 1 + group17Absorbed (c :: cs)
          else 1 + group17Absorbed (b :: rest)
        else group17Absorbed (b :: rest)
      else group17Absorbed (b :: rest)) := by
  rw [group17Absorbed.eq_def]

theorem group17Absorbed_nonlead (b : UInt8) (rest : List UInt8)
    (hb : group17IsLead b = false) :
    group17Absorbed (b :: rest) = group17Absorbed rest := by
  cases rest with
  | nil => rfl
  | cons c cs =>
    rw [group17Absorbed_cons_cons, hb]
    simp only [Bool.false_eq_true, ↓reduceIte]

theorem group17Seek_step (s : JString) (n : Index) (fuel : Nat) (i : Index) (b : UInt8) :
    group17LengthSeek s n (fuel + 1) i b =
      (let i := i + ix 1
       if i.val > n.val then none
       else if group17IsLead b then some (i, b)
       else group17LengthSeek s n fuel i (JuliaLean.base.strings.string.stringByteAt s i)) := by
  rfl

theorem group17Read_drop (s : JString) (p : Nat) (i : Index)
    (b : UInt8) (rest : List UInt8) (hi : i.val = (p : Int) + 1)
    (hdrop : s.bytes.drop p = b :: rest) :
    JuliaLean.base.strings.string.stringByteAt s i = b := by
  change s.bytes.getD (i.val.toNat - 1) 0 = b
  have he : i.val.toNat - 1 = p := by omega
  rw [he]
  have h := getD_of_drop s.bytes (b :: rest) p 0 0 hdrop
  simpa only [Nat.add_zero, List.getD_cons_zero] using h

theorem group17Seek_spec (s : JString) (n : Index) (hn : n.val = s.bytes.length) :
    ∀ (fuel p : Nat) (i : Index) (a : UInt8) (rest : List UInt8),
    s.bytes.drop p = a :: rest → i.val = (p : Int) + 1 → rest.length ≤ fuel →
    match group17LengthSeek s n fuel i a with
    | none => group17Absorbed (a :: rest) = 0
    | some (j, lead) => ∃ q tail,
        p < q ∧ q < s.bytes.length ∧ j.val = (q : Int) + 1 ∧
        s.bytes.drop q = tail ∧ group17IsLead lead = true ∧
        group17Absorbed (a :: rest) = group17Absorbed (lead :: tail) := by
  intro fuel
  induction fuel with
  | zero =>
    intro p i a rest hd hi hf
    have hz : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst rest
    rfl
  | succ fuel ih =>
    intro p i a rest hd hi hf
    have hs := s.small
    have hl := congrArg List.length hd
    simp only [List.length_drop, List.length_cons] at hl
    have hp : p < s.bytes.length := by omega
    have hi1 := indexAddOne i (by omega) (by omega)
    rw [group17Seek_step]
    by_cases hout : (i + ix 1).val > n.val
    · rw [if_pos hout]
      have hz : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst rest
      rfl
    · rw [if_neg hout]
      cases rest with
      | nil => simp only [List.length_nil] at hl; omega
      | cons b bs =>
        have hd1 : s.bytes.drop (p + 1) = b :: bs := by
          have h := congrArg (List.drop 1) hd
          simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using h
        have hr := group17Read_drop s (p + 1) (i + ix 1) b bs (by omega) hd1
        cases hlead : group17IsLead a with
        | false =>
          simp only [hlead, Bool.false_eq_true, ↓reduceIte, hr]
          have ht := ih (p + 1) (i + ix 1) b bs hd1 (by omega) (by
            simp only [List.length_cons] at hf
            omega)
          cases he : group17LengthSeek s n fuel (i + ix 1) b with
          | none =>
            rw [he] at ht
            rw [group17Absorbed_nonlead a (b :: bs) hlead]
            exact ht
          | some pair =>
            rcases pair with ⟨j, lead⟩
            rw [he] at ht
            rcases ht with ⟨q, tail, hq, hqn, hj, htail, hlead', hcount⟩
            exact ⟨q, tail, by omega, hqn, hj, htail, hlead',
              (group17Absorbed_nonlead a (b :: bs) hlead).trans hcount⟩
        | true =>
          simp only [hlead, ↓reduceIte]
          exact ⟨p + 1, b :: bs, by omega, by omega, by omega, hd1, True.intro, rfl⟩

theorem group17Count_step (s : JString) (n : Index) (fuel : Nat)
    (i : Index) (b : UInt8) (count : Index) :
    group17LengthCount s n (fuel + 1) i b count =
      (match group17LengthSeek s n fuel i b with
      | none => count
      | some (i, lead) =>
          let b := JuliaLean.base.strings.string.stringByteAt s i
          let first := group17IsCont b
          let count := count - JuliaLean.base.strings.string.stringIndexBool first
          if !(first && lead ≥ 0xe0) then
            group17LengthCount s n fuel i b count
          else
            let i := i + ix 1
            if i.val > n.val then count
            else
              let b := JuliaLean.base.strings.string.stringByteAt s i
              let second := group17IsCont b
              let count := count - JuliaLean.base.strings.string.stringIndexBool second
              if !(second && lead ≥ 0xf0) then
                group17LengthCount s n fuel i b count
              else
                let i := i + ix 1
                if i.val > n.val then count
                else
                  let b := JuliaLean.base.strings.string.stringByteAt s i
                  group17LengthCount s n fuel i b
                    (count - JuliaLean.base.strings.string.stringIndexBool (group17IsCont b))) := by
  rfl

theorem group17SubBool_value (c : Index) (b : Bool)
    (hlo : (if b then (1 : Int) else 0) ≤ c.val) (hhi : c.val ≤ 2 ^ 62) :
    (c - JuliaLean.base.strings.string.stringIndexBool b).val =
      c.val - (if b then 1 else 0) := by
  have hv : (JuliaLean.base.strings.string.stringIndexBool b).val =
      (if b then (1 : Int) else 0) := by
    cases b <;> rfl
  change wrapInt .i64 (c.val -
    (JuliaLean.base.strings.string.stringIndexBool b).val) = _
  rw [hv]
  apply wrapInt_of_inRange
  change -(2 ^ 63 : Int) ≤ c.val - (if b then 1 else 0) ∧
    c.val - (if b then 1 else 0) ≤ 2 ^ 63 - 1
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hlo ⊢ <;> constructor <;> omega

theorem group17SubFalse_value (c : Index) (hlo : 0 ≤ c.val) (hhi : c.val ≤ 2 ^ 62) :
    (c - JuliaLean.base.strings.string.stringIndexBool false).val = c.val := by
  have h := group17SubBool_value c false
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using hlo) hhi
  simpa only [Bool.false_eq_true, ↓reduceIte, Int.sub_zero] using h

theorem group17SubTrue_value (c : Index) (hlo : 1 ≤ c.val) (hhi : c.val ≤ 2 ^ 62) :
    (c - JuliaLean.base.strings.string.stringIndexBool true).val = c.val - 1 := by
  have h := group17SubBool_value c true
    (by simpa only [↓reduceIte] using hlo) hhi
  simpa only [↓reduceIte] using h

theorem group17Count_spec (s : JString) (n : Index) (hn : n.val = s.bytes.length) :
    ∀ (fuel p : Nat) (i : Index) (a : UInt8) (rest : List UInt8) (count : Index),
    s.bytes.drop p = a :: rest → i.val = (p : Int) + 1 →
    (a :: rest).length ≤ fuel →
    (group17Absorbed (a :: rest) : Int) ≤ count.val → count.val ≤ 2 ^ 62 →
    (group17LengthCount s n fuel i a count).val =
      count.val - (group17Absorbed (a :: rest) : Int) := by
  intro fuel
  induction fuel with
  | zero =>
    intro p i a rest count hd hi hf
    simp only [List.length_cons] at hf
    all_goals omega
  | succ fuel ih =>
    intro p i a rest count hd hi hf hlo hhi
    have hs := s.small
    have hl := congrArg List.length hd
    simp only [List.length_drop, List.length_cons] at hl hf
    have hseek := group17Seek_spec s n hn fuel p i a rest hd hi (by omega)
    rw [group17Count_step]
    cases hstep : group17LengthSeek s n fuel i a with
    | none =>
      rw [hstep] at hseek
      simp only [hseek, Int.natCast_zero, Int.sub_zero]
    | some pair =>
      rcases pair with ⟨j, lead⟩
      rw [hstep] at hseek
      rcases hseek with ⟨q, tail, hpq, hqn, hj, htail, hlead, habsorbed⟩
      cases tail with
      | nil =>
        have hlen := congrArg List.length htail
        simp only [List.length_drop, List.length_nil] at hlen
        all_goals omega
      | cons b bs =>
        have hlen := congrArg List.length htail
        simp only [List.length_drop, List.length_cons] at hlen
        have hb := group17Read_drop s q j b bs hj htail
        simp only [hb]
        have hb1 : (j + ix 1).val = (q : Int) + 2 := by
          rw [indexAddOne j (by omega) (by omega), hj]
          all_goals omega
        rw [habsorbed]
        rw [habsorbed] at hlo
        cases hc1 : group17IsCont b with
        | false =>
          have ha : group17Absorbed (lead :: b :: bs) = group17Absorbed (b :: bs) := by
            simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, hlead, hc1, Bool.false_eq_true, ↓reduceIte]
          have hv := group17SubFalse_value count (by rw [ha] at hlo; omega) hhi
          simp only [hc1, Bool.false_and, Bool.not_false, ↓reduceIte]
          rw [ih q j b bs _ htail hj (by simp only [List.length_cons]; omega) (by rw [hv]; rw [ha] at hlo; omega)
            (by rw [hv]; omega), hv, ha]
          all_goals omega
        | true =>
          by_cases he0 : 0xe0 ≤ lead
          · have hv := group17SubTrue_value count (by
              simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, hlead, hc1, he0, ↓reduceIte] at hlo
              cases bs with
              | nil => simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons] at hlo; omega
              | cons c cs =>
                cases hc2 : group17IsCont c <;>
                  simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hlo
                · omega
                · by_cases he1 : 0xf0 ≤ lead <;> simp only [he1, ↓reduceIte] at hlo
                  · cases cs with
                    | nil => dsimp only at hlo; omega
                    | cons d ds =>
                      cases hc3 : group17IsCont d <;>
                        simp only [hc3, Bool.false_eq_true, ↓reduceIte] at hlo <;> omega
                  · omega) hhi
            simp only [hc1, he0, decide_true, Bool.true_and, Bool.not_true,
              Bool.false_eq_true, ↓reduceIte]
            by_cases hout1 : (j + ix 1).val > n.val
            · rw [if_pos hout1]
              have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
              subst bs
              simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, hlead, hc1, he0, ↓reduceIte]
              exact hv
            · rw [if_neg hout1]
              cases bs with
              | nil => simp only [List.length_nil] at hlen; omega
              | cons c cs =>
                try simp only [List.length_cons] at hlen
                have htail1 : s.bytes.drop (q + 1) = c :: cs := by
                  have h := congrArg (List.drop 1) htail
                  simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using h
                have hc := group17Read_drop s (q + 1) (j + ix 1) c cs (by omega) htail1
                simp only [hc]
                cases hc2 : group17IsCont c with
                | false =>
                  have ha : group17Absorbed (lead :: b :: c :: cs) =
                      1 + group17Absorbed (c :: cs) := by
                    simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, hlead, hc1, he0, hc2,
                      Bool.false_eq_true, ↓reduceIte]
                  have hv2 := group17SubFalse_value
                    (count - JuliaLean.base.strings.string.stringIndexBool true)
                    (by rw [hv]; rw [ha] at hlo; omega) (by rw [hv]; omega)
                  simp only [hc2, Bool.false_and, Bool.not_false, ↓reduceIte]
                  rw [ih (q + 1) (j + ix 1) c cs _ htail1 (by omega) (by simp only [List.length_cons]; omega)
                    (by rw [hv2, hv]; rw [ha] at hlo; omega)
                    (by rw [hv2, hv]; omega), hv2, hv, ha]
                  all_goals omega
                | true =>
                  by_cases he1 : 0xf0 ≤ lead
                  · have hv2 := group17SubTrue_value
                      (count - JuliaLean.base.strings.string.stringIndexBool true)
                      (by
                        rw [hv]
                        simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, hlead, hc1, he0, hc2, he1,
                          ↓reduceIte] at hlo
                        cases cs with
                        | nil => dsimp only at hlo; omega
                        | cons d ds =>
                          cases hc3 : group17IsCont d <;>
                            simp only [hc3, Bool.false_eq_true, ↓reduceIte] at hlo <;> omega)
                      (by rw [hv]; omega)
                    simp only [hc2, he1, decide_true, Bool.true_and, Bool.not_true,
                      Bool.false_eq_true, ↓reduceIte]
                    have hb2 : (j + ix 1 + ix 1).val = (q : Int) + 3 := by
                      rw [indexAddOne (j + ix 1) (by omega) (by omega), hb1]
                      all_goals omega
                    by_cases hout2 : (j + ix 1 + ix 1).val > n.val
                    · rw [if_pos hout2]
                      have hnil : cs = [] := List.eq_nil_of_length_eq_zero (by
                        try simp only [List.length_cons] at hlen
                        omega)
                      subst cs
                      simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, hlead, hc1, he0, hc2, he1, ↓reduceIte]
                      rw [hv2, hv]
                      all_goals omega
                    · rw [if_neg hout2]
                      cases cs with
                      | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
                      | cons d ds =>
                        try simp only [List.length_cons] at hlen
                        have htail2 : s.bytes.drop (q + 2) = d :: ds := by
                          have h := congrArg (List.drop 2) htail
                          simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using h
                        have hd := group17Read_drop s (q + 2) (j + ix 1 + ix 1) d ds
                          (by omega) htail2
                        simp only [hd]
                        have ha : group17Absorbed (lead :: b :: c :: d :: ds) =
                            (if group17IsCont d then 3 else 2) + group17Absorbed (d :: ds) := by
                          simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, hlead, hc1, he0, hc2, he1, ↓reduceIte]
                        have hv3 := group17SubBool_value
                          (count - JuliaLean.base.strings.string.stringIndexBool true -
                            JuliaLean.base.strings.string.stringIndexBool true) (group17IsCont d)
                          (by
                            rw [hv2, hv]
                            rw [ha] at hlo
                            cases hthird : group17IsCont d <;> simp only [hthird, Bool.false_eq_true, ↓reduceIte] at hlo ⊢ <;> omega)
                          (by rw [hv2, hv]; omega)
                        rw [ih (q + 2) (j + ix 1 + ix 1) d ds _ htail2 (by omega)
                          (by try simp only [List.length_cons] at hlen ⊢; omega)
                          (by
                            rw [hv3, hv2, hv]
                            rw [ha] at hlo
                            cases hthird : group17IsCont d <;> simp only [hthird, Bool.false_eq_true, ↓reduceIte] at hlo ⊢ <;> omega)
                          (by rw [hv3, hv2, hv]; cases hthird : group17IsCont d <;>
                            simp only [hthird, Bool.false_eq_true, ↓reduceIte] <;> omega), hv3, hv2, hv, ha]
                        cases hthird : group17IsCont d <;> simp only [hthird, Bool.false_eq_true, ↓reduceIte] <;> omega
                  · have ha : group17Absorbed (lead :: b :: c :: cs) =
                        2 + group17Absorbed (c :: cs) := by
                      simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, hlead, hc1, he0, hc2, he1, ↓reduceIte]
                    have hv2 := group17SubTrue_value
                      (count - JuliaLean.base.strings.string.stringIndexBool true)
                      (by rw [hv]; rw [ha] at hlo; omega) (by rw [hv]; omega)
                    simp only [hc2, he1, decide_false, Bool.and_false, Bool.not_false, ↓reduceIte]
                    rw [ih (q + 1) (j + ix 1) c cs _ htail1 (by omega) (by simp only [List.length_cons]; omega)
                      (by rw [hv2, hv]; rw [ha] at hlo; omega) (by rw [hv2, hv]; omega),
                      hv2, hv, ha]
                    all_goals omega
          · have ha : group17Absorbed (lead :: b :: bs) =
                1 + group17Absorbed (b :: bs) := by
              simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, hlead, hc1, he0, ↓reduceIte]
            have hv := group17SubTrue_value count (by rw [ha] at hlo; omega) hhi
            simp only [hc1, he0, decide_false, Bool.and_false, Bool.not_false, ↓reduceIte]
            rw [ih q j b bs _ htail hj (by simp only [List.length_cons]; omega) (by rw [hv]; rw [ha] at hlo; omega)
              (by rw [hv]; omega), hv, ha]
            all_goals omega

theorem group17Absorbed_le : ∀ bytes : List UInt8, group17Absorbed bytes ≤ bytes.length := by
  have main : ∀ n : Nat, ∀ bytes : List UInt8, bytes.length = n →
      group17Absorbed bytes ≤ bytes.length := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro bytes hlen
      cases bytes with
      | nil => simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, List.length_nil, Nat.le_refl]
      | cons a rest =>
        cases rest with
        | nil => simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, List.length_cons, List.length_nil]; omega
        | cons b bs =>
          have hb := ih (b :: bs).length (by try simp only [List.length_cons] at hlen ⊢; omega)
            (b :: bs) rfl
          rw [group17Absorbed_cons_cons]
          split
          · split
            · split
              · cases bs with
                | nil => simp only [List.length_cons, List.length_nil]; omega
                | cons c cs =>
                  dsimp only
                  have hc := ih (c :: cs).length
                    (by try simp only [List.length_cons] at hlen ⊢; omega) (c :: cs) rfl
                  split
                  · split
                    · cases cs with
                      | nil => simp only [List.length_cons, List.length_nil]; omega
                      | cons d ds =>
                        dsimp only
                        have hd := ih (d :: ds).length
                          (by try simp only [List.length_cons] at hlen ⊢; omega) (d :: ds) rfl
                        split <;> simp only [List.length_cons] at hb hc hd ⊢ <;> omega
                    · simp only [List.length_cons] at hc ⊢; omega
                  · simp only [List.length_cons] at hc ⊢; omega
              · simp only [List.length_cons] at hb ⊢; omega
            · simp only [List.length_cons] at hb ⊢; omega
          · simp only [List.length_cons] at hb ⊢; omega
  intro bytes
  exact main bytes.length bytes rfl

theorem group17Continued_model (s : JString) (i n c : Index) :
    JuliaLean.base.strings.string.lengthContinuedInternal
      JuliaLean.base.strings.string.stringByteAt s i n c =
    (if !(i.val < n.val) then c
     else group17LengthCount s n (n.val - i.val + 1).toNat i
       (JuliaLean.base.strings.string.stringByteAt s i) c) := rfl

theorem group17StringLength_absorbed (s : JString) :
    (JuliaLean.base.strings.string.stringLength s).val =
      (s.bytes.length : Int) - (group17Absorbed s.bytes : Int) := by
  have hs := s.small
  have hn : (JuliaLean.base.strings.string.stringNcodeunits s).val = s.bytes.length :=
    ixVal _ (by omega) (by omega)
  unfold JuliaLean.base.strings.string.stringLength JuliaLean.base.strings.string.lengthString
    JuliaLean.base.strings.string.lengthContinuedString
  rw [group17Continued_model]
  have h1 : (JuliaLean.Strings.ix 1).val = 1 := rfl
  simp only [h1, hn]
  by_cases hsmall : 1 < (s.bytes.length : Int)
  · simp only [hsmall, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hfuel : ((s.bytes.length : Int) - 1 + 1).toNat = s.bytes.length := by omega
    rw [hfuel]
    cases hbytes : s.bytes with
    | nil => simp only [hbytes, List.length_nil] at hsmall; omega
    | cons a rest =>
      have hread : JuliaLean.base.strings.string.stringByteAt s (JuliaLean.Strings.ix 1) = a := by
        apply group17Read_drop s 0 (JuliaLean.Strings.ix 1) a rest (by rfl)
        simpa only [List.drop_zero] using hbytes
      rw [hread]
      have h := group17Count_spec s (JuliaLean.base.strings.string.stringNcodeunits s) hn
        s.bytes.length 0 (JuliaLean.Strings.ix 1) a rest
        (JuliaLean.base.strings.string.stringNcodeunits s)
        (by simpa only [List.drop_zero] using hbytes) (by rfl)
        (by rw [hbytes]; exact Nat.le_refl _)
        (by rw [hn, ← hbytes]; have hb := group17Absorbed_le s.bytes; omega)
        (by rw [hn]; omega)
      simpa only [hn, hbytes] using h
  · simp only [hsmall, decide_false, Bool.not_false, ↓reduceIte]
    have ha : group17Absorbed s.bytes = 0 := by
      cases hb : s.bytes with
      | nil => rfl
      | cons a rest =>
        have hz : rest = [] := by
          have hl : (s.bytes.length : Int) ≤ 1 := by omega
          simp only [hb, List.length_cons] at hl
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst rest
        rfl
    rw [ha]
    omega

end JuliaLean.ChatGPT.Batch4.Group17

namespace JuliaLean.ChatGPT.Batch4.Group17
open JuliaLean.Transcode

set_option maxRecDepth 8192

theorem group17WfBounds1 (a : UInt8) (hw : wfChar [a] = true) :
    a.toNat < 128 := by
  simp only [wfChar, decide_eq_true_eq, UInt8.le_iff_toNat_le] at hw
  change a.toNat ≤ 127 at hw
  omega

theorem group17WfBounds2 (a b : UInt8) (hw : wfChar [a, b] = true) :
    192 ≤ a.toNat ∧ a.toNat < 224 ∧ 128 ≤ b.toNat ∧ b.toNat < 192 := by
  simp only [wfChar, isC, Bool.and_eq_true, decide_eq_true_eq,
    UInt8.le_iff_toNat_le] at hw
  change (194 ≤ a.toNat ∧ a.toNat ≤ 223) ∧ (128 ≤ b.toNat ∧ b.toNat ≤ 191) at hw
  omega

theorem group17WfBounds3 (a b c : UInt8) (hw : wfChar [a, b, c] = true) :
    224 ≤ a.toNat ∧ a.toNat < 240 ∧ 128 ≤ b.toNat ∧ b.toNat < 192 ∧
    128 ≤ c.toNat ∧ c.toNat < 192 := by
  by_cases h0 : a = 0xe0
  · subst a
    simp only [wfChar, beq_self_eq_true, ↓reduceIte, isC,
      Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at hw
    change (128 ≤ c.toNat ∧ c.toNat ≤ 191) ∧ (160 ≤ b.toNat ∧ b.toNat ≤ 191) at hw
    change 224 ≤ 224 ∧ 224 < 240 ∧ 128 ≤ b.toNat ∧ b.toNat < 192 ∧
      128 ≤ c.toNat ∧ c.toNat < 192
    omega
  · have h0b : (a == 0xe0) = false := beq_eq_false_iff_ne.mpr h0
    by_cases hd : a = 0xed
    · subst a
      simp only [wfChar, h0b, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, isC,
        Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at hw
      change (128 ≤ c.toNat ∧ c.toNat ≤ 191) ∧ (128 ≤ b.toNat ∧ b.toNat ≤ 159) at hw
      change 224 ≤ 237 ∧ 237 < 240 ∧ 128 ≤ b.toNat ∧ b.toNat < 192 ∧
        128 ≤ c.toNat ∧ c.toNat < 192
      omega
    · have hdb : (a == 0xed) = false := beq_eq_false_iff_ne.mpr hd
      simp only [wfChar, h0b, hdb, Bool.false_eq_true, ↓reduceIte, isC,
        Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at hw
      change (128 ≤ c.toNat ∧ c.toNat ≤ 191) ∧
        ((225 ≤ a.toNat ∧ a.toNat ≤ 239) ∧ (128 ≤ b.toNat ∧ b.toNat ≤ 191)) at hw
      omega

theorem group17WfBounds4 (a b c d : UInt8) (hw : wfChar [a, b, c, d] = true) :
    240 ≤ a.toNat ∧ a.toNat < 248 ∧ 128 ≤ b.toNat ∧ b.toNat < 192 ∧
    128 ≤ c.toNat ∧ c.toNat < 192 ∧ 128 ≤ d.toNat ∧ d.toNat < 192 := by
  by_cases h0 : a = 0xf0
  · subst a
    simp only [wfChar, beq_self_eq_true, ↓reduceIte, isC,
      Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at hw
    change ((128 ≤ c.toNat ∧ c.toNat ≤ 191) ∧ (128 ≤ d.toNat ∧ d.toNat ≤ 191)) ∧
      (144 ≤ b.toNat ∧ b.toNat ≤ 191) at hw
    change 240 ≤ 240 ∧ 240 < 248 ∧ 128 ≤ b.toNat ∧ b.toNat < 192 ∧
      128 ≤ c.toNat ∧ c.toNat < 192 ∧ 128 ≤ d.toNat ∧ d.toNat < 192
    omega
  · have h0b : (a == 0xf0) = false := beq_eq_false_iff_ne.mpr h0
    by_cases h4 : a = 0xf4
    · subst a
      simp only [wfChar, h0b, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, isC,
        Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at hw
      change ((128 ≤ c.toNat ∧ c.toNat ≤ 191) ∧ (128 ≤ d.toNat ∧ d.toNat ≤ 191)) ∧
        (128 ≤ b.toNat ∧ b.toNat ≤ 143) at hw
      change 240 ≤ 244 ∧ 244 < 248 ∧ 128 ≤ b.toNat ∧ b.toNat < 192 ∧
        128 ≤ c.toNat ∧ c.toNat < 192 ∧ 128 ≤ d.toNat ∧ d.toNat < 192
      omega
    · have h4b : (a == 0xf4) = false := beq_eq_false_iff_ne.mpr h4
      simp only [wfChar, h0b, h4b, Bool.false_eq_true, ↓reduceIte, isC,
        Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le] at hw
      change ((128 ≤ c.toNat ∧ c.toNat ≤ 191) ∧ (128 ≤ d.toNat ∧ d.toNat ≤ 191)) ∧
        ((241 ≤ a.toNat ∧ a.toNat ≤ 243) ∧ (128 ≤ b.toNat ∧ b.toNat ≤ 191)) at hw
      omega

open JuliaLean.Proofs.base.strings.cstring

set_option maxRecDepth 10000 in
theorem group17Cont_table : ∀ x : Fin 256,
    group17IsCont (UInt8.ofNat x.val) = decide (128 ≤ x.val ∧ x.val < 192) := by
  decide

theorem group17Cont_bounds (b : UInt8) :
    group17IsCont b = decide (128 ≤ b.toNat ∧ b.toNat < 192) := by
  have h := group17Cont_table ⟨b.toNat, UInt8.toNat_lt b⟩
  simpa only [UInt8.ofNat_toNat] using h

theorem group17Cont_nonlead (b : UInt8) (hb : group17IsCont b = true) :
    group17IsLead b = false := by
  rw [group17Cont_bounds] at hb
  simp only [decide_eq_true_eq] at hb
  simp only [group17IsLead, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    UInt8.le_iff_toNat_le, UInt8.toNat_ofNat]
  left
  omega

theorem group17Lead_of_nat (a : UInt8) (hlo : 192 ≤ a.toNat) (hhi : a.toNat < 248) :
    group17IsLead a = true := by
  simp only [group17IsLead, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le]
  change 192 ≤ a.toNat ∧ a.toNat ≤ 247
  omega

theorem group17Nonlead_of_nat (a : UInt8) (ha : a.toNat < 192) :
    group17IsLead a = false := by
  simp only [group17IsLead, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    UInt8.le_iff_toNat_le]
  left
  change ¬ 192 ≤ a.toNat
  omega

theorem group17Cont_of_nat (a : UInt8) (hlo : 128 ≤ a.toNat) (hhi : a.toNat < 192) :
    group17IsCont a = true := by
  rw [group17Cont_bounds]
  exact decide_eq_true ⟨hlo, hhi⟩

theorem group17Absorbed_valid : ∀ (cs : List (List UInt8)),
    (∀ c ∈ cs, JuliaLean.Transcode.wfChar c = true) →
    group17Absorbed cs.flatten + cs.length = cs.flatten.length := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons ch cs ih =>
    intro h
    have hw := h ch List.mem_cons_self
    have hi := ih (fun c hc => h c (List.mem_cons_of_mem ch hc))
    rw [List.flatten_cons, List.length_cons]
    rcases utf8WfCases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ |
      ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩
    · have hb := group17WfBounds1 a hw
      have ha := group17Nonlead_of_nat a (by omega)
      simp only [List.cons_append, List.nil_append, List.length_cons,
        group17Absorbed_nonlead a _ ha]
      omega
    · obtain ⟨ha0, ha1, hb0, hb1⟩ := group17WfBounds2 a b hw
      have ha := group17Lead_of_nat a ha0 (by omega)
      have hb := group17Cont_of_nat b hb0 hb1
      have hbn := group17Nonlead_of_nat b hb1
      have he0 : ¬ (0xe0 : UInt8) ≤ a := by
        intro he
        have he' := UInt8.le_iff_toNat_le.mp he
        change 224 ≤ a.toNat at he'
        omega
      simp only [List.cons_append, List.nil_append, group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, ha, hb, he0,
        ↓reduceIte, group17Absorbed_nonlead b _ hbn, List.length_cons]
      omega
    · obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1⟩ := group17WfBounds3 a b c hw
      have ha := group17Lead_of_nat a (by omega) (by omega)
      have hb := group17Cont_of_nat b hb0 hb1
      have hc := group17Cont_of_nat c hc0 hc1
      have hcn := group17Nonlead_of_nat c hc1
      have he0 : (0xe0 : UInt8) ≤ a := UInt8.le_iff_toNat_le.mpr ha0
      have hf0 : ¬ (0xf0 : UInt8) ≤ a := by
        intro he
        have he' := UInt8.le_iff_toNat_le.mp he
        change 240 ≤ a.toNat at he'
        omega
      simp only [List.cons_append, List.nil_append, group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, ha, hb, he0, hc, hf0,
        ↓reduceIte, group17Absorbed_nonlead c _ hcn, List.length_cons]
      omega
    · obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩ := group17WfBounds4 a b c d hw
      have ha := group17Lead_of_nat a (by omega) ha1
      have hb := group17Cont_of_nat b hb0 hb1
      have hc := group17Cont_of_nat c hc0 hc1
      have hd := group17Cont_of_nat d hd0 hd1
      have hdn := group17Nonlead_of_nat d hd1
      have he0 : (0xe0 : UInt8) ≤ a := UInt8.le_iff_toNat_le.mpr (by change 224 ≤ a.toNat; omega)
      have hf0 : (0xf0 : UInt8) ≤ a := UInt8.le_iff_toNat_le.mpr ha0
      simp only [List.cons_append, List.nil_append, group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, ha, hb, he0, hc, hf0, hd,
        ↓reduceIte, group17Absorbed_nonlead d _ hdn, List.length_cons]
      omega

theorem group17StringLength_valid (s : JuliaLean.base.strings.cstring.JString) (cs : List (List UInt8))
    (hcs : ∀ c ∈ cs, JuliaLean.Transcode.wfChar c = true)
    (hbytes : s.bytes = cs.flatten) :
    (JuliaLean.base.strings.string.stringLength s).val = (cs.length : Int) := by
  rw [group17StringLength_absorbed, hbytes]
  have h := group17Absorbed_valid cs hcs
  omega

theorem group17SmallByte_filter (b : UInt8) (hb : b.toNat < 240) :
    decide (0xf0 ≤ b) = false := by
  apply decide_eq_false
  intro he
  have hn := UInt8.le_iff_toNat_le.mp he
  change 240 ≤ b.toNat at hn
  omega

theorem group17Units16_count : ∀ (cs : List (List UInt8)),
    (∀ c ∈ cs, JuliaLean.Transcode.wfChar c = true) →
    (cs.flatMap units16).length = cs.length +
      (cs.flatten.filter (fun b => decide (0xf0 ≤ b))).length := by
  intro cs
  induction cs with
  | nil => intro _; rfl
  | cons ch cs ih =>
    intro h
    have hw := h ch List.mem_cons_self
    have hi := ih (fun c hc => h c (List.mem_cons_of_mem ch hc))
    simp only [List.flatMap_cons, List.flatten_cons, List.length_append,
      List.filter_append, List.length_cons, hi]
    rcases utf8WfCases ch hw with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ |
      ⟨a, b, c, rfl⟩ | ⟨a, b, c, d, rfl⟩
    · have hb := group17WfBounds1 a hw
      have f1 := group17SmallByte_filter a (by omega)
      simp only [units16, List.length_cons, List.length_nil, List.filter_cons, f1,
        Bool.false_eq_true, ↓reduceIte, List.filter_nil]
      omega
    · obtain ⟨ha0, ha1, hb0, hb1⟩ := group17WfBounds2 a b hw
      have f1 := group17SmallByte_filter a (by omega)
      have f2 := group17SmallByte_filter b (by omega)
      simp only [units16, List.length_cons, List.length_nil, List.filter_cons, f1, f2,
        Bool.false_eq_true, ↓reduceIte, List.filter_nil]
      omega
    · obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1⟩ := group17WfBounds3 a b c hw
      have f1 := group17SmallByte_filter a ha1
      have f2 := group17SmallByte_filter b (by omega)
      have f3 := group17SmallByte_filter c (by omega)
      simp only [units16, List.length_cons, List.length_nil, List.filter_cons, f1, f2, f3,
        Bool.false_eq_true, ↓reduceIte, List.filter_nil]
      omega
    · obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd0, hd1⟩ := group17WfBounds4 a b c d hw
      have f1 : decide (0xf0 ≤ a) = true := decide_eq_true (UInt8.le_iff_toNat_le.mpr ha0)
      have f2 := group17SmallByte_filter b (by omega)
      have f3 := group17SmallByte_filter c (by omega)
      have f4 := group17SmallByte_filter d (by omega)
      simp only [units16, List.length_cons, List.length_nil, List.filter_cons, f1, f2, f3, f4,
        Bool.false_eq_true, ↓reduceIte, List.filter_nil]
      omega

theorem group17Utf16Length_from_character_transcode
    (hchars : ∀ (s : JuliaLean.base.strings.cstring.JString) (cs : List (List UInt8)),
      (∀ c ∈ cs, JuliaLean.Transcode.wfChar c = true) → s.bytes = cs.flatten →
      JuliaLean.base.strings.cstring.transcode (T := UInt16) (Output := List UInt16) s =
        .ok (cs.flatMap units16)) :
    ∀ (s : JuliaLean.base.strings.cstring.JString) (units : List UInt16),
      JuliaLean.Transcode.ValidUtf8 s.bytes →
      JuliaLean.base.strings.cstring.transcode (T := UInt16) (Output := List UInt16) s = .ok units →
      (units.length : Int) = (JuliaLean.base.strings.string.stringLength s).val +
        ((s.bytes.filter (fun b => decide (0xf0 ≤ b))).length : Int) := by
  intro s units hvalid htrans
  rcases hvalid with ⟨cs, hcs, hbytes⟩
  rw [hchars s cs hcs hbytes] at htrans
  injection htrans with hu
  subst units
  rw [group17Units16_count cs hcs, group17StringLength_valid s cs hcs hbytes, hbytes]
  all_goals omega

end JuliaLean.ChatGPT.Batch4.Group17

namespace JuliaLean.ChatGPT.Batch4.Group17
open JuliaLean.Proofs.base.strings.cstring

theorem TranscodeUtf16Length_proven : JuliaLean.Proofs.base.strings.cstring.Utf16LengthSpec :=
  group17Utf16Length_from_character_transcode transcodeUtf16String_chars

end JuliaLean.ChatGPT.Batch4.Group17
namespace JuliaLean.ChatGPT.Batch8.Group8

/-- An abstract iteration prefix, independent of byte decoding or code-unit conversion. -/
def g8CstringGenericPrefix {Cursor Character : Type}
    (iterate : Cursor → Option (Character × Cursor)) :
    List Character → Cursor → Cursor → Prop
  | [], start, stop => start = stop
  | character :: characters, start, stop =>
    Exists fun next => iterate start = some (character, next) ∧
      g8CstringGenericPrefix iterate characters next stop

/-- Moving one step from the accumulator length to the trace length preserves their sum. -/
theorem g8CstringCoreLengthShift (before trace : Nat) :
    (before + 1) + trace = before + (trace + 1) := by
  induction trace with
  | zero => rfl
  | succ trace ih =>
    exact congrArg Nat.succ ih

/-- Success of any loop with these three source equations gives a complete iteration trace.

The finalizer only needs to preserve length. No validity assumptions about the characters or
the conversion function are required. The equations are hypotheses, not a replacement model.
-/
theorem g8CstringGenericLoopTrace {Cursor Character UnitValue Error : Type}
    (iterate : Cursor → Option (Character × Cursor))
    (convert : Character → Except Error UnitValue)
    (loop : Nat → Cursor → List UnitValue → Except Error (List UnitValue))
    (finish : List UnitValue → List UnitValue)
    (finishLength : ∀ before, (finish before).length = before.length)
    (zeroFails : ∀ start before output, loop 0 start before = .ok output → False)
    (noneStep : ∀ fuel start before, iterate start = none →
      loop (fuel + 1) start before = .ok (finish before))
    (someStep : ∀ fuel start before character next,
      iterate start = some (character, next) →
      loop (fuel + 1) start before =
        match convert character with
        | .error error => .error error
        | .ok value => loop fuel next (value :: before)) :
    ∀ fuel start before output, loop fuel start before = .ok output →
      Exists fun characters => Exists fun stop =>
        g8CstringGenericPrefix iterate characters start stop ∧
        iterate stop = none ∧ output.length = before.length + characters.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro start before output h
    exact False.elim (zeroFails start before output h)
  | succ fuel ih =>
    intro start before output h
    cases hiter : iterate start with
    | none =>
      rw [noneStep fuel start before hiter] at h
      cases h
      exact ⟨[], start, rfl, hiter, finishLength before⟩
    | some pair =>
      cases pair with
      | mk character next =>
        rw [someStep fuel start before character next hiter] at h
        cases hconvert : convert character with
        | error error =>
          rw [hconvert] at h
          cases h
        | ok value =>
          rw [hconvert] at h
          cases ih next (value :: before) output h with
          | intro characters hexists =>
            cases hexists with
            | intro stop htrace =>
              exact ⟨character :: characters, stop, ⟨next, hiter, htrace.1⟩,
                htrace.2.1, Eq.trans htrace.2.2
                  (g8CstringCoreLengthShift before.length characters.length)⟩

open JuliaLean.Proofs.base.strings.cstring
open JuliaLean.base.strings.cstring


end JuliaLean.ChatGPT.Batch8.Group8

namespace JuliaLean.ChatGPT.Batch8.Group8
open JuliaLean.ChatGPT.Batch4.Group17
open JuliaLean
open JuliaLean.Proofs.base.strings.cstring
open JuliaLean.base.strings.cstring
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The concrete source adapter and the already imported byte-string iterator agree. -/
theorem g8CstringIterate_basic (s : JString) (i : Index) :
    iterateCstringString s i = JuliaLean.Strings.iterate s i := by
  have hc (j : Index) (u : UInt32) :
      JuliaLean.base.strings.string.iterateContinued
        JuliaLean.Strings.ncodeunits JuliaLean.Strings.cu s j u =
      JuliaLean.Strings.iterateContinued s j u := by
    simp only [JuliaLean.base.strings.string.iterateContinued,
      JuliaLean.Strings.iterateContinued, Id.run, pure, JuliaLean.Strings.isCont, bne_eq]
  unfold iterateCstringString
  change JuliaLean.base.strings.string.iterateString (fun _ => ix 1)
    JuliaLean.Strings.ncodeunits JuliaLean.Strings.cu JuliaLean.Strings.between s i = _
  simp only [JuliaLean.base.strings.string.iterateString, JuliaLean.Strings.iterate, hc]

theorem g8CstringShift24 (b : UInt8) : (b.toUInt32 <<< 24).toNat = b.toNat * 2 ^ 24 := by
  have := UInt8.toNat_lt b
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, Nat.shiftLeft_eq]
  have e : (24 : UInt32).toNat % 32 = 24 := rfl
  rw [e]
  exact Nat.mod_eq_of_lt (by omega)

theorem g8CstringShift16 (b : UInt8) : (b.toUInt32 <<< 16).toNat = b.toNat * 2 ^ 16 := by
  have := UInt8.toNat_lt b
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, Nat.shiftLeft_eq]
  have e : (16 : UInt32).toNat % 32 = 16 := rfl
  rw [e]
  exact Nat.mod_eq_of_lt (by omega)

theorem g8CstringShift8 (b : UInt8) : (b.toUInt32 <<< 8).toNat = b.toNat * 2 ^ 8 := by
  have := UInt8.toNat_lt b
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, Nat.shiftLeft_eq]
  have e : (8 : UInt32).toNat % 32 = 8 := rfl
  rw [e]
  exact Nat.mod_eq_of_lt (by omega)

def g8CstringTopByte (u : UInt32) (l : Nat) : Prop :=
  ∃ r, r < 2 ^ 24 ∧ u.toNat = l * 2 ^ 24 + r

theorem g8CstringTopByte_init (b : UInt8) : g8CstringTopByte (b.toUInt32 <<< 24) b.toNat :=
  ⟨0, by decide, by rw [g8CstringShift24]; omega⟩

theorem g8CstringTopByte_or (u y : UInt32) (l : Nat) (h : g8CstringTopByte u l)
    (hy : y.toNat < 2 ^ 24) : g8CstringTopByte (u ||| y) l := by
  obtain ⟨r, hr, hu⟩ := h
  refine ⟨r ||| y.toNat, Nat.or_lt_two_pow hr hy, ?_⟩
  rw [UInt32.toNat_or, hu]
  have he : l * 2 ^ 24 + r = (l <<< 24) ||| r := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hr, Nat.shiftLeft_eq]
  rw [he, Nat.or_assoc, ← Nat.shiftLeft_add_eq_or_of_lt (Nat.or_lt_two_pow hr hy),
    Nat.shiftLeft_eq]

theorem g8CstringTopByte_threshold {u : UInt32} {l k : Nat}
    (h : g8CstringTopByte u l) (hk : k < 256) :
    decide (u.toNat < k * 2 ^ 24) = decide (l < k) := by
  obtain ⟨r, hr, hu⟩ := h
  simp only [decide_eq_decide, hu]
  omega

end JuliaLean.ChatGPT.Batch8.Group8

namespace JuliaLean.ChatGPT.Batch8.Group8
open JuliaLean.ChatGPT.Batch4.Group17
open JuliaLean
open JuliaLean.Proofs.base.strings.cstring
open JuliaLean.base.strings.cstring
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def g8CstringByteAt (s : JString) (p : Int) : UInt8 :=
  s.bytes.getD (p.toNat - 1) 0

theorem g8CstringCu_eq (s : JString) (i : Index) :
    JuliaLean.Strings.cu s i = g8CstringByteAt s i.val := rfl

def g8CstringLeadNext (s : JString) (p n : Int) (lead : Nat) : Int :=
  if p + 1 > n then p + 1
  else if !group17IsCont (g8CstringByteAt s (p + 1)) then p + 1
  else if p + 2 > n || lead < 224 then p + 2
  else if !group17IsCont (g8CstringByteAt s (p + 2)) then p + 2
  else if p + 3 > n || lead < 240 then p + 3
  else if !group17IsCont (g8CstringByteAt s (p + 3)) then p + 3 else p + 4

theorem g8CstringIte_snd {A B : Type} {p : Prop} [Decidable p] (x y : A × B) :
    (if p then x else y).2 = if p then x.2 else y.2 := by split <;> rfl

theorem g8CstringIte_val {p : Prop} [Decidable p] (x y : Index) :
    (if p then x else y).val = if p then x.val else y.val := by split <;> rfl

/-- Only the lead byte controls the iterator's continuation thresholds. -/
theorem g8CstringIterateContinued_next (s : JString) (i : Index)
    (hi0 : 1 ≤ i.val) (hin : i.val ≤ s.bytes.length)
    (hlead : 192 ≤ (JuliaLean.Strings.cu s i).toNat) :
    (JuliaLean.Strings.iterateContinued s i
      ((JuliaLean.Strings.cu s i).toUInt32 <<< 24)).2.val =
      g8CstringLeadNext s i.val (s.bytes.length : Int) (JuliaLean.Strings.cu s i).toNat := by
  have hs := s.small
  have hn : (JuliaLean.Strings.ncodeunits s).val = s.bytes.length :=
    ixVal _ (by omega) (by omega)
  have e1 : (i + ix 1).val = i.val + 1 := indexAddOne i (by omega) (by omega)
  have e2 : (i + ix 1 + ix 1).val = i.val + 2 := by
    rw [indexAddOne (i + ix 1) (by omega) (by omega), e1]
    omega
  have e3 : (i + ix 1 + ix 1 + ix 1).val = i.val + 3 := by
    rw [indexAddOne (i + ix 1 + ix 1) (by omega) (by omega), e2]
    omega
  have e4 : (i + ix 1 + ix 1 + ix 1 + ix 1).val = i.val + 4 := by
    rw [indexAddOne (i + ix 1 + ix 1 + ix 1) (by omega) (by omega), e3]
    omega
  have t0 := g8CstringTopByte_init (JuliaLean.Strings.cu s i)
  have t1 := g8CstringTopByte_or _ ((JuliaLean.Strings.cu s (i + ix 1)).toUInt32 <<< 16) _ t0
    (by rw [g8CstringShift16]; have := UInt8.toNat_lt (JuliaLean.Strings.cu s (i + ix 1)); omega)
  have t2 := g8CstringTopByte_or _ ((JuliaLean.Strings.cu s (i + ix 1 + ix 1)).toUInt32 <<< 8) _ t1
    (by rw [g8CstringShift8]; have := UInt8.toNat_lt (JuliaLean.Strings.cu s (i + ix 1 + ix 1)); omega)
  have hc0 : ¬ (JuliaLean.Strings.cu s i).toUInt32 <<< 24 < 0xc0000000 := by
    intro h
    have h' := UInt32.lt_iff_toNat_lt.mp h
    change _ < 192 * 2 ^ 24 at h'
    rw [g8CstringShift24] at h'
    omega
  have he0 : decide
      ((((JuliaLean.Strings.cu s i).toUInt32 <<< 24) |||
        ((JuliaLean.Strings.cu s (i + ix 1)).toUInt32 <<< 16)) < 0xe0000000) =
      decide ((JuliaLean.Strings.cu s i).toNat < 224) := by
    apply decide_eq_decide.mpr
    rw [UInt32.lt_iff_toNat_lt]
    exact decide_eq_decide.mp (g8CstringTopByte_threshold (k := 224) t1 (by decide))
  have hf0 : decide
      (((((JuliaLean.Strings.cu s i).toUInt32 <<< 24) |||
        ((JuliaLean.Strings.cu s (i + ix 1)).toUInt32 <<< 16)) |||
        ((JuliaLean.Strings.cu s (i + ix 1 + ix 1)).toUInt32 <<< 8)) < 0xf0000000) =
      decide ((JuliaLean.Strings.cu s i).toNat < 240) := by
    apply decide_eq_decide.mpr
    rw [UInt32.lt_iff_toNat_lt]
    exact decide_eq_decide.mp (g8CstringTopByte_threshold (k := 240) t2 (by decide))
  unfold JuliaLean.Strings.iterateContinued
  simp only [hc0, ↓reduceIte, g8CstringIte_snd, g8CstringIte_val, he0, hf0, hn]
  simp only [g8CstringCu_eq, e1, e2, e3, e4] <;> rfl

/-- Number of bytes in the next Julia character, including malformed character groups. -/
def g8CstringStepSize (a : UInt8) : List UInt8 → Nat
  | [] => 1
  | b :: rest =>
      if group17IsLead a then
        if group17IsCont b then
          if a ≥ 0xe0 then
            match rest with
            | [] => 2
            | c :: cs =>
                if group17IsCont c then
                  if a ≥ 0xf0 then
                    match cs with
                    | [] => 3
                    | d :: _ => if group17IsCont d then 4 else 3
                  else 3
                else 2
          else 2
        else 1
      else 1

theorem g8CstringStepSize_nil (a : UInt8) : g8CstringStepSize a [] = 1 := rfl

theorem g8CstringStepSize_cons (a b : UInt8) (rest : List UInt8) :
    g8CstringStepSize a (b :: rest) =
      (if group17IsLead a then
        if group17IsCont b then
          if a ≥ 0xe0 then
            match rest with
            | [] => 2
            | c :: cs =>
                if group17IsCont c then
                  if a ≥ 0xf0 then
                    match cs with
                    | [] => 3
                    | d :: _ => if group17IsCont d then 4 else 3
                  else 3
                else 2
          else 2
        else 1
      else 1) := by
  rw [g8CstringStepSize.eq_def]

theorem g8CstringStepSize_bounds (a : UInt8) (rest : List UInt8) :
    1 ≤ g8CstringStepSize a rest ∧ g8CstringStepSize a rest ≤ (a :: rest).length := by
  cases rest with
  | nil =>
    simp only [g8CstringStepSize_nil, List.length_cons, List.length_nil] <;> omega
  | cons b bs =>
    cases bs with
    | nil =>
      simp only [g8CstringStepSize_cons, List.length_cons, List.length_nil]
      repeat' split
      all_goals omega
    | cons c cs =>
      cases cs with
      | nil =>
        simp only [g8CstringStepSize_cons, List.length_cons, List.length_nil]
        repeat' split
        all_goals omega
      | cons d ds =>
        simp only [g8CstringStepSize_cons, List.length_cons, List.length_nil]
        repeat' split
        all_goals omega

/-- A character step accounts for precisely its continuation bytes. -/
theorem g8CstringAbsorbed_step (a : UInt8) (rest : List UInt8) :
    group17Absorbed (a :: rest) =
      (g8CstringStepSize a rest - 1) +
        group17Absorbed ((a :: rest).drop (g8CstringStepSize a rest)) := by
  cases rest with
  | nil => rfl
  | cons b bs =>
    cases hlead : group17IsLead a with
    | false =>
      simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, g8CstringStepSize_nil, g8CstringStepSize_cons, hlead, Bool.false_eq_true, ↓reduceIte,
        Nat.sub_self, Nat.zero_add, List.drop_succ_cons, List.drop_zero]
    | true =>
      cases hb : group17IsCont b with
      | false =>
        simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, g8CstringStepSize_nil, g8CstringStepSize_cons, hlead, hb, Bool.false_eq_true, ↓reduceIte,
          Nat.sub_self, Nat.zero_add, List.drop_succ_cons, List.drop_zero]
      | true =>
        have hbLead := group17Cont_nonlead b hb
        by_cases he0 : 0xe0 ≤ a
        · cases bs with
          | nil =>
            simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, g8CstringStepSize_nil, g8CstringStepSize_cons, hlead, hb, he0, ↓reduceIte,
              List.drop_succ_cons, List.drop_zero, List.drop_nil]
          | cons c cs =>
            cases hc : group17IsCont c with
            | false =>
              simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, g8CstringStepSize_nil, g8CstringStepSize_cons, hlead, hb, he0, hc,
                Bool.false_eq_true, ↓reduceIte, List.drop_succ_cons, List.drop_zero]
            | true =>
              have hcLead := group17Cont_nonlead c hc
              by_cases hf0 : 0xf0 ≤ a
              · cases cs with
                | nil =>
                  simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, g8CstringStepSize_nil, g8CstringStepSize_cons, hlead, hb, he0, hc, hf0,
                    ↓reduceIte, List.drop_succ_cons, List.drop_zero, List.drop_nil]
                | cons d ds =>
                  cases hd : group17IsCont d with
                  | false =>
                    simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, g8CstringStepSize_nil, g8CstringStepSize_cons, hlead, hb, he0, hc, hf0, hd,
                      Bool.false_eq_true, ↓reduceIte, List.drop_succ_cons, List.drop_zero]
                  | true =>
                    have hdLead := group17Cont_nonlead d hd
                    simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, g8CstringStepSize_nil, g8CstringStepSize_cons, hlead, hb, he0, hc, hf0, hd,
                      ↓reduceIte, group17Absorbed_nonlead d _ hdLead,
                      List.drop_succ_cons, List.drop_zero]
              · simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, g8CstringStepSize_nil, g8CstringStepSize_cons, hlead, hb, he0, hc, hf0,
                  ↓reduceIte, group17Absorbed_nonlead c _ hcLead,
                  List.drop_succ_cons, List.drop_zero]
        · simp only [group17Absorbed_nil, group17Absorbed_single, group17Absorbed_cons_cons, g8CstringStepSize_nil, g8CstringStepSize_cons, hlead, hb, he0, ↓reduceIte,
            group17Absorbed_nonlead b _ hbLead, List.drop_succ_cons, List.drop_zero]

/-- Character count decreases by one when advancing through one character group. -/
theorem g8CstringCount_step_size (a : UInt8) (rest : List UInt8) :
    ((a :: rest).length : Int) - (group17Absorbed (a :: rest) : Int) =
      1 + (((a :: rest).drop (g8CstringStepSize a rest)).length : Int) -
        (group17Absorbed ((a :: rest).drop (g8CstringStepSize a rest)) : Int) := by
  have hs := g8CstringStepSize_bounds a rest
  have ha := g8CstringAbsorbed_step a rest
  have hl : ((a :: rest).drop (g8CstringStepSize a rest)).length =
      (a :: rest).length - g8CstringStepSize a rest := List.length_drop
  omega

theorem g8CstringByteAt_offset (s : JString) (p : Nat) (i : Int) (bytes : List UInt8)
    (hi : i = (p : Int) + 1) (hd : s.bytes.drop p = bytes) (k : Nat) :
    g8CstringByteAt s (i + k) = bytes.getD k 0 := by
  unfold g8CstringByteAt
  have he : (i + k).toNat - 1 = p + k := by omega
  rw [he]
  exact getD_of_drop s.bytes bytes p k 0 hd

theorem g8CstringLeadNext_step (s : JString) (p : Nat) (i : Int)
    (a : UInt8) (rest : List UInt8)
    (hi : i = (p : Int) + 1) (hd : s.bytes.drop p = a :: rest)
    (hlead : group17IsLead a = true) :
    g8CstringLeadNext s i (s.bytes.length : Int) a.toNat = i + g8CstringStepSize a rest := by
  have hl := congrArg List.length hd
  simp only [Int.cast_ofNat_Int, List.length_drop, List.length_cons] at hl
  have hp : p < s.bytes.length := by omega
  have hb1 := g8CstringByteAt_offset s p i (a :: rest) hi hd 1
  have hb2 := g8CstringByteAt_offset s p i (a :: rest) hi hd 2
  have hb3 := g8CstringByteAt_offset s p i (a :: rest) hi hd 3
  cases rest with
  | nil =>
    have hout : i + 1 > (s.bytes.length : Int) := by simp only [Int.cast_ofNat_Int, List.length_nil] at hl; omega
    simp only [Int.cast_ofNat_Int, g8CstringLeadNext, hout, ↓reduceIte, g8CstringStepSize_nil, g8CstringStepSize_cons]
  | cons b bs =>
    have hout : ¬ i + 1 > (s.bytes.length : Int) := by simp only [Int.cast_ofNat_Int, List.length_cons] at hl; omega
    have eb1 : g8CstringByteAt s (i + 1) = b := hb1
    simp only [Int.cast_ofNat_Int, g8CstringLeadNext, hout, ↓reduceIte, eb1, g8CstringStepSize_nil, g8CstringStepSize_cons, hlead]
    cases hc1 : group17IsCont b with
    | false => simp only [Int.cast_ofNat_Int, hc1, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    | true =>
      simp only [Int.cast_ofNat_Int, hc1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases he0 : 0xe0 ≤ a
      · have he0' : ¬ a.toNat < 224 := by
          have h := UInt8.le_iff_toNat_le.mp he0
          change 224 ≤ a.toNat at h
          omega
        simp only [Int.cast_ofNat_Int, he0, he0', decide_false, Bool.or_false, ↓reduceIte]
        cases bs with
        | nil =>
          have hout2 : i + 2 > (s.bytes.length : Int) := by
            simp only [Int.cast_ofNat_Int, List.length_cons, List.length_nil] at hl
            omega
          simp only [Int.cast_ofNat_Int, hout2, decide_true, ↓reduceIte]
        | cons c cs =>
          have hout2 : ¬ i + 2 > (s.bytes.length : Int) := by
            simp only [Int.cast_ofNat_Int, List.length_cons] at hl
            omega
          have eb2 : g8CstringByteAt s (i + 2) = c := hb2
          simp only [Int.cast_ofNat_Int, hout2, decide_false, Bool.false_eq_true, ↓reduceIte, eb2]
          cases hc2 : group17IsCont c with
          | false => simp only [Int.cast_ofNat_Int, hc2, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
          | true =>
            simp only [Int.cast_ofNat_Int, hc2, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            by_cases hf0 : 0xf0 ≤ a
            · have hf0' : ¬ a.toNat < 240 := by
                have h := UInt8.le_iff_toNat_le.mp hf0
                change 240 ≤ a.toNat at h
                omega
              simp only [Int.cast_ofNat_Int, hf0, hf0', decide_false, Bool.or_false, ↓reduceIte]
              cases cs with
              | nil =>
                have hout3 : i + 3 > (s.bytes.length : Int) := by
                  simp only [Int.cast_ofNat_Int, List.length_cons, List.length_nil] at hl
                  omega
                simp only [Int.cast_ofNat_Int, hout3, decide_true, ↓reduceIte]
              | cons d ds =>
                have hout3 : ¬ i + 3 > (s.bytes.length : Int) := by
                  simp only [Int.cast_ofNat_Int, List.length_cons] at hl
                  omega
                have eb3 : g8CstringByteAt s (i + 3) = d := hb3
                simp only [Int.cast_ofNat_Int, hout3, decide_false, Bool.false_eq_true, ↓reduceIte, eb3]
                cases hc3 : group17IsCont d <;>
                  simp only [Int.cast_ofNat_Int, hc3, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            · have hf0' : a.toNat < 240 := by
                have h := UInt8.lt_iff_toNat_lt.mp (UInt8.not_le.mp hf0)
                exact h
              simp only [Int.cast_ofNat_Int, hf0, hf0', decide_true, Bool.or_true, ↓reduceIte]
      · have he0' : a.toNat < 224 := by
          have h := UInt8.lt_iff_toNat_lt.mp (UInt8.not_le.mp he0)
          exact h
        simp only [Int.cast_ofNat_Int, he0, he0', decide_true, Bool.or_true, ↓reduceIte]

theorem g8CstringUnsigned_index (i : Index) (hi : 1 ≤ i.val) :
    (JInt.rem .u64 i - JInt.lit .u64 1).val = i.val - 1 := by
  have hb := indexVal_lt i
  have hw : wrapInt .u64 i.val = i.val := by
    apply wrapInt_of_inRange
    change 0 ≤ i.val ∧ i.val ≤ 2 ^ 64 - 1
    constructor <;> omega
  rw [subU64Val, remU64Val, litU64One, hw]
  apply wrapInt_of_inRange
  change 0 ≤ i.val - 1 ∧ i.val - 1 ≤ 2 ^ 64 - 1
  constructor <;> omega

/-- The source iterator advances by the size of the byte group it actually consumes. -/
theorem g8CstringIterate_stepValue (s : JString) (p : Nat) (i : Index)
    (a : UInt8) (rest : List UInt8) (character : UInt32) (next : Index)
    (hi : i.val = (p : Int) + 1) (hd : s.bytes.drop p = a :: rest)
    (hit : iterateCstringString s i = some (character, next)) :
    next.val = i.val + g8CstringStepSize a rest := by
  have hs := s.small
  have hl := congrArg List.length hd
  simp only [List.length_drop, List.length_cons] at hl
  have hp : p < s.bytes.length := by omega
  have hread : JuliaLean.Strings.cu s i = a := group17Read_drop s p i a rest hi hd
  have hn : (JuliaLean.Strings.ncodeunits s).val = s.bytes.length :=
    ixVal _ (by omega) (by omega)
  have hg : decide ((JInt.rem .u64 i - JInt.lit .u64 1).val <
      (JuliaLean.Strings.ncodeunits s).val) = true := by
    rw [g8CstringUnsigned_index i (by omega), hn]
    exact decide_eq_true (by omega)
  have simple (u : UInt32) (h : some (u, i + ix 1) = some (character, next))
      (hsize : g8CstringStepSize a rest = 1) :
      next.val = i.val + g8CstringStepSize a rest := by
    have hnext := congrArg (fun x : UInt32 × Index => x.2.val) (Option.some.inj h)
    simp only at hnext
    rw [← hnext, indexAddOne i (by omega) (by omega), hsize] <;>
      simp only [Int.cast_ofNat_Int]
  rw [g8CstringIterate_basic] at hit
  unfold JuliaLean.Strings.iterate at hit
  simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hread] at hit
  cases hb : JuliaLean.Strings.between a 0x80 0xf7 with
  | false =>
    simp only [hb, Bool.not_false, ↓reduceIte] at hit
    have hlead : group17IsLead a = false := by
      simp only [JuliaLean.Strings.between, Bool.and_eq_false_iff, decide_eq_false_iff_not,
        UInt8.le_iff_toNat_le, UInt8.toNat_ofNat] at hb
      simp only [group17IsLead, Bool.and_eq_false_iff, decide_eq_false_iff_not,
        UInt8.le_iff_toNat_le, UInt8.toNat_ofNat]
      omega
    apply simple _ hit
    cases rest <;> simp only [g8CstringStepSize_nil, g8CstringStepSize_cons, hlead, Bool.false_eq_true, ↓reduceIte]
  | true =>
    simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hit
    by_cases hc0 : a < 0xc0
    · have hu : a.toUInt32 <<< 24 < 0xc0000000 := by
        rw [UInt32.lt_iff_toNat_lt, g8CstringShift24]
        have ha := UInt8.lt_iff_toNat_lt.mp hc0
        change a.toNat < 192 at ha
        change a.toNat * 2 ^ 24 < 192 * 2 ^ 24
        omega
      unfold JuliaLean.Strings.iterateContinued at hit
      rw [if_pos hu] at hit
      apply simple _ hit
      have hlead : group17IsLead a = false := by
        simp only [group17IsLead, Bool.and_eq_false_iff, decide_eq_false_iff_not]
        exact Or.inl (UInt8.not_le.mpr hc0)
      cases rest <;> simp only [g8CstringStepSize_nil, g8CstringStepSize_cons, hlead, Bool.false_eq_true, ↓reduceIte]
    · have hlead : group17IsLead a = true := by
        simp only [JuliaLean.Strings.between, Bool.and_eq_true, decide_eq_true_eq] at hb
        simp only [group17IsLead, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨UInt8.not_lt.mp hc0, hb.2⟩
      have ha : 192 ≤ (JuliaLean.Strings.cu s i).toNat := by
        rw [hread]
        have h := UInt8.le_iff_toNat_le.mp (UInt8.not_lt.mp hc0)
        exact h
      have hind := g8CstringIterateContinued_next s i (by omega) (by omega) ha
      rw [hread] at hind
      have hpair : JuliaLean.Strings.iterateContinued s i (a.toUInt32 <<< 24) =
          (character, next) := Option.some.inj hit
      rw [hpair] at hind
      exact hind.trans (g8CstringLeadNext_step s p i.val a rest hi hd hlead)

theorem g8CstringIterate_some_of_inbounds (s : JString) (i : Index)
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ s.bytes.length) :
    ∃ character next, iterateCstringString s i = some (character, next) := by
  have hs := s.small
  have hn : (JuliaLean.Strings.ncodeunits s).val = s.bytes.length :=
    ixVal _ (by omega) (by omega)
  have hg : decide ((JInt.rem .u64 i - JInt.lit .u64 1).val <
      (JuliaLean.Strings.ncodeunits s).val) = true := by
    rw [g8CstringUnsigned_index i hlo, hn]
    exact decide_eq_true (by omega)
  rw [g8CstringIterate_basic]
  unfold JuliaLean.Strings.iterate
  simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split
  · exact ⟨_, _, rfl⟩
  · cases hcontinued : JuliaLean.Strings.iterateContinued s i
        ((JuliaLean.Strings.cu s i).toUInt32 <<< 24) with
    | mk character next => exact ⟨character, next, rfl⟩

def g8CstringRemainingCount (s : JString) (i : Index) : Int :=
  let remaining := s.bytes.drop (i.val.toNat - 1)
  (remaining.length : Int) - (group17Absorbed remaining : Int)

/-- One successful iteration reduces the remaining character count by exactly one. -/
theorem g8CstringIteration_count (s : JString) (i : Index) (character : UInt32) (next : Index)
    (hit : iterateCstringString s i = some (character, next)) :
    1 ≤ next.val ∧ next.val ≤ (s.bytes.length : Int) + 1 ∧
      g8CstringRemainingCount s i = 1 + g8CstringRemainingCount s next := by
  have hi := iterateCstring_some s i character next hit
  let p := i.val.toNat - 1
  have hp : p < s.bytes.length := by dsimp [p]; omega
  have hpi : i.val = (p : Int) + 1 := by dsimp [p]; omega
  obtain ⟨a, rest, hd⟩ : ∃ a rest, s.bytes.drop p = a :: rest := by
    have hpos : 0 < (s.bytes.drop p).length := by simp only [List.length_drop]; omega
    cases h : s.bytes.drop p with
    | nil => simp only [h, List.length_nil] at hpos; omega
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hnext := g8CstringIterate_stepValue s p i a rest character next hpi hd hit
  have hsize := g8CstringStepSize_bounds a rest
  have hlen := congrArg List.length hd
  simp only [List.length_drop] at hlen
  have hq : next.val.toNat - 1 = p + g8CstringStepSize a rest := by omega
  have hdnext : s.bytes.drop (next.val.toNat - 1) =
      (a :: rest).drop (g8CstringStepSize a rest) := by
    rw [hq, ← List.drop_drop, hd]
  refine ⟨by omega, by omega, ?_⟩
  unfold g8CstringRemainingCount
  change ((s.bytes.drop p).length : Int) - (group17Absorbed (s.bytes.drop p) : Int) = _
  rw [hd, hdnext]
  change ((a :: rest).length : Int) - (group17Absorbed (a :: rest) : Int) =
    1 + ((((a :: rest).drop (g8CstringStepSize a rest)).length : Int) -
      (group17Absorbed ((a :: rest).drop (g8CstringStepSize a rest)) : Int))
  have h := g8CstringCount_step_size a rest
  omega

/-- A completed prefix accounts for its entire number of iteration steps. -/
theorem g8CstringPrefix_count (s : JString) :
    ∀ (chars : List UInt32) (i cursor : Index),
    1 ≤ i.val → i.val ≤ (s.bytes.length : Int) + 1 →
    cstringStringPrefix s chars i cursor →
    1 ≤ cursor.val ∧ cursor.val ≤ (s.bytes.length : Int) + 1 ∧
      g8CstringRemainingCount s i = (chars.length : Int) + g8CstringRemainingCount s cursor := by
  intro chars
  induction chars with
  | nil =>
    intro i cursor hlo hhi hp
    change i = cursor at hp
    subst cursor
    exact ⟨hlo, hhi, by simp only [List.length_nil, Int.natCast_zero, Int.zero_add]⟩
  | cons character chars ih =>
    intro i cursor hlo hhi hp
    rcases hp with ⟨next, hit, hprefix⟩
    have hstep := g8CstringIteration_count s i character next hit
    have htail := ih next cursor hstep.1 hstep.2.1 hprefix
    refine ⟨htail.1, htail.2.1, ?_⟩
    simp only [List.length_cons]
    omega

/-- String length is the number of characters in any complete iteration trace. -/
theorem g8CstringStringLength_trace (s : JString) (chars : List UInt32) (cursor : Index)
    (hp : cstringStringPrefix s chars (ix 1) cursor)
    (hd : iterateCstringString s cursor = none) :
    (JuliaLean.base.strings.string.stringLength s).val = (chars.length : Int) := by
  have h := g8CstringPrefix_count s chars (ix 1) cursor (by decide) (by
    have hz : (ix 1).val = 1 := rfl
    rw [hz]
    omega) hp
  have hcursor : cursor.val = (s.bytes.length : Int) + 1 := by
    by_cases hbound : cursor.val ≤ s.bytes.length
    · obtain ⟨character, next, he⟩ := g8CstringIterate_some_of_inbounds s cursor h.1 hbound
      rw [hd] at he
      cases he
    · omega
  have hremaining : g8CstringRemainingCount s cursor = 0 := by
    unfold g8CstringRemainingCount
    have hindex : cursor.val.toNat - 1 = s.bytes.length := by omega
    rw [hindex, List.drop_length]
    rfl
  rw [group17StringLength_absorbed]
  have hstart : g8CstringRemainingCount s (ix 1) =
      (s.bytes.length : Int) - (group17Absorbed s.bytes : Int) := by rfl
  rw [hstart, hremaining] at h
  omega

end JuliaLean.ChatGPT.Batch8.Group8


namespace JuliaLean.ChatGPT.Batch8.Group8
open JuliaLean.ChatGPT.Batch4.Group17
open JuliaLean.Proofs.base.strings.cstring
open JuliaLean.base.strings.cstring
/-- The checked abstract trace specializes to the frozen source trace definition. -/
theorem g8CstringGenericPrefix_source (s : JString) (characters : List UInt32)
    (start stop : Index)
    (h : g8CstringGenericPrefix (iterateCstringString s) characters start stop) :
    cstringStringPrefix s characters start stop := by
  induction characters generalizing start with
  | nil => exact h
  | cons character characters ih =>
    obtain ⟨next, hstep, htail⟩ := h
    exact ⟨next, hstep, ih next htail⟩

/-- A successful generic UTF-32 loop converts exactly the characters in its iteration prefix. -/
theorem g8CstringLoop32_trace {T : Type} (s : JString)
    (convertChar : UInt32 → StringResult T) :
    ∀ (fuel : Nat) (i : Index) (before output : List T),
    loop32With (iterateCstringString s) convertChar fuel i before = .ok output →
    ∃ chars cursor,
      cstringStringPrefix s chars i cursor ∧
      iterateCstringString s cursor = none ∧
      output.length = before.length + chars.length := by
  intro fuel i before output h
  obtain ⟨chars, cursor, hprefix, hdone, hlength⟩ :=
    g8CstringGenericLoopTrace (iterateCstringString s) convertChar
      (loop32With (iterateCstringString s) convertChar) List.reverse
      (by intro before; exact List.length_reverse)
      (by intro start before output hzero; cases hzero)
      (by
        intro fuel start before hnone
        exact loop32With_none _ _ fuel start before hnone)
      (by
        intro fuel start before character next hsome
        rw [loop32With_some _ _ fuel start before character next hsome]
        cases convertChar character <;> rfl)
      fuel i before output h
  exact ⟨chars, cursor, g8CstringGenericPrefix_source s chars i cursor hprefix,
    hdone, hlength⟩

/-- Every successful string-to-UTF-32 result has one unit per completed iteration step. -/
theorem g8CstringUtf32_length_of_trace {T : Type} [Utf32CodeUnit T]
    [conversion : Utf32CharacterConversion T] (s : JString) (units : List T)
    (htrans : transcode (T := T) (Output := List T) s = .ok units) :
    ∃ chars cursor,
      cstringStringPrefix s chars (ix 1) cursor ∧
      iterateCstringString s cursor = none ∧ units.length = chars.length := by
  have heq : transcode (T := T) (Output := List T) s =
      loop32With (iterateCstringString s) conversion.convertChar
        (s.bytes.length + 1) (ix 1) [] := by
    refine transcode_of_run _ (transcodeString32 conversion.convertChar) rfl s _ ?_
    unfold transcodeString32
    exact transcodeString32Loop_eq_with conversion.convertChar s _ _ _
  rw [heq] at htrans
  obtain ⟨chars, cursor, hp, hd, hl⟩ := g8CstringLoop32_trace s conversion.convertChar
    (s.bytes.length + 1) (ix 1) [] units htrans
  exact ⟨chars, cursor, hp, hd, by simpa only [List.length_nil, Nat.zero_add] using hl⟩


/-- Stronger generic length conclusion: no character-conversion-law hypothesis is needed. -/
theorem g8CstringSlimUtf32Target {T : Type} [Utf32CodeUnit T]
    [Utf32CharacterConversion T] (s : JString) (units : List T)
    (htrans : transcode (T := T) (Output := List T) s = .ok units) :
    (units.length : Int) = (JuliaLean.base.strings.string.stringLength s).val := by
  obtain ⟨chars, cursor, hp, hd, hl⟩ := g8CstringUtf32_length_of_trace s units htrans
  rw [g8CstringStringLength_trace s chars cursor hp hd, hl]

end JuliaLean.ChatGPT.Batch8.Group8

namespace JuliaLean.ChatGPT.Batch8.Group8
open JuliaLean.ChatGPT.Batch4.Group17

theorem TranscodeUtf32Length_proven : JuliaLean.Proofs.base.strings.cstring.Utf32StringLengthSpec := by
  constructor
  · intro inst conversion s units _ htrans
    exact g8CstringSlimUtf32Target s units htrans
  · intro inst conversion s units _ htrans
    exact g8CstringSlimUtf32Target s units htrans

end JuliaLean.ChatGPT.Batch8.Group8

namespace JuliaLean.Proofs.base.strings.cstring

open JuliaLean.Registry

def entries : List Entry := [
  provenEntry (entry "transcode-utf8-utf16-total" ["transcode(::Type{UInt16}, ::AbstractVector{UInt8})", "transcode(::Type{UInt16}, ::String)"] "transcode(UInt16, src) returns for every byte vector, valid UTF-8 or not (overlong forms, surrogates, truncated sequences, stray continuation bytes, bytes F5-FF), and never reads past the end of src." "base/strings/cstring.jl:140-142: \"it always succeeds for conversions between UTF-XX encodings, even for invalid Unicode data.\"" ``Utf8ToUtf16TotalSpec) ``utf8ToUtf16Total_proven,
  provenEntry (entry "transcode-utf16-utf8-complete" ["transcode(::Type{UInt8}, ::AbstractVector{UInt16})", "transcode(::Type{String}, ::Vector{UInt16})"] "For every UTF-16 vector whose precomputed UTF-8 size fits Julia's string limit, transcoding succeeds, allocates capacity exactly equal to the byte count, and writes every allocated byte." "base/strings/cstring.jl:140-142 (always succeeds); cstring.jl:241-246 (sizes are precomputed so that dst is never grown); invariant" ``Utf16ToUtf8TotalSpec) ``utf16ToUtf8Total_proven,
  refutedEntry (entry "transcode-utf32-invalid" ["transcode(::Type{UInt32}, ::String)"] "transcode(UInt32, s) returns for every String s, including malformed UTF-8." "base/strings/cstring.jl:140-142: \"it always succeeds for conversions between UTF-XX encodings, even for invalid Unicode data.\"" ``Utf32StringTotalSpec) ``utf32StringTotal_refuted "none found (queries: issues 'transcode', 'transcode InvalidCharError', 'transcode UInt32 invalid UTF-8', 'transcode always succeeds', 'Cwstring invalid UTF-8'; prs 'transcode UInt32'); related: #25452 (closed, UTF-8 decoding of overlong and surrogate sequences), #27810 (merged, AbstractVector support in transcode; unrelated scope)",
  refutedEntry (entry "transcode-utf32-out-of-range" ["transcode(::Type{UInt8}, ::Vector{UInt32})"] "transcode(UInt8, v::Vector{UInt32}) returns for every vector v, including one containing 0x00200000." "base/strings/cstring.jl:140-142: \"it always succeeds for conversions between UTF-XX encodings, even for invalid Unicode data.\"" ``Utf32ToUtf8TotalSpec) ``utf32ToUtf8Total_refuted "none found",
  provenEntry (entry "transcode-utf16-roundtrip" ["transcode(::Type{UInt16}, ::String)", "transcode(::Type{String}, ::Vector{UInt16})"] "For valid UTF-8 strings, UTF-16 transcoding round-trips to the original String and allocates a UTF-8 byte buffer with capacity exactly ncodeunits(s)." "base/strings/cstring.jl:157-158 (doctest transcode(String, transcode(UInt16, str)) == str); invariant" ``Utf16RoundtripSpec) ``utf16Roundtrip_proven,
  provenEntry (entry "transcode-utf16-wellformed" ["transcode(::Type{UInt16}, ::String)"] "For a valid string s, transcode(UInt16, s) is well-formed UTF-16: every high surrogate is immediately followed by a low surrogate, and every low surrogate immediately follows a high surrogate." "invariant (UTF-16 output of valid input; Unicode D91)" ``Utf16WellformedSpec) ``utf16Wellformed_proven,
  provenEntry (entry "transcode-utf16-length" ["transcode(::Type{UInt16}, ::String)", "length(::String)"] "For a valid string s, length(transcode(UInt16, s)) == length(s) + count(>=(0xf0), codeunits(s)): one code unit per character and two for characters outside the BMP." "invariant" ``Utf16LengthSpec) ``JuliaLean.ChatGPT.Batch4.Group17.TranscodeUtf16Length_proven,
  provenEntry (entry "transcode-utf32-length" ["transcode(::Type{UInt32}, ::String)", "transcode(::Type{Int32}, ::String)", "length(::String)"] "Whenever transcode(T, s) returns for T equal to Int32 or UInt32, its length equals length(s), for any byte string s." "invariant (one UTF-32 code unit per character)" ``Utf32StringLengthSpec) ``JuliaLean.ChatGPT.Batch8.Group8.TranscodeUtf32Length_proven,
  provenEntry (entry "transcode-containsnul-agree" ["containsnul(::String)", "containsnul(::AbstractString)"] "The String and AbstractString forms agree both ways for every byte string, return false exactly when no NUL occurs, and the AbstractString form does not error." "base/strings/cstring.jl:78-81; invariant" ``ContainsnulSpec) ``containsnul_proven,
  provenEntry (entry "transcode-cstring-nul-check" ["unsafe_convert(::Type{Cstring}, ::String)", "ccall with Cstring arguments"] "unsafe_convert(Cstring, s::String) throws ArgumentError exactly when '\\0' in s; otherwise the C function receives all of s's bytes followed by one NUL terminator, with no embedded NUL." "base/strings/cstring.jl:83-88; Cstring docstring (cstring.jl:21-22): \"Cstrings are NUL-terminated\"" ``CStringNulSpec) ``cstringNul_proven,
  provenEntry (entry "transcode-cwstring-nul-terminated" ["cconvert(::Type{Cwstring}, ::AbstractString)", "cconvert(::Type{Cwstring}, ::Vector{Cwchar_t})"] "cconvert(Cwstring, s) passes NUL-terminated data without an embedded NUL to C, both on Windows (Cwchar_t = UInt16) and on Linux/macOS (Cwchar_t = Int32)." "Cwstring docstring (base/strings/cstring.jl:8-9): \"Cwstrings are NUL-terminated\"; cstring.jl:92-100" ``CwstringAbstractSpec) ``cwstringAbstract_proven,
  refutedEntry (entry "transcode-cwstring-overlong-nul" ["Base.cwstring(::AbstractString)"] "Base.cwstring(s) returns UTF-16 data whose only NUL is the terminator." "base/strings/cstring.jl:112-113: \"Convert a string s to a NUL-terminated Vector{Cwchar_t}, suitable for passing to C functions\"; the embedded-NUL check at :121" ``CwstringWindowsNulSpec) ``cwstringWindowsNul_refuted "no exact duplicate; related issues #25452 and #56795; overlong UTF-8 C0 80 decodes to an embedded UTF-16 NUL after the byte-level check",
  { (entry "transcode-cwstring-empty-vector" ["cconvert(::Type{Cwstring}, ::Vector{Cwchar_t})"] "cconvert(Cwstring, v::Vector{Cwchar_t}) throws ArgumentError for every v that is not NUL-terminated." "base/strings/cstring.jl:97-98: v[end] == 0 || throw(ArgumentError(\"C string data must be NUL terminated: ...\"))" ``CwstringVectorTerminatorTotalSpec) with notes := "Opaque Cwchar_t lacks the platform inhabitance binding required to relate the quantified Prop to real wide-character vectors." },
  provenEntry (entry "transcode-unsafe-string-nul" ["unsafe_string(::Ptr{UInt16})", "unsafe_string(::Ptr{UInt16}, ::Integer)"] "unsafe_string(p::Ptr{UInt16}) reads the code units up to and including the first NUL and nothing after it, and returns transcode(String, ...) of the units before the NUL." "base/strings/cstring.jl:309-319 (unsafe_string docstring: C-style NUL-terminated data)" ``UnsafeWideSpec) ``unsafeWide_proven,
  { (entry "stringscova-cwstring-pointer-type" ["Ptr{T}(::Cwstring)"] "Ptr{T}(Cwstring) returns a value of the requested Ptr{T} type and preserves the original pointer address." "constructor and conversion invariant; base/strings/cstring.jl:34,39" ``CwstringPointerTargetSpec) with notes := "Prop equates phantom pointer tags; prose promises requested Ptr type and address preservation." },
  provenEntry (entry "stringscova-cstring-pointer-operations" ["==(::Union{Cstring,Cwstring}, ::Ptr)", "==(::Ptr, ::Union{Cstring,Cwstring})", "unsafe_string(::Cstring)"] "C-string pointer equality compares converted addresses, and unsafe_string reads bytes through the first NUL." "base/strings/cstring.jl:59-62" ``PointerOperationsSpec) ``pointerOperations_proven,
  provenEntry (entry "stringscova-cstring-conversion-wrappers" ["containsnul(::Ptr, len)", "containsnul(::String)", "containsnul(::AbstractString)"] "Pointer containsnul reports NUL exactly within the requested prefix; String and AbstractString forms agree both ways, return false exactly when no NUL occurs, and AbstractString does not error." "base/strings/cstring.jl:78-81" ``CStringConversionWrappersSpec) ``cstringConversionWrappers_proven,
  provenEntry (entry "stringscova-transcode-wrappers" ["transcode(::Type{String}, ::Vector{UInt8})"] "Vector{UInt8} to String transcode returns a String whose bytes equal the source vector's bytes." "base/strings/cstring.jl:182; String(view(src, :))" ``TranscodeVectorStringSpec) ``transcodeVectorString_proven,
  provenEntry (entry "stringscova-unsafe-wide-strings" ["unsafe_string(::Ptr{T}, ::Integer)", "unsafe_string(::Ptr{T})"] "Wide unsafe_string with a length transcodes exactly the requested code-unit prefix; the NUL-terminated form transcodes exactly the prefix before the first zero." "base/strings/cstring.jl:321-330" ``UnsafeWideSpec) ``unsafeWide_proven,
  provenEntry (entry "stringscova-cstring-eq-ptr-faithful" ["==(::Union{Cstring,Cwstring}, ::Ptr)"] "C-string equality with a pointer compares the converted address." "base/strings/cstring.jl:59" ``PointerOperationsSpec) ``pointerOperations_proven,
  provenEntry (entry "stringscova-ptr-eq-cstring-faithful" ["==(::Ptr, ::Union{Cstring,Cwstring})"] "Pointer equality with a C string compares against the converted address." "base/strings/cstring.jl:60" ``PointerOperationsSpec) ``pointerOperations_proven,
  provenEntry (entry "stringscova-cstring-unsafe-string-faithful" ["unsafe_string(::Cstring)"] "unsafe_string(Cstring) converts to Ptr{UInt8} and copies through the first NUL." "base/strings/cstring.jl:62" ``PointerOperationsSpec) ``pointerOperations_proven,
  provenEntry (entry "stringscova-cwstring-cconvert-abstract-faithful" ["cconvert(::Type{Cwstring}, ::AbstractString)"] "cconvert(Cwstring,AbstractString) first constructs a String, transcodes to the platform wide type, appends NUL, and applies the wide-vector checks in order." "base/strings/cstring.jl:69-73" ``CwstringAbstractSpec) ``cwstringAbstract_proven,
  provenEntry (entry "stringscova-containsnul-ptr-faithful" ["containsnul(::Ptr, len)"] "containsnul calls memchr for zero over exactly len bytes." "base/strings/cstring.jl:78-79" ``ContainsnulSpec) ``containsnul_proven,
  provenEntry (entry "stringscova-containsnul-string-faithful" ["containsnul(::String)"] "String NUL detection converts the storage pointer and scans exactly sizeof(s) bytes, excluding the trailing terminator." "base/strings/cstring.jl:80" ``ContainsnulSpec) ``containsnul_proven,
  provenEntry (entry "stringscova-cstring-unsafe-string-convert-faithful" ["unsafe_convert(::Type{Cstring}, ::String)"] "String-to-Cstring conversion scans exactly the String bytes for embedded NUL, throws when one is present, and otherwise preserves the address and all bytes followed by the terminating NUL." "base/strings/cstring.jl:83-88" ``CStringNulSpec) ``JuliaLean.ChatGPT.Batch4.Group17.StringscovaCstringUnsafeStringConvertFaithful_proven,
  provenEntry (entry "stringscova-cwstring-cconvert-vector-faithful" ["cconvert(::Type{Cwstring}, ::Vector{Cwchar_t})"] "Wide-vector conversion rejects embedded NULs before the last element, requires a final NUL, and preserves every accepted vector." "base/strings/cstring.jl:92-100" ``CwstringVectorSpec) ``cwstringVector_proven,
  provenEntry (entry "stringscova-cwstring-windows-faithful" ["cwstring(::AbstractString)"] "Windows cwstring first constructs a String, rejects zero bytes, transcodes its bytes to UInt16, and appends one terminating NUL." "base/strings/cstring.jl:119-123" ``CwstringWindowsSpec) ``cwstringWindows_proven,
  provenEntry (entry "stringscova-transcode-string32-faithful" ["transcode(::Type{UInt32}, ::String)", "transcode(::Type{Int32}, ::String)"] "String-to-Int32 or UInt32 transcode returns the first character-conversion error after any successfully converted prefix." "base/strings/cstring.jl:164" ``Utf32StringErrorSpec) ``transcodeString32Error_proven,
  provenEntry (entry "stringscova-transcode-32-to-bytes-faithful" ["transcode(::Type{UInt8}, ::Vector{UInt32})", "transcode(::Type{UInt8}, ::Vector{Int32})"] "Int32 or UInt32 to UTF-8 transcode returns the first Char-construction error after any valid prefix; a UInt32 value at or above 0x00200000 raises CodePointError." "base/strings/cstring.jl:170-176" ``Utf32ToUtf8ErrorSpec) ``transcode32To8Error_proven,
  provenEntry (entry "stringscova-transcode-vector-string-faithful" ["transcode(::Type{String}, ::Vector{UInt8})"] "Vector{UInt8} to String transcode returns a String whose bytes equal the source vector's bytes." "base/strings/cstring.jl:182; String(view(src, :))" ``TranscodeVectorStringSpec) ``transcodeVectorString_proven,
  provenEntry (entry "stringscova-unsafe-wide-length-faithful" ["unsafe_string(::Ptr{T}, ::Integer)"] "For every valid pointer and nonnegative Integer length, wide unsafe_string wraps exactly that many units without ownership and transcodes them to String." "base/strings/cstring.jl:321-323" ``UnsafeWideSpec) ``unsafeWide_proven,
  provenEntry (entry "stringscova-unsafe-wide-nul-faithful" ["unsafe_string(::Ptr{T})"] "For every documented valid NUL-terminated pointer, wide unsafe_string loads consecutive units from index one, excludes the first zero, and calls the length-qualified method." "base/strings/cstring.jl:324-330" ``UnsafeWideSpec) ``unsafeWide_proven,
] ++ wrapperEntries

end JuliaLean.Proofs.base.strings.cstring

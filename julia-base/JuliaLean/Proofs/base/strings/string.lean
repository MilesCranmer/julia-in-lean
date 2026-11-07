import JuliaLean.base.strings.string
import JuliaLean.base.strings.basic
import JuliaLean.base.char
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.strings.util
import JuliaLean.base.strings.stringview
import JuliaLean.base.int

open JuliaLean
open JuliaLean.base.strings.string

namespace JuliaLean.Proofs.base.strings.string

/-- A trace records each source byte index, decoded character, and next index. -/
inductive IterTrace {S : Type} (iterateAt : S → Index → Option (UInt32 × Index))
    (s : S) : Index → List (Index × UInt32 × Index) → Prop where
  | stop {i} (h : iterateAt s i = none) : IterTrace iterateAt s i []
  | step {i c next rows} (h : iterateAt s i = some (c, next))
      (tail : IterTrace iterateAt s next rows) :
      IterTrace iterateAt s i ((i, c, next) :: rows)

def validByteIndices {S : Type} (ncodeunits : S → Index)
    (isvalid : S → Index → Bool) (s : S) : List Index :=
  (List.range (ncodeunits s).val.toNat).map
    (fun i => JuliaLean.Strings.ix (Int.ofNat (i + 1))) |>.filter (isvalid s)

def viewValidByteIndex (view : StringView (List UInt8)) (i : Index) : Bool :=
  1 ≤ i.val && i.val ≤ Int.ofNat view.data.length &&
    (stringViewByteAt view i &&& 0xc0) != 0x80

def IterateVisitsValid : Prop :=
  (∀ s rows, IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows →
    rows.map (fun row => row.1) = validByteIndices stringNcodeunits stringIsvalidIndex s) ∧
  (∀ view rows, IterTrace stringViewIterate view (JuliaLean.Strings.ix 1) rows →
    rows.map (fun row => row.1) = validByteIndices stringViewNcodeunits viewValidByteIndex view)

def LengthIterateSteps : Prop :=
  ∀ s rows, IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows →
    stringLength s = JuliaLean.Strings.ix (Int.ofNat rows.length)

def ThisindIdempotent : Prop :=
  ∀ s i j, stringThisind s i = .ok j → stringThisind s j = .ok j

def ThisindWithinThree : Prop :=
  ∀ s i j, stringIsvalidIndex s i = true → stringThisind s i = .ok j →
    j.val ≤ i.val ∧ i.val - j.val ≤ 3 ∧ stringIsvalidIndex s j = true

def NextindAdvance : Prop :=
  ∀ s i j, stringIsvalidIndex s i = true → i.val ≥ 1 →
    i.val ≤ (stringNcodeunits s).val → stringNextind s i = .ok j →
    i.val < j.val ∧ j.val ≤ (stringNcodeunits s).val + 1 ∧ j.val - i.val ≤ 4

def PrevindAfterNextind : Prop :=
  ∀ (prevind : JString → Index → StringResult Index) s i j,
    stringIsvalidIndex s i = true → i.val ≥ 1 →
    stringNextind s i = .ok j → prevind s j = .ok i

def NextindAfterPrevind : Prop :=
  ∀ (prevind : JString → Index → StringResult Index) s i j,
    stringIsvalidIndex s i = true → i.val ≥ 1 →
    prevind s i = .ok j → stringNextind s j = .ok i

inductive Utf8WellFormed : List UInt8 → Prop where
  | empty : Utf8WellFormed []
  | ascii {b rest} (lead : b.toNat < 0x80) (tail : Utf8WellFormed rest) :
      Utf8WellFormed (b :: rest)
  | twoByte {b1 b2 rest} (lead : 0xc2 ≤ b1 ∧ b1 ≤ 0xdf)
      (continuation : 0x80 ≤ b2 ∧ b2 ≤ 0xbf) (tail : Utf8WellFormed rest) :
      Utf8WellFormed (b1 :: b2 :: rest)
  | threeE0 {b2 b3 rest} (second : 0xa0 ≤ b2 ∧ b2 ≤ 0xbf)
      (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf) (tail : Utf8WellFormed rest) :
      Utf8WellFormed (0xe0 :: b2 :: b3 :: rest)
  | threeNormal {b1 b2 b3 rest}
      (lead : (0xe1 ≤ b1 ∧ b1 ≤ 0xec) ∨ (0xee ≤ b1 ∧ b1 ≤ 0xef))
      (second : 0x80 ≤ b2 ∧ b2 ≤ 0xbf) (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf)
      (tail : Utf8WellFormed rest) : Utf8WellFormed (b1 :: b2 :: b3 :: rest)
  | threeEd {b2 b3 rest} (second : 0x80 ≤ b2 ∧ b2 ≤ 0x9f)
      (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf) (tail : Utf8WellFormed rest) :
      Utf8WellFormed (0xed :: b2 :: b3 :: rest)
  | fourF0 {b2 b3 b4 rest} (second : 0x90 ≤ b2 ∧ b2 ≤ 0xbf)
      (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf) (fourth : 0x80 ≤ b4 ∧ b4 ≤ 0xbf)
      (tail : Utf8WellFormed rest) : Utf8WellFormed (0xf0 :: b2 :: b3 :: b4 :: rest)
  | fourNormal {b1 b2 b3 b4 rest} (lead : 0xf1 ≤ b1 ∧ b1 ≤ 0xf3)
      (second : 0x80 ≤ b2 ∧ b2 ≤ 0xbf) (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf)
      (fourth : 0x80 ≤ b4 ∧ b4 ≤ 0xbf) (tail : Utf8WellFormed rest) :
      Utf8WellFormed (b1 :: b2 :: b3 :: b4 :: rest)
  | fourF4 {b2 b3 b4 rest} (second : 0x80 ≤ b2 ∧ b2 ≤ 0x8f)
      (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf) (fourth : 0x80 ≤ b4 ∧ b4 ≤ 0xbf)
      (tail : Utf8WellFormed rest) : Utf8WellFormed (0xf4 :: b2 :: b3 :: b4 :: rest)

def vectorBytes {V : Type} (length : V → Int) (getByte : V → Int → UInt8)
    (bytes : V) : List UInt8 :=
  (List.range (length bytes).toNat).map
    (fun i => getByte bytes (Int.ofNat (i + 1)))

def Utf8Validity : Prop :=
  (∀ {V : Type} (length : V → Int) (getByte : V → Int → UInt8)
      (firstindex lastindex : V → Int) (isAscii : V → Int → Int → Bool) (bytes : V),
    0 ≤ length bytes →
    (∀ first last, isAscii bytes first last =
      byteListIsAscii (vectorBytes length getByte bytes) first last) →
    let values := vectorBytes length getByte bytes
    (byteStringClassifyVector length getByte firstindex lastindex isAscii bytes = 1 ↔
      byteListIsAscii values 1 (Int.ofNat values.length) = true) ∧
    (byteStringClassifyVector length getByte firstindex lastindex isAscii bytes = 2 ↔
      byteListIsAscii values 1 (Int.ofNat values.length) = false ∧ Utf8WellFormed values) ∧
    (byteStringClassifyVector length getByte firstindex lastindex isAscii bytes = 0 ↔
      ¬ Utf8WellFormed values) ∧
    (isvalidStringBytes length getByte firstindex lastindex isAscii bytes = true ↔
      Utf8WellFormed values)) ∧
  (∀ {S V : Type} (codeunits : S → V) (length : V → Int)
      (getByte : V → Int → UInt8) (firstindex lastindex : V → Int)
      (isAscii : V → Int → Int → Bool) (s : S),
    (∀ values first last, isAscii values first last =
      byteListIsAscii (vectorBytes length getByte values) first last) →
    let values := vectorBytes length getByte (codeunits s)
    (isvalidStringAbstract codeunits length getByte firstindex lastindex isAscii s = true
      ↔ Utf8WellFormed values) ∧
    (isvalidAbstractString codeunits length getByte firstindex lastindex isAscii s = true
      ↔ Utf8WellFormed values))

def ContinuationByte : Prop :=
  ∀ b, isValidContinuation b = true ↔ 0x80 ≤ b ∧ b ≤ 0xbf

def FindNonasciiChunkFirst : Prop :=
  ∀ {V : Type} (isAscii : V → Int → Int → Bool) (chunkSize : Int)
    (bytes : V) (first last start : Int),
    0 < chunkSize → first ≤ last → chunkSize ≤ last - first + 1 →
    (findNonasciiChunk isAscii chunkSize bytes first last = none ↔
      isAscii bytes first last = true) ∧
    (findNonasciiChunk isAscii chunkSize bytes first last = some start →
      first ≤ start ∧ start ≤ last ∧
      isAscii bytes first (start - 1) = true ∧
      isAscii bytes start (min last (start + chunkSize - 1)) = false)

def ScalarGetindexMatchesIteration : Prop :=
  (∀ s i c next, stringIsvalidIndex s i = true →
    stringIterate s i = some (c, next) → stringGetindex s i = .ok c) ∧
  (∀ (firstindex : StringView (List UInt8) → Index)
      (isvalid : StringView (List UInt8) → Index → Bool)
      (ncodeunits : StringView (List UInt8) → Index)
      (codeunit : StringView (List UInt8) → Index → UInt8)
      (checkedCodeunit : StringView (List UInt8) → Index → StringResult UInt8)
      (view : StringView (List UInt8)) i c next,
    isvalid view i = true →
    iterateString firstindex ncodeunits codeunit stringBetweenByte view i = some (c, next) →
    getindexString isvalid ncodeunits codeunit checkedCodeunit stringBetweenByte view i = .ok c)

def GetindexContinuedMatchesIteration : Prop :=
  (∀ s i u c next, stringIsvalidIndex s i = true →
    iterateContinued stringNcodeunits stringByteAt s i u = (c, next) →
    getindexContinued stringIsvalidIndex stringNcodeunits stringByteAt s i u = .ok c) ∧
  (∀ (isvalid : StringView (List UInt8) → Index → Bool)
      (ncodeunits : StringView (List UInt8) → Index)
      (codeunit : StringView (List UInt8) → Index → UInt8)
      (view : StringView (List UInt8)) i u c next,
    isvalid view i = true →
    iterateContinued ncodeunits codeunit view i u = (c, next) →
    getindexContinued isvalid ncodeunits codeunit view i u = .ok c)

def StringViewAccessesInBounds : Prop :=
  (∀ view i, stringViewIterate view i ≠ none ↔
    1 ≤ i.val ∧ i.val ≤ Int.ofNat view.data.length) ∧
  (∀ (isvalid : StringView (List UInt8) → Index → Bool)
      (ncodeunits : StringView (List UInt8) → Index)
      (codeunit : StringView (List UInt8) → Index → UInt8)
      (checkedCodeunit : StringView (List UInt8) → Index → StringResult UInt8)
      (view : StringView (List UInt8)) i result,
    (∀ value byte read, checkedCodeunit value byte = .ok read →
      1 ≤ byte.val ∧ byte.val ≤ (ncodeunits value).val) →
    getindexString isvalid ncodeunits codeunit checkedCodeunit stringBetweenByte view i =
      .ok result →
    1 ≤ i.val ∧ i.val ≤ (ncodeunits view).val)

def StringIndexValidity : Prop :=
  ∀ s i, 1 ≤ i.val → i.val ≤ (stringNcodeunits s).val →
    (stringIsvalidIndex s i = true ↔
      (stringByteAt s i &&& 0xc0) != 0x80)

def LengthViewAgreement : Prop :=
  ∀ s, stringViewLength ⟨s.bytes⟩ = stringLength s

def AsciiStringAgreement : Prop :=
  ∀ s, stringIsascii s = byteListIsAscii s.bytes 1 (Int.ofNat s.bytes.length)

def BetweenInclusive : Prop :=
  ∀ {T : Type} (lessOrEqual : T → T → Bool) (value lower upper : T),
    between lessOrEqual value lower upper =
      (lessOrEqual lower value && lessOrEqual value upper)

def CodeunitTypeUInt8 : Prop :=
  codeunitType = UInt8

def ByteLengthMatchesStorage : Prop :=
  ∀ s, stringNcodeunits s = JuliaLean.Strings.ix (Int.ofNat s.bytes.length)

def StringCodeunitBytes : Prop :=
  ∀ s i, 1 ≤ i.val → i.val ≤ (stringNcodeunits s).val →
    stringCodeunit s i = .ok (stringByteAt s i)

def StringCodeunitBounds : Prop :=
  ∀ s i, i.val < 1 ∨ (stringNcodeunits s).val < i.val →
    stringCodeunit s i = .error (.jl .boundsError)

def StringPointerOffsets : Prop :=
  ∀ s i, pointerAt stringUnsafeConvert (fun i : Index => i.val) s i =
    pointerString stringUnsafeConvert s + i.val - 1

def StringTypeminEmpty : Prop :=
  typeminStringType = JuliaLean.Strings.JStr.empty ∧
    ∀ s, typeminString typeminStringType s = JuliaLean.Strings.JStr.empty

def StringViewConstruction : Prop :=
  ∀ {α : Type} (requireOneBased : α → StringResult Unit) concrete data,
    match requireOneBased data with
    | .error e => stringViewCtor requireOneBased concrete data = .error e
    | .ok _ =>
      if concrete then
        ∃ view, stringViewCtor requireOneBased concrete data = .ok view ∧ view.data = data
      else
        stringViewCtor requireOneBased concrete data =
          .error (.jl (.argumentError "StringView must be parameterized with a concrete type"))

def IndexErrorAtRequestedIndex : Prop :=
  ∀ {α I : Type} (toInt : I → Index) (s : α) (i : I),
    stringIndexErr toInt s i = .error (.stringIndexError (toInt i).val)

def StringIndexErrorDisplay : Prop :=
  ∀ (print : List String → List String → List String)
    (firstindex : JString → Index)
    (isEmptyRange : Index → Index → Bool)
    (checkbounds : JString → Index → Index → StringResult Unit)
    (toCsize : JInt .u64 → StringResult Nat)
    (allocateString : Nat → StringResult JString) (toInt : Index → Int)
    (preserve : JString → JString → (Unit → JString) → JString)
    (unsafeCopyTo : Int → Int → Nat → JString → JString)
    (escapeString : JString → String) (toString : Index → String)
    (io : List String) (s : JString) (index : Index),
    showStringIndexError print firstindex stringNcodeunits stringThisind stringNextind
      (stringGetindexRange isEmptyRange checkbounds toCsize allocateString toInt preserve unsafeCopyTo)
      escapeString toString io s index = do
        let output := print io ["StringIndexError: ", "invalid index [", toString index, "]"]
        if firstindex s ≤ index && index ≤ stringNcodeunits s then
          let iprev ← stringThisind s index
          let inext ← stringNextind s iprev
          let previous ← stringGetindexRange isEmptyRange checkbounds toCsize allocateString
            toInt preserve unsafeCopyTo s iprev iprev
          let previousText := escapeString previous
          if inext ≤ stringNcodeunits s then
            let next ← stringGetindexRange isEmptyRange checkbounds toCsize allocateString
              toInt preserve unsafeCopyTo s inext inext
            pure (print output [", valid nearby indices [", toString iprev, "]=>'",
              previousText, "', [", toString inext, "]=>'", escapeString next, "'"])
          else
            pure (print output [", valid nearby index [", toString iprev, "]=>'",
              previousText, "'"])
        else
          pure output

def StringAllocationSize : Prop :=
  ∀ {I : Type} (toCsize : I → StringResult Nat)
    (allocateString : Nat → StringResult JString) (n : I) (size : Nat) (result : JString),
    toCsize n = .ok size →
    (∀ count output, allocateString count = .ok output → output.bytes.length = count) →
    stringN toCsize allocateString n = .ok result →
    result.bytes.length = size

def StringFromAbstractStringBytes : Prop :=
  ∀ {S : Type} (printToString : S → JString) (bytes : S → List UInt8) (s : S),
    (printToString s).bytes = bytes s →
      (stringAbstractString printToString s).bytes = bytes s

def StringSymbolConversion : Prop :=
  ∀ {S : Type} (unsafeConvert : S → Int) null
    (pointerBytes : Int → List UInt8) (pointerToCString : Int → JString) (s : S),
    (∀ pointer, (pointerToCString pointer).bytes =
      (pointerBytes pointer).takeWhile (fun byte => byte != 0)) →
    let pointer := unsafeConvert s
    if pointer = null then
      stringSymbol unsafeConvert null pointerToCString s =
        .error (.jl (.argumentError "cannot convert NULL to string"))
    else
      ∃ result, stringSymbol unsafeConvert null pointerToCString s = .ok result ∧
        result.bytes = (pointerBytes pointer).takeWhile (fun byte => byte != 0)

def UnsafeStringLengthCopiesBytes : Prop :=
  ∀ {I : Type} (toInt : I → Index) null
    (pointerBytes : Int → Nat → List UInt8)
    (pointerToString : Int → Index → JString) (pointer : Int) (len : I),
    (∀ address count, (pointerToString address count).bytes =
      pointerBytes address count.val.toNat) →
    pointer ≠ null →
    ∃ result, unsafeStringLength toInt null pointerToString pointer len = .ok result ∧
      result.bytes = pointerBytes pointer (toInt len).val.toNat

def UnsafeStringNulCopiesPrefix : Prop :=
  ∀ null (pointerBytes : Int → List UInt8) (pointerToCString : Int → JString)
    (pointer : Int),
    (∀ address, (pointerToCString address).bytes =
      (pointerBytes address).takeWhile (fun byte => byte != 0)) →
    pointer ≠ null →
    (unsafeStringNul null pointerToCString pointer).map (fun string => string.bytes) =
      .ok ((pointerBytes pointer).takeWhile (fun byte => byte != 0))

def UnsafeStringRejectsNull : Prop :=
  ∀ {I : Type} (toInt : I → Index) null pointerToString pointerToCString len,
    unsafeStringLength toInt null pointerToString null len =
      .error (.jl (.argumentError "cannot convert NULL to string")) ∧
    unsafeStringNul null pointerToCString null =
      .error (.jl (.argumentError "cannot convert NULL to string"))

def UnsafeTakeStringBytes : Prop :=
  ∀ m empty memoryLength memoryToString,
    (empty m = true → m.bytes = []) →
    (empty m = false → (memoryToString m (memoryLength m)).bytes = m.bytes) →
    (unsafeTakestring empty memoryLength memoryToString m).bytes = m.bytes

def AbstractVectorStringBytes : Prop :=
  ∀ (v : ByteVector) allocate copyTo empty memoryLength memoryToString,
    let memory := copyTo (allocate v.length) v
    memory.bytes = v.bytes →
    (empty memory = true → memory.bytes = []) →
    (empty memory = false → (memoryToString memory (memoryLength memory)).bytes = memory.bytes) →
    (stringAbstractVector (fun vector : ByteVector => vector.length) allocate copyTo
      empty memoryLength memoryToString v).bytes = v.bytes

def StringVectorTransfer : Prop :=
  ∀ (v : ByteVector) genericMemoryToString pointerToString emptyMemoryRef,
    let result := stringVector genericMemoryToString pointerToString emptyMemoryRef v
    if v.length = 0 then
      result.string.bytes = [] ∧ result.vector.length = v.length ∧ result.sharedStorage = none
    else
      result.vector.length = 0 ∧ result.vector.ref = emptyMemoryRef ∧
        (if v.ref.ptrOrOffset = v.ref.mem.pointer then
          ∃ memory, result.sharedStorage = some memory ∧ memory.pointer = v.ref.mem.pointer
        else result.sharedStorage = none)

def StringVectorImmutable : Prop :=
  ∀ (v : ByteVector) genericMemoryToString pointerToString emptyMemoryRef,
    (stringVector genericMemoryToString pointerToString emptyMemoryRef v).sharedStorage = none

def StringStorageConversions : Prop :=
  (∀ (s : JString) (stringToMemory : JString → Memory),
    (stringToMemory s).bytes = s.bytes →
    (unsafeWrapMemory stringToMemory s).bytes = s.bytes) ∧
  (∀ (s : JString) (stringToMemory : JString → Memory)
      (wrapArray : Memory → ByteVector),
    (stringToMemory s).bytes = s.bytes →
    (∀ memory, (wrapArray memory).bytes = memory.bytes) →
    (unsafeWrapVector stringToMemory wrapArray s).bytes = s.bytes) ∧
  (∀ {C : Type} (bytesOf : C → List UInt8) (length : C → Nat)
      (allocate : Nat → ByteVector) (copyTo : ByteVector → C → ByteVector) (source : C),
    length source = (bytesOf source).length →
    (∀ destination value, (copyTo destination value).bytes = bytesOf value) →
    (vectorCodeUnits length allocate copyTo source).bytes = bytesOf source) ∧
  (∀ (s : JString) (codeunits : JString → List UInt8)
      (length : List UInt8 → Nat) (allocate : Nat → ByteVector)
      (copyTo : ByteVector → List UInt8 → ByteVector),
    codeunits s = s.bytes →
    (∀ destination value, (copyTo destination value).bytes = value) →
    (vectorString codeunits length allocate copyTo s).bytes = s.bytes) ∧
  (∀ (vectorString : JString → ByteVector) (s : JString),
    (vectorString s).bytes = s.bytes →
    (arrayString vectorString s).bytes = s.bytes) ∧
  (∀ {C : Type} (parent : C → JString) (bytesOf : C → List UInt8) (s : C),
    (parent s).bytes = bytesOf s →
    (stringCodeUnits parent s).bytes = bytesOf s)

def StringEqualityByContents : Prop :=
  ∀ (same : JString → JString → Bool) (a b : JString),
    same a b = decide (a.bytes = b.bytes) →
    eqString same a b = decide (a.bytes = b.bytes)

def compareByteLists : List UInt8 → List UInt8 → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs =>
      if a < b then -1 else if b < a then 1 else compareByteLists as bs

def CmpAgreesGeneric : Prop :=
  ∀ (ops : JuliaLean.base.strings.basic.StringOps JString Unit UInt32 UInt8 Unit StringError)
    (sizeof : JString → Index)
    (memcmpLength : JString → JString → Index → Int)
    (cmpLength : Index → Index → Int) (a b : JString) (genericResult : Index),
    (∀ s, sizeof s = JuliaLean.Strings.ix (Int.ofNat s.bytes.length)) →
    (∀ x y count,
      let actual := memcmpLength x y count
      let expected := compareByteLists (x.bytes.take count.val.toNat)
        (y.bytes.take count.val.toNat)
      (actual < 0 ↔ expected < 0) ∧ (actual = 0 ↔ expected = 0) ∧
        (actual > 0 ↔ expected > 0)) →
    (∀ left right,
      cmpLength left right =
        if left.val < right.val then -1 else if left.val > right.val then 1 else 0) →
    (∀ x y, ops.sameReference x y = decide (x.bytes = y.bytes)) →
    (∀ s, ops.iterateFirst s = .ok (stringIterate s (JuliaLean.Strings.ix 1))) →
    (∀ s i, ops.iterateAt s i = .ok (stringIterate s i)) →
    (∀ s, s.bytes.length ≤ ops.iterationBound s) →
    (∀ x y, ops.equalChar x y = JuliaLean.base.char.eq_Char x y) →
    (∀ x y, ops.lessChar x y = JuliaLean.base.char.isless_Char x y) →
    JuliaLean.base.strings.basic.cmpString ops a b = .ok genericResult →
    cmpString sizeof memcmpLength cmpLength a b = genericResult.val

def StringRangeAccessesInBounds : Prop :=
  ∀ (isEmptyRange : Index → Index → Bool)
    (checkbounds : JString → Index → Index → StringResult Unit)
    (toCsize : JInt .u64 → StringResult Nat)
    (allocateString : Nat → StringResult JString) (toInt : Index → Int)
    (preserve : JString → JString → (Unit → JString) → JString)
    (unsafeCopyTo : Int → Int → Nat → JString → JString)
    (s : JString) (i j next : Index) (size : Nat) (allocated output : JString),
    isEmptyRange i j = false →
    checkbounds s i j = .ok () →
    stringIsvalidIndex s i = true →
    stringIsvalidIndex s j = true →
    nextindString stringNcodeunits stringBetweenIndex stringBetweenByte stringCodeunitAt
      s j = .ok next →
    let count := JInt.rem .u64 (next - JuliaLean.Strings.ix 1 - i + JuliaLean.Strings.ix 1)
    toCsize count = .ok size →
    allocateString size = .ok allocated →
    allocated.bytes.length = size →
    (∀ destination source amount initial,
      (unsafeCopyTo destination source amount initial).bytes.length = amount) →
    (∀ source destination write, preserve source destination write = write ()) →
    stringGetindexRange isEmptyRange checkbounds toCsize allocateString toInt preserve
      unsafeCopyTo s i j = .ok output →
    output.bytes.length = count.val.toNat ∧
      1 ≤ i.val ∧ i.val ≤ next.val ∧ next.val ≤ (stringNcodeunits s).val + 1

structure RepeatCharOps (C I : Type) where
  isNegative : I → Bool
  showInteger : I → String
  toUInt : I → StringResult (JInt .u64)
  charBits : C → StringResult UInt32
  swapBytes : UInt32 → UInt32
  leadingZeros : UInt32 → Nat
  maxUInt : Nat
  toCsize : Nat → StringResult Nat
  allocateString : Nat → StringResult JString
  unsafeConvertString : JString → Int
  withPreserve : JString → (Unit → JString) → JString
  memset : JString → Int → UInt8 → Nat → JString
  reinterpretPtr16 : Int → Int
  store16 : JString → Int → UInt16 → Nat → JString
  reinterpretPtr32 : Int → Int
  store32 : JString → Int → UInt32 → Nat → JString
  store8 : JString → Int → UInt8 → Nat → JString
  toUInt8 : UInt32 → UInt8
  toUInt16 : UInt32 → UInt16

def RepeatCharRejectsNegative : Prop :=
  ∀ {C I : Type} (ops : RepeatCharOps C I) (c : C) (count : I),
    ops.isNegative count = true →
    repeatChar ops.isNegative ops.showInteger ops.toUInt ops.charBits ops.swapBytes
      ops.leadingZeros ops.maxUInt ops.toCsize ops.allocateString ops.unsafeConvertString
      ops.withPreserve ops.memset ops.reinterpretPtr16 ops.store16 ops.reinterpretPtr32
      ops.store32 ops.store8 ops.toUInt8 ops.toUInt16 c count =
        .error (.jl (.argumentError
          ("can't repeat a character " ++ ops.showInteger count ++ " times")))
def nonContinuationCount {S : Type} (byteAt : S → Index → UInt8)
    (s : S) (first last : Index) : Nat :=
  if last.val < first.val then 0 else
    ((List.range (last.val - first.val + 1).toNat).filter
      (fun offset => !(isValidContinuation
        (byteAt s (first + JuliaLean.Strings.ix (Int.ofNat offset)))))).length

def CharacterLengthRange : Prop :=
  (∀ s i j, 0 < i.val → i.val ≤ (stringNcodeunits s).val + 1 →
    0 ≤ j.val → j.val < (stringNcodeunits s).val + 1 →
    if j.val < i.val then
      stringLengthRange s i j = .ok (JuliaLean.Strings.ix 0)
    else
      ∃ start, stringThisind s i = .ok start ∧
        stringLengthRange s i j =
          .ok (JuliaLean.Strings.ix (Int.ofNat (nonContinuationCount stringByteAt s start j)))) ∧
  (∀ view i j, 0 < i.val → i.val ≤ (stringViewNcodeunits view).val + 1 →
    0 ≤ j.val → j.val < (stringViewNcodeunits view).val + 1 →
    if j.val < i.val then
      stringViewLengthRange view i j = .ok (JuliaLean.Strings.ix 0)
    else
      ∃ start, stringViewThisind view i = .ok start ∧
        stringViewLengthRange view i j =
          .ok (JuliaLean.Strings.ix
            (Int.ofNat (nonContinuationCount stringViewByteAt view start j))))


namespace Round1

open JuliaLean
open JuliaLean.Proofs.base.strings.string
open JuliaLean.base.strings.basic
open JuliaLean.Proofs.base.strings.util.Round6

abbrev Index := JuliaLean.base.strings.string.Index
abbrev JString := JuliaLean.base.strings.string.JString

def validIndexCount {S : Type} (isvalid : S → Index → Bool)
    (s : S) (first last : Index) : Nat :=
  if last.val < first.val then 0
  else
    ((List.range (last.val - first.val + 1).toNat).filter
      (fun offset => isvalid s (first + JuliaLean.Strings.ix (Int.ofNat offset)))).length

def traceHasStart (rows : List (Index × UInt32 × Index)) (i : Index) : Bool :=
  rows.any (fun row => row.1.val == i.val)

def compareStringIndex (a b : Index) : Int :=
  JuliaLean.base.operators.cmpInteger JuliaLean.base.int.lt JuliaLean.base.int.lt a b

def compareStringValues (a b : JString) : Int :=
  JuliaLean.base.strings.string.cmpString stringCoreSizeof
    (fun x y n => JuliaLean.Proofs.base.strings.util.Round6.compareBytes x.bytes y.bytes n)
    compareStringIndex a b

/-- `length(::String)` equals the number of characters produced by a complete iteration.
Source: `base/strings/basic.jl:367-376`; `base/strings/string.jl:508-514,598-600`. -/
def StringLengthIterationCount : Prop :=
  ∀ s, ∃ rows, IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows ∧
    stringLength s = JuliaLean.Strings.ix (Int.ofNat rows.length)

/-- On valid String character starts, `prevind(s,nextind(s,i))` returns `i`. This composes
the installed String `nextind` model with the generic `prevind` model over `Round6`'s exact
String/SubString adapter. Source: `base/strings/string.jl:273-306`;
`base/strings/basic.jl:505-514,564-573`. -/
def PrevindAfterNextind : Prop :=
  ∀ s i j, stringIsvalidIndex s i = true → stringNextind s i = .ok j →
    (do
      let prepared ← JuliaLean.Proofs.base.strings.util.Round6.prepare s
      JuliaLean.Proofs.base.strings.util.Round6.previous prepared j) = .ok i

/-- For a valid String character start after the first code unit,
`nextind(s,prevind(s,i))` returns `i`. The generic `prevind` model runs over the installed
String/SubString adapter. Source: `base/strings/string.jl:273-306`;
`base/strings/basic.jl:505-514,564-573`. -/
def NextindAfterPrevind : Prop :=
  ∀ s i, stringIsvalidIndex s i = true → 1 < i.val →
    ∃ j,
      (do
        let prepared ← JuliaLean.Proofs.base.strings.util.Round6.prepare s
        JuliaLean.Proofs.base.strings.util.Round6.previous prepared i) = .ok j ∧
      stringNextind s j = .ok i

/-- Byte-specialized String comparison agrees with generic character comparison for every String,
including malformed byte sequences. Keep the malformed claim separate because the byte comparison
already has a reproducer. Source: `base/strings/string.jl:221-236`;
`base/strings/basic.jl:275-282,308-317`. -/
def CmpAgreesOnAllStrings : Prop :=
  ∀ a b, ∃ pa pb genericResult,
    JuliaLean.Proofs.base.strings.util.Round6.prepare a = .ok pa ∧
    JuliaLean.Proofs.base.strings.util.Round6.prepare b = .ok pb ∧
    JuliaLean.base.strings.basic.cmpString
      JuliaLean.Proofs.base.strings.util.Round6.preparedOps pa pb = .ok genericResult ∧
    compareStringValues a b = genericResult.val

/-- On well-formed UTF-8 strings, byte-specialized `cmp(::String,::String)` agrees with the
Unicode-code-point comparison used by `cmp(::AbstractString,::AbstractString)`. Malformed inputs
are recorded separately because they do not encode Unicode code points. Source:
`base/strings/string.jl:221-236`; `base/strings/basic.jl:275-282,308-317`. -/
def CmpAgreesOnValidUtf8 : Prop :=
  ∀ a b, stringBytesAreValidUtf8 a.bytes = true →
    stringBytesAreValidUtf8 b.bytes = true →
    ∃ pa pb genericResult,
      JuliaLean.Proofs.base.strings.util.Round6.prepare a = .ok pa ∧
      JuliaLean.Proofs.base.strings.util.Round6.prepare b = .ok pb ∧
      JuliaLean.base.strings.basic.cmpString
        JuliaLean.Proofs.base.strings.util.Round6.preparedOps pa pb = .ok genericResult ∧
      compareStringValues a b = genericResult.val

/-- Scalar String indexing at a valid character start returns the character yielded by iteration.
Source: `base/strings/string.jl:508-514,540-545`;
`base/strings/basic.jl:112-116`. -/
def ScalarGetindexMatchesIteration : Prop :=
  ∀ s i, stringIsvalidIndex s i = true →
    ∃ c next, stringIterate s i = some (c, next) ∧ stringGetindex s i = .ok c

/-- A String index is valid exactly when it occurs as a start in iteration from the first
index, including for malformed byte sequences. Source: `base/strings/basic.jl:112-116,148-153`;
`base/strings/string.jl:508-514,662`. -/
def StringIndexValidityMatchesIteration : Prop :=
  ∀ s i,
    stringIsvalidIndex s i = true ↔
      ∃ rows, IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows ∧ traceHasStart rows i

/-- String range length counts valid character-start indices in the requested interval.
Source: `base/strings/basic.jl:367-376`; `base/strings/string.jl:607-658`. -/
def StringCharacterLengthRangeCountsValidIndices : Prop :=
  ∀ s i j, 0 < i.val → i.val ≤ (stringNcodeunits s + JuliaLean.Strings.ix 1).val →
    0 ≤ j.val → j.val < (stringNcodeunits s + JuliaLean.Strings.ix 1).val →
    stringLengthRange s i j =
      .ok (JuliaLean.Strings.ix (Int.ofNat (validIndexCount stringIsvalidIndex s i j)))

/-- `isascii(::String)` is true exactly when every character yielded by iteration is ASCII.
Source: `base/strings/basic.jl:590-592`; `base/strings/string.jl:508-514,665`. -/
def AsciiMatchesIteratedCharacters : Prop :=
  ∀ s, ∃ rows, IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows ∧
    stringIsascii s = rows.all (fun row => row.2.1.toNat < 0x80)

end Round1

namespace Round2

open _root_.JuliaLean.base.strings.string _root_.JuliaLean.base.strings.basic

/-- `isascii(::String)` is true exactly when every character yielded by iteration is ASCII. The
predicate uses the installed packed-Char model (`base/strings/basic.jl:588-592,618-620`;
`base/strings/string.jl:508-514,665`). -/
def AsciiMatchesIteratedCharacters : Prop :=
  ∀ s, ∃ rows, IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows ∧
    stringIsascii s = rows.all (fun row => isasciiChar row.2.1)

end Round2
namespace JuliaLean.ChatGPT.Batch2.Group2

open JuliaLean
open JuliaLean.base.strings.string
open JuliaLean.Proofs.base.strings.util.Round6

namespace Indexing

theorem addOneNcodeunits (s : JString) :
    (stringNcodeunits s + JuliaLean.Strings.ix 1).val = (s.bytes.length : Int) + 1 := by
  have hs := s.small
  change wrapInt .i64 ((stringNcodeunits s).val + (JuliaLean.Strings.ix 1).val) = _
  rw [stringNcodeunits_val, show (JuliaLean.Strings.ix 1).val = 1 by decide]
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

theorem thisindZero (s : JString) :
    stringThisind s (JuliaLean.Strings.ix 0) = .ok (JuliaLean.Strings.ix 0) := by
  rfl

theorem thisindEnd (s : JString) (i : Index)
    (hi : i.val = (s.bytes.length : Int) + 1) :
    stringThisind s i = .ok i := by
  have h0 : (i.val == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    omega
  have hend : (i.val == (stringNcodeunits s + JuliaLean.Strings.ix 1).val) = true := by
    rw [addOneNcodeunits, hi]
    exact beq_self_eq_true _
  simp only [stringThisind, thisindString, thisindStr, h0, Bool.false_eq_true,
    ite_false, hend, ite_true, pure, Except.pure]

theorem thisindBounds (s : JString) (i j : Index)
    (h : stringThisind s i = .ok j) (h0 : i.val ≠ 0)
    (hend : i.val ≠ (s.bytes.length : Int) + 1) :
    1 ≤ i.val ∧ i.val ≤ (s.bytes.length : Int) := by
  have hzero : (i.val == 0) = false := beq_eq_false_iff_ne.mpr h0
  have hlast : (i.val == (stringNcodeunits s + JuliaLean.Strings.ix 1).val) = false := by
    rw [addOneNcodeunits]
    exact beq_eq_false_iff_ne.mpr hend
  by_cases hb : stringBetweenIndex i (JuliaLean.Strings.ix 1) (stringNcodeunits s) = true
  · simpa only [stringBetweenIndex, between, Bool.and_eq_true, decide_eq_true_eq,
      stringNcodeunits_val, show (JuliaLean.Strings.ix 1).val = 1 by decide] using hb
  · have hbf : stringBetweenIndex i (JuliaLean.Strings.ix 1) (stringNcodeunits s) = false :=
      Bool.eq_false_iff.mpr hb
    simp only [stringThisind, thisindString, thisindStr, hzero, hlast, hbf,
      Bool.false_eq_true, ite_false, Bool.not_false, ite_true, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind] at h
    cases h

theorem thisindPureResult (s : JString) (i : Index)
    (h1 : 1 ≤ i.val) (hn : i.val ≤ (s.bytes.length : Int)) :
    ∃ j, stringThisind s i = .ok j ∧ j.val = thisindPure (parentByte s) i.val := by
  have hs := s.small
  exact thisindStr_pure stringNcodeunits stringCodeunitAt s (parentByte s) i
    (fun k _ _ => stringCodeunitAt_unchecked s k) h1
    (by rw [stringNcodeunits_val]; exact hn)
    (by rw [stringNcodeunits_val]; omega)

end Indexing

/-- Every successful character-start normalization is idempotent, including sentinel indices. -/
theorem StringsThisindIdempotent_proven :
    JuliaLean.Proofs.base.strings.string.ThisindIdempotent := by
  intro s i j h
  by_cases h0 : i.val = 0
  · have hi : i = JuliaLean.Strings.ix 0 := Subtype.ext h0
    subst i
    rw [Indexing.thisindZero] at h
    cases h
    exact Indexing.thisindZero s
  · by_cases hend : i.val = (s.bytes.length : Int) + 1
    · rw [Indexing.thisindEnd s i hend] at h
      cases h
      exact Indexing.thisindEnd s i hend
    · obtain ⟨h1, hn⟩ := Indexing.thisindBounds s i j h h0 hend
      obtain ⟨r, hr, hrv⟩ := Indexing.thisindPureResult s i h1 hn
      rw [h] at hr
      cases hr
      have hj1 : 1 ≤ j.val := by
        rw [hrv]
        exact thisindPure_ge_one _ _ h1
      have hjn : j.val ≤ (s.bytes.length : Int) := by
        rw [hrv]
        exact Int.le_trans (thisindPure_le _ _) hn
      obtain ⟨k, hk, hkv⟩ := Indexing.thisindPureResult s j hj1 hjn
      have hkj : k = j := by
        apply Subtype.ext
        rw [hkv, hrv, thisindPure_idem]
      rw [hkj] at hk
      exact hk

/-- The checked code-unit read returns the stored byte at every in-bounds index. -/
theorem StringsCodeunitBytes_proven :
    JuliaLean.Proofs.base.strings.string.StringCodeunitBytes := by
  intro s i h1 hn
  have hn' : i.val ≤ (s.bytes.length : Int) := by
    rwa [stringNcodeunits_val] at hn
  have hc : stringCheckbounds s i = .ok () := by
    simp only [stringCheckbounds, h1, hn', decide_true, Bool.true_and, ite_true]
  have hi : (i.val - 1).toNat = i.val.toNat - 1 := by omega
  simp only [stringCodeunit, codeunitInteger, codeunitInt, hc, ite_true,
    bind, Except.bind, pure, Except.pure, stringPreserveByte, stringUnsafeLoad,
    pointerAt, pointerString, stringUnsafeConvert, Int.zero_add, hi, stringByteAt]

end JuliaLean.ChatGPT.Batch2.Group2

namespace JuliaLean.ChatGPT.Batch2.Group2

open JuliaLean
open JuliaLean.base.strings.string
open JuliaLean.Proofs.base.strings.util.Round6

namespace Navigation

/-- Successful validity includes the ordinary one-based byte bounds. -/
theorem validBounds (s : JString) (i : Index) (h : stringIsvalidIndex s i = true) :
    1 ≤ i.val ∧ i.val ≤ (s.bytes.length : Int) := by
  unfold stringIsvalidIndex isvalidStringIndex at h
  have hb := (Bool.and_eq_true_iff.mp h).1
  simpa only [stringCheckboundsBool, Bool.and_eq_true, decide_eq_true_eq] using hb

/-- Preparing a whole String succeeds and preserves its complete byte interval. -/
theorem prepareWhole (s : JString) :
    ∃ p, prepare s = .ok p ∧ p.view.string = s ∧ p.view.offset.val = 0 ∧
      p.view.ncodeunits.val = (s.bytes.length : Int) := by
  let v : View := ⟨s, JuliaLean.base.strings.substring.one -
    JuliaLean.base.strings.substring.one, stringNcodeunits s⟩
  have hoff : v.offset.val = 0 := oneSubOne_val
  have hn : v.ncodeunits.val = (s.bytes.length : Int) := stringNcodeunits_val s
  obtain ⟨p, hp, hv⟩ := prepareView_ok v (by simpa only [hoff] using (Int.le_refl 0))
    (by rw [hn]; exact Int.natCast_nonneg _) (by change v.offset.val + v.ncodeunits.val ≤ (s.bytes.length : Int); rw [hoff, hn]; omega)
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · unfold prepare
    rw [rawView_eq, ok_bind']
    exact hp
  · rw [hv]
  · rw [hv]; exact hoff
  · rw [hv]; exact hn

/-- The prepared predecessor is the pure character start immediately before its argument. -/
theorem previousWhole (s : JString) (p : Prepared) (hp : prepare s = .ok p)
    (hs : p.view.string = s) (hoff : p.view.offset.val = 0)
    (hn : p.view.ncodeunits.val = (s.bytes.length : Int))
    (i : Index) (h1 : 2 ≤ i.val) (hmax : i.val ≤ (s.bytes.length : Int) + 1) :
    ∃ j, previous p i = .ok j ∧ j.val = thisindPure (parentByte s) (i.val - 1) := by
  obtain ⟨j, hj, _, hval⟩ := previous_spec p (goodView_ofPrepare s p hp) i
    (by omega) (by rw [hn]; exact hmax)
  refine ⟨j, hj, ?_⟩
  have hv := hval h1
  simpa only [hs, hoff, Int.zero_add] using hv

/-- The last byte before a successor belongs to the initial character. -/
theorem predecessorOfSuccessor (rd : Int → UInt8) (i j : Int)
    (hv : ¬ joined rd i) (hij : i < j)
    (hgap : ∀ q, i < q → q < j → joined rd q) :
    thisindPure rd (j - 1) = i := by
  have hlo := thisindPure_ge_valid rd (j - 1) i hv (by omega)
  have hle := thisindPure_le rd (j - 1)
  have hstart := (thisindPure_eq_iff rd (thisindPure rd (j - 1))).mp
    (thisindPure_idem rd (j - 1))
  apply Int.le_antisymm
  · apply Int.not_lt.mp
    intro hgt
    exact hstart (hgap _ hgt (by omega))
  · exact hlo

end Navigation

/-- strings-prevind-after-nextind: The installed predecessor inverts String's successor. -/
theorem StringsPrevindAfterNextind_proven :
    JuliaLean.Proofs.base.strings.string.Round1.PrevindAfterNextind := by
  intro s i j hvalid hnext
  obtain ⟨hi1, hin⟩ := Navigation.validBounds s i hvalid
  have hv : ¬ joined (parentByte s) i.val :=
    (thisindPure_eq_iff _ _).mp ((stringIsvalid_iff_pure s i hi1 hin).mp hvalid)
  obtain ⟨m, hm, hgt, hle, _, hgap⟩ := stringNextind_next s i hi1 hin hv
  have hmj : m = j := by
    exact Except.ok.inj (hm.symm.trans hnext)
  subst m
  obtain ⟨p, hp, hs, hoff, hn⟩ := Navigation.prepareWhole s
  obtain ⟨r, hr, hrv⟩ := Navigation.previousWhole s p hp hs hoff hn j (by omega) hle
  have hri : r = i := by
    apply Subtype.ext
    exact hrv.trans (Navigation.predecessorOfSuccessor (parentByte s) i.val j.val hv hgt hgap)
  subst r
  rw [hp, ok_bind']
  exact hr

/-- strings-nextind-after-prevind: String's successor inverts the installed predecessor. -/
theorem StringsNextindAfterPrevind_proven :
    JuliaLean.Proofs.base.strings.string.Round1.NextindAfterPrevind := by
  intro s i hvalid hfirst
  obtain ⟨hi1, hin⟩ := Navigation.validBounds s i hvalid
  have hvi : ¬ joined (parentByte s) i.val :=
    (thisindPure_eq_iff _ _).mp ((stringIsvalid_iff_pure s i hi1 hin).mp hvalid)
  obtain ⟨p, hp, hs, hoff, hn⟩ := Navigation.prepareWhole s
  obtain ⟨j, hj, hjval⟩ := Navigation.previousWhole s p hp hs hoff hn i (by omega) (by omega)
  have hj1 : 1 ≤ j.val := by
    rw [hjval]
    exact thisindPure_ge_one _ _ (by omega)
  have hjlt : j.val < i.val := by
    have ht := thisindPure_le (parentByte s) (i.val - 1)
    omega
  have hvj : ¬ joined (parentByte s) j.val := by
    rw [hjval]
    exact (thisindPure_eq_iff _ _).mp (thisindPure_idem _ _)
  obtain ⟨m, hm, hjm, hmn, hmv, hgap⟩ := stringNextind_next s j hj1 (by omega) hvj
  have hmi : m = i := by
    apply Subtype.ext
    apply Int.le_antisymm
    · apply Int.not_lt.mp
      intro him
      exact hvi (hgap i.val hjlt him)
    · apply Int.not_lt.mp
      intro hmi
      have hmj : thisindPure (parentByte s) (i.val - 1) < m.val := by omega
      have hjoined := thisindPure_gap (parentByte s) (i.val - 1) m.val hmj (by omega)
      rcases hmv with hend | hstart
      · omega
      · exact hstart hjoined
  refine ⟨j, ?_, ?_⟩
  · rw [hp, ok_bind']
    exact hj
  · rw [← hmi]
    exact hm

end JuliaLean.ChatGPT.Batch2.Group2

namespace JuliaLean.ChatGPT.Batch2.Group2
namespace Compare

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

open JuliaLean.Proofs.base.strings.util.Round6

/-- These are the exact two-byte inputs constructed by the companion Julia script. -/
def left : Raw := ⟨[0xc2, 0xff], by decide⟩
def right : Raw := ⟨[0xc2, 0x80], by decide⟩
def leftPrepared : Prepared :=
  ⟨⟨left, JuliaLean.Strings.ix 0, JuliaLean.Strings.ix 2⟩, JuliaLean.Strings.ix 2⟩
def rightPrepared : Prepared :=
  ⟨⟨right, JuliaLean.Strings.ix 0, JuliaLean.Strings.ix 2⟩, JuliaLean.Strings.ix 1⟩

theorem prepare_left : prepare left = .ok leftPrepared := by
  rfl

theorem rawView_right : rawView right = .ok rightPrepared.view := by
  rfl

theorem right_last :
    viewThisind rightPrepared.view (JuliaLean.Strings.ix 2) =
      .ok (JuliaLean.Strings.ix 1) := by
  rfl

theorem prepare_right : prepare right = .ok rightPrepared := by
  unfold prepare
  rw [rawView_right]
  change prepareView rightPrepared.view = .ok rightPrepared
  unfold prepareView
  rw [show JuliaLean.base.strings.substring.lastindexSubString viewThisind rightPrepared.view =
    viewThisind rightPrepared.view (JuliaLean.Strings.ix 2) from rfl, right_last]
  rfl

theorem bytes_compare :
    JuliaLean.Proofs.base.strings.string.Round1.compareStringValues left right = 1 := by
  rfl

theorem characters_compare :
    JuliaLean.base.strings.basic.cmpString preparedOps leftPrepared rightPrepared =
      .ok (JuliaLean.Strings.ix (-1)) := by
  rfl

end Compare

/-- strings-cmp-malformed: the four bytes in the companion Julia script reverse the
ordering between the String specialization and generic AbstractString comparison. -/
theorem StringsCmpMalformed_refuted :
    ¬ JuliaLean.Proofs.base.strings.string.Round1.CmpAgreesOnAllStrings := by
  intro h
  obtain ⟨pa, pb, result, ha, hb, hc, hcompare⟩ := h Compare.left Compare.right
  rw [Compare.prepare_left] at ha
  cases ha
  rw [Compare.prepare_right] at hb
  cases hb
  rw [Compare.characters_compare] at hc
  cases hc
  rw [Compare.bytes_compare] at hcompare
  have hneg : (JuliaLean.Strings.ix (-1)).val = -1 := by decide
  rw [hneg] at hcompare
  omega

end JuliaLean.ChatGPT.Batch2.Group2
namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean
open JuliaLean.Proofs.base.strings.string
open JuliaLean.Proofs.base.strings.util.Round6

theorem cmpBindSuccess {A B E : Type} (f : A → Except E B) (v : A) :
    (do let x ← (Except.ok v : Except E A); f x) = f v := by
  rfl

theorem cmpPrepareWhole (s : Raw) :
    prepare s = prepareView ⟨s, JuliaLean.base.strings.substring.one -
      JuliaLean.base.strings.substring.one, Str.stringNcodeunits s⟩ := by
  let v : View := ⟨s, JuliaLean.base.strings.substring.one -
    JuliaLean.base.strings.substring.one, Str.stringNcodeunits s⟩
  have heq : prepare s = (do let x ← (Except.ok v : Result View); prepareView x) :=
    congrArg (fun r : Result View => do let x ← r; prepareView x) (rawView_eq s)
  exact heq.trans (cmpBindSuccess prepareView v)

/-- Preparation of the installed whole-string adapter succeeds for every representable String. -/
theorem cmpPrepareExists (s : Raw) : ∃ p, prepare s = .ok p := by
  let v : View := ⟨s, JuliaLean.base.strings.substring.one -
    JuliaLean.base.strings.substring.one, Str.stringNcodeunits s⟩
  have gv : GoodView v := goodView_rawView s
  obtain ⟨p, hp, _⟩ := prepareView_ok v gv.off gv.len gv.fit
  exact ⟨p, (cmpPrepareWhole s).trans hp⟩

/-- The preparation adapter preserves the parent and its complete length. -/
theorem cmpPreparedView (s : Raw) (p : Prepared) (hp : prepare s = .ok p) :
    p.view = ⟨s, JuliaLean.base.strings.substring.one -
      JuliaLean.base.strings.substring.one, Str.stringNcodeunits s⟩ := by
  have hview : prepareView ⟨s, JuliaLean.base.strings.substring.one -
      JuliaLean.base.strings.substring.one, Str.stringNcodeunits s⟩ = .ok p :=
    (cmpPrepareWhole s).symm.trans hp
  exact prepareView_view hview

/-- The preparation adapter preserves the complete byte list. -/
theorem cmpPreparedBytes (s : Raw) (p : Prepared) (hp : prepare s = .ok p) :
    preparedBytes p = s.bytes := by
  have hv := cmpPreparedView s p hp
  unfold preparedBytes viewBytes
  rw [hv]
  simp only [oneSubOne_val, Int.toNat_zero, List.drop_zero, stringNcodeunits_val,
    Int.toNat_natCast, List.take_length]

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## CmpAdapterCore -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean
open JuliaLean.base.strings.string

theorem cmpAdapterLengthVal (s : JString) :
    (stringNcodeunits s).val = (s.bytes.length : Int) := by
  have hs := s.small
  change wrapInt .i64 (s.bytes.length : Int) = _
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

theorem cmpAdapterZeroAdd (i : Index) : JuliaLean.Strings.ix 0 + i = i := by
  apply Subtype.ext
  change wrapInt .i64 ((JuliaLean.Strings.ix 0).val + i.val) = i.val
  rw [show (JuliaLean.Strings.ix 0).val = 0 by rfl, Int.zero_add]
  exact wrapInt_of_inRange .i64 _ i.property

theorem cmpAdapterSubZero (i : Index) : i - JuliaLean.Strings.ix 0 = i := by
  apply Subtype.ext
  change wrapInt .i64 (i.val - (JuliaLean.Strings.ix 0).val) = i.val
  rw [show (JuliaLean.Strings.ix 0).val = 0 by rfl, Int.sub_zero]
  exact wrapInt_of_inRange .i64 _ i.property

theorem cmpAdapterEndVal (s : JString) :
    (stringNcodeunits s + JuliaLean.base.strings.substring.one).val =
      (s.bytes.length : Int) + 1 := by
  have hs := s.small
  change wrapInt .i64 ((stringNcodeunits s).val +
    JuliaLean.base.strings.substring.one.val) = _
  rw [cmpAdapterLengthVal, show JuliaLean.base.strings.substring.one.val = 1 by rfl]
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

theorem cmpAdapterRawEnd (s : JString) (i : Index)
    (hi : i.val = (s.bytes.length : Int) + 1) : stringIterate s i = none := by
  have hs := s.small
  have hu : (JInt.rem .u64 i).val = i.val := by
    change wrapInt .u64 i.val = _
    exact wrapInt_of_inRange .u64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)
  have hm : (JInt.rem .u64 i - JInt.lit .u64 1).val = (s.bytes.length : Int) := by
    change wrapInt .u64 ((JInt.rem .u64 i).val - (JInt.lit .u64 1).val) = _
    rw [hu, hi, show (JInt.lit .u64 1).val = 1 by rfl, Int.add_sub_cancel]
    exact wrapInt_of_inRange .u64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)
  unfold stringIterate iterateString
  rw [hm, cmpAdapterLengthVal]
  simp only [Int.lt_irrefl, decide_false, Bool.not_false, ite_true]

theorem cmpAdapterReturnSame (r : Option (UInt32 × Index)) :
    (match r with
      | none => (Except.ok none : StringResult (Option (UInt32 × Index)))
      | some (c, next) => .ok (some (c, next - JuliaLean.Strings.ix 0))) = .ok r := by
  cases r with
  | none => rfl
  | some row =>
      rcases row with ⟨c, next⟩
      change Except.ok (some (c, next - JuliaLean.Strings.ix 0)) =
        (Except.ok (some (c, next)) : StringResult (Option (UInt32 × Index)))
      rw [cmpAdapterSubZero]


theorem cmpZeroSubstringIterateGeneric {S : Type} (s : S) (n i : Index)
    (f : S → Index → Option (UInt32 × Index))
    (hend : i.val = (n + JuliaLean.base.strings.substring.one).val → f s i = none)
    (hb : i.val ≠ (n + JuliaLean.base.strings.substring.one).val →
      1 ≤ i.val ∧ i.val ≤ n.val) :
    JuliaLean.base.strings.substring.iterateSubString JuliaLean.base.int.eq_int
      (fun v i => if 1 ≤ i.val ∧ i.val ≤ v.ncodeunits.val then
        (Except.ok () : StringResult Unit) else .error (.jl .boundsError))
      (fun offset i => .ok (offset + i)) (fun s i => .ok (f s i))
      (⟨s, JuliaLean.Strings.ix 0, n⟩ :
        JuliaLean.base.strings.substring.SubString S) i = .ok (f s i) := by
  unfold JuliaLean.base.strings.substring.iterateSubString
  rw [JuliaLean.Proofs.base.int.eq_int_eq]
  by_cases he : i.val = (n + JuliaLean.base.strings.substring.one).val
  · simp only [he, decide_true, ite_true, pure, Except.pure, hend he]
  · have hb' := hb he
    simp only [he, decide_false, Bool.false_eq_true, ite_false, hb', and_self, ite_true,
      bind, Except.bind, cmpAdapterZeroAdd, pure, Except.pure]
    generalize f s i = result
    cases result with
    | none => rfl
    | some row =>
        rcases row with ⟨c, next⟩
        change Except.ok (some (c, next - JuliaLean.Strings.ix 0)) =
          (Except.ok (some (c, next)) : StringResult (Option (UInt32 × Index)))
        rw [cmpAdapterSubZero]

theorem cmpWholeSubstringIterate (s : JString) (i : Index)
    (hi : 1 ≤ i.val) (hn : i.val ≤ (s.bytes.length : Int) + 1) :
    JuliaLean.base.strings.substring.iterateSubString JuliaLean.base.int.eq_int
      (fun v i => if 1 ≤ i.val ∧ i.val ≤ v.ncodeunits.val then
        (Except.ok () : StringResult Unit) else .error (.jl .boundsError))
      (fun offset i => .ok (offset + i)) (fun s i => .ok (stringIterate s i))
      (⟨s, JuliaLean.Strings.ix 0, stringNcodeunits s⟩ :
        JuliaLean.base.strings.substring.SubString JString) i = .ok (stringIterate s i) := by
  apply cmpZeroSubstringIterateGeneric
  · intro he
    apply cmpAdapterRawEnd
    rw [cmpAdapterEndVal] at he
    exact he
  · intro he
    rw [cmpAdapterEndVal] at he
    rw [cmpAdapterLengthVal]
    omega

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## CmpAdapter -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean
open JuliaLean.base.strings.string
open JuliaLean.Proofs.base.strings.util.Round6

theorem cmpPreparedIterateAt (s : Raw) (p : Prepared) (hp : prepare s = .ok p)
    (i : Index) (hi : 1 ≤ i.val) (hn : i.val ≤ (s.bytes.length : Int) + 1) :
    preparedOps.iterateAt p i = .ok (stringIterate s i) := by
  change viewIterate p.view i = .ok (stringIterate s i)
  rw [cmpPreparedView s p hp]
  exact cmpWholeSubstringIterate s i hi hn

theorem cmpPreparedIterateFirst (s : Raw) (p : Prepared) (hp : prepare s = .ok p) :
    preparedOps.iterateFirst p = .ok (stringIterate s (JuliaLean.Strings.ix 1)) := by
  exact cmpPreparedIterateAt s p hp (JuliaLean.Strings.ix 1) (by decide) (by
    change (1 : Int) ≤ (s.bytes.length : Int) + 1
    omega)

theorem cmpPreparedIterationBound (s : Raw) (p : Prepared) (hp : prepare s = .ok p) :
    preparedOps.iterationBound p = s.bytes.length + 1 := by
  change p.view.ncodeunits.val.toNat + 1 = s.bytes.length + 1
  rw [cmpPreparedView s p hp, cmpAdapterLengthVal, Int.toNat_natCast]

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## CmpShape -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean.base.strings.string

inductive CmpUtf8Shape : List UInt8 → Prop where
  | empty : CmpUtf8Shape []
  | ascii {b rest} (hb : b.toNat < 128) (tail : CmpUtf8Shape rest) :
      CmpUtf8Shape (b :: rest)
  | two {b1 b2 rest} (lead : 192 ≤ b1.toNat ∧ b1.toNat < 224)
      (c2 : 128 ≤ b2.toNat ∧ b2.toNat < 192) (tail : CmpUtf8Shape rest) :
      CmpUtf8Shape (b1 :: b2 :: rest)
  | three {b1 b2 b3 rest} (lead : 224 ≤ b1.toNat ∧ b1.toNat < 240)
      (c2 : 128 ≤ b2.toNat ∧ b2.toNat < 192)
      (c3 : 128 ≤ b3.toNat ∧ b3.toNat < 192) (tail : CmpUtf8Shape rest) :
      CmpUtf8Shape (b1 :: b2 :: b3 :: rest)
  | four {b1 b2 b3 b4 rest} (lead : 240 ≤ b1.toNat ∧ b1.toNat < 248)
      (c2 : 128 ≤ b2.toNat ∧ b2.toNat < 192)
      (c3 : 128 ≤ b3.toNat ∧ b3.toNat < 192)
      (c4 : 128 ≤ b4.toNat ∧ b4.toNat < 192) (tail : CmpUtf8Shape rest) :
      CmpUtf8Shape (b1 :: b2 :: b3 :: b4 :: rest)

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## CmpLex -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean
open JuliaLean.base.strings.string

/-- The byte-aligned representation used by Julia's Char. -/
def cmpPack (a b c d : UInt8) : UInt32 :=
  (a.toUInt32 <<< 24) ||| ((b.toUInt32 <<< 16) ||| ((c.toUInt32 <<< 8) ||| d.toUInt32))

theorem cmpShift24 (b : UInt8) : (b.toUInt32 <<< 24).toNat = b.toNat * 16777216 := by
  have hb := b.toNat_lt
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  change (b.toNat <<< 24) % 4294967296 = _
  rw [Nat.shiftLeft_eq]
  omega

theorem cmpShift16 (b : UInt8) : (b.toUInt32 <<< 16).toNat = b.toNat * 65536 := by
  have hb := b.toNat_lt
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  change (b.toNat <<< 16) % 4294967296 = _
  rw [Nat.shiftLeft_eq]
  omega

theorem cmpShift8 (b : UInt8) : (b.toUInt32 <<< 8).toNat = b.toNat * 256 := by
  have hb := b.toNat_lt
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32]
  change (b.toNat <<< 8) % 4294967296 = _
  rw [Nat.shiftLeft_eq]
  omega

theorem cmpPackNat (a b c d : UInt8) : (cmpPack a b c d).toNat =
    a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat := by
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have e1 : (c.toNat * 256 ||| d.toNat) = c.toNat * 256 + d.toNat := by
    have h := Nat.two_pow_add_eq_or_of_lt (i := 8) hd c.toNat
    simpa only [Nat.reducePow, Nat.mul_comm] using h.symm
  have e2 : (b.toNat * 65536 ||| (c.toNat * 256 + d.toNat)) =
      b.toNat * 65536 + (c.toNat * 256 + d.toNat) := by
    have h := Nat.two_pow_add_eq_or_of_lt (i := 16)
      (show c.toNat * 256 + d.toNat < 2 ^ 16 by omega) b.toNat
    simpa only [Nat.reducePow, Nat.mul_comm] using h.symm
  have e3 : (a.toNat * 16777216 ||| (b.toNat * 65536 + (c.toNat * 256 + d.toNat))) =
      a.toNat * 16777216 + (b.toNat * 65536 + (c.toNat * 256 + d.toNat)) := by
    have h := Nat.two_pow_add_eq_or_of_lt (i := 24)
      (show b.toNat * 65536 + (c.toNat * 256 + d.toNat) < 2 ^ 24 by omega) a.toNat
    simpa only [Nat.reducePow, Nat.mul_comm] using h.symm
  simp only [cmpPack, UInt32.toNat_or, cmpShift24, cmpShift16, cmpShift8,
    UInt8.toNat_toUInt32, e1, e2, e3]
  omega

inductive CmpGlyph where
  | ascii (a : UInt8) (ha : a.toNat < 128)
  | two (a b : UInt8) (ha : 192 ≤ a.toNat ∧ a.toNat < 224)
      (hb : 128 ≤ b.toNat ∧ b.toNat < 192)
  | three (a b c : UInt8) (ha : 224 ≤ a.toNat ∧ a.toNat < 240)
      (hb : 128 ≤ b.toNat ∧ b.toNat < 192) (hc : 128 ≤ c.toNat ∧ c.toNat < 192)
  | four (a b c d : UInt8) (ha : 240 ≤ a.toNat ∧ a.toNat < 248)
      (hb : 128 ≤ b.toNat ∧ b.toNat < 192) (hc : 128 ≤ c.toNat ∧ c.toNat < 192)
      (hd : 128 ≤ d.toNat ∧ d.toNat < 192)

def CmpGlyph.bytes : CmpGlyph → List UInt8
  | .ascii a _ => [a]
  | .two a b _ _ => [a,b]
  | .three a b c _ _ _ => [a,b,c]
  | .four a b c d _ _ _ _ => [a,b,c,d]

def CmpGlyph.bits : CmpGlyph → UInt32
  | .ascii a _ => cmpPack a 0 0 0
  | .two a b _ _ => cmpPack a b 0 0
  | .three a b c _ _ _ => cmpPack a b c 0
  | .four a b c d _ _ _ _ => cmpPack a b c d

def cmpGlyphBytes (cs : List CmpGlyph) : List UInt8 := cs.flatMap CmpGlyph.bytes

theorem cmpShapeGlyphs {bs : List UInt8} (h : CmpUtf8Shape bs) :
    ∃ cs : List CmpGlyph, cmpGlyphBytes cs = bs := by
  induction h with
  | empty => exact ⟨[], rfl⟩
  | @ascii b rest hb h ih =>
    obtain ⟨cs, rfl⟩ := ih
    exact ⟨CmpGlyph.ascii b hb :: cs, rfl⟩
  | @two a b rest ha hb h ih =>
    obtain ⟨cs, rfl⟩ := ih
    exact ⟨CmpGlyph.two a b ha hb :: cs, rfl⟩
  | @three a b c rest ha hb hc h ih =>
    obtain ⟨cs, rfl⟩ := ih
    exact ⟨CmpGlyph.three a b c ha hb hc :: cs, rfl⟩
  | @four a b c d rest ha hb hc hd h ih =>
    obtain ⟨cs, rfl⟩ := ih
    exact ⟨CmpGlyph.four a b c d ha hb hc hd :: cs, rfl⟩

def cmpLexBytes : List UInt8 → List UInt8 → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs =>
      if a < b then -1 else if b < a then 1 else cmpLexBytes as bs

def cmpLexChars : List UInt32 → List UInt32 → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs =>
      if a < b then -1 else if b < a then 1 else cmpLexChars as bs

def cmpSelect (a b : Nat) (rest : Int) : Int :=
  if a < b then -1 else if b < a then 1 else rest

theorem cmpSelectDigit (a b x y k : Nat) (hx : x < k) (hy : y < k) (r : Int) :
    cmpSelect (a*k+x) (b*k+y) r = cmpSelect a b (cmpSelect x y r) := by
  by_cases hab : a < b
  · have hm : (a+1)*k ≤ b*k := Nat.mul_le_mul_right k hab
    simp only [Nat.add_mul, Nat.one_mul] at hm
    have hxy : a*k+x < b*k+y := by omega
    simp only [cmpSelect, hab, hxy, ite_true]
  · by_cases hba : b < a
    · have hm : (b+1)*k ≤ a*k := Nat.mul_le_mul_right k hba
      simp only [Nat.add_mul, Nat.one_mul] at hm
      have hxy : b*k+y < a*k+x := by omega
      have hnot : ¬a*k+x < b*k+y := by omega
      simp only [cmpSelect, hab, hba, hxy, hnot, ite_true, ite_false]
    · have heq : a = b := by omega
      subst b
      simp only [cmpSelect, Nat.lt_irrefl, ite_false, Nat.add_lt_add_iff_left]

theorem cmpPackSelect (a b c d e f g h : UInt8) (r : Int) :
    cmpSelect (cmpPack a b c d).toNat (cmpPack e f g h).toNat r =
      cmpSelect a.toNat e.toNat (cmpSelect b.toNat f.toNat
        (cmpSelect c.toNat g.toNat (cmpSelect d.toNat h.toNat r))) := by
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have hf := f.toNat_lt
  have hg := g.toNat_lt
  have hh := h.toNat_lt
  rw [cmpPackNat, cmpPackNat]
  rw [show a.toNat*16777216+b.toNat*65536+c.toNat*256+d.toNat =
    a.toNat*16777216+(b.toNat*65536+(c.toNat*256+d.toNat)) by omega]
  rw [show e.toNat*16777216+f.toNat*65536+g.toNat*256+h.toNat =
    e.toNat*16777216+(f.toNat*65536+(g.toNat*256+h.toNat)) by omega]
  rw [cmpSelectDigit _ _ _ _ 16777216 (by omega) (by omega),
    cmpSelectDigit _ _ _ _ 65536 (by omega) (by omega),
    cmpSelectDigit _ _ _ _ 256 (by omega) (by omega)]

theorem cmpLexBytes_cons (a b : UInt8) (xs ys : List UInt8) :
    cmpLexBytes (a::xs) (b::ys) = cmpSelect a.toNat b.toNat (cmpLexBytes xs ys) := rfl

theorem cmpGlyphLex (a b : CmpGlyph) (xs ys : List UInt8) :
    cmpLexBytes (a.bytes ++ xs) (b.bytes ++ ys) =
      if a.bits < b.bits then -1 else if b.bits < a.bits then 1 else cmpLexBytes xs ys := by
  change cmpLexBytes (a.bytes ++ xs) (b.bytes ++ ys) =
    cmpSelect a.bits.toNat b.bits.toNat (cmpLexBytes xs ys)
  cases a <;> cases b
  all_goals simp only [CmpGlyph.bytes, CmpGlyph.bits, List.cons_append, List.nil_append,
    cmpPackSelect, cmpLexBytes_cons, show (0 : UInt8).toNat = 0 from rfl]
  all_goals first
    | rfl
    | (simp (disch := omega) only [cmpSelect, ite_eq_left, ite_eq_right])

 theorem cmpGlyphLexLists (xs ys : List CmpGlyph) :
    cmpLexBytes (cmpGlyphBytes xs) (cmpGlyphBytes ys) =
      cmpLexChars (xs.map CmpGlyph.bits) (ys.map CmpGlyph.bits) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => cases y <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => cases x <;> rfl
    | cons y ys =>
      change cmpLexBytes (x.bytes ++ cmpGlyphBytes xs) (y.bytes ++ cmpGlyphBytes ys) = _
      rw [cmpGlyphLex, ih]
      rfl

theorem cmpGlyphNonempty (g : CmpGlyph) : 0 < g.bytes.length := by
  cases g <;> simp only [CmpGlyph.bytes, List.length_cons, List.length_nil] <;> omega

theorem cmpGlyphCount (cs : List CmpGlyph) : cs.length ≤ (cmpGlyphBytes cs).length := by
  induction cs with
  | nil => exact Nat.le_refl 0
  | cons c cs ih =>
    have hc := cmpGlyphNonempty c
    change cs.length+1 ≤ (c.bytes ++ cmpGlyphBytes cs).length
    rw [List.length_append]
    omega

theorem cmpLexBytesSelf (bs : List UInt8) : cmpLexBytes bs bs = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [cmpLexBytes,UInt8.lt_iff_toNat_lt,Nat.lt_irrefl,ite_false,ih]

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## CmpDecode -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean
open JuliaLean.base.strings.string

def cmpIndex (offset : Nat) : Index := JuliaLean.Strings.ix (((offset + 1 : Nat) : Int))

theorem cmpIndexVal (o : Nat) (ho : o < 2 ^ 62 + 8) : (cmpIndex o).val = ((o + 1 : Nat) : Int) := by
  change wrapInt .i64 (((o + 1 : Nat) : Int)) = _
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

theorem cmpIndexNext (o : Nat) (ho : o < 2 ^ 62 + 7) :
    cmpIndex o + JuliaLean.Strings.ix 1 = cmpIndex (o+1) := by
  apply Subtype.ext
  change wrapInt .i64 ((cmpIndex o).val + (JuliaLean.Strings.ix 1).val) = _
  rw [cmpIndexVal _ (by omega), cmpIndexVal _ (by omega),
    show (JuliaLean.Strings.ix 1).val = 1 by decide]
  rw [wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)]
  omega

theorem cmpStorageLength (s : JString) : (stringNcodeunits s).val = (s.bytes.length : Int) := by
  have h := s.small
  change wrapInt .i64 (s.bytes.length : Int) = _
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

theorem cmpReadNat (s : JString) (o : Nat) (ho : o < 2 ^ 62 + 8) :
    stringByteAt s (cmpIndex o) = s.bytes.getD o 0 := by
  unfold stringByteAt
  rw [cmpIndexVal o ho, Int.toNat_natCast, Nat.add_sub_cancel]

theorem cmpReadPrefix (s : JString) (pre bs : List UInt8) (h : s.bytes = pre ++ bs)
    (k : Nat) (hk : pre.length+k < 2 ^ 62 + 8) :
    stringByteAt s (cmpIndex (pre.length+k)) = bs.getD k 0 := by
  rw [cmpReadNat _ _ hk, h]
  simp only [List.getD, List.getElem?_append_right (by omega : pre.length ≤ pre.length+k),
    Nat.add_sub_cancel_left]

theorem cmpIterateInBounds (s : JString) (o : Nat) (ho : o < s.bytes.length) :
    stringIterate s (cmpIndex o) =
      if !stringBetweenByte (stringByteAt s (cmpIndex o)) 0x80 0xf7 then
        some ((stringByteAt s (cmpIndex o)).toUInt32 <<< 24,
          cmpIndex o + JuliaLean.Strings.ix 1)
      else some (iterateContinued stringNcodeunits stringByteAt s (cmpIndex o)
        ((stringByteAt s (cmpIndex o)).toUInt32 <<< 24)) := by
  have hs := s.small
  have hu : (JInt.rem .u64 (cmpIndex o)).val = (cmpIndex o).val := by
    change wrapInt .u64 (cmpIndex o).val = _
    rw [cmpIndexVal _ (by omega)]
    exact wrapInt_of_inRange .u64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)
  have hc : (JInt.rem .u64 (cmpIndex o) - JInt.lit .u64 1).val = (o : Int) := by
    change wrapInt .u64 ((JInt.rem .u64 (cmpIndex o)).val - (JInt.lit .u64 1).val) = _
    rw [hu, cmpIndexVal _ (by omega), show (JInt.lit .u64 1).val = 1 by decide]
    rw [wrapInt_of_inRange .u64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)]
    omega
  unfold stringIterate iterateString
  rw [hc, cmpStorageLength]
  simp only [Int.ofNat_lt, ho, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]

set_option maxRecDepth 100000 in
theorem cmpContinuation (b : UInt8) (hb : 128 ≤ b.toNat ∧ b.toNat < 192) :
    ((b &&& 0xc0) != 0x80) = false := by
  have key : ∀ n, n < 256 → 128 ≤ n ∧ n < 192 →
      (((UInt8.ofNat n) &&& 0xc0) != 0x80) = false := by decide
  have h := key b.toNat b.toNat_lt hb
  simpa only [UInt8.ofNat_toNat] using h

theorem cmpPackOne (a : UInt8) : cmpPack a 0 0 0 = a.toUInt32 <<< 24 := by
  apply UInt32.toNat_inj.mp
  rw [cmpPackNat, cmpShift24]
  simp only [show (0 : UInt8).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]

theorem cmpPackTwo (a b : UInt8) :
    cmpPack a b 0 0 = (a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16) := by
  unfold cmpPack
  have hz1 : ((0 : UInt8).toUInt32 <<< 8) = 0 := rfl
  have hz2 : (0 : UInt8).toUInt32 = 0 := rfl
  rw [hz1,hz2,UInt32.or_zero,UInt32.or_zero]

theorem cmpPackThree (a b c : UInt8) :
    cmpPack a b c 0 = ((a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16)) ||| (c.toUInt32 <<< 8) := by
  unfold cmpPack
  have hz : (0 : UInt8).toUInt32 = 0 := rfl
  rw [hz,UInt32.or_zero,UInt32.or_assoc]

theorem cmpPackFour (a b c d : UInt8) :
    cmpPack a b c d = (((a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16)) |||
      (c.toUInt32 <<< 8)) ||| d.toUInt32 := by
  unfold cmpPack
  rw [UInt32.or_assoc,UInt32.or_assoc]

theorem cmpIterAscii (s : JString) (pre rest : List UInt8) (a : UInt8)
    (h : s.bytes = pre ++ a::rest) (ha : a.toNat < 128) :
    stringIterate s (cmpIndex pre.length) =
      some (cmpPack a 0 0 0, cmpIndex (pre.length+1)) := by
  have hs := s.small
  have hlen := congrArg List.length h
  simp only [List.length_append,List.length_cons] at hlen
  have hr : stringByteAt s (cmpIndex pre.length) = a := by
    have hh := cmpReadPrefix s pre (a::rest) h 0 (by omega)
    simpa only [Nat.add_zero,List.getD,List.getElem?_cons_zero,Option.getD_some] using hh
  rw [cmpIterateInBounds s _ (by omega),hr]
  have hb : stringBetweenByte a 0x80 0xf7 = false := by
    simp only [stringBetweenByte,between,UInt8.le_iff_toNat_le]
    have hl : ¬(0x80 : UInt8).toNat ≤ a.toNat := by change ¬128≤a.toNat; omega
    simp only [hl,decide_false,Bool.false_and]
  rw [hb]
  simp only [Bool.not_false,ite_true]
  rw [cmpPackOne,cmpIndexNext _ (by omega)]


theorem cmpPackThreshold (a b c d : UInt8) (k : Nat) (hk : k < 256) :
    (cmpPack a b c d < UInt32.ofNat (k * 16777216) ↔ a.toNat < k) := by
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  rw [UInt32.lt_iff_toNat_lt, cmpPackNat, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem cmpPackC0 (a b c d : UInt8) :
    (cmpPack a b c d < 0xc0000000 ↔ a.toNat < 192) :=
  cmpPackThreshold a b c d 192 (by decide)

theorem cmpPackE0 (a b c d : UInt8) :
    (cmpPack a b c d < 0xe0000000 ↔ a.toNat < 224) :=
  cmpPackThreshold a b c d 224 (by decide)

theorem cmpPackF0 (a b c d : UInt8) :
    (cmpPack a b c d < 0xf0000000 ↔ a.toNat < 240) :=
  cmpPackThreshold a b c d 240 (by decide)

theorem cmpLeadBetween (a : UInt8) (ha : 192 ≤ a.toNat ∧ a.toNat < 248) :
    stringBetweenByte a 0x80 0xf7 = true := by
  simp only [stringBetweenByte, between, Bool.and_eq_true, decide_eq_true_eq,
    UInt8.le_iff_toNat_le]
  change 128 ≤ a.toNat ∧ a.toNat ≤ 247
  omega

theorem cmpIterTwo (s : JString) (pre rest : List UInt8) (a b : UInt8)
    (h : s.bytes = pre ++ a::b::rest) (ha : 192 ≤ a.toNat ∧ a.toNat < 224)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192) :
    stringIterate s (cmpIndex pre.length) =
      some (cmpPack a b 0 0, cmpIndex (pre.length+2)) := by
  have hs := s.small
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_cons] at hlen
  have hread (k : Nat) (hk : k ≤ 2) :
      stringByteAt s (cmpIndex (pre.length+k)) = (a::b::rest).getD k 0 :=
    cmpReadPrefix s pre (a::b::rest) h k (by omega)
  have r0 := hread 0 (by omega)
  have r1 := hread 1 (by omega)
  simp only [Nat.add_zero, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at r0 r1
  have nx1 := cmpIndexNext pre.length (by omega)
  have nx2 := cmpIndexNext (pre.length+1) (by omega)
  rw [show pre.length+1+1=pre.length+2 by omega] at nx2
  have hn1 : ¬(cmpIndex (pre.length+1)).val > (stringNcodeunits s).val := by
    rw [cmpIndexVal _ (by omega), cmpStorageLength]
    omega
  have hc0 : ¬ (a.toUInt32 <<< 24 < 0xc0000000) := by
    rw [←cmpPackOne, cmpPackC0]
    omega
  have hc1 : (a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) < 0xe0000000 := by
    rw [←cmpPackTwo, cmpPackE0]
    exact ha.2
  rw [cmpIterateInBounds s _ (by omega), r0, cmpLeadBetween a (by omega)]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  simp only [iterateContinued, Id.run, pure, hc0, ite_false, nx1, hn1, r1,
    cmpContinuation b hb, Bool.false_eq_true, nx2, hc1, decide_true,
    Bool.or_true, ite_true]
  rw [cmpPackTwo]

theorem cmpIterThree (s : JString) (pre rest : List UInt8) (a b c : UInt8)
    (h : s.bytes = pre ++ a::b::c::rest) (ha : 224 ≤ a.toNat ∧ a.toNat < 240)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192) (hc : 128 ≤ c.toNat ∧ c.toNat < 192) :
    stringIterate s (cmpIndex pre.length) =
      some (cmpPack a b c 0, cmpIndex (pre.length+3)) := by
  have hs := s.small
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_cons] at hlen
  have hread (k : Nat) (hk : k ≤ 3) :
      stringByteAt s (cmpIndex (pre.length+k)) = (a::b::c::rest).getD k 0 :=
    cmpReadPrefix s pre (a::b::c::rest) h k (by omega)
  have r0 := hread 0 (by omega)
  have r1 := hread 1 (by omega)
  have r2 := hread 2 (by omega)
  simp only [Nat.add_zero, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at r0 r1 r2
  have nx1 := cmpIndexNext pre.length (by omega)
  have nx2 := cmpIndexNext (pre.length+1) (by omega)
  have nx3 := cmpIndexNext (pre.length+2) (by omega)
  rw [show pre.length+1+1=pre.length+2 by omega] at nx2
  rw [show pre.length+2+1=pre.length+3 by omega] at nx3
  have hn1 : ¬(cmpIndex (pre.length+1)).val > (stringNcodeunits s).val := by
    rw [cmpIndexVal _ (by omega), cmpStorageLength]
    omega
  have hn2 : ¬(cmpIndex (pre.length+2)).val > (stringNcodeunits s).val := by
    rw [cmpIndexVal _ (by omega), cmpStorageLength]
    omega
  have hc0 : ¬ (a.toUInt32 <<< 24 < 0xc0000000) := by
    rw [←cmpPackOne, cmpPackC0]
    omega
  have hc1 : ¬ (a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) < 0xe0000000 := by
    rw [←cmpPackTwo, cmpPackE0]
    omega
  have hc2 : ((a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) ||| (c.toUInt32 <<< 8)) <
      0xf0000000 := by
    rw [←cmpPackThree, cmpPackF0]
    exact ha.2
  rw [cmpIterateInBounds s _ (by omega), r0, cmpLeadBetween a (by omega)]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  simp only [iterateContinued, Id.run, pure, hc0, ite_false, nx1, hn1, r1,
    cmpContinuation b hb, Bool.false_eq_true, nx2, hc1, decide_false,
    Bool.or_false, nx3, hn2, r2, cmpContinuation c hc, hc2, decide_true,
    Bool.or_true, ite_true]
  rw [cmpPackThree]

theorem cmpIterFour (s : JString) (pre rest : List UInt8) (a b c d : UInt8)
    (h : s.bytes = pre ++ a::b::c::d::rest) (ha : 240 ≤ a.toNat ∧ a.toNat < 248)
    (hb : 128 ≤ b.toNat ∧ b.toNat < 192) (hc : 128 ≤ c.toNat ∧ c.toNat < 192)
    (hd : 128 ≤ d.toNat ∧ d.toNat < 192) :
    stringIterate s (cmpIndex pre.length) =
      some (cmpPack a b c d, cmpIndex (pre.length+4)) := by
  have hs := s.small
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_cons] at hlen
  have hread (k : Nat) (hk : k ≤ 4) :
      stringByteAt s (cmpIndex (pre.length+k)) = (a::b::c::d::rest).getD k 0 :=
    cmpReadPrefix s pre (a::b::c::d::rest) h k (by omega)
  have r0 := hread 0 (by omega)
  have r1 := hread 1 (by omega)
  have r2 := hread 2 (by omega)
  have r3 := hread 3 (by omega)
  simp only [Nat.add_zero, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some] at r0 r1 r2 r3
  have nx1 := cmpIndexNext pre.length (by omega)
  have nx2 := cmpIndexNext (pre.length+1) (by omega)
  have nx3 := cmpIndexNext (pre.length+2) (by omega)
  have nx4 := cmpIndexNext (pre.length+3) (by omega)
  rw [show pre.length+1+1=pre.length+2 by omega] at nx2
  rw [show pre.length+2+1=pre.length+3 by omega] at nx3
  rw [show pre.length+3+1=pre.length+4 by omega] at nx4
  have hn1 : ¬(cmpIndex (pre.length+1)).val > (stringNcodeunits s).val := by
    rw [cmpIndexVal _ (by omega), cmpStorageLength]
    omega
  have hn2 : ¬(cmpIndex (pre.length+2)).val > (stringNcodeunits s).val := by
    rw [cmpIndexVal _ (by omega), cmpStorageLength]
    omega
  have hn3 : ¬(cmpIndex (pre.length+3)).val > (stringNcodeunits s).val := by
    rw [cmpIndexVal _ (by omega), cmpStorageLength]
    omega
  have hc0 : ¬ (a.toUInt32 <<< 24 < 0xc0000000) := by
    rw [←cmpPackOne, cmpPackC0]
    omega
  have hc1 : ¬ (a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) < 0xe0000000 := by
    rw [←cmpPackTwo, cmpPackE0]
    omega
  have hc2 : ¬ ((a.toUInt32 <<< 24 ||| (b.toUInt32 <<< 16)) ||| (c.toUInt32 <<< 8)) <
      0xf0000000 := by
    rw [←cmpPackThree, cmpPackF0]
    omega
  rw [cmpIterateInBounds s _ (by omega), r0, cmpLeadBetween a (by omega)]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  simp only [iterateContinued, Id.run, pure, hc0, ite_false, nx1, hn1, r1,
    cmpContinuation b hb, Bool.false_eq_true, nx2, hc1, decide_false,
    Bool.or_false, nx3, hn2, r2, cmpContinuation c hc, hc2, nx4, hn3,
    r3, cmpContinuation d hd]
  rw [cmpPackFour]

theorem cmpIterEnd (s : JString) : stringIterate s (cmpIndex s.bytes.length) = none := by
  have hs := s.small
  have hu : (JInt.rem .u64 (cmpIndex s.bytes.length)).val = (cmpIndex s.bytes.length).val := by
    change wrapInt .u64 (cmpIndex s.bytes.length).val = _
    rw [cmpIndexVal _ (by omega)]
    exact wrapInt_of_inRange .u64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)
  have hc : (JInt.rem .u64 (cmpIndex s.bytes.length) - JInt.lit .u64 1).val =
      (s.bytes.length : Int) := by
    change wrapInt .u64 ((JInt.rem .u64 (cmpIndex s.bytes.length)).val -
      (JInt.lit .u64 1).val) = _
    rw [hu, cmpIndexVal _ (by omega), show (JInt.lit .u64 1).val = 1 by decide]
    rw [wrapInt_of_inRange .u64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)]
    omega
  unfold stringIterate iterateString
  rw [hc, cmpStorageLength]
  simp only [Int.lt_irrefl, decide_false, Bool.not_false, ite_true]


theorem cmpIterGlyph (s : JString) (pre rest : List UInt8) (g : CmpGlyph)
    (h : s.bytes = pre ++ g.bytes ++ rest) :
    stringIterate s (cmpIndex pre.length) =
      some (g.bits, cmpIndex (pre.length+g.bytes.length)) := by
  cases g with
  | ascii a ha =>
    simp only [CmpGlyph.bytes, List.append_assoc, List.cons_append, List.nil_append] at h
    exact cmpIterAscii s pre rest a h ha
  | two a b ha hb =>
    simp only [CmpGlyph.bytes, List.append_assoc, List.cons_append, List.nil_append] at h
    exact cmpIterTwo s pre rest a b h ha hb
  | three a b c ha hb hc =>
    simp only [CmpGlyph.bytes, List.append_assoc, List.cons_append, List.nil_append] at h
    exact cmpIterThree s pre rest a b c h ha hb hc
  | four a b c d ha hb hc hd =>
    simp only [CmpGlyph.bytes, List.append_assoc, List.cons_append, List.nil_append] at h
    exact cmpIterFour s pre rest a b c d h ha hb hc hd

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## CmpGeneric -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean
open JuliaLean.base.strings.basic

/-- A complete character run through the installed AbstractString iteration interface. -/
inductive CmpRun {C E : Type} (next : JuliaLean.base.strings.basic.Index → Except E (Option (C × JuliaLean.base.strings.basic.Index))) :
    Option (C × JuliaLean.base.strings.basic.Index) → List C → Prop where
  | done : CmpRun next none []
  | step {c : C} {i : JuliaLean.base.strings.basic.Index} {value : Option (C × JuliaLean.base.strings.basic.Index)} {rest : List C}
      (hnext : next i = .ok value) (tail : CmpRun next value rest) :
      CmpRun next (some (c,i)) (c::rest)

theorem cmpLoopRun {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (a b : S) {iv1 : Option (C × JuliaLean.base.strings.basic.Index)} {xs : List C}
    (hx : CmpRun (ops.iterateAt a) iv1 xs)
    {iv2 : Option (C × JuliaLean.base.strings.basic.Index)} {ys : List C} (fuel : Nat)
    (hy : CmpRun (ops.iterateAt b) iv2 ys) (hbound : xs.length+ys.length<fuel) :
    cmpLoop ops a b fuel iv1 iv2 = .ok (lexCompare ops.equalChar ops.lessChar xs ys) := by
  induction hx generalizing iv2 ys fuel with
  | done =>
    cases fuel with
    | zero => omega
    | succ fuel => cases hy <;> rfl
  | @step c i next xs hnext htail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases hy with
      | done => rfl
      | @step d j nextB ys hnextB htailB =>
        by_cases heq : ops.equalChar c d = true
        · have hf : xs.length+ys.length<fuel := by
            simp only [List.length_cons] at hbound
            omega
          have hr := ih fuel htailB hf
          simpa only [cmpLoop,heq,Bool.not_true,Bool.false_eq_true,ite_false,
            hnext,hnextB,bind,Except.bind,pure,Except.pure,lexCompare,ite_true] using hr
        · have hne : ops.equalChar c d = false := Bool.eq_false_iff.mpr heq
          cases hl : ops.lessChar c d <;>
            simp only [cmpLoop,hne,Bool.not_false,ite_true,
              JuliaLean.base.operators.ifelseValue,hl,Bool.false_eq_true,ite_false,
              lexCompare,pure,Except.pure]

theorem cmpGenericRun {S R C CU CT E : Type} (ops : StringOps S R C CU CT E)
    (a b : S) (xs ys : List C) (iv1 iv2 : Option (C × JuliaLean.base.strings.basic.Index))
    (hsame : ops.sameReference a b = false)
    (hfirstA : ops.iterateFirst a = .ok iv1) (hfirstB : ops.iterateFirst b = .ok iv2)
    (ha : CmpRun (ops.iterateAt a) iv1 xs) (hb : CmpRun (ops.iterateAt b) iv2 ys)
    (hba : xs.length ≤ ops.iterationBound a) (hbb : ys.length ≤ ops.iterationBound b) :
    JuliaLean.base.strings.basic.cmpString ops a b = .ok (lexCompare ops.equalChar ops.lessChar xs ys) := by
  have hr := cmpLoopRun ops a b ha
    (ops.iterationBound a+ops.iterationBound b+1) hb (by omega)
  simpa only [JuliaLean.base.strings.basic.cmpString,cmp,hsame,Bool.false_eq_true,ite_false,hfirstA,hfirstB,
    bind,Except.bind,pure,Except.pure] using hr

theorem cmpLexCharsValue (xs ys : List UInt32) :
    (lexCompare JuliaLean.base.char.eq_Char JuliaLean.base.char.isless_Char xs ys).val =
      cmpLexChars xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      by_cases heq : x=y
      · subst y
        simpa only [lexCompare,JuliaLean.base.char.eq_Char,beq_self_eq_true,ite_true,
          cmpLexChars,UInt32.lt_iff_toNat_lt,Nat.lt_irrefl,ite_false] using ih ys
      · have hn : (x == y) = false := beq_eq_false_iff_ne.mpr heq
        have hv : x.toNat ≠ y.toNat := fun h => heq (UInt32.toNat_inj.mp h)
        rcases Nat.lt_or_gt_of_ne hv with hlt | hgt
        · have hl : x<y := UInt32.lt_iff_toNat_lt.mpr hlt
          simp only [lexCompare,JuliaLean.base.char.eq_Char,hn,Bool.false_eq_true,ite_false,
            JuliaLean.base.char.isless_Char,hl,decide_true,ite_true,cmpLexChars]
          rfl
        · have hnlt : ¬x<y := by rw [UInt32.lt_iff_toNat_lt]; omega
          have hrev : y<x := UInt32.lt_iff_toNat_lt.mpr hgt
          simp only [lexCompare,JuliaLean.base.char.eq_Char,hn,Bool.false_eq_true,ite_false,
            JuliaLean.base.char.isless_Char,hnlt,decide_false,cmpLexChars,hrev,ite_true]
          rfl

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## CmpMemory -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean
open JuliaLean.base.cmem.StandardC

/-- The memory loop has the same value as a lexical comparison of its finite byte windows. -/
theorem cmpMemoryLex (heap : JuliaLean.base.pointer.ByteHeap) (a b : List UInt8)
    (left right : Nat) (hlen : a.length = b.length)
    (ha : ∀ k, k < a.length →
      (heap.readByte (left+k)).val = ((a.getD k 0).toNat : Int))
    (hb : ∀ k, k < b.length →
      (heap.readByte (right+k)).val = ((b.getD k 0).toNat : Int)) :
    (cMemcmp heap left right a.length).val = cmpLexBytes a b := by
  induction a generalizing b left right with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => simp only [List.length_nil,List.length_cons] at hlen; omega
  | cons x xs ih =>
    cases b with
    | nil => simp only [List.length_nil,List.length_cons] at hlen; omega
    | cons y ys =>
      have hx : (heap.readByte left).val = (x.toNat : Int) := by
        have h := ha 0 (by simp only [List.length_cons]; omega)
        simpa only [Nat.add_zero,List.getD,List.getElem?_cons_zero,Option.getD_some] using h
      have hy : (heap.readByte right).val = (y.toNat : Int) := by
        have h := hb 0 (by simp only [List.length_cons]; omega)
        simpa only [Nat.add_zero,List.getD,List.getElem?_cons_zero,Option.getD_some] using h
      by_cases heq : x = y
      · have hm : heap.readByte left = heap.readByte right := by
          apply Subtype.ext
          rw [hx,hy,heq]
        have hxs : ∀ k, k < xs.length →
            (heap.readByte (left+1+k)).val = ((xs.getD k 0).toNat : Int) := by
          intro k hk
          have h := ha (k+1) (by simp only [List.length_cons]; omega)
          simpa only [Nat.add_assoc,List.getD,List.getElem?_cons_succ,Nat.add_comm 1 k] using h
        have hys : ∀ k, k < ys.length →
            (heap.readByte (right+1+k)).val = ((ys.getD k 0).toNat : Int) := by
          intro k hk
          have h := hb (k+1) (by simp only [List.length_cons]; omega)
          simpa only [Nat.add_assoc,List.getD,List.getElem?_cons_succ,Nat.add_comm 1 k] using h
        have hr := ih ys (left+1) (right+1)
          (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen) hxs hys
        simp only [List.length_cons,cMemcmp,hm,ite_true]
        rw [hr]
        subst y
        simp only [cmpLexBytes,UInt8.lt_iff_toNat_lt,Nat.lt_irrefl,ite_false]
      · have hm : heap.readByte left ≠ heap.readByte right := by
          intro h
          have hv := congrArg Subtype.val h
          rw [hx,hy] at hv
          exact heq (UInt8.toNat_inj.mp (by exact_mod_cast hv))
        have hxy : x.toNat ≠ y.toNat := fun h => heq (UInt8.toNat_inj.mp h)
        rcases Nat.lt_or_gt_of_ne hxy with hlt | hgt
        · have hl : (heap.readByte left).val < (heap.readByte right).val := by
            rw [hx,hy]; exact_mod_cast hlt
          simp only [List.length_cons,cMemcmp,hm,ite_false,hl,ite_true,i32Lit,
            cmpLexBytes,UInt8.lt_iff_toNat_lt,hlt]
        · have hl : ¬ (heap.readByte left).val < (heap.readByte right).val := by
            rw [hx,hy]; omega
          have hn : ¬ x.toNat < y.toNat := by omega
          simp only [List.length_cons,cMemcmp,hm,ite_false,hl,i32Lit,
            cmpLexBytes,UInt8.lt_iff_toNat_lt,hn,hgt,ite_true]


def cmpLengthOrder (a b : Nat) : Int :=
  if a < b then -1 else if b < a then 1 else 0

def cmpMemoryResult (c : Int) (a b : Nat) : Int :=
  if c < 0 then -1 else if c > 0 then 1 else cmpLengthOrder a b

/-- Truncating the byte scan at the shorter length and then comparing lengths gives lexical order. -/
theorem cmpMemoryStringLex (heap : JuliaLean.base.pointer.ByteHeap) (a b : List UInt8)
    (left right : Nat)
    (ha : ∀ k, k < a.length →
      (heap.readByte (left+k)).val = ((a.getD k 0).toNat : Int))
    (hb : ∀ k, k < b.length →
      (heap.readByte (right+k)).val = ((b.getD k 0).toNat : Int)) :
    cmpMemoryResult (cMemcmp heap left right (min a.length b.length)).val a.length b.length =
      cmpLexBytes a b := by
  induction a generalizing b left right with
  | nil =>
      cases b with
      | nil => rfl
      | cons y ys =>
          simp only [List.length_nil, Nat.zero_min, cMemcmp, i32Lit, cmpMemoryResult,
            cmpLengthOrder, List.length_cons, cmpLexBytes]
          omega
  | cons x xs ih =>
    cases b with
    | nil =>
        simp only [List.length_nil, Nat.min_zero, cMemcmp, i32Lit, cmpMemoryResult,
          cmpLengthOrder, List.length_cons, cmpLexBytes]
        omega
    | cons y ys =>
      have hx : (heap.readByte left).val = (x.toNat : Int) := by
        have h := ha 0 (by simp only [List.length_cons]; omega)
        simpa only [Nat.add_zero, List.getD_cons_zero] using h
      have hy : (heap.readByte right).val = (y.toNat : Int) := by
        have h := hb 0 (by simp only [List.length_cons]; omega)
        simpa only [Nat.add_zero, List.getD_cons_zero] using h
      have hmin : min (x::xs).length (y::ys).length = min xs.length ys.length+1 := by
        simp only [List.length_cons]
        omega
      rw [hmin]
      by_cases heq : x = y
      · have hm : heap.readByte left = heap.readByte right := by
          apply Subtype.ext
          rw [hx, hy, heq]
        have hxs : ∀ k, k < xs.length →
            (heap.readByte (left+1+k)).val = ((xs.getD k 0).toNat : Int) := by
          intro k hk
          have h := ha (k+1) (by simp only [List.length_cons]; omega)
          simpa only [Nat.add_assoc, List.getD_cons_succ, Nat.add_comm 1 k] using h
        have hys : ∀ k, k < ys.length →
            (heap.readByte (right+1+k)).val = ((ys.getD k 0).toNat : Int) := by
          intro k hk
          have h := hb (k+1) (by simp only [List.length_cons]; omega)
          simpa only [Nat.add_assoc, List.getD_cons_succ, Nat.add_comm 1 k] using h
        have hr := ih ys (left+1) (right+1) hxs hys
        have horder : cmpLengthOrder (xs.length+1) (ys.length+1) =
            cmpLengthOrder xs.length ys.length := by
          simp only [cmpLengthOrder, Nat.add_lt_add_iff_right]
        rw [cMemcmp, ite_eq_left hm]
        simp only [List.length_cons, cmpMemoryResult, horder]
        change cmpMemoryResult (cMemcmp heap (left+1) (right+1) (min xs.length ys.length)).val
          xs.length ys.length = _
        rw [hr]
        subst y
        simp only [cmpLexBytes, UInt8.lt_iff_toNat_lt, Nat.lt_irrefl, ite_false]
      · have hm : heap.readByte left ≠ heap.readByte right := by
          intro h
          have hv := congrArg Subtype.val h
          rw [hx, hy] at hv
          exact heq (UInt8.toNat_inj.mp (by omega))
        have hxy : x.toNat ≠ y.toNat := fun h => heq (UInt8.toNat_inj.mp h)
        rcases Nat.lt_or_gt_of_ne hxy with hlt | hgt
        · have hl : (heap.readByte left).val < (heap.readByte right).val := by
            rw [hx, hy]
            omega
          simp only [cMemcmp, hm, ite_false, hl, ite_true, i32Lit, cmpMemoryResult,
            cmpLexBytes, UInt8.lt_iff_toNat_lt, hlt]
          rfl
        · have hl : ¬ (heap.readByte left).val < (heap.readByte right).val := by
            rw [hx, hy]
            omega
          have hn : ¬ x.toNat < y.toNat := by omega
          simp only [cMemcmp, hm, ite_false, hl, i32Lit, cmpMemoryResult,
            cmpLexBytes, UInt8.lt_iff_toNat_lt, hn, hgt, ite_true]
          rfl

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## CmpMemoryBridge -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean
open JuliaLean.base.strings.string
open JuliaLean.Proofs.base.strings.util.Round6

 theorem cmpMemoryByteValue (b : UInt8) :
    (JInt.lit .u8 (b.toNat : Int)).val = b.toNat := by
  change wrapInt .u8 (b.toNat : Int) = b.toNat
  exact wrapInt_of_inRange .u8 _ (by
    have hb := b.toNat_lt
    simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

 theorem cmpPairReadLeft (a b : Raw) (k : Nat) (hk : k < a.bytes.length) :
    ((pairHeap a.bytes b.bytes).readByte (0+k)).val = ((a.bytes.getD k 0).toNat : Int) := by
  rw [Nat.zero_add, pairHeap_left a.bytes b.bytes k hk (by have ha := a.small; have hb := b.small; omega)]
  exact cmpMemoryByteValue _

 theorem cmpPairReadRight (a b : Raw) (k : Nat) (hk : k < b.bytes.length) :
    ((pairHeap a.bytes b.bytes).readByte (a.bytes.length+1+k)).val =
      ((b.bytes.getD k 0).toNat : Int) := by
  rw [pairHeap_right a.bytes b.bytes k hk (by have ha := a.small; have hb := b.small; omega)]
  exact cmpMemoryByteValue _

 theorem cmpBytesModel (a b : Raw) (n : Index) (hn : n.val = (min a.bytes.length b.bytes.length : Nat)) :
    compareBytes a.bytes b.bytes n =
      (JuliaLean.base.cmem.StandardC.cMemcmp (pairHeap a.bytes b.bytes) 0
        (a.bytes.length+1) (min a.bytes.length b.bytes.length)).val := by
  have hrem : (JInt.rem .u64 n).val.toNat = min a.bytes.length b.bytes.length := by
    change (wrapInt .u64 n.val).toNat = _
    rw [hn]
    have ha := a.small
    rw [wrapInt_of_inRange .u64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)]
    rfl
  simp only [compareBytes, memcmpLength, hrem]
  congr 2

 theorem cmpIfelseDecide {A : Type} (p : Prop) [Decidable p] (x y : A) :
    JuliaLean.base.operators.ifelseValue (decide p) x y = if p then x else y := by
  by_cases h : p
  · simp only [h, decide_true, ite_true, JuliaLean.base.operators.ifelseValue]
  · simp only [h, decide_false, ite_false, JuliaLean.base.operators.ifelseValue]

 theorem cmpIndexInteger (a b : Index) :
    JuliaLean.Proofs.base.strings.string.Round1.compareStringIndex a b =
      if a.val < b.val then -1 else if b.val < a.val then 1 else 0 := by
  unfold JuliaLean.Proofs.base.strings.string.Round1.compareStringIndex
    JuliaLean.base.operators.cmpInteger
  rw [JuliaLean.Proofs.base.int.lt_eq, JuliaLean.Proofs.base.int.lt_eq]
  rw [cmpIfelseDecide, cmpIfelseDecide]

 theorem cmpIndexLength (a b : Raw) :
    JuliaLean.Proofs.base.strings.string.Round1.compareStringIndex
      (stringCoreSizeof a) (stringCoreSizeof b) = cmpLengthOrder a.bytes.length b.bytes.length := by
  have ha : (stringCoreSizeof a).val = a.bytes.length := stringNcodeunits_val a
  have hb : (stringCoreSizeof b).val = b.bytes.length := stringNcodeunits_val b
  rw [cmpIndexInteger, ha, hb]
  simp only [Int.ofNat_lt, cmpLengthOrder]

 theorem cmpStringFormula (sizeof : JString → Index)
    (mem : JString → JString → Index → Int) (compareLength : Index → Index → Int)
    (a b : JString) :
    JuliaLean.base.strings.string.cmpString sizeof mem compareLength a b =
      (let n := if (sizeof a).val ≤ (sizeof b).val then sizeof a else sizeof b
       let c := mem a b n
       if c < 0 then -1 else if c > 0 then 1 else compareLength (sizeof a) (sizeof b)) := by
  rfl

theorem cmpStringMemoryAt (size : JString → Index)
    (mem : JString → JString → Index → Int) (cmpLength : Index → Index → Int)
    (a b : JString) (n : Index) (value : Int) (alen blen : Nat)
    (hn : n = if (size a).val ≤ (size b).val then size a else size b)
    (hmem : mem a b n = value)
    (hlen : cmpLength (size a) (size b) = cmpLengthOrder alen blen) :
    JuliaLean.base.strings.string.cmpString size mem cmpLength a b =
      cmpMemoryResult value alen blen := by
  rw [cmpStringFormula]
  change (if mem a b (if (size a).val ≤ (size b).val then size a else size b) < 0 then -1
    else if mem a b (if (size a).val ≤ (size b).val then size a else size b) > 0 then 1
    else cmpLength (size a) (size b)) = _
  rw [←hn, hmem, hlen]
  rfl

theorem cmpStringValuesDef (a b : Raw) :
    JuliaLean.Proofs.base.strings.string.Round1.compareStringValues a b =
      JuliaLean.base.strings.string.cmpString stringCoreSizeof
        (fun x y count => compareBytes x.bytes y.bytes count)
        JuliaLean.Proofs.base.strings.string.Round1.compareStringIndex a b := by
  rfl

theorem cmpStringValuesResultAt (a b : Raw) (n : Index) (value : Int)
    (hn : n = if (stringCoreSizeof a).val ≤ (stringCoreSizeof b).val then
      stringCoreSizeof a else stringCoreSizeof b)
    (hm : compareBytes a.bytes b.bytes n = value) :
    JuliaLean.Proofs.base.strings.string.Round1.compareStringValues a b =
      cmpMemoryResult value a.bytes.length b.bytes.length := by
  exact (cmpStringValuesDef a b).trans
    (cmpStringMemoryAt stringCoreSizeof (fun x y k => compareBytes x.bytes y.bytes k)
      JuliaLean.Proofs.base.strings.string.Round1.compareStringIndex a b n value
      a.bytes.length b.bytes.length hn hm (cmpIndexLength a b))

theorem cmpStringValuesBytesAt (a b : Raw) (n : Index)
    (hn : n = if (stringCoreSizeof a).val ≤ (stringCoreSizeof b).val then
      stringCoreSizeof a else stringCoreSizeof b) :
    JuliaLean.Proofs.base.strings.string.Round1.compareStringValues a b =
      cmpMemoryResult (compareBytes a.bytes b.bytes n) a.bytes.length b.bytes.length :=
  cmpStringValuesResultAt a b n _ hn rfl

theorem cmpStringValuesLexAt (a b : Raw) (n : Index)
    (hselect : n = if (stringCoreSizeof a).val ≤ (stringCoreSizeof b).val then
      stringCoreSizeof a else stringCoreSizeof b)
    (hn : n.val = (min a.bytes.length b.bytes.length : Nat)) :
    JuliaLean.Proofs.base.strings.string.Round1.compareStringValues a b =
      cmpLexBytes a.bytes b.bytes := by
  exact (cmpStringValuesBytesAt a b n hselect).trans
    ((congrArg (fun value => cmpMemoryResult value a.bytes.length b.bytes.length)
      (cmpBytesModel a b n hn)).trans
      (cmpMemoryStringLex (pairHeap a.bytes b.bytes) a.bytes b.bytes 0 (a.bytes.length+1)
        (cmpPairReadLeft a b) (cmpPairReadRight a b)))

theorem cmpSelectedIndexValue (x y : Index) (na nb : Nat)
    (ha : x.val = na) (hb : y.val = nb) :
    (if x.val ≤ y.val then x else y).val = (min na nb : Nat) := by
  by_cases h : x.val ≤ y.val
  · rw [ite_eq_left h, ha, Nat.min_eq_left (by omega)]
  · rw [ite_eq_right h, hb, Nat.min_eq_right (by omega)]

theorem cmpCompareStringValuesLex (a b : Raw) :
    JuliaLean.Proofs.base.strings.string.Round1.compareStringValues a b =
      cmpLexBytes a.bytes b.bytes := by
  exact cmpStringValuesLexAt a b
    (if (stringCoreSizeof a).val ≤ (stringCoreSizeof b).val then
      stringCoreSizeof a else stringCoreSizeof b) rfl
    (cmpSelectedIndexValue (stringCoreSizeof a) (stringCoreSizeof b)
      a.bytes.length b.bytes.length (stringNcodeunits_val a) (stringNcodeunits_val b))

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## Utf8Dfa -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean.base.strings.string

 theorem cmpDfaStepRow (state : UInt32) (b : UInt8) :
    utfDfaStep state b = (utf8DfaClassRow (utf8DfaClass b) >>> state) &&& 0x0000001e := by
  have hb : b.toNat < 256 := UInt8.toNat_lt b
  unfold utfDfaStep utf8DfaTable
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa only [List.length_range] using hb)]
  simp only [List.getElem_range, Option.map_some, Option.getD_some, UInt8.ofNat_toNat]

 theorem cmpDfaAsciiStep (b : UInt8) (hb : b.toNat < 128) :
    utfDfaStep utf8DfaAccept b = utf8DfaAccept := by
  rw [cmpDfaStepRow]
  simp only [utf8DfaClass, hb, ite_eq_left]
  rfl

 theorem cmpDfaClassLt (b : UInt8) : utf8DfaClass b < 12 := by
  dsimp only [utf8DfaClass]
  repeat first | apply iteInduction (motive := (· < 12)) <;> intros | decide

 theorem cmpDfaInvalidStep (b : UInt8) :
    utfDfaStep utf8DfaInvalid b = utf8DfaInvalid := by
  rw [cmpDfaStepRow]
  have h := cmpDfaClassLt b
  generalize utf8DfaClass b = k at *
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def cmpDfaClassRange (b : UInt8) (k : Nat) : Prop :=
  match k with
  | 0 => b.toNat < 128
  | 1 | 7 | 9 => 128 ≤ b.toNat ∧ b.toNat < 192
  | 2 => 192 ≤ b.toNat ∧ b.toNat < 224
  | 3 | 4 | 10 => 224 ≤ b.toNat ∧ b.toNat < 240
  | 5 | 6 | 11 => 240 ≤ b.toNat ∧ b.toNat < 248
  | _ => True

theorem cmpDfaClassRangeOk (b : UInt8) : cmpDfaClassRange b (utf8DfaClass b) := by
  dsimp only [utf8DfaClass]
  repeat first
    | apply iteInduction (motive := cmpDfaClassRange b) <;> intros
    | (simp only [cmpDfaClassRange, beq_iff_eq] at * <;> omega)

inductive CmpDfaPending : UInt32 → Nat → Prop where
  | complete : CmpDfaPending utf8DfaAccept 0
  | one : CmpDfaPending 14 1
  | two18 : CmpDfaPending 18 2
  | two24 : CmpDfaPending 24 2
  | two8 : CmpDfaPending 8 2
  | three12 : CmpDfaPending 12 3
  | three20 : CmpDfaPending 20 3
  | three26 : CmpDfaPending 26 3

theorem cmpDfaRowPendingStep (k : Nat) (hk : k < 12)
    (state : UInt32) (n : Nat) (hp : CmpDfaPending state (n + 1))
    (hne : (utf8DfaClassRow k >>> state) &&& 0x0000001e ≠ utf8DfaInvalid) :
    (k = 1 ∨ k = 7 ∨ k = 9) ∧
      CmpDfaPending ((utf8DfaClassRow k >>> state) &&& 0x0000001e) n := by
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
  cases hp <;>
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact False.elim (hne rfl)
      | exact ⟨by decide, .complete⟩
      | exact ⟨by decide, .one⟩
      | exact ⟨by decide, .two18⟩

theorem cmpDfaPendingStep (b : UInt8) (state : UInt32) (n : Nat)
    (hp : CmpDfaPending state (n + 1))
    (hne : utfDfaStep state b ≠ utf8DfaInvalid) :
    (128 ≤ b.toNat ∧ b.toNat < 192) ∧ CmpDfaPending (utfDfaStep state b) n := by
  have hrow := cmpDfaRowPendingStep (utf8DfaClass b) (cmpDfaClassLt b) state n hp
    (by rw [← cmpDfaStepRow]; exact hne)
  refine ⟨?_, by rw [cmpDfaStepRow]; exact hrow.2⟩
  have hr := cmpDfaClassRangeOk b
  rcases hrow.1 with h | h | h <;> rw [h] at hr <;> exact hr

theorem cmpDfaFromAccept (b : UInt8)
    (hne : utfDfaStep utf8DfaAccept b ≠ utf8DfaInvalid) :
    (b.toNat < 128 ∧ utfDfaStep utf8DfaAccept b = utf8DfaAccept) ∨
    (192 ≤ b.toNat ∧ b.toNat < 224) ∧ CmpDfaPending (utfDfaStep utf8DfaAccept b) 1 ∨
    (224 ≤ b.toNat ∧ b.toNat < 240) ∧ CmpDfaPending (utfDfaStep utf8DfaAccept b) 2 ∨
    (240 ≤ b.toNat ∧ b.toNat < 248) ∧ CmpDfaPending (utfDfaStep utf8DfaAccept b) 3 := by
  have hk := cmpDfaClassLt b
  have hr := cmpDfaClassRangeOk b
  rw [cmpDfaStepRow] at hne ⊢
  generalize utf8DfaClass b = k at *
  have hcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl ⟨hr, rfl⟩
  · exact False.elim (hne rfl)
  · exact .inr (.inl ⟨hr, .one⟩)
  · exact .inr (.inr (.inl ⟨hr, .two18⟩))
  · exact .inr (.inr (.inl ⟨hr, .two8⟩))
  · exact .inr (.inr (.inr ⟨hr, .three26⟩))
  · exact .inr (.inr (.inr ⟨hr, .three12⟩))
  · exact False.elim (hne rfl)
  · exact False.elim (hne rfl)
  · exact False.elim (hne rfl)
  · exact .inr (.inr (.inl ⟨hr, .two24⟩))
  · exact .inr (.inr (.inr ⟨hr, .three20⟩))

theorem cmpDfaInvalidFold (bs : List UInt8) :
    bs.foldl utfDfaStep utf8DfaInvalid = utf8DfaInvalid := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rw [List.foldl_cons, cmpDfaInvalidStep, ih]

inductive CmpUtf8Remainder : Nat → List UInt8 → Prop where
  | complete {bs} (shape : CmpUtf8Shape bs) : CmpUtf8Remainder 0 bs
  | continuation {n b rest} (hb : 128 ≤ b.toNat ∧ b.toNat < 192)
      (tail : CmpUtf8Remainder n rest) : CmpUtf8Remainder (n + 1) (b :: rest)

theorem cmpShapeFromRemainderOne {b : UInt8} {rest : List UInt8}
    (hb : 192 ≤ b.toNat ∧ b.toNat < 224) (hrest : CmpUtf8Remainder 1 rest) :
    CmpUtf8Shape (b :: rest) := by
  cases hrest with
  | continuation hc ht =>
      cases ht with
      | complete hs => exact .two hb hc hs

theorem cmpShapeFromRemainderTwo {b : UInt8} {rest : List UInt8}
    (hb : 224 ≤ b.toNat ∧ b.toNat < 240) (hrest : CmpUtf8Remainder 2 rest) :
    CmpUtf8Shape (b :: rest) := by
  cases hrest with
  | continuation hc ht =>
      cases ht with
      | continuation hd hu =>
          cases hu with
          | complete hs => exact .three hb hc hd hs

theorem cmpShapeFromRemainderThree {b : UInt8} {rest : List UInt8}
    (hb : 240 ≤ b.toNat ∧ b.toNat < 248) (hrest : CmpUtf8Remainder 3 rest) :
    CmpUtf8Shape (b :: rest) := by
  cases hrest with
  | continuation hc ht =>
      cases ht with
      | continuation hd hu =>
          cases hu with
          | continuation he hv =>
              cases hv with
              | complete hs => exact .four hb hc hd he hs

theorem cmpDfaAcceptedRemainder (bs : List UInt8) :
    ∀ (state : UInt32) (n : Nat), CmpDfaPending state n →
      bs.foldl utfDfaStep state = utf8DfaAccept → CmpUtf8Remainder n bs := by
  induction bs with
  | nil =>
      intro state n hp hacc
      cases hp
      · exact .complete .empty
      all_goals have hn := congrArg UInt32.toNat hacc
      all_goals simp only [List.foldl_nil, utf8DfaAccept, UInt32.toNat_ofNat] at hn
      all_goals contradiction
  | cons b bs ih =>
      intro state n hp hacc
      have ht : bs.foldl utfDfaStep (utfDfaStep state b) = utf8DfaAccept := hacc
      have hne : utfDfaStep state b ≠ utf8DfaInvalid := by
        intro heq
        rw [heq, cmpDfaInvalidFold] at ht
        exact (by decide : utf8DfaInvalid ≠ utf8DfaAccept) ht
      cases n with
      | zero =>
          cases hp
          apply CmpUtf8Remainder.complete
          rcases cmpDfaFromAccept b hne with ⟨hb, hstep⟩ | ⟨hb, hn⟩ | ⟨hb, hn⟩ | ⟨hb, hn⟩
          · rw [hstep] at ht
            have hr := ih utf8DfaAccept 0 .complete ht
            cases hr with
            | complete hs => exact .ascii hb hs
          · exact cmpShapeFromRemainderOne hb (ih _ _ hn ht)
          · exact cmpShapeFromRemainderTwo hb (ih _ _ hn ht)
          · exact cmpShapeFromRemainderThree hb (ih _ _ hn ht)
      | succ n =>
          obtain ⟨hb, hn⟩ := cmpDfaPendingStep b state n hp hne
          exact .continuation hb (ih _ _ hn ht)

theorem cmpUtf8Shape_of_dfa (bs : List UInt8)
    (h : bs.foldl utfDfaStep utf8DfaAccept = utf8DfaAccept) : CmpUtf8Shape bs := by
  have hr := cmpDfaAcceptedRemainder bs utf8DfaAccept 0 .complete h
  cases hr with
  | complete hs => exact hs

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## DfaClassifier -/

namespace JuliaLean.ChatGPT.Batch2.Group5
open JuliaLean.base.strings.string

local macro "cmpOriginalDfaRun" : term =>
  pure (Lean.mkIdent (((Lean.Name.num `_private.JuliaLean.base.strings.string 0).append
    `JuliaLean.base.strings.string.utfDfaRunLoop)))
local macro "cmpOriginalFind" : term =>
  pure (Lean.mkIdent (((Lean.Name.num `_private.JuliaLean.base.strings.string 0).append
    `JuliaLean.base.strings.string.findNonasciiLoop)))
local macro "cmpOriginalSkip" : term =>
  pure (Lean.mkIdent (((Lean.Name.num `_private.JuliaLean.base.strings.string 0).append
    `JuliaLean.base.strings.string.skipAsciiChunks)))
local macro "cmpOriginalClassify" : term =>
  pure (Lean.mkIdent (((Lean.Name.num `_private.JuliaLean.base.strings.string 0).append
    `JuliaLean.base.strings.string.classifyNonasciiLoop)))

abbrev cmpDfaRun {V : Type} (getByte : V → Int → UInt8) (bytes : V)
    (last : Int) (fuel : Nat) (i : Int) (state : UInt32) :=
  cmpOriginalDfaRun getByte bytes last fuel i state

abbrev cmpFind {V : Type} (isAscii : V → Int → Int → Bool)
    (bytes : V) (last chunk : Int) (fuel : Nat) (i : Int) :=
  cmpOriginalFind isAscii bytes last chunk fuel i

abbrev cmpSkip {V : Type} (isAscii : V → Int → Int → Bool)
    (bytes : V) (chunk last : Int) (fuel : Nat) (first stop : Int) (state : UInt32) :=
  cmpOriginalSkip isAscii bytes chunk last fuel first stop state

abbrev cmpClassify {V : Type} (getByte : V → Int → UInt8)
    (firstindex lastindex : V → Int) (isAscii : V → Int → Int → Bool)
    (bytes : V) (chunk last : Int) (fuel : Nat) (first stop : Int) (state : UInt32) :=
  cmpOriginalClassify getByte firstindex lastindex isAscii bytes chunk last fuel first stop state

def cmpDfaRange (rd : Int → UInt8) : Int → Nat → UInt32 → UInt32
  | _, 0, st => st
  | first, n+1, st => cmpDfaRange rd (first+1) n (utfDfaStep st (rd first))

theorem cmpDfaRange_append (rd : Int → UInt8) (first : Int) (n m : Nat) (st : UInt32) :
    cmpDfaRange rd first (n+m) st =
      cmpDfaRange rd (first + n) m (cmpDfaRange rd first n st) := by
  induction n generalizing first st with
  | zero => simp only [Nat.zero_add, Int.natCast_zero, Int.add_zero, cmpDfaRange]
  | succ n ih =>
      rw [Nat.succ_add]
      simp only [cmpDfaRange]
      rw [ih]
      congr 1
      omega

theorem cmpDfaRun_eq {V : Type} (getByte : V → Int → UInt8) (bs : V)
    (last first : Int) (fuel : Nat) (st : UInt32)
    (hf : (last-first+1).toNat ≤ fuel) :
    cmpDfaRun getByte bs last fuel first st =
      cmpDfaRange (getByte bs) first (last-first+1).toNat st := by
  induction fuel generalizing first st with
  | zero =>
      have h : (last-first+1).toNat = 0 := by omega
      rw [h]
      rfl
  | succ fuel ih =>
      change (if first ≤ last then
        cmpDfaRun getByte bs last fuel (first+1) (utfDfaStep st (getByte bs first))
        else st) = _
      by_cases hi : first ≤ last
      · rw [ite_eq_left hi, ih (first+1) (utfDfaStep st (getByte bs first)) (by omega)]
        have he : (last-first+1).toNat = (last-(first+1)+1).toNat + 1 := by omega
        rw [he]
        rfl
      · rw [ite_eq_right hi]
        have hz : (last-first+1).toNat = 0 := by omega
        rw [hz]
        rfl


def cmpDfaWindow (rd : Int → UInt8) (first last : Int) (st : UInt32) : UInt32 :=
  cmpDfaRange rd first (last-first+1).toNat st

theorem cmpDfaWindow_empty (rd : Int → UInt8) (first last : Int) (st : UInt32)
    (h : last < first) : cmpDfaWindow rd first last st = st := by
  have hz : (last-first+1).toNat = 0 := by omega
  simp only [cmpDfaWindow, hz, cmpDfaRange]

theorem cmpDfaWindow_split (rd : Int → UInt8) (first mid last : Int) (st : UInt32)
    (h1 : first ≤ mid) (h2 : mid ≤ last+1) :
    cmpDfaWindow rd first last st =
      cmpDfaWindow rd mid last (cmpDfaWindow rd first (mid-1) st) := by
  have hn : (last-first+1).toNat = (mid-1-first+1).toNat + (last-mid+1).toNat := by omega
  have hi : first + ((mid-1-first+1).toNat : Int) = mid := by omega
  simp only [cmpDfaWindow]
  rw [hn, cmpDfaRange_append, hi]

theorem cmpDfaWindow_advance (rd : Int → UInt8) (first last chunk : Int) (st : UInt32)
    (_hf : first ≤ last) (hc : 0 < chunk) :
    cmpDfaWindow rd first last st =
      cmpDfaWindow rd (first+chunk) last
        (cmpDfaWindow rd first (min last (first+chunk-1)) st) := by
  by_cases h : first+chunk ≤ last
  · rw [Int.min_eq_right (by omega)]
    exact cmpDfaWindow_split rd first (first+chunk) last st (by omega) (by omega)
  · rw [Int.min_eq_left (by omega), cmpDfaWindow_empty rd (first+chunk) last _ (by omega)]

theorem cmpDfaRange_ascii (asciiStep : ∀ b : UInt8, b.toNat < 128 →
      utfDfaStep utf8DfaAccept b = utf8DfaAccept)
    (rd : Int → UInt8) (first : Int) (n : Nat)
    (h : ∀ k : Int, first ≤ k → k < first+n → (rd k).toNat < 128) :
    cmpDfaRange rd first n utf8DfaAccept = utf8DfaAccept := by
  induction n generalizing first with
  | zero => rfl
  | succ n ih =>
      simp only [cmpDfaRange, asciiStep _ (h first (Int.le_refl _) (by omega))]
      exact ih (first+1) (fun k hk1 hk2 => h k (by omega) (by omega))

theorem cmpDfaWindow_ascii (asciiStep : ∀ b : UInt8, b.toNat < 128 →
      utfDfaStep utf8DfaAccept b = utf8DfaAccept)
    (rd : Int → UInt8) (first last : Int)
    (h : ∀ k : Int, first ≤ k → k ≤ last → (rd k).toNat < 128) :
    cmpDfaWindow rd first last utf8DfaAccept = utf8DfaAccept := by
  apply cmpDfaRange_ascii asciiStep
  intro k h1 h2
  exact h k h1 (by omega)

theorem cmpByteAscii (bs : List UInt8) (first last k : Int)
    (ha : byteListIsAscii bs first last = true)
    (h1 : first ≤ k) (h2 : k ≤ last) : (byteListGet bs k).toNat < 128 := by
  have hf : ¬ first > last := by omega
  simp only [byteListIsAscii, hf, ite_false, List.all_eq_true] at ha
  have hk : (k-first).toNat ∈ List.range (last-first+1).toNat := by
    rw [List.mem_range]
    omega
  have h := ha (k-first).toNat hk
  have he : first + ((k-first).toNat : Int) = k := by omega
  have hh : (byteListGet bs (first + ((k-first).toNat : Int))).toNat < 128 :=
    of_decide_eq_true h
  rw [he] at hh
  exact hh

theorem cmpIsvalidDfa_eq {V : Type} (rd : V → Int → UInt8) (bs : V)
    (fi li : V → Int) (first last : Int) (st : UInt32) :
    isvalidUtf8Dfa rd fi li st bs first last =
      cmpDfaWindow (rd bs) first last st := by
  unfold isvalidUtf8Dfa
  change cmpDfaRun rd bs last
    (if first ≤ last then (last-first+1).toNat else 0) first st = _
  apply cmpDfaRun_eq
  split <;> omega

theorem cmpSkip_step {V : Type} (ascii : V → Int → Int → Bool) (bs : V)
    (chunk last : Int) (fuel : Nat) (first stop : Int) (st : UInt32) :
    cmpSkip ascii bs chunk last (fuel+1) first stop st =
      (if st == utf8DfaAccept && ascii bs first stop then
        let next := first+chunk
        if next ≤ last then cmpSkip ascii bs chunk last fuel next (min last (stop+chunk)) st
        else (first,stop,st)
      else (first,stop,st)) := by rfl

theorem cmpSkip_spec {V : Type}
    (asciiStep : ∀ b : UInt8, b.toNat < 128 → utfDfaStep utf8DfaAccept b = utf8DfaAccept)
    (ascii : V → Int → Int → Bool) (bs : V) (rd : Int → UInt8)
    (asciiLaw : ∀ a b k, ascii bs a b = true → a ≤ k → k ≤ b → (rd k).toNat < 128)
    (chunk last : Int) (hc : 0 < chunk) (fuel : Nat) (first stop : Int) (st : UInt32)
    (hs : stop = min last (first+chunk-1)) (hfirst : first ≤ last) :
    let r := cmpSkip ascii bs chunk last fuel first stop st
    first ≤ r.1 ∧ r.1 ≤ last ∧ r.2.1 = min last (r.1+chunk-1) ∧ r.2.2 = st ∧
      cmpDfaWindow rd first last st = cmpDfaWindow rd r.1 last r.2.2 := by
  induction fuel generalizing first stop with
  | zero => exact ⟨Int.le_refl _, hfirst, hs, rfl, rfl⟩
  | succ fuel ih =>
      rw [cmpSkip_step]
      by_cases hcond : (st == utf8DfaAccept && ascii bs first stop) = true
      · rw [ite_eq_left hcond]
        by_cases hnext : first+chunk ≤ last
        · rw [ite_eq_left hnext]
          have stopEq : stop = first+chunk-1 := by rw [hs, Int.min_eq_right (by omega)]
          have newStop : min last (stop+chunk) = min last (first+chunk+chunk-1) := by
            rw [stopEq]
            congr 1 <;> omega
          obtain ⟨hlo, hhi, hstop, hst, hwindow⟩ := ih (first+chunk) (min last (stop+chunk)) newStop hnext
          refine ⟨by omega, hhi, hstop, hst, ?_⟩
          rw [← hwindow]
          have hbits : (st == utf8DfaAccept) = true ∧ ascii bs first stop = true := by
            simpa only [Bool.and_eq_true] using hcond
          have heq : st = utf8DfaAccept := beq_iff_eq.mp hbits.1
          rw [heq, cmpDfaWindow_split rd first (first+chunk) last _ (by omega) (by omega)]
          congr 1
          apply cmpDfaWindow_ascii asciiStep
          intro k h1 h2
          exact asciiLaw first stop k hbits.2 h1 (by omega)
        · rw [ite_eq_right hnext]
          exact ⟨Int.le_refl _, hfirst, hs, rfl, rfl⟩
      · rw [ite_eq_right hcond]
        exact ⟨Int.le_refl _, hfirst, hs, rfl, rfl⟩


theorem cmpClassify_step {V : Type} (rd : V → Int → UInt8)
    (fi li : V → Int) (ascii : V → Int → Int → Bool) (bs : V)
    (chunk last : Int) (fuel : Nat) (first stop : Int) (st : UInt32) :
    cmpClassify rd fi li ascii bs chunk last (fuel+1) first stop st =
      (if first ≤ last then
        let r := cmpSkip ascii bs chunk last fuel first stop st
        let nextState := isvalidUtf8Dfa rd fi li r.2.2 bs r.1 r.2.1
        if nextState == utf8DfaInvalid then 0
        else cmpClassify rd fi li ascii bs chunk last fuel
          (r.1+chunk) (min last (r.2.1+chunk)) nextState
      else if st == utf8DfaAccept then 2 else 0) := by rfl

theorem cmpClassify_sound {V : Type}
    (asciiStep : ∀ b : UInt8, b.toNat < 128 → utfDfaStep utf8DfaAccept b = utf8DfaAccept)
    (rd : V → Int → UInt8) (fi li : V → Int)
    (ascii : V → Int → Int → Bool) (bs : V)
    (asciiLaw : ∀ a b k, ascii bs a b = true → a ≤ k → k ≤ b → (rd bs k).toNat < 128)
    (chunk last : Int) (hc : 0 < chunk) (fuel : Nat) (first stop : Int) (st : UInt32)
    (hs : stop = min last (first+chunk-1))
    (hrun : cmpClassify rd fi li ascii bs chunk last fuel first stop st ≠ 0) :
    cmpDfaWindow (rd bs) first last st = utf8DfaAccept := by
  induction fuel generalizing first stop st with
  | zero =>
      change (if first ≤ last then 0 else if st == utf8DfaAccept then 2 else 0) ≠ 0 at hrun
      by_cases hf : first ≤ last
      · rw [ite_eq_left hf] at hrun
        exact False.elim (hrun rfl)
      · rw [ite_eq_right hf] at hrun
        have he : st = utf8DfaAccept := by
          by_cases he : st == utf8DfaAccept
          · exact beq_iff_eq.mp he
          · rw [ite_eq_right he] at hrun
            exact False.elim (hrun rfl)
        rw [cmpDfaWindow_empty _ _ _ _ (by omega), he]
  | succ fuel ih =>
      rw [cmpClassify_step] at hrun
      by_cases hf : first ≤ last
      · rw [ite_eq_left hf] at hrun
        obtain ⟨hlo, hhi, ht, hv, hw⟩ :=
          cmpSkip_spec asciiStep ascii bs (rd bs) asciiLaw chunk last hc fuel first stop st hs hf
        cases heq : cmpSkip ascii bs chunk last fuel first stop st with
        | mk f p =>
          cases p with
          | mk t v =>
              rw [heq] at hrun hlo hhi ht hv hw
              dsimp only at hrun hlo hhi ht hv hw
              have hstate : isvalidUtf8Dfa rd fi li v bs f t =
                  cmpDfaWindow (rd bs) f t v := by
                exact cmpIsvalidDfa_eq rd bs fi li f t v
              rw [hstate] at hrun
              by_cases herr : cmpDfaWindow (rd bs) f t v == utf8DfaInvalid
              · rw [ite_eq_left herr] at hrun
                exact False.elim (hrun rfl)
              · rw [ite_eq_right herr] at hrun
                have hstop : min last (t+chunk) = min last (f+chunk+chunk-1) := by
                  rw [ht]
                  omega
                have hind := ih (f+chunk) (min last (t+chunk))
                  (cmpDfaWindow (rd bs) f t v) hstop hrun
                rw [hw, cmpDfaWindow_advance (rd bs) f last chunk v (by omega) hc]
                rw [← ht]
                exact hind
      · rw [ite_eq_right hf] at hrun
        have he : st = utf8DfaAccept := by
          by_cases he : st == utf8DfaAccept
          · exact beq_iff_eq.mp he
          · rw [ite_eq_right he] at hrun
            exact False.elim (hrun rfl)
        rw [cmpDfaWindow_empty _ _ _ _ (by omega), he]


theorem cmpFind_step {V : Type} (ascii : V → Int → Int → Bool) (bs : V)
    (last chunk : Int) (fuel : Nat) (first : Int) :
    cmpFind ascii bs last chunk (fuel+1) first =
      (if first ≤ last-chunk then
        if !ascii bs first (first+chunk-1) then some first
        else cmpFind ascii bs last chunk fuel (first+chunk)
      else none) := by rfl

theorem cmpFind_spec {V : Type} (ascii : V → Int → Int → Bool) (bs : V)
    (rd : Int → UInt8)
    (asciiLaw : ∀ a b k, ascii bs a b = true → a ≤ k → k ≤ b → (rd k).toNat < 128)
    (last chunk : Int) (hc : 0 < chunk) (fuel : Nat) (first : Int)
    (hf : (last-first+1).toNat ≤ fuel) :
    match cmpFind ascii bs last chunk fuel first with
    | some start => first ≤ start ∧ start ≤ last ∧
        ∀ k, first ≤ k → k < start → (rd k).toNat < 128
    | none => ∀ k, first ≤ k → k ≤ last-chunk → (rd k).toNat < 128 := by
  induction fuel generalizing first with
  | zero =>
      change ∀ k, first ≤ k → k ≤ last-chunk → _
      intro k h1 h2
      omega
  | succ fuel ih =>
      rw [cmpFind_step]
      by_cases hscan : first ≤ last-chunk
      · rw [ite_eq_left hscan]
        cases ha : ascii bs first (first+chunk-1) with
        | false =>
            simp only [Bool.not_false, ite_true]
            exact ⟨Int.le_refl _, by omega, fun k h1 h2 => by omega⟩
        | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            have hs := ih (first+chunk) (by omega)
            cases hr : cmpFind ascii bs last chunk fuel (first+chunk) with
            | none =>
                rw [hr] at hs
                intro k hk1 hk2
                by_cases hk : k < first+chunk
                · exact asciiLaw first (first+chunk-1) k ha hk1 (by omega)
                · exact hs k (by omega) hk2
            | some start =>
                rw [hr] at hs
                refine ⟨by omega, hs.2.1, ?_⟩
                intro k hk1 hk2
                by_cases hk : k < first+chunk
                · exact asciiLaw first (first+chunk-1) k ha hk1 (by omega)
                · exact hs.2.2 k (by omega) hk2
      · rw [ite_eq_right hscan]
        intro k h1 h2
        omega

theorem cmpFindChunk_spec {V : Type} (ascii : V → Int → Int → Bool) (bs : V)
    (rd : Int → UInt8)
    (asciiLaw : ∀ a b k, ascii bs a b = true → a ≤ k → k ≤ b → (rd k).toNat < 128)
    (last chunk first : Int) (hc : 0 < chunk) (hsize : first+chunk-1 ≤ last) :
    match findNonasciiChunk ascii chunk bs first last with
    | some start => first ≤ start ∧ start ≤ last ∧
        ∀ k, first ≤ k → k < start → (rd k).toNat < 128
    | none => ∀ k, first ≤ k → k ≤ last → (rd k).toNat < 128 := by
  have hfl : first ≤ last := by omega
  change (match (match cmpFind ascii bs last chunk
      (if first ≤ last then (last-first+1).toNat+1 else 1) first with
    | some i => some i
    | none => if !ascii bs (last-chunk+1) last then some (last-chunk+1) else none) with
    | some start => first ≤ start ∧ start ≤ last ∧
        ∀ k, first ≤ k → k < start → (rd k).toNat < 128
    | none => ∀ k, first ≤ k → k ≤ last → (rd k).toNat < 128)
  rw [ite_eq_left hfl]
  have hs := cmpFind_spec ascii bs rd asciiLaw last chunk hc
    ((last-first+1).toNat+1) first (by omega)
  cases hr : cmpFind ascii bs last chunk ((last-first+1).toNat+1) first with
  | some start =>
      rw [hr] at hs
      exact hs
  | none =>
      rw [hr] at hs
      cases ha : ascii bs (last-chunk+1) last with
      | false =>
          simp only [Bool.not_false, ite_true]
          exact ⟨by omega, by omega, fun k h1 h2 => hs k h1 (by omega)⟩
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          intro k h1 h2
          by_cases hk : k ≤ last-chunk
          · exact hs k h1 hk
          · exact asciiLaw (last-chunk+1) last k ha (by omega) h2


theorem cmpNonascii_sound (bs : List UInt8) (first last : Int)
    (h : byteStringClassifyNonascii byteListGet byteListFirstindex byteListLastindex
      byteListIsAscii bs first last ≠ 0) :
    cmpDfaWindow (byteListGet bs) first last utf8DfaAccept = utf8DfaAccept := by
  exact cmpClassify_sound cmpDfaAsciiStep byteListGet byteListFirstindex byteListLastindex
    byteListIsAscii bs (fun a b k ha h1 h2 => cmpByteAscii bs a b k ha h1 h2)
    256 last (by decide) _ first (min last (first+256-1)) utf8DfaAccept rfl h

theorem cmpValid_window (bs : List UInt8) (h : stringBytesAreValidUtf8 bs = true) :
    cmpDfaWindow (byteListGet bs) 1 bs.length utf8DfaAccept = utf8DfaAccept := by
  have hclass : byteStringClassifyVector byteListLength byteListGet byteListFirstindex
      byteListLastindex byteListIsAscii bs ≠ 0 := by
    simpa only [stringBytesAreValidUtf8, isvalidStringBytes, bne_iff_ne] using h
  change (if (bs.length : Int) > 1536 then
      (match findNonasciiChunk byteListIsAscii 1024 bs 1 bs.length with
      | none => 1
      | some start => byteStringClassifyNonascii byteListGet byteListFirstindex
          byteListLastindex byteListIsAscii bs start bs.length)
    else if byteListIsAscii bs 1 bs.length then 1
    else byteStringClassifyNonascii byteListGet byteListFirstindex byteListLastindex
      byteListIsAscii bs 1 bs.length) ≠ 0 at hclass
  by_cases hlong : (bs.length : Int) > 1536
  · rw [ite_eq_left hlong] at hclass
    have hspec := cmpFindChunk_spec byteListIsAscii bs (byteListGet bs)
      (fun a b k ha h1 h2 => cmpByteAscii bs a b k ha h1 h2)
      bs.length 1024 1 (by decide) (by omega)
    cases hfind : findNonasciiChunk byteListIsAscii 1024 bs 1 bs.length with
    | none =>
        rw [hfind] at hspec
        exact cmpDfaWindow_ascii cmpDfaAsciiStep _ _ _ hspec
    | some start =>
        rw [hfind] at hspec hclass
        have hprefix := cmpDfaWindow_ascii cmpDfaAsciiStep (byteListGet bs) 1 (start-1)
          (fun k h1 h2 => hspec.2.2 k h1 (by omega))
        rw [cmpDfaWindow_split (byteListGet bs) 1 start bs.length _ hspec.1 (by omega), hprefix]
        exact cmpNonascii_sound bs start bs.length hclass
  · rw [ite_eq_right hlong] at hclass
    cases ha : byteListIsAscii bs 1 bs.length with
    | false =>
        rw [ha] at hclass
        exact cmpNonascii_sound bs 1 bs.length hclass
    | true =>
        exact cmpDfaWindow_ascii cmpDfaAsciiStep _ _ _
          (fun k h1 h2 => cmpByteAscii bs 1 bs.length k ha h1 h2)

theorem cmpDfaRange_list (rd : Int → UInt8) (xs : List UInt8)
    (first : Int) (st : UInt32)
    (h : ∀ k : Nat, k < xs.length → rd (first+k) = xs.getD k 0) :
    cmpDfaRange rd first xs.length st = xs.foldl utfDfaStep st := by
  induction xs generalizing first st with
  | nil => rfl
  | cons b xs ih =>
      have hb : rd first = b := by
        have hh := h 0 (by simp only [List.length_cons]; omega)
        simpa only [Int.natCast_zero, Int.add_zero, List.getD_cons_zero] using hh
      simp only [List.length_cons, cmpDfaRange, List.foldl_cons, hb]
      apply ih
      intro k hk
      have hh := h (k+1) (by simp only [List.length_cons]; omega)
      have hp : first + ((k+1 : Nat) : Int) = first+1+k := by omega
      rw [hp] at hh
      exact hh

theorem cmpDfaWindow_bytes (bs : List UInt8) (st : UInt32) :
    cmpDfaWindow (byteListGet bs) 1 bs.length st = bs.foldl utfDfaStep st := by
  unfold cmpDfaWindow
  have hn : ((bs.length : Int)-1+1).toNat = bs.length := by omega
  rw [hn]
  apply cmpDfaRange_list
  intro k hk
  unfold byteListGet
  have hi : ((1 : Int)+k).toNat - 1 = k := by omega
  rw [hi]

theorem cmpDfaAccept_of_valid (bs : List UInt8) (h : stringBytesAreValidUtf8 bs = true) :
    bs.foldl utfDfaStep utf8DfaAccept = utf8DfaAccept := by
  rw [← cmpDfaWindow_bytes]
  exact cmpValid_window bs h

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## Utf8Bridge -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean.base.strings.string

theorem cmpUtf8Shape_of_valid (bs : List UInt8)
    (h : stringBytesAreValidUtf8 bs = true) : CmpUtf8Shape bs :=
  cmpUtf8Shape_of_dfa bs (cmpDfaAccept_of_valid bs h)

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## Cmp -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean
open JuliaLean.base.strings.string
open JuliaLean.Proofs.base.strings.string
open JuliaLean.Proofs.base.strings.util.Round6

/-- A glyph suffix produces a complete run through the installed prepared-string adapter. -/
theorem cmpPreparedGlyphRun (s : Raw) (p : Prepared) (hp : prepare s = .ok p)
    (cs : List CmpGlyph) (pre : List UInt8) (hs : s.bytes = pre ++ cmpGlyphBytes cs) :
    ∃ first, preparedOps.iterateAt p (cmpIndex pre.length) = .ok first ∧
      CmpRun (preparedOps.iterateAt p) first (cs.map CmpGlyph.bits) := by
  induction cs generalizing pre with
  | nil =>
    have hbytes : s.bytes = pre := by simpa only [cmpGlyphBytes,List.flatMap_nil,List.append_nil] using hs
    have hlen : pre.length = s.bytes.length := (congrArg List.length hbytes).symm
    refine ⟨none, ?_, CmpRun.done⟩
    rw [hlen]
    rw [cmpPreparedIterateAt s p hp _
      (by rw [cmpIndexVal _ (by have := s.small; omega)]; omega)
      (by rw [cmpIndexVal _ (by have := s.small; omega)]; omega)]
    rw [cmpIterEnd]
  | cons c cs ih =>
    have hbytes : s.bytes = pre ++ c.bytes ++ cmpGlyphBytes cs := by
      simpa only [cmpGlyphBytes,List.flatMap_cons,List.append_assoc] using hs
    have hlen := congrArg List.length hbytes
    simp only [List.length_append] at hlen
    have hsmall := s.small
    obtain ⟨next, hnext, hrun⟩ := ih (pre ++ c.bytes) hbytes
    refine ⟨some (c.bits,cmpIndex (pre.length+c.bytes.length)), ?_, ?_⟩
    · rw [cmpPreparedIterateAt s p hp _
        (by rw [cmpIndexVal _ (by omega)]; omega)
        (by rw [cmpIndexVal _ (by omega)]; omega),
        cmpIterGlyph s pre (cmpGlyphBytes cs) c hbytes]
    · apply CmpRun.step _ hrun
      simpa only [List.length_append] using hnext

/-- Complete prepared runs and their loop budget for a whole String. -/
theorem cmpPreparedWholeRun (s : Raw) (p : Prepared) (hp : prepare s = .ok p)
    (cs : List CmpGlyph) (hcs : cmpGlyphBytes cs = s.bytes) :
    ∃ first, preparedOps.iterateFirst p = .ok first ∧
      CmpRun (preparedOps.iterateAt p) first (cs.map CmpGlyph.bits) ∧
      (cs.map CmpGlyph.bits).length ≤ preparedOps.iterationBound p := by
  obtain ⟨first,hfirst,hrun⟩ := cmpPreparedGlyphRun s p hp cs [] (by exact hcs.symm)
  refine ⟨first, ?_, hrun, ?_⟩
  · exact hfirst
  · change (cs.map CmpGlyph.bits).length ≤ p.view.ncodeunits.val.toNat+1
    rw [List.length_map,cmpPreparedView s p hp,stringNcodeunits_val,Int.toNat_natCast]
    have hc := cmpGlyphCount cs
    rw [hcs] at hc
    omega

/-- On well-formed UTF-8, the installed byte comparator and generic Char comparator agree. -/
theorem cmpFromByteOrder
    (hByteLex : ∀ a b : Raw, Round1.compareStringValues a b = cmpLexBytes a.bytes b.bytes) :
    JuliaLean.Proofs.base.strings.string.Round1.CmpAgreesOnValidUtf8 := by
  intro a b ha hb
  obtain ⟨as,has⟩ := cmpShapeGlyphs (cmpUtf8Shape_of_valid a.bytes ha)
  obtain ⟨bs,hbs⟩ := cmpShapeGlyphs (cmpUtf8Shape_of_valid b.bytes hb)
  obtain ⟨pa,hpa⟩ := cmpPrepareExists a
  obtain ⟨pb,hpb⟩ := cmpPrepareExists b
  cases hsame : preparedOps.sameReference pa pb with
  | true =>
    have hv : pa.view=pb.view := by
      change (pa.view == pb.view) = true at hsame
      exact beq_iff_eq.mp hsame
    have hab : a=b := by
      have h := congrArg (fun v : View => v.string) hv
      simpa only [cmpPreparedView a pa hpa,cmpPreparedView b pb hpb] using h
    refine ⟨pa,pb,JuliaLean.base.strings.basic.int 0,hpa,hpb,?_,?_⟩
    · simp only [JuliaLean.base.strings.basic.cmpString,JuliaLean.base.strings.basic.cmp,
        hsame,ite_true,pure,Except.pure]
    · rw [hab,hByteLex,cmpLexBytesSelf]
      rfl
  | false =>
    obtain ⟨fa,hfa,hra,hba⟩ := cmpPreparedWholeRun a pa hpa as has
    obtain ⟨fb,hfb,hrb,hbb⟩ := cmpPreparedWholeRun b pb hpb bs hbs
    let result := JuliaLean.base.strings.basic.lexCompare
      JuliaLean.base.char.eq_Char JuliaLean.base.char.isless_Char
      (as.map CmpGlyph.bits) (bs.map CmpGlyph.bits)
    refine ⟨pa,pb,result,hpa,hpb,?_,?_⟩
    · exact cmpGenericRun preparedOps pa pb _ _ fa fb hsame hfa hfb hra hrb hba hbb
    · calc
        Round1.compareStringValues a b = cmpLexBytes a.bytes b.bytes := hByteLex a b
        _ = cmpLexBytes (cmpGlyphBytes as) (cmpGlyphBytes bs) := by rw [has,hbs]
        _ = cmpLexChars (as.map CmpGlyph.bits) (bs.map CmpGlyph.bits) := cmpGlyphLexLists as bs
        _ = result.val := (cmpLexCharsValue _ _).symm

/-- strings-cmp-valid-utf8: the frozen comparison contract. -/
theorem StringsCmpValidUtf8_proven : JuliaLean.Proofs.base.strings.string.Round1.CmpAgreesOnValidUtf8 :=
  cmpFromByteOrder cmpCompareStringValuesLex

end JuliaLean.ChatGPT.Batch2.Group5


/-! ## Iteration -/

namespace JuliaLean.ChatGPT.Batch2.Group5

open JuliaLean
open JuliaLean.base.strings.string
open JuliaLean.Proofs.base.strings.string
open JuliaLean.Proofs.base.strings.util.Round6

theorem iterationByteAt (s : JString) (i : Index) :
    stringByteAt s i = parentByte s i.val := by
  unfold stringByteAt parentByte
  congr 1
  omega

theorem iterationUnsignedIndex (s : JString) (i : Index) (hlo : 1 ≤ i.val)
    (hhi : i.val ≤ s.bytes.length + 1) :
    (JInt.rem .u64 i - JInt.lit .u64 1).val = i.val - 1 := by
  have hs := s.small
  have hu : (JInt.rem .u64 i).val = i.val := by
    change wrapInt .u64 i.val = i.val
    exact wrapInt_of_inRange .u64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)
  change wrapInt .u64 ((JInt.rem .u64 i).val - (JInt.lit .u64 1).val) = _
  rw [hu, show (JInt.lit .u64 1).val = 1 by decide]
  exact wrapInt_of_inRange .u64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

theorem iterationEnd (s : JString) (i : Index) (hend : i.val = s.bytes.length + 1) :
    stringIterate s i = none := by
  have hcond := iterationUnsignedIndex s i (by omega) (by omega)
  unfold stringIterate iterateString
  rw [hcond, stringNcodeunits_val]
  simp only [hend, Int.add_sub_cancel, Int.lt_irrefl, decide_false, Bool.not_false, ite_true]

theorem iterationInBounds (s : JString) (i : Index) (hlo : 1 ≤ i.val)
    (hhi : i.val ≤ s.bytes.length) :
    stringIterate s i =
      if !stringBetweenByte (stringByteAt s i) 0x80 0xf7 then
        some ((stringByteAt s i).toUInt32 <<< 24, i + JuliaLean.Strings.ix 1)
      else some (iterateContinued stringNcodeunits stringByteAt s i
        ((stringByteAt s i).toUInt32 <<< 24)) := by
  have hcond := iterationUnsignedIndex s i hlo (by omega)
  unfold stringIterate iterateString
  rw [hcond, stringNcodeunits_val]
  simp only [show i.val - 1 < (s.bytes.length : Int) by omega, decide_true,
    Bool.not_true, Bool.false_eq_true, ite_false]

theorem iterationValidBounds (s : JString) (i : Index)
    (hv : stringIsvalidIndex s i = true) : 1 ≤ i.val ∧ i.val ≤ s.bytes.length := by
  unfold stringIsvalidIndex isvalidStringIndex at hv
  have hc := (Bool.and_eq_true_iff.mp hv).1
  simpa only [stringCheckboundsBool, Bool.and_eq_true, decide_eq_true_eq] using hc

theorem iterationValidThisind (s : JString) (i : Index)
    (hv : stringIsvalidIndex s i = true) : stringThisind s i = .ok i := by
  unfold stringIsvalidIndex isvalidStringIndex at hv
  have hc := (Bool.and_eq_true_iff.mp hv).2
  change (match stringThisind s i with
    | .ok j => j.val == i.val
    | .error _ => false) = true at hc
  cases ht : stringThisind s i with
  | error e => rw [ht] at hc; cases hc
  | ok j =>
    rw [ht] at hc
    have hji : j = i := Subtype.ext (beq_iff_eq.mp hc)
    rw [hji]

theorem iterationShift24 (b : UInt8) :
    (b.toUInt32 <<< 24).toNat = b.toNat * 2 ^ 24 := by
  have hb := UInt8.toNat_lt b
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, Nat.shiftLeft_eq]
  have e : (24 : UInt32).toNat % 32 = 24 := rfl
  rw [e]
  exact Nat.mod_eq_of_lt (by omega)

theorem iterationShift16 (b : UInt8) :
    (b.toUInt32 <<< 16).toNat = b.toNat * 2 ^ 16 := by
  have hb := UInt8.toNat_lt b
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, Nat.shiftLeft_eq]
  have e : (16 : UInt32).toNat % 32 = 16 := rfl
  rw [e]
  exact Nat.mod_eq_of_lt (by omega)

theorem iterationShift8 (b : UInt8) :
    (b.toUInt32 <<< 8).toNat = b.toNat * 2 ^ 8 := by
  have hb := UInt8.toNat_lt b
  rw [UInt32.toNat_shiftLeft, UInt8.toNat_toUInt32, Nat.shiftLeft_eq]
  have e : (8 : UInt32).toNat % 32 = 8 := rfl
  rw [e]
  exact Nat.mod_eq_of_lt (by omega)

def iterationTopByte (u : UInt32) (l : Nat) : Prop :=
  ∃ r, r < 2 ^ 24 ∧ u.toNat = l * 2 ^ 24 + r

theorem iterationTopInitial (b : UInt8) :
    iterationTopByte (b.toUInt32 <<< 24) b.toNat :=
  ⟨0, by decide, by rw [iterationShift24]; omega⟩

theorem iterationTopOr (u y : UInt32) (l : Nat)
    (h : iterationTopByte u l) (hy : y.toNat < 2 ^ 24) :
    iterationTopByte (u ||| y) l := by
  obtain ⟨r, hr, hu⟩ := h
  refine ⟨r ||| y.toNat, Nat.or_lt_two_pow hr hy, ?_⟩
  rw [UInt32.toNat_or, hu]
  have heq : l * 2 ^ 24 + r = (l <<< 24) ||| r := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hr, Nat.shiftLeft_eq]
  rw [heq, Nat.or_assoc, ← Nat.shiftLeft_add_eq_or_of_lt (Nat.or_lt_two_pow hr hy),
    Nat.shiftLeft_eq]

theorem iterationTopLt (u : UInt32) (l k : Nat) (h : iterationTopByte u l)
    (hk : k < 256) :
    (u < UInt32.ofNat (k * 2 ^ 24) ↔ l < k) := by
  obtain ⟨r, hr, hu⟩ := h
  rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega), hu]
  omega

theorem iterationIteSecond {α β : Type} (c : Prop) [Decidable c] (x y : α × β) :
    (if c then x else y).2 = if c then x.2 else y.2 := by
  split <;> rfl

/-- The continuation decoder's next index depends only on its leading byte and boundaries. -/
theorem iterationContinuedSecond (s : JString) (i : Index) :
    (iterateContinued stringNcodeunits stringByteAt s i
      ((stringByteAt s i).toUInt32 <<< 24)).2 =
    if stringByteAt s i < 0xc0 then i + JuliaLean.Strings.ix 1 else
    let j := i + JuliaLean.Strings.ix 1
    if j.val > (stringNcodeunits s).val then j else
    if (stringByteAt s j &&& 0xc0) != 0x80 then j else
    let k := j + JuliaLean.Strings.ix 1
    if k.val > (stringNcodeunits s).val || stringByteAt s i < 0xe0 then k else
    if (stringByteAt s k &&& 0xc0) != 0x80 then k else
    let l := k + JuliaLean.Strings.ix 1
    if l.val > (stringNcodeunits s).val || stringByteAt s i < 0xf0 then l else
    if (stringByteAt s l &&& 0xc0) != 0x80 then l else l + JuliaLean.Strings.ix 1 := by
  have h0 := iterationTopInitial (stringByteAt s i)
  have h1 := iterationTopOr _ ((stringByteAt s (i + JuliaLean.Strings.ix 1)).toUInt32 <<< 16)
    _ h0 (by rw [iterationShift16]; have := UInt8.toNat_lt (stringByteAt s (i + JuliaLean.Strings.ix 1)); omega)
  have h2 := iterationTopOr _ ((stringByteAt s
      (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)).toUInt32 <<< 8)
    _ h1 (by rw [iterationShift8]; have := UInt8.toNat_lt (stringByteAt s
      (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)); omega)
  have hc0 : ((stringByteAt s i).toUInt32 <<< 24 < 0xc0000000) ↔ stringByteAt s i < 0xc0 := by
    exact (iterationTopLt _ _ 192 h0 (by decide)).trans (lt192_iff _).symm
  have hc1 : (((stringByteAt s i).toUInt32 <<< 24 |||
      ((stringByteAt s (i + JuliaLean.Strings.ix 1)).toUInt32 <<< 16)) < 0xe0000000) ↔
      stringByteAt s i < 0xe0 := by
    exact (iterationTopLt _ _ 224 h1 (by decide)).trans (lt224_iff _).symm
  have hc2 : ((((stringByteAt s i).toUInt32 <<< 24 |||
      ((stringByteAt s (i + JuliaLean.Strings.ix 1)).toUInt32 <<< 16)) |||
      ((stringByteAt s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)).toUInt32 <<< 8))
      < 0xf0000000) ↔ stringByteAt s i < 0xf0 := by
    exact (iterationTopLt _ _ 240 h2 (by decide)).trans (lt240_iff _).symm
  unfold iterateContinued
  simp only [Id.run, pure, hc0, hc1, hc2]
  simp only [Id, iterationIteSecond]
  repeat' split
  all_goals rfl

theorem iterationOkIte {E A : Type} (c : Prop) [Decidable c] (x y : A) :
    (Except.ok (if c then x else y) : Except E A) =
      if c then Except.ok x else Except.ok y := by
  split <;> rfl

theorem iterationNextSecond (s : JString) (i : Index)
    (hv : stringIsvalidIndex s i = true) :
    stringNextind s i =
      if !stringBetweenByte (stringByteAt s i) 0x80 0xf7 then
        .ok (i + JuliaLean.Strings.ix 1)
      else .ok (iterateContinued stringNcodeunits stringByteAt s i
        ((stringByteAt s i).toUInt32 <<< 24)).2 := by
  obtain ⟨hlo, hhi⟩ := iterationValidBounds s i hv
  have hzero : (i.val == 0) = false := by
    simp only [beq_eq_false_iff_ne]
    omega
  have hbetween : stringBetweenIndex i (JuliaLean.Strings.ix 1) (stringNcodeunits s) = true := by
    simp only [stringBetweenIndex, between, Bool.and_eq_true, decide_eq_true_eq,
      stringNcodeunits_val, show (JuliaLean.Strings.ix 1).val = 1 by decide]
    exact ⟨hlo, hhi⟩
  have hread : ∀ k : Index, stringCodeunitAt false s k = .ok (stringByteAt s k) := by
    intro k
    rw [iterationByteAt]
    exact stringCodeunitAt_unchecked s k
  have hthis := iterationValidThisind s i hv
  change thisindString stringNcodeunits stringBetweenIndex stringBetweenByte stringCodeunitAt s i =
    .ok i at hthis
  rw [iterationContinuedSecond]
  unfold stringNextind nextindString nextindStr
  simp only [hzero, hbetween, hread, hthis, Bool.false_eq_true, ite_false, Bool.not_true,
    bind, Except.bind, pure, Except.pure, Int.le_refl, ite_true,
    iterationOkIte]

/-- A valid string index has an iteration step with the same successor as `nextind`. -/
theorem iterationNextBridge (s : JString) (i : Index)
    (hv : stringIsvalidIndex s i = true) :
    ∃ c next, stringIterate s i = some (c, next) ∧ stringNextind s i = .ok next := by
  obtain ⟨hlo, hhi⟩ := iterationValidBounds s i hv
  rw [iterationInBounds s i hlo hhi, iterationNextSecond s i hv]
  by_cases hb : (!stringBetweenByte (stringByteAt s i) 0x80 0xf7) = true
  · rw [ite_eq_left hb, ite_eq_left hb]
    exact ⟨_, _, rfl, rfl⟩
  · rw [ite_eq_right hb, ite_eq_right hb]
    generalize iterateContinued stringNcodeunits stringByteAt s i
      ((stringByteAt s i).toUInt32 <<< 24) = result
    exact ⟨result.1, result.2, congrArg some (Prod.eta result).symm, rfl⟩

/-- An installed iteration step advances to the next valid index, skipping only invalid indices. -/
theorem iterationStep (s : JString) (i : Index)
    (hv : stringIsvalidIndex s i = true) :
    ∃ c next, stringIterate s i = some (c, next) ∧
      i.val < next.val ∧ next.val ≤ s.bytes.length + 1 ∧
      (next.val ≤ s.bytes.length → stringIsvalidIndex s next = true) ∧
      ∀ j : Index, i.val < j.val → j.val < next.val → stringIsvalidIndex s j = false := by
  obtain ⟨hlo, hhi⟩ := iterationValidBounds s i hv
  have hpure := (stringIsvalid_iff_pure s i hlo hhi).mp hv
  have hnot := (thisindPure_eq_iff (parentByte s) i.val).mp hpure
  obtain ⟨m, hm, hgt, hle, hend, hgap⟩ := stringNextind_next s i hlo hhi hnot
  obtain ⟨c, next, hit, hnext⟩ := iterationNextBridge s i hv
  have hnm : next = m := Except.ok.inj (hnext.symm.trans hm)
  subst next
  refine ⟨c, m, hit, hgt, hle, ?_, ?_⟩
  · intro hmn
    apply (stringIsvalid_iff_pure s m (by omega) hmn).mpr
    apply (thisindPure_eq_iff (parentByte s) m.val).mpr
    rcases hend with he | hn
    · omega
    · exact hn
  · intro j hij hjm
    cases hj : stringIsvalidIndex s j with
    | false => rfl
    | true =>
      obtain ⟨hj1, hjn⟩ := iterationValidBounds s j hj
      have hjpure := (stringIsvalid_iff_pure s j hj1 hjn).mp hj
      have hjnot := (thisindPure_eq_iff (parentByte s) j.val).mp hjpure
      exact (hjnot (hgap j.val hij hjm)).elim

/-- Complete iteration from a character start, together with its exact set of starts. -/
theorem iterationTraceFrom (s : JString) :
    ∀ (k : Nat) (i : Index), 1 ≤ i.val → i.val ≤ s.bytes.length + 1 →
      (k : Int) = s.bytes.length + 1 - i.val →
      (i.val ≤ s.bytes.length → stringIsvalidIndex s i = true) →
      ∃ rows, IterTrace stringIterate s i rows ∧
        ∀ j, Round1.traceHasStart rows j = true ↔
          i.val ≤ j.val ∧ stringIsvalidIndex s j = true := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i hlo hhi hk hv
    by_cases hdone : i.val = s.bytes.length + 1
    · refine ⟨[], .stop (iterationEnd s i hdone), ?_⟩
      intro j
      change false = true ↔ _
      constructor
      · intro h; cases h
      · rintro ⟨hij, hj⟩
        obtain ⟨_, hjn⟩ := iterationValidBounds s j hj
        omega
    · have hinside : i.val ≤ s.bytes.length := by omega
      have hi := hv hinside
      obtain ⟨c, next, hit, hgt, hn, hvnext, hgap⟩ := iterationStep s i hi
      let remaining : Nat := (s.bytes.length + 1 - next.val).toNat
      have hremaining : (remaining : Int) = s.bytes.length + 1 - next.val := by
        exact Int.toNat_of_nonneg (by omega)
      have hlt : remaining < k := by omega
      obtain ⟨rows, htrace, hstarts⟩ := ih remaining hlt next (by omega) hn hremaining hvnext
      refine ⟨(i, c, next) :: rows, .step hit htrace, ?_⟩
      intro j
      change ((i.val == j.val) || Round1.traceHasStart rows j) = true ↔ _
      rw [Bool.or_eq_true, beq_iff_eq, hstarts]
      constructor
      · intro h
        rcases h with heq | ⟨hnext, hj⟩
        · have hij : i = j := Subtype.ext heq
          subst j
          exact ⟨Int.le_refl _, hi⟩
        · exact ⟨by omega, hj⟩
      · rintro ⟨hij, hj⟩
        by_cases heq : i.val = j.val
        · exact Or.inl heq
        · right
          refine ⟨?_, hj⟩
          apply Int.not_lt.mp
          intro hnot
          have hfalse := hgap j (by omega) hnot
          rw [hfalse] at hj
          cases hj

theorem iterationFirstValid (s : JString) (hn : 1 ≤ (s.bytes.length : Int)) :
    stringIsvalidIndex s (JuliaLean.Strings.ix 1) = true := by
  have h1 : (JuliaLean.Strings.ix 1).val = 1 := by decide
  apply (stringIsvalid_iff_pure s _ (by rw [h1]; exact Int.le_refl 1)
    (by rw [h1]; exact hn)).mpr
  rw [h1]
  unfold thisindPure
  rw [show decide ((1 : Int) - 1 > 0) = false by decide]
  simp only [Bool.and_false, Bool.not_false, ite_true]

theorem iterationComplete (s : JString) :
    ∃ rows, IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows ∧
      ∀ j, Round1.traceHasStart rows j = true ↔ stringIsvalidIndex s j = true := by
  have h1 : (JuliaLean.Strings.ix 1).val = 1 := by decide
  obtain ⟨rows, htrace, hstarts⟩ := iterationTraceFrom s s.bytes.length (JuliaLean.Strings.ix 1)
    (by rw [h1]; exact Int.le_refl 1) (by rw [h1]; omega) (by rw [h1]; omega)
    (by rw [h1]; exact iterationFirstValid s)
  refine ⟨rows, htrace, ?_⟩
  intro j
  rw [hstarts, h1]
  constructor
  · exact And.right
  · intro hj
    exact ⟨(iterationValidBounds s j hj).1, hj⟩

theorem iterationTraceUnique {S : Type} (step : S → Index → Option (UInt32 × Index))
    (s : S) {i : Index} {a b : List (Index × UInt32 × Index)}
    (ha : IterTrace step s i a) (hb : IterTrace step s i b) : a = b := by
  induction ha generalizing b with
  | stop hstop =>
    cases hb with
    | stop _ => rfl
    | step hstep _ => rw [hstop] at hstep; cases hstep
  | @step i c next rows hstep htail ih =>
    cases hb with
    | stop hstop => rw [hstop] at hstep; cases hstep
    | @step _ d next' rows' hstep' htail' =>
      have hp : (c, next) = (d, next') := Option.some.inj (hstep.symm.trans hstep')
      cases hp
      rw [ih htail']

theorem StringIterationStringOnly_proven :
    JuliaLean.Proofs.base.strings.string.Round1.StringIndexValidityMatchesIteration := by
  intro s i
  obtain ⟨rows, htrace, hstarts⟩ := iterationComplete s
  constructor
  · intro hi
    exact ⟨rows, htrace, (hstarts i).mpr hi⟩
  · rintro ⟨other, hother, hi⟩
    have heq := iterationTraceUnique stringIterate s hother htrace
    rw [heq] at hi
    exact (hstarts i).mp hi

end JuliaLean.ChatGPT.Batch2.Group5

namespace Round3

open JuliaLean JuliaLean.base.strings.string JuliaLean.Proofs.base.strings.string

def traceStarts (rows : List (Index × UInt32 × Index)) : List Index :=
  rows.map (fun row => row.1)

/-- thisind returns the start of the character covering an in-bounds byte, preserves the two sentinel indices, and throws outside that domain.
Julia source: base/strings/string.jl:245,252-271 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/strings/basic.jl:416-443; doc/src/manual/strings.md:410-424,773 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def ThisindLocatesCharacter : Prop :=
  ∀ s : JString, ∃ rows, IterTrace stringIterate s (JInt.lit .i64 1) rows ∧
    ∀ i : Index,
      (i.val = 0 ∨ i.val = (stringNcodeunits s).val + 1 →
        stringThisind s i = .ok i) ∧
      (1 ≤ i.val ∧ i.val ≤ (stringNcodeunits s).val →
        ∃ start c next, (start, c, next) ∈ rows ∧
          start.val ≤ i.val ∧ i.val < next.val ∧ i.val - start.val ≤ 3 ∧
          stringThisind s i = .ok start) ∧
      (i.val < 0 ∨ (stringNcodeunits s).val + 1 < i.val →
        stringThisind s i = .error (.jl .boundsError))

/-- nextind advances an arbitrary in-bounds byte to the following character boundary, maps zero to one, and throws for every other index.
Julia source: base/strings/string.jl:273-306 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/strings/basic.jl:516-527; doc/src/manual/strings.md:389-390,410-424,774 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def NextindLocatesFollowingCharacter : Prop :=
  ∀ s : JString, ∃ rows, IterTrace stringIterate s (JInt.lit .i64 1) rows ∧
    ∀ i : Index,
      (i.val = 0 → stringNextind s i = .ok (JInt.lit .i64 1)) ∧
      (1 ≤ i.val ∧ i.val ≤ (stringNcodeunits s).val →
        ∃ start c next, (start, c, next) ∈ rows ∧
          start.val ≤ i.val ∧ i.val < next.val ∧ next.val - i.val ≤ 4 ∧
          next.val ≤ (stringNcodeunits s).val + 1 ∧ stringNextind s i = .ok next) ∧
      (i.val < 0 ∨ (stringNcodeunits s).val < i.val →
        stringNextind s i = .error (.jl .boundsError))

def storageByte? (bytes : List UInt8) (i : Int) : Option UInt8 :=
  if i < 1 then none else bytes[(i - 1).toNat]?

/-- Checked native-Int codeunit access returns the stored byte at each one-based byte position and raises BoundsError everywhere else.
Julia source: base/strings/string.jl:213-217 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/strings/basic.jl:45-68,71-105; doc/src/manual/strings.md:405-408 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def CodeunitHasExactlyStorageDomain : Prop :=
  ∀ (s : JString) (i : Index),
    stringCodeunit s i =
      match storageByte? s.bytes i.val with
      | some b => .ok b
      | none => .error (.jl .boundsError)

/-- lastindex identifies the final character start, with zero for an empty String.
Julia source: base/strings/string.jl:249 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/abstractarray.jl:410-418; doc/src/manual/strings.md:195-199,766-768 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def LastindexIsFinalCharacterStart : Prop :=
  ∀ s : JString, ∃ rows, IterTrace stringIterate s (JInt.lit .i64 1) rows ∧
    lastindexString stringNcodeunits stringBetweenIndex stringBetweenByte stringCodeunitAt s =
      .ok ((traceStarts rows).getLast?.getD (JInt.lit .i64 0))

/-- Native-Int range length counts actual iterated character starts in the inclusive span, accepts the documented sentinels, and throws BoundsError outside that domain.
Julia source: base/strings/string.jl:607-609,615-658 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/strings/basic.jl:367-379; doc/src/manual/strings.md:769-770 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def RangeLengthHasExactlyCharacterDomain : Prop :=
  ∀ s : JString, ∃ rows, IterTrace stringIterate s (JInt.lit .i64 1) rows ∧
    ∀ i j : Index,
      stringLengthRange s i j =
        if 0 < i.val ∧ i.val ≤ (stringNcodeunits s).val + 1 ∧
            0 ≤ j.val ∧ j.val ≤ (stringNcodeunits s).val then
          .ok (JInt.lit .i64 (Int.ofNat ((traceStarts rows).filter
            (fun start => decide (i.val ≤ start.val ∧ start.val ≤ j.val))).length))
        else .error (.jl .boundsError)

end Round3


end JuliaLean.Proofs.base.strings.string

/-! ASCII classification agrees with complete iteration, including malformed UTF-8. -/

namespace JuliaLean.ChatGPT.Batch3.Group4

open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string
open _root_.JuliaLean.base.strings.basic (isasciiChar)
open _root_.JuliaLean.Proofs.base.strings.string
open _root_.JuliaLean.Proofs.base.strings.string.JuliaLean.ChatGPT.Batch2.Group5

/-- The packed representation of one byte has the byte's ASCII classification. -/
theorem StringAsciiPacked (b : UInt8) :
    isasciiChar (b.toUInt32 <<< 24) = true ↔ b.toNat < 128 := by
  have hb : b.toUInt32 < 0x100 := by
    rw [UInt32.lt_iff_toNat_lt, UInt8.toNat_toUInt32]
    exact b.toNat_lt
  have h := (_root_.JuliaLean.Proofs.base.strings.basic.isasciiChar_proven.2.2.2.2.1
    b.toUInt32 hb).2
  simpa only [UInt32.lt_iff_toNat_lt, UInt8.toNat_toUInt32,
    show (0x80 : UInt32).toNat = 128 from rfl] using h

/-- Projecting the character component commutes with the decoder's branches. -/
theorem StringAsciiIteFirst {α β : Type} (p : Prop) [Decidable p] (x y : α × β) :
    (if p then x else y).1 = if p then x.1 else y.1 := by
  split <;> rfl

/-- Continuation decoding never changes the leading byte of the packed character. -/
theorem StringAsciiContinuedTop (s : JString) (i : Index) :
    iterationTopByte
      (iterateContinued stringNcodeunits stringByteAt s i
        ((stringByteAt s i).toUInt32 <<< 24)).1
      (stringByteAt s i).toNat := by
  have h0 := iterationTopInitial (stringByteAt s i)
  have h1 := iterationTopOr _
    ((stringByteAt s (i + JuliaLean.Strings.ix 1)).toUInt32 <<< 16) _ h0
    (by
      rw [iterationShift16]
      have := UInt8.toNat_lt (stringByteAt s (i + JuliaLean.Strings.ix 1))
      omega)
  have h2 := iterationTopOr _
    ((stringByteAt s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)).toUInt32 <<< 8)
    _ h1 (by
      rw [iterationShift8]
      have := UInt8.toNat_lt
        (stringByteAt s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1))
      omega)
  have h3 := iterationTopOr _
    (stringByteAt s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1 +
      JuliaLean.Strings.ix 1)).toUInt32 _ h2 (by
      rw [UInt8.toNat_toUInt32]
      have := UInt8.toNat_lt
        (stringByteAt s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1 +
          JuliaLean.Strings.ix 1))
      omega)
  unfold iterateContinued
  simp only [Id.run, pure]
  split
  · exact h0
  · split
    · exact h0
    · split
      · exact h0
      · split
        · exact h1
        · split
          · exact h1
          · split
            · exact h2
            · split
              · exact h2
              · exact h3

/-- A non-ASCII leading byte forces the packed character to be non-ASCII. -/
theorem StringAsciiTopFalse (c : UInt32) (b : Nat)
    (htop : iterationTopByte c b) (hb : 128 ≤ b) :
    isasciiChar c = false := by
  apply _root_.JuliaLean.Proofs.base.strings.basic.isasciiChar_proven.2.2.1
  obtain ⟨r, hr, hc⟩ := htop
  change 2147483648 ≤ c.toNat
  omega

/-- A byte below 0x80 takes the single-byte branch of the public iterator. -/
theorem StringAsciiStepOfByte (s : JString) (i : Index) (c : UInt32) (next : Index)
    (hstep : stringIterate s i = some (c, next))
    (hb : (stringByteAt s i).toNat < 128) :
    isasciiChar c = true ∧ next = i + JuliaLean.Strings.ix 1 := by
  have hbetween : stringBetweenByte (stringByteAt s i) 0x80 0xf7 = false := by
    simp only [stringBetweenByte, between, UInt8.le_iff_toNat_le]
    have hlo : ¬ (0x80 : UInt8).toNat ≤ (stringByteAt s i).toNat := by
      change ¬ 128 ≤ (stringByteAt s i).toNat
      omega
    simp only [hlo, decide_false, Bool.false_and]
  unfold stringIterate iterateString at hstep
  split at hstep
  · cases hstep
  · simp only [hbetween, Bool.not_false, ite_true] at hstep
    have hp := Option.some.inj hstep
    have hc : c = (stringByteAt s i).toUInt32 <<< 24 := (congrArg Prod.fst hp).symm
    have hn : next = i + JuliaLean.Strings.ix 1 := (congrArg Prod.snd hp).symm
    refine ⟨?_, hn⟩
    rw [hc]
    exact (StringAsciiPacked (stringByteAt s i)).mpr hb

/-- ASCII iterator output identifies an ASCII source byte and advances exactly one byte. -/
theorem StringAsciiStepOfChar (s : JString) (i : Index) (c : UInt32) (next : Index)
    (hstep : stringIterate s i = some (c, next)) (hc : isasciiChar c = true) :
    (stringByteAt s i).toNat < 128 ∧ next = i + JuliaLean.Strings.ix 1 := by
  have hb : (stringByteAt s i).toNat < 128 := by
    by_cases hn : (stringByteAt s i).toNat < 128
    · exact hn
    have hge : 128 ≤ (stringByteAt s i).toNat := by omega
    have hfalse : isasciiChar c = false := by
      unfold stringIterate iterateString at hstep
      split at hstep
      · cases hstep
      · dsimp only at hstep
        split at hstep
        · have heq := congrArg Prod.fst (Option.some.inj hstep)
          dsimp only at heq
          rw [← heq]
          exact StringAsciiTopFalse _ _ (iterationTopInitial _) hge
        · have heq := congrArg Prod.fst (Option.some.inj hstep)
          dsimp only at heq
          rw [← heq]
          exact StringAsciiTopFalse _ _ (StringAsciiContinuedTop s i) hge
    rw [hfalse] at hc
    cases hc
  exact ⟨hb, (StringAsciiStepOfByte s i c next hstep hb).2⟩

/-- In the allocated string range the increment of a byte index cannot wrap. -/
theorem StringAsciiNextVal (s : JString) (i : Index)
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ s.bytes.length) :
    (i + JuliaLean.Strings.ix 1).val = i.val + 1 := by
  have hs := s.small
  change wrapInt .i64 (i.val + (JuliaLean.Strings.ix 1).val) = _
  rw [show (JuliaLean.Strings.ix 1).val = 1 by decide]
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

/-- A stopped trace in the index interval ends immediately after the final byte. -/
theorem StringAsciiStopIndex (s : JString) (i : Index)
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ s.bytes.length + 1)
    (hstop : stringIterate s i = none) : i.val = s.bytes.length + 1 := by
  by_cases hn : i.val = s.bytes.length + 1
  · exact hn
  have hin : i.val ≤ s.bytes.length := by omega
  rw [iterationInBounds s i hlo hin] at hstop
  split at hstop <;> cases hstop

/-- A successful step starting within the string or its end sentinel starts on a byte. -/
theorem StringAsciiStepIndex (s : JString) (i : Index) (c : UInt32) (next : Index)
    (hhi : i.val ≤ s.bytes.length + 1)
    (hstep : stringIterate s i = some (c, next)) : i.val ≤ s.bytes.length := by
  by_cases hn : i.val ≤ s.bytes.length
  · exact hn
  have he : i.val = s.bytes.length + 1 := by omega
  rw [iterationEnd s i he] at hstep
  cases hstep

/-- For any complete trace, an ASCII suffix of characters is exactly an ASCII suffix of bytes. -/
theorem StringAsciiTraceAll (s : JString) {i : Index}
    {rows : List (Index × UInt32 × Index)} (trace : IterTrace stringIterate s i rows) :
    1 ≤ i.val → i.val ≤ s.bytes.length + 1 →
      (rows.all (fun row => isasciiChar row.2.1) = true ↔
        ∀ k : Nat, i.val ≤ (k : Int) + 1 → k < s.bytes.length →
          (s.bytes.getD k 0).toNat < 128) := by
  induction trace with
  | @stop i hstop =>
      intro hlo hhi
      have he := StringAsciiStopIndex s i hlo hhi hstop
      constructor
      · intro _ k hk hkn
        omega
      · intro _
        rfl
  | @step i c next rows hstep htail ih =>
      intro hlo hhi
      have hin := StringAsciiStepIndex s i c next hhi hstep
      constructor
      · intro hall
        change (isasciiChar c && rows.all (fun row => isasciiChar row.2.1)) = true at hall
        obtain ⟨hc, hrows⟩ := Bool.and_eq_true_iff.mp hall
        obtain ⟨hb, hn⟩ := StringAsciiStepOfChar s i c next hstep hc
        have hval : next.val = i.val + 1 := by
          rw [hn]
          exact StringAsciiNextVal s i hlo hin
        have hrest := (ih (by omega) (by omega)).mp hrows
        intro k hk hkn
        by_cases he : (k : Int) + 1 = i.val
        · have hindex : i.val.toNat - 1 = k := by omega
          simpa only [stringByteAt, hindex] using hb
        · exact hrest k (by omega) hkn
      · intro hbytes
        have hb : (stringByteAt s i).toNat < 128 := by
          unfold stringByteAt
          exact hbytes (i.val.toNat - 1) (by omega) (by omega)
        obtain ⟨hc, hn⟩ := StringAsciiStepOfByte s i c next hstep hb
        have hval : next.val = i.val + 1 := by
          rw [hn]
          exact StringAsciiNextVal s i hlo hin
        change (isasciiChar c && rows.all (fun row => isasciiChar row.2.1)) = true
        apply Bool.and_eq_true_iff.mpr
        refine ⟨hc, (ih (by omega) (by omega)).mpr ?_⟩
        intro k hk hkn
        exact hbytes k (by omega) hkn

/-- One-based access to the byte vector corresponds to zero-based list access. -/
theorem StringAsciiByteListGet (bytes : List UInt8) (k : Nat) :
    byteListGet bytes (1 + (k : Int)) = bytes.getD k 0 := by
  unfold byteListGet
  have hindex : (1 + (k : Int)).toNat - 1 = k := by omega
  rw [hindex]

/-- The public String ASCII test checks all and only the allocated source bytes. -/
theorem StringAsciiSourceAll (s : JString) :
    stringIsascii s = true ↔
      ∀ k : Nat, k < s.bytes.length → (s.bytes.getD k 0).toNat < 128 := by
  unfold stringIsascii _root_.JuliaLean.base.strings.string.isasciiString byteListIsAscii
  by_cases hempty : s.bytes.length = 0
  · simp only [hempty]
    constructor
    · intro _ k hk
      omega
    · intro _
      rfl
  · have hn : ¬ (1 : Int) > (s.bytes.length : Int) := by omega
    have hcount : ((s.bytes.length : Int) - 1 + 1).toNat = s.bytes.length := by omega
    simp only [Int.ofNat_eq_natCast, hn, ite_false, hcount, List.all_eq_true, List.mem_range,
      StringAsciiByteListGet, decide_eq_true_eq]

/-- strings-ascii-agreement: A String is ASCII exactly when every iterated character is ASCII. -/
theorem StringsAsciiAgreement_proven :
    _root_.JuliaLean.Proofs.base.strings.string.Round2.AsciiMatchesIteratedCharacters := by
  intro s
  obtain ⟨rows, htrace, _⟩ := iterationComplete s
  refine ⟨rows, htrace, ?_⟩
  apply Bool.eq_iff_iff.mpr
  have hfirst : (JuliaLean.Strings.ix 1).val = 1 := by decide
  have htraceAll := StringAsciiTraceAll s htrace
    (by rw [hfirst]; omega) (by rw [hfirst]; omega)
  rw [StringAsciiSourceAll, htraceAll]
  constructor
  · intro h k _ hk
    exact h k hk
  · intro h k hk
    exact h k (by rw [hfirst]; omega) hk

end JuliaLean.ChatGPT.Batch3.Group4
section




namespace JuliaLean.ChatGPT.Batch4.Group11
open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string

theorem memoryStringBytes (memory : Memory) empty memoryLength memoryToString
    (hempty : empty memory = true → memory.bytes = [])
    (hfull : empty memory = false →
      (memoryToString memory (memoryLength memory)).bytes = memory.bytes) :
    (unsafeTakestring empty memoryLength memoryToString memory).bytes = memory.bytes := by
  cases h : empty memory with
  | false => simp only [unsafeTakestring, h, Bool.false_eq_true, ite_false]; exact hfull h
  | true => simp only [unsafeTakestring, h, ite_true, JuliaLean.Strings.JStr.empty]; exact (hempty h).symm

theorem simpleModelStringsCodeunitType :
  codeunitType = UInt8 := by
  rfl

theorem simpleModelStringsByteLength :
  ∀ s, stringNcodeunits s = JuliaLean.Strings.ix (Int.ofNat s.bytes.length) := by
  intro s
  rfl

theorem simpleModelStringsPointerOffsets :
  ∀ s i, pointerAt stringUnsafeConvert (fun i : Index => i.val) s i =
    pointerString stringUnsafeConvert s + i.val - 1 := by
  intro s i
  rfl

theorem simpleModelStringsStringTypemin :
  typeminStringType = JuliaLean.Strings.JStr.empty ∧
    ∀ s, typeminString typeminStringType s = JuliaLean.Strings.JStr.empty := by
  exact ⟨rfl, fun _ => rfl⟩

theorem simpleModelStringsStringviewConstruction :
  ∀ {α : Type} (requireOneBased : α → StringResult Unit) concrete data,
    match requireOneBased data with
    | .error e => stringViewCtor requireOneBased concrete data = .error e
    | .ok _ =>
      if concrete then
        ∃ view, stringViewCtor requireOneBased concrete data = .ok view ∧ view.data = data
      else
        stringViewCtor requireOneBased concrete data =
          .error (.jl (.argumentError "StringView must be parameterized with a concrete type")) := by
  intro α require concrete data
  cases h : require data with
  | error e =>
      simp only [stringViewCtor, h, bind, Except.bind]
  | ok result =>
      cases result
      cases concrete <;>
        simp only [stringViewCtor, h, bind, Except.bind, Bool.not_false,
          Bool.not_true, Bool.false_eq_true, ite_true, ite_false, pure, Except.pure]
      exact ⟨⟨data⟩, rfl, rfl⟩

theorem simpleModelStringsIndexErrorDisplay :
  ∀ (print : List String → List String → List String)
    (firstindex : JString → Index)
    (isEmptyRange : Index → Index → Bool)
    (checkbounds : JString → Index → Index → StringResult Unit)
    (toCsize : JInt .u64 → StringResult Nat)
    (allocateString : Nat → StringResult JString) (toInt : Index → Int)
    (preserve : JString → JString → (Unit → JString) → JString)
    (unsafeCopyTo : Int → Int → Nat → JString → JString)
    (escapeString : JString → String) (toString : Index → String)
    (io : List String) (s : JString) (index : Index),
    showStringIndexError print firstindex stringNcodeunits stringThisind stringNextind
      (stringGetindexRange isEmptyRange checkbounds toCsize allocateString toInt preserve unsafeCopyTo)
      escapeString toString io s index = (do
        let output := print io ["StringIndexError: ", "invalid index [", toString index, "]"]
        if firstindex s ≤ index && index ≤ stringNcodeunits s then
          let iprev ← stringThisind s index
          let inext ← stringNextind s iprev
          let previous ← stringGetindexRange isEmptyRange checkbounds toCsize allocateString
            toInt preserve unsafeCopyTo s iprev iprev
          let previousText := escapeString previous
          if inext ≤ stringNcodeunits s then
            let next ← stringGetindexRange isEmptyRange checkbounds toCsize allocateString
              toInt preserve unsafeCopyTo s inext inext
            pure (print output [", valid nearby indices [", toString iprev, "]=>'",
              previousText, "', [", toString inext, "]=>'", escapeString next, "'"])
          else
            pure (print output [", valid nearby index [", toString iprev, "]=>'",
              previousText, "'"])
        else
          pure output) := by
  intros
  rfl

theorem simpleModelStringsStringFromAbstract :
  ∀ {S : Type} (printToString : S → JString) (bytes : S → List UInt8) (s : S),
    (printToString s).bytes = bytes s →
      (stringAbstractString printToString s).bytes = bytes s := by
  intro S printToString bytes s h
  exact h

theorem simpleModelStringsSymbolString :
  ∀ {S : Type} (unsafeConvert : S → Int) null
    (pointerBytes : Int → List UInt8) (pointerToCString : Int → JString) (s : S),
    (∀ pointer, (pointerToCString pointer).bytes =
      (pointerBytes pointer).takeWhile (fun byte => byte != 0)) →
    let pointer := unsafeConvert s
    if pointer = null then
      stringSymbol unsafeConvert null pointerToCString s =
        .error (.jl (.argumentError "cannot convert NULL to string"))
    else
      ∃ result, stringSymbol unsafeConvert null pointerToCString s = .ok result ∧
        result.bytes = (pointerBytes pointer).takeWhile (fun byte => byte != 0) := by
  intro S toPointer null pointerBytes pointerToCString s h
  dsimp only
  by_cases hp : toPointer s = null
  · simp only [hp, ite_true, stringSymbol, unsafeStringNul,
      StringNullPointer.isNull, beq_self_eq_true, StringNulCall.nullError]
  · rw [ite_eq_right hp]
    exact ⟨pointerToCString (toPointer s), by
      simp only [stringSymbol, unsafeStringNul, StringNullPointer.isNull,
        beq_eq_false_iff_ne.mpr hp, Bool.false_eq_true, ite_false, StringNulCall.lift], h _⟩

theorem simpleModelStringsUnsafeStringLengthCopiesBytes :
  ∀ {I : Type} (toInt : I → Index) null
    (pointerBytes : Int → Nat → List UInt8)
    (pointerToString : Int → Index → JString) (pointer : Int) (len : I),
    (∀ address count, (pointerToString address count).bytes =
      pointerBytes address count.val.toNat) →
    pointer ≠ null →
    ∃ result, unsafeStringLength toInt null pointerToString pointer len = .ok result ∧
      result.bytes = pointerBytes pointer (toInt len).val.toNat := by
  intro I toInt null pointerBytes pointerToString pointer len h hp
  refine ⟨pointerToString pointer (toInt len), ?_, h _ _⟩
  simp only [unsafeStringLength, beq_eq_false_iff_ne.mpr hp, Bool.false_eq_true, ite_false]

theorem simpleModelStringsUnsafeStringNulPrefix :
  ∀ null (pointerBytes : Int → List UInt8) (pointerToCString : Int → JString)
    (pointer : Int),
    (∀ address, (pointerToCString address).bytes =
      (pointerBytes address).takeWhile (fun byte => byte != 0)) →
    pointer ≠ null →
    (unsafeStringNul null pointerToCString pointer).map (fun string => string.bytes) =
      .ok ((pointerBytes pointer).takeWhile (fun byte => byte != 0)) := by
  intro null pointerBytes pointerToCString pointer h hp
  simp only [unsafeStringNul, StringNullPointer.isNull,
    beq_eq_false_iff_ne.mpr hp, Bool.false_eq_true, ite_false, StringNulCall.lift,
    Except.map, h]

theorem simpleModelStringsUnsafeStringNull :
  ∀ {I : Type} (toInt : I → Index) null pointerToString pointerToCString len,
    unsafeStringLength toInt null pointerToString null len =
      .error (.jl (.argumentError "cannot convert NULL to string")) ∧
    unsafeStringNul null pointerToCString null =
      .error (.jl (.argumentError "cannot convert NULL to string")) := by
  intro I toInt null pointerToString pointerToCString len
  simp only [unsafeStringLength, unsafeStringNul, StringNullPointer.isNull,
    beq_self_eq_true, ite_true, StringNulCall.nullError, and_self]

theorem simpleModelStringsAbstractvectorConstruction :
  ∀ (v : ByteVector) allocate copyTo empty memoryLength memoryToString,
    let memory := copyTo (allocate v.length) v
    memory.bytes = v.bytes →
    (empty memory = true → memory.bytes = []) →
    (empty memory = false → (memoryToString memory (memoryLength memory)).bytes = memory.bytes) →
    (stringAbstractVector (fun vector : ByteVector => vector.length) allocate copyTo
      empty memoryLength memoryToString v).bytes = v.bytes := by
  intro v allocate copyTo empty memoryLength memoryToString
  dsimp only
  intro hbytes hempty hfull
  exact (memoryStringBytes _ empty memoryLength memoryToString hempty hfull).trans hbytes

theorem simpleModelStringsVectorTransfer :
  ∀ (v : ByteVector) genericMemoryToString pointerToString emptyMemoryRef,
    let result := stringVector genericMemoryToString pointerToString emptyMemoryRef v
    if v.length = 0 then
      result.string.bytes = [] ∧ result.vector.length = v.length ∧ result.sharedStorage = none
    else
      result.vector.length = 0 ∧ result.vector.ref = emptyMemoryRef ∧
        (if v.ref.ptrOrOffset = v.ref.mem.pointer then
          ∃ memory, result.sharedStorage = some memory ∧ memory.pointer = v.ref.mem.pointer
        else result.sharedStorage = none) := by
  intro v genericMemoryToString pointerToString emptyMemoryRef
  dsimp only
  by_cases hz : v.length = 0
  · simp only [hz, ite_true, stringVector, beq_self_eq_true, JuliaLean.Strings.JStr.empty,
      Id.run, pure, bind, and_self]
  · simp only [ite_eq_right hz]
    by_cases hp : v.ref.ptrOrOffset = v.ref.mem.pointer
    · simp only [stringVector, beq_eq_false_iff_ne.mpr hz, Bool.false_eq_true, ite_false,
        beq_iff_eq, hp, ite_true, Id.run, pure, bind]
      exact ⟨True.intro, True.intro, ⟨v.ref.mem, rfl, rfl⟩⟩
    · simp only [stringVector, beq_eq_false_iff_ne.mpr hz, Bool.false_eq_true, ite_false,
        beq_eq_false_iff_ne.mpr hp, ite_eq_right hp, Id.run, pure, bind]
      exact ⟨True.intro, True.intro, True.intro⟩

theorem simpleModelStringsStorageConversions :
  (∀ (s : JString) (stringToMemory : JString → Memory),
    (stringToMemory s).bytes = s.bytes →
    (unsafeWrapMemory stringToMemory s).bytes = s.bytes) ∧
  (∀ (s : JString) (stringToMemory : JString → Memory)
      (wrapArray : Memory → ByteVector),
    (stringToMemory s).bytes = s.bytes →
    (∀ memory, (wrapArray memory).bytes = memory.bytes) →
    (unsafeWrapVector stringToMemory wrapArray s).bytes = s.bytes) ∧
  (∀ {C : Type} (bytesOf : C → List UInt8) (length : C → Nat)
      (allocate : Nat → ByteVector) (copyTo : ByteVector → C → ByteVector) (source : C),
    length source = (bytesOf source).length →
    (∀ destination value, (copyTo destination value).bytes = bytesOf value) →
    (vectorCodeUnits length allocate copyTo source).bytes = bytesOf source) ∧
  (∀ (s : JString) (codeunits : JString → List UInt8)
      (length : List UInt8 → Nat) (allocate : Nat → ByteVector)
      (copyTo : ByteVector → List UInt8 → ByteVector),
    codeunits s = s.bytes →
    (∀ destination value, (copyTo destination value).bytes = value) →
    (vectorString codeunits length allocate copyTo s).bytes = s.bytes) ∧
  (∀ (vectorString : JString → ByteVector) (s : JString),
    (vectorString s).bytes = s.bytes →
    (arrayString vectorString s).bytes = s.bytes) ∧
  (∀ {C : Type} (parent : C → JString) (bytesOf : C → List UInt8) (s : C),
    (parent s).bytes = bytesOf s →
    (stringCodeUnits parent s).bytes = bytesOf s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s stringToMemory h
    exact h
  · intro s stringToMemory wrapArray hmem hwrap
    exact (hwrap _).trans hmem
  · intro C bytesOf length allocate copyTo source hlen hcopy
    exact hcopy _ _
  · intro s codeunits length allocate copyTo hcode hcopy
    exact (hcopy _ _).trans hcode
  · intro vectorString s h
    exact h
  · intro C parent bytesOf s h
    exact h

theorem simpleModelStringsStringEqualityBytes :
  ∀ (same : JString → JString → Bool) (a b : JString),
    same a b = decide (a.bytes = b.bytes) →
    eqString same a b = decide (a.bytes = b.bytes) := by
  intro same a b h
  exact h

end JuliaLean.ChatGPT.Batch4.Group11


namespace JuliaLean.ChatGPT.Batch4.Group11
open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string

theorem scalarLengthValue (s : JString) : (stringNcodeunits s).val = (s.bytes.length : Int) := by
  change wrapInt .i64 (s.bytes.length : Int) = _
  apply wrapInt_of_inRange
  have hs := s.small
  change -9223372036854775808 ≤ (s.bytes.length : Int) ∧ (s.bytes.length : Int) ≤ 9223372036854775807
  omega

theorem scalarValidBounds (s : JString) (i : Index)
    (hv : stringIsvalidIndex s i = true) : 1 ≤ i.val ∧ i.val ≤ (s.bytes.length : Int) := by
  unfold stringIsvalidIndex isvalidStringIndex at hv
  have hc := (Bool.and_eq_true_iff.mp hv).1
  simpa only [stringCheckboundsBool, Bool.and_eq_true, decide_eq_true_eq] using hc

theorem scalarUnsignedPositive (i : Index) (h1 : 1 ≤ i.val) :
    (JInt.rem .u64 i - JInt.lit .u64 1).val = i.val - 1 := by
  have hi := i.property
  change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807 at hi
  have hu : (JInt.rem .u64 i).val = i.val := by
    change wrapInt .u64 i.val = i.val
    apply wrapInt_of_inRange
    change 0 ≤ i.val ∧ i.val ≤ 18446744073709551615
    omega
  change wrapInt .u64 ((JInt.rem .u64 i).val - (JInt.lit .u64 1).val) = _
  rw [hu, show (JInt.lit .u64 1).val = 1 by decide]
  apply wrapInt_of_inRange
  change 0 ≤ i.val - 1 ∧ i.val - 1 ≤ 18446744073709551615
  omega

theorem scalarIterationAt (s : JString) (i : Index) (h1 : 1 ≤ i.val)
    (hn : i.val ≤ (s.bytes.length : Int)) :
    stringIterate s i =
      if !stringBetweenByte (stringByteAt s i) 0x80 0xf7 then
        some ((stringByteAt s i).toUInt32 <<< 24, i + JuliaLean.Strings.ix 1)
      else some (iterateContinued stringNcodeunits stringByteAt s i
        ((stringByteAt s i).toUInt32 <<< 24)) := by
  unfold stringIterate iterateString
  rw [scalarUnsignedPositive i h1, scalarLengthValue]
  simp only [show i.val - 1 < (s.bytes.length : Int) by omega, decide_true,
    Bool.not_true, Bool.false_eq_true, ite_false]

theorem scalarCheckedByte (s : JString) (i : Index) (h1 : 1 ≤ i.val)
    (hn : i.val ≤ (s.bytes.length : Int)) : stringCodeunit s i = .ok (stringByteAt s i) := by
  have hc : stringCheckbounds s i = .ok () := by
    simp only [stringCheckbounds, h1, hn, decide_true, Bool.true_and, ite_true]
  have hi : (i.val - 1).toNat = i.val.toNat - 1 := by omega
  simp only [stringCodeunit, codeunitInteger, codeunitInt, hc, ite_true,
    bind, Except.bind, pure, Except.pure, stringPreserveByte, stringUnsafeLoad,
    pointerAt, pointerString, stringUnsafeConvert, Int.zero_add, hi, stringByteAt]

/-- The scalar decoder and iterator construct the same packed character. -/
theorem scalarContinuedFirst {S : Type} (isvalid : S → Index → Bool)
    (ncodeunits : S → Index) (codeunit : S → Index → UInt8)
    (s : S) (i : Index) (u : UInt32) (hv : isvalid s i = true) :
    getindexContinued isvalid ncodeunits codeunit s i u =
      .ok (iterateContinued ncodeunits codeunit s i u).1 := by
  unfold getindexContinued iterateContinued
  simp only [hv, ite_true, pure, Except.pure, bind, Except.bind, Id.run]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split <;> rfl

theorem scalarGetindexModel (s : JString) (i : Index)
    (hv : stringIsvalidIndex s i = true) :
    ∃ c next, stringIterate s i = some (c, next) ∧ stringGetindex s i = .ok c := by
  obtain ⟨h1, hn⟩ := scalarValidBounds s i hv
  have hb := scalarCheckedByte s i h1 hn
  rw [scalarIterationAt s i h1 hn]
  unfold stringGetindex getindexString
  rw [hb]
  simp only [bind, Except.bind]
  by_cases hc : (!stringBetweenByte (stringByteAt s i) 0x80 0xf7) = true
  · simp only [hc, ite_true, pure, Except.pure]
    exact ⟨_, _, rfl, rfl⟩
  · simp only [hc, ite_false]
    rw [scalarContinuedFirst _ _ _ s i _ hv]
    exact ⟨_, _, congrArg some (Prod.eta _).symm, rfl⟩

def scalarStorageByte (bytes : List UInt8) (i : Int) : Option UInt8 :=
  if i < 1 then none else bytes[(i - 1).toNat]?

theorem scalarCodeunitDomain :
    ∀ (s : JString) (i : Index), stringCodeunit s i =
      match scalarStorageByte s.bytes i.val with
      | some b => .ok b
      | none => .error (.jl .boundsError) := by
  intro s i
  by_cases hlo : i.val < 1
  · have hnot : ¬ 1 ≤ i.val := by omega
    simp only [scalarStorageByte, hlo, ite_true, stringCodeunit, codeunitInteger,
      codeunitInt, stringCheckbounds, hnot, decide_false, Bool.false_and,
      Bool.false_eq_true, ite_false, ite_true, bind, Except.bind]
  · have h1 : 1 ≤ i.val := by omega
    by_cases hhi : i.val ≤ (s.bytes.length : Int)
    · have hk : (i.val - 1).toNat < s.bytes.length := by omega
      have hcode := scalarCheckedByte s i h1 hhi
      rw [hcode]
      simp only [scalarStorageByte, hlo, ite_false, List.getElem?_eq_getElem hk]
      congr 1
      unfold stringByteAt
      have he : i.val.toNat - 1 = (i.val - 1).toNat := by omega
      rw [he]
      exact List.getD_eq_getElem?_getD.trans (by rw [List.getElem?_eq_getElem hk]; rfl)
    · have hk : s.bytes.length ≤ (i.val - 1).toNat := by omega
      simp only [scalarStorageByte, hlo, ite_false, List.getElem?_eq_none hk,
        stringCodeunit, codeunitInteger, codeunitInt, stringCheckbounds, h1, hhi,
        decide_true, decide_false, Bool.true_and, Bool.false_eq_true, ite_false,
        ite_true, bind, Except.bind]

end JuliaLean.ChatGPT.Batch4.Group11


namespace JuliaLean.ChatGPT.Batch4.Group11
open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string
open _root_.JuliaLean.Proofs.base.strings.string

local macro "group11OriginalSeek" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JuliaLean.base.strings.string
    `JuliaLean.base.strings.string.lengthSeekLead))
local macro "group11OriginalCount" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JuliaLean.base.strings.string
    `JuliaLean.base.strings.string.lengthCountLoop))

abbrev lengthSeekModel {S : Type} (codeunit : S → Index → UInt8)
    (s : S) (n : Index) (fuel : Nat) (i : Index) (b : UInt8) :=
  group11OriginalSeek codeunit s n fuel i b
abbrev lengthCountModel {S : Type} (codeunit : S → Index → UInt8)
    (s : S) (n : Index) (fuel : Nat) (i : Index) (b : UInt8) (c : Index) :=
  group11OriginalCount codeunit s n fuel i b c

theorem lengthSeekModel_step {S : Type} (codeunit : S → Index → UInt8)
    (s : S) (n : Index) (fuel : Nat) (i : Index) (b : UInt8) :
    lengthSeekModel codeunit s n (fuel + 1) i b =
      (let i := i + JuliaLean.Strings.ix 1
       if i.val > n.val then none
       else if 0xc0 ≤ b && b ≤ 0xf7 then some (i, b)
       else lengthSeekModel codeunit s n fuel i (codeunit s i)) := by
  rfl

theorem lengthCountModel_step {S : Type} (codeunit : S → Index → UInt8)
    (s : S) (n : Index) (fuel : Nat) (i : Index) (b : UInt8) (count : Index) :
    lengthCountModel codeunit s n (fuel + 1) i b count =
      (match lengthSeekModel codeunit s n fuel i b with
      | none => count
      | some (i, lead) =>
          let b := codeunit s i
          let firstIsContinuation := isValidContinuation b
          let count := count - stringIndexBool firstIsContinuation
          if !(firstIsContinuation && lead ≥ 0xe0) then
            lengthCountModel codeunit s n fuel i b count
          else
            let i := i + JuliaLean.Strings.ix 1
            if i.val > n.val then count
            else
              let b := codeunit s i
              let secondIsContinuation := isValidContinuation b
              let count := count - stringIndexBool secondIsContinuation
              if !(secondIsContinuation && lead ≥ 0xf0) then
                lengthCountModel codeunit s n fuel i b count
              else
                let i := i + JuliaLean.Strings.ix 1
                if i.val > n.val then count
                else
                  let b := codeunit s i
                  lengthCountModel codeunit s n fuel i b
                    (count - stringIndexBool (isValidContinuation b))) := by
  rfl

theorem lengthSeekModel_congr {S T : Type} (f : S → Index → UInt8)
    (g : T → Index → UInt8) (s : S) (t : T)
    (h : ∀ k, f s k = g t k) (n : Index) (fuel : Nat) (i : Index) (b : UInt8) :
    lengthSeekModel f s n fuel i b = lengthSeekModel g t n fuel i b := by
  induction fuel generalizing i b with
  | zero => rfl
  | succ fuel ih =>
    simp only [lengthSeekModel_step, h, ih]

theorem lengthCountModel_congr {S T : Type} (f : S → Index → UInt8)
    (g : T → Index → UInt8) (s : S) (t : T)
    (h : ∀ k, f s k = g t k) (n : Index) (fuel : Nat) (i : Index) (b : UInt8) (c : Index) :
    lengthCountModel f s n fuel i b c = lengthCountModel g t n fuel i b c := by
  induction fuel generalizing i b c with
  | zero => rfl
  | succ fuel ih =>
    simp only [lengthCountModel_step, lengthSeekModel_congr f g s t h, h, ih]

theorem lengthContinuedInternal_congr {S T : Type} (f : S → Index → UInt8)
    (g : T → Index → UInt8) (s : S) (t : T)
    (h : ∀ k, f s k = g t k) (i n c : Index) :
    lengthContinuedInternal f s i n c = lengthContinuedInternal g t i n c := by
  change (if !(i.val < n.val) then c else
      lengthCountModel f s n (n.val - i.val + 1).toNat i (f s i) c) =
    (if !(i.val < n.val) then c else
      lengthCountModel g t n (n.val - i.val + 1).toNat i (g t i) c)
  rw [h, lengthCountModel_congr f g s t h]

theorem StringscovaStringLengthViewRebuilt_proven : JuliaLean.Proofs.base.strings.string.LengthViewAgreement := by
  intro s
  change lengthContinuedInternal (fun bytes i => byteListGet bytes i.val) s.bytes
      (JuliaLean.Strings.ix 1) (stringNcodeunits s) (stringNcodeunits s) =
    lengthContinuedInternal stringByteAt s
      (JuliaLean.Strings.ix 1) (stringNcodeunits s) (stringNcodeunits s)
  exact lengthContinuedInternal_congr _ _ s.bytes s (fun _ => rfl) _ _ _

theorem StringsLengthViewAgreement_proven : JuliaLean.Proofs.base.strings.string.LengthViewAgreement := by
  exact StringscovaStringLengthViewRebuilt_proven

end JuliaLean.ChatGPT.Batch4.Group11


namespace JuliaLean.ChatGPT.Batch4.Group11
open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string

/-- A successful checked scalar read inherits the checked byte reader's bounds. -/
theorem checkedScalarAccessBounds
    (isvalid : StringView (List UInt8) → Index → Bool)
    (ncodeunits : StringView (List UInt8) → Index)
    (codeunit : StringView (List UInt8) → Index → UInt8)
    (checkedCodeunit : StringView (List UInt8) → Index → StringResult UInt8)
    (view : StringView (List UInt8)) (i : Index) (result : UInt32)
    (hcheck : ∀ value byte read, checkedCodeunit value byte = .ok read →
      1 ≤ byte.val ∧ byte.val ≤ (ncodeunits value).val)
    (hresult : getindexString isvalid ncodeunits codeunit checkedCodeunit
      stringBetweenByte view i = .ok result) :
    1 ≤ i.val ∧ i.val ≤ (ncodeunits view).val := by
  unfold getindexString at hresult
  cases hread : checkedCodeunit view i with
  | error e => simp only [hread, bind, Except.bind] at hresult; cases hresult
  | ok b => exact hcheck view i b hread

/-- No JString-valued callback can return every natural-number byte length. -/
theorem universalCopyLengthImpossible (copy : Int → Int → Nat → JString → JString) :
    ¬ (∀ destination source amount initial,
      (copy destination source amount initial).bytes.length = amount) := by
  intro h
  have hlen := h 0 0 (2 ^ 62) JuliaLean.Strings.JStr.empty
  have hsmall := (copy 0 0 (2 ^ 62) JuliaLean.Strings.JStr.empty).small
  rw [hlen] at hsmall
  exact Nat.lt_irrefl _ hsmall

/-- Exact frozen target; its universal copy-length premise is inconsistent.
This is a logical closure, and does not establish the intended runtime bounds claim. -/
theorem modelMemsafetyStringRangeCopy :
  ∀ (isEmptyRange : Index → Index → Bool)
    (checkbounds : JString → Index → Index → StringResult Unit)
    (toCsize : JInt .u64 → StringResult Nat)
    (allocateString : Nat → StringResult JString) (toInt : Index → Int)
    (preserve : JString → JString → (Unit → JString) → JString)
    (unsafeCopyTo : Int → Int → Nat → JString → JString)
    (s : JString) (i j next : Index) (size : Nat) (allocated output : JString),
    isEmptyRange i j = false →
    checkbounds s i j = .ok () →
    stringIsvalidIndex s i = true →
    stringIsvalidIndex s j = true →
    nextindString stringNcodeunits stringBetweenIndex stringBetweenByte stringCodeunitAt
      s j = .ok next →
    let count := JInt.rem .u64 (next - JuliaLean.Strings.ix 1 - i + JuliaLean.Strings.ix 1)
    toCsize count = .ok size →
    allocateString size = .ok allocated →
    allocated.bytes.length = size →
    (∀ destination source amount initial,
      (unsafeCopyTo destination source amount initial).bytes.length = amount) →
    (∀ source destination write, preserve source destination write = write ()) →
    stringGetindexRange isEmptyRange checkbounds toCsize allocateString toInt preserve
      unsafeCopyTo s i j = .ok output →
    output.bytes.length = count.val.toNat ∧
      1 ≤ i.val ∧ i.val ≤ next.val ∧ next.val ≤ (stringNcodeunits s).val + 1 := by
  intro isEmptyRange checkbounds toCsize allocateString toInt preserve copy
    s i j next size allocated output hempty hbounds hvalidI hvalidJ hnext
  dsimp only
  intro hsize hallocate hallocatedLength hcopy hpreserve hresult
  exact False.elim (universalCopyLengthImpossible copy hcopy)

end JuliaLean.ChatGPT.Batch4.Group11

namespace JuliaLean.ChatGPT.Batch4.Group11
open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string

/-- Three bytes written to a fresh IOBuffer before retaining a reshaped alias. -/
def aliasBytes : List UInt8 := [0x61, 0x62, 0x63]
def aliasString : JString := ⟨aliasBytes, by decide⟩
def aliasMemory (address : Int) : Memory := ⟨address, 3, false, aliasBytes⟩
def aliasVector (address : Int) : ByteVector :=
  ⟨3, ⟨address, aliasMemory address⟩, aliasBytes⟩
/-- Concrete allocation addresses recorded by the exact pinned Julia diagnostic. -/
def aliasInputAddress : Int := 139709294024824
def aliasEmptyAddress : Int := 139709496169024
def aliasEmptyRef : VectorRef :=
  ⟨aliasEmptyAddress, ⟨aliasEmptyAddress, 0, true, []⟩⟩

/-- The storage marker is independent of the address and all runtime callbacks. -/
theorem aliasTransferShared (address : Int)
    (genericMemoryToString : Memory → Nat → JString)
    (pointerToString : VectorRef → Nat → JString) (emptyMemoryRef : VectorRef) :
    (stringVector genericMemoryToString pointerToString
      emptyMemoryRef (aliasVector address)).sharedStorage = some (aliasMemory address) := by
  simp only [stringVector, aliasVector, aliasMemory, beq_self_eq_true,
    show (3 == 0) = false from rfl, Bool.false_eq_true, ite_false, ite_true,
    Id.run, pure, bind]

theorem modelAliasRefutation :
    ¬ (∀ (v : ByteVector) genericMemoryToString pointerToString emptyMemoryRef,
      (stringVector genericMemoryToString pointerToString emptyMemoryRef v).sharedStorage = none) := by
  intro h
  have hshared := h (aliasVector aliasInputAddress) (fun _ _ => aliasString)
    (fun _ _ => aliasString) aliasEmptyRef
  rw [aliasTransferShared] at hshared
  cases hshared

end JuliaLean.ChatGPT.Batch4.Group11


namespace JuliaLean.ChatGPT.Batch4.Group11
open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string
open _root_.JuliaLean.Proofs.base.strings.string

def standaloneContinuation : JString := ⟨[0x80], by decide⟩

/-- A malformed-byte character still has a valid start at byte one. -/
theorem standaloneContinuationValid :
    stringIsvalidIndex standaloneContinuation (JuliaLean.Strings.ix 1) = true := by
  decide

theorem standaloneContinuationMask :
    ((stringByteAt standaloneContinuation (JuliaLean.Strings.ix 1) &&& 0xc0) != 0x80) = false := by
  decide

/-- The stale mask-based range count omits this actual one-byte character. -/
theorem standaloneContinuationRange :
    stringLengthRange standaloneContinuation (JuliaLean.Strings.ix 1)
      (JuliaLean.Strings.ix 1) = .ok (JuliaLean.Strings.ix 1) ∧
    nonContinuationCount stringByteAt standaloneContinuation (JuliaLean.Strings.ix 1)
      (JuliaLean.Strings.ix 1) = 0 := by
  decide

end JuliaLean.ChatGPT.Batch4.Group11


namespace JuliaLean.ChatGPT.Batch4.Group11

open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string

def iterationReviewView : StringView (List UInt8) := ⟨[0x80]⟩

theorem iterationReviewViewStep :
    stringViewIterate iterationReviewView (JuliaLean.Strings.ix 1) =
      some (0x80000000, JuliaLean.Strings.ix 2) := by decide

theorem iterationReviewViewStop :
    stringViewIterate iterationReviewView (JuliaLean.Strings.ix 2) = none := by decide

/-- Direct evaluation of the frozen view-index predicate on the one-byte witness. -/
theorem iterationReviewViewPredicate :
    (1 ≤ (JuliaLean.Strings.ix 1).val &&
      (JuliaLean.Strings.ix 1).val ≤ Int.ofNat iterationReviewView.data.length &&
      (stringViewByteAt iterationReviewView (JuliaLean.Strings.ix 1) &&& 0xc0) != 0x80) = false := by
  decide

/-- The exact filtered-enumeration expression from the frozen view conjunct, specialized here. -/
theorem iterationReviewViewFilter :
    ((List.range (stringViewNcodeunits iterationReviewView).val.toNat).map
      (fun i => JuliaLean.Strings.ix (Int.ofNat (i + 1))) |>.filter
        (fun i => 1 ≤ i.val && i.val ≤ Int.ofNat iterationReviewView.data.length &&
          (stringViewByteAt iterationReviewView i &&& 0xc0) != 0x80)) = [] := by
  decide

end JuliaLean.ChatGPT.Batch4.Group11


namespace JuliaLean.ChatGPT.Batch4.Group11
open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string
open _root_.JuliaLean.Proofs.base.strings.string

theorem StringsCodeunitType_proven : JuliaLean.Proofs.base.strings.string.CodeunitTypeUInt8 :=
  simpleModelStringsCodeunitType

theorem StringsByteLength_proven : JuliaLean.Proofs.base.strings.string.ByteLengthMatchesStorage :=
  simpleModelStringsByteLength

theorem StringsPointerOffsets_proven : JuliaLean.Proofs.base.strings.string.StringPointerOffsets :=
  simpleModelStringsPointerOffsets

theorem StringsStringTypemin_proven : JuliaLean.Proofs.base.strings.string.StringTypeminEmpty :=
  simpleModelStringsStringTypemin

theorem StringsStringviewConstruction_proven : JuliaLean.Proofs.base.strings.string.StringViewConstruction :=
  simpleModelStringsStringviewConstruction

theorem StringsIndexErrorDisplay_proven : JuliaLean.Proofs.base.strings.string.StringIndexErrorDisplay :=
  simpleModelStringsIndexErrorDisplay

theorem StringsStringFromAbstract_proven : JuliaLean.Proofs.base.strings.string.StringFromAbstractStringBytes :=
  simpleModelStringsStringFromAbstract

theorem StringsSymbolString_proven : JuliaLean.Proofs.base.strings.string.StringSymbolConversion :=
  simpleModelStringsSymbolString

theorem StringsUnsafeStringLengthCopiesBytes_proven : JuliaLean.Proofs.base.strings.string.UnsafeStringLengthCopiesBytes :=
  simpleModelStringsUnsafeStringLengthCopiesBytes

theorem StringsUnsafeStringNulPrefix_proven : JuliaLean.Proofs.base.strings.string.UnsafeStringNulCopiesPrefix :=
  simpleModelStringsUnsafeStringNulPrefix

theorem StringsUnsafeStringNull_proven : JuliaLean.Proofs.base.strings.string.UnsafeStringRejectsNull :=
  simpleModelStringsUnsafeStringNull

theorem StringsAbstractvectorConstruction_proven : JuliaLean.Proofs.base.strings.string.AbstractVectorStringBytes :=
  simpleModelStringsAbstractvectorConstruction

theorem StringsVectorTransfer_proven : JuliaLean.Proofs.base.strings.string.StringVectorTransfer :=
  simpleModelStringsVectorTransfer

theorem StringsStorageConversions_proven : JuliaLean.Proofs.base.strings.string.StringStorageConversions :=
  simpleModelStringsStorageConversions

theorem StringsStringEqualityBytes_proven : JuliaLean.Proofs.base.strings.string.StringEqualityByContents :=
  simpleModelStringsStringEqualityBytes

theorem StringscovaStringGetindexRebuilt_proven : JuliaLean.Proofs.base.strings.string.Round1.ScalarGetindexMatchesIteration :=
  scalarGetindexModel

theorem StringsCodeunitBounds_proven : JuliaLean.Proofs.base.strings.string.Round3.CodeunitHasExactlyStorageDomain :=
  scalarCodeunitDomain

/-- The exact frozen premise is inconsistent; see the independent review. -/
theorem MemsafetyStringRangeCopy_proven : JuliaLean.Proofs.base.strings.string.StringRangeAccessesInBounds :=
  modelMemsafetyStringRangeCopy

theorem TranscodeStringVectorAlias_refuted : ¬ JuliaLean.Proofs.base.strings.string.StringVectorImmutable :=
  modelAliasRefutation

theorem StringsRepeatCharacter_proven : JuliaLean.Proofs.base.strings.string.RepeatCharRejectsNegative := by
  intro C I ops c count h
  simp only [repeatChar, h, ite_true, throw, throwThe, MonadExceptOf.throw,
    bind, Except.bind]

end JuliaLean.ChatGPT.Batch4.Group11


namespace JuliaLean.ChatGPT.Batch4.Group11

open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string
open _root_.JuliaLean.Proofs.base.strings.string
open _root_.JuliaLean.Proofs.base.strings.util.Round6
open _root_.JuliaLean.Proofs.base.strings.string.JuliaLean.ChatGPT.Batch2.Group5

theorem iterRowStep {S : Type} (step : S → Index → Option (UInt32 × Index))
    (s : S) {i a next : Index} {c : UInt32} {rows : List (Index × UInt32 × Index)}
    (ht : IterTrace step s i rows) (hm : (a, c, next) ∈ rows) :
    step s a = some (c, next) := by
  induction ht with
  | stop h => exact (List.not_mem_nil hm).elim
  | step h tail ih =>
    rcases List.mem_cons.mp hm with heq | hmem
    · cases heq
      exact h
    · exact ih hmem

theorem iterHasStartIff (rows : List (Index × UInt32 × Index)) (i : Index) :
    Round1.traceHasStart rows i = true ↔ ∃ c next, (i, c, next) ∈ rows := by
  simp only [Round1.traceHasStart, List.any_eq_true]
  constructor
  · rintro ⟨⟨a, c, next⟩, hm, ha⟩
    have heq : a = i := Subtype.ext (beq_iff_eq.mp ha)
    subst a
    exact ⟨c, next, hm⟩
  · rintro ⟨c, next, hm⟩
    exact ⟨(i, c, next), hm, beq_self_eq_true _⟩

theorem iterStepFacts (s : JString) (i next : Index) (c : UInt32)
    (hv : stringIsvalidIndex s i = true) (hit : stringIterate s i = some (c, next)) :
    i.val < next.val ∧ next.val ≤ s.bytes.length + 1 ∧
      (next.val ≤ s.bytes.length → stringIsvalidIndex s next = true) ∧
      (∀ j : Index, i.val < j.val → j.val < next.val → stringIsvalidIndex s j = false) := by
  obtain ⟨c', next', hit', hgt, hle, hvalid, hgap⟩ := iterationStep s i hv
  have heq := Option.some.inj (hit.symm.trans hit')
  cases heq
  exact ⟨hgt, hle, hvalid, hgap⟩

theorem iterNcodeunitsSuccVal (s : JString) :
    (stringNcodeunits s + JuliaLean.Strings.ix 1).val = s.bytes.length + 1 := by
  have hs := s.small
  change wrapInt .i64 ((stringNcodeunits s).val + (JuliaLean.Strings.ix 1).val) = _
  rw [stringNcodeunits_val, show (JuliaLean.Strings.ix 1).val = 1 by decide]
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

theorem iterThisindPure (s : JString) (i : Index)
    (hi1 : 1 ≤ i.val) (hin : i.val ≤ s.bytes.length) :
    ∃ r, stringThisind s i = .ok r ∧ r.val = thisindPure (parentByte s) i.val := by
  have hs := s.small
  exact thisindStr_pure stringNcodeunits stringCodeunitAt s (parentByte s) i
    (fun k _ _ => stringCodeunitAt_unchecked s k) hi1
    (by rw [stringNcodeunits_val]; exact hin)
    (by rw [stringNcodeunits_val]; omega)

theorem iterThisindSentinel (s : JString) (i : Index)
    (hi : i.val = 0 ∨ i.val = (stringNcodeunits s).val + 1) :
    stringThisind s i = .ok i := by
  rcases hi with hz | hend
  · have heq : JuliaLean.Strings.ix 0 = i := Subtype.ext (by exact hz.symm)
    simp only [stringThisind, thisindString, thisindStr, hz, beq_self_eq_true,
      ite_true, pure, Except.pure, heq]
  · have hne : (i.val == 0) = false := by
      rw [stringNcodeunits_val] at hend
      apply beq_eq_false_iff_ne.mpr
      omega
    have heq : (i.val == (stringNcodeunits s + JuliaLean.Strings.ix 1).val) = true := by
      rw [iterNcodeunitsSuccVal, stringNcodeunits_val] at *
      exact beq_iff_eq.mpr hend
    simp only [stringThisind, thisindString, thisindStr, hne, Bool.false_eq_true,
      ite_false, heq, ite_true, pure, Except.pure]

theorem iterThisindOutside (s : JString) (i : Index)
    (hi : i.val < 0 ∨ (stringNcodeunits s).val + 1 < i.val) :
    stringThisind s i = .error (.jl .boundsError) := by
  rw [stringNcodeunits_val] at hi
  have hne0 : (i.val == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    omega
  have hneEnd : (i.val == (stringNcodeunits s + JuliaLean.Strings.ix 1).val) = false := by
    rw [iterNcodeunitsSuccVal]
    apply beq_eq_false_iff_ne.mpr
    omega
  have hbetween : stringBetweenIndex i (JuliaLean.Strings.ix 1) (stringNcodeunits s) = false := by
    simp only [stringBetweenIndex, between, stringNcodeunits_val,
      show (JuliaLean.Strings.ix 1).val = 1 by decide, Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    omega
  simp only [stringThisind, thisindString, thisindStr, hne0, hneEnd,
    Bool.false_eq_true, ite_false, hbetween, Bool.not_false, ite_true,
    throw_bind']

theorem iterThisindRow (s : JString) (rows : List (Index × UInt32 × Index))
    (ht : IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows)
    (hstarts : ∀ k, Round1.traceHasStart rows k = true ↔ stringIsvalidIndex s k = true)
    (i : Index) (hi1 : 1 ≤ i.val) (hin : i.val ≤ s.bytes.length) :
    ∃ start c next, (start, c, next) ∈ rows ∧
      start.val ≤ i.val ∧ i.val < next.val ∧ i.val - start.val ≤ 3 ∧
      stringThisind s i = .ok start := by
  obtain ⟨start, hthis, hpure⟩ := iterThisindPure s i hi1 hin
  have hslo : 1 ≤ start.val := by
    rw [hpure]
    exact thisindPure_ge_one _ _ hi1
  have hsle : start.val ≤ i.val := by
    rw [hpure]
    exact thisindPure_le _ _
  have hvalid : stringIsvalidIndex s start = true := by
    apply (stringIsvalid_iff_pure s start hslo (by omega)).mpr
    rw [hpure]
    exact thisindPure_idem _ _
  obtain ⟨c, next, hmem⟩ := (iterHasStartIff rows start).mp ((hstarts start).mpr hvalid)
  have hstep := iterRowStep stringIterate s ht hmem
  obtain ⟨hgt, hnext, hvnext, hgap⟩ := iterStepFacts s start next c hvalid hstep
  have hinext : i.val < next.val := by
    by_cases hni : next.val ≤ i.val
    · have hnvalid := hvnext (by omega)
      have hnpure := (stringIsvalid_iff_pure s next (by omega) (by omega)).mp hnvalid
      have hnjoined := (thisindPure_eq_iff (parentByte s) next.val).mp hnpure
      have hnle := thisindPure_ge_valid (parentByte s) i.val next.val hnjoined hni
      rw [← hpure] at hnle
      omega
    · omega
  have hthree : i.val - start.val ≤ 3 := by
    rw [hpure]
    rcases thisindPure_cases (parentByte s) i.val with h | h | h | h <;> omega
  exact ⟨start, c, next, hmem, hsle, hinext, hthree, hthis⟩

theorem StringscovaStringThisindRebuilt_proven :
    JuliaLean.Proofs.base.strings.string.Round3.ThisindLocatesCharacter := by
  intro s
  obtain ⟨rows, ht, hstarts⟩ := iterationComplete s
  refine ⟨rows, ht, ?_⟩
  intro i
  refine ⟨iterThisindSentinel s i, ?_, iterThisindOutside s i⟩
  rintro ⟨hlo, hhi⟩
  rw [stringNcodeunits_val] at hhi
  exact iterThisindRow s rows ht hstarts i hlo hhi

theorem iterTraceAtEndEmpty (s : JString) {i : Index}
    {rows : List (Index × UInt32 × Index)}
    (ht : IterTrace stringIterate s i rows) (hend : i.val = s.bytes.length + 1) :
    rows = [] :=
  iterationTraceUnique stringIterate s ht (.stop (iterationEnd s i hend))

theorem iterFinalRow (s : JString) {i start next : Index} {c : UInt32}
    {rows : List (Index × UInt32 × Index)}
    (ht : IterTrace stringIterate s i rows) (hm : (start, c, next) ∈ rows)
    (hend : next.val = s.bytes.length + 1) :
    (Round3.traceStarts rows).getLast? = some start := by
  induction ht with
  | stop h => exact (List.not_mem_nil hm).elim
  | @step j d jnext tailRows h tail ih =>
    rcases List.mem_cons.mp hm with heq | hmem
    · cases heq
      have hnil := iterTraceAtEndEmpty s tail hend
      rw [hnil]
      rfl
    · have htlast := ih hmem
      cases tailRows with
      | nil => exact (List.not_mem_nil hmem).elim
      | cons a rest =>
        simpa only [Round3.traceStarts, List.map_cons, List.getLast?_cons_cons] using htlast

theorem StringsLastindexCharacterStart_proven :
    JuliaLean.Proofs.base.strings.string.Round3.LastindexIsFinalCharacterStart := by
  intro s
  obtain ⟨rows, ht, hstarts⟩ := iterationComplete s
  refine ⟨rows, ht, ?_⟩
  change stringThisind s (stringNcodeunits s) = _
  by_cases hz : s.bytes.length = 0
  · have hnil := iterTraceAtEndEmpty s ht (by
      rw [hz]
      decide)
    rw [hnil]
    change stringThisind s (stringNcodeunits s) = .ok (JuliaLean.Strings.ix 0)
    have hnzero : stringNcodeunits s = JuliaLean.Strings.ix 0 := by
      apply Subtype.ext
      rw [stringNcodeunits_val, hz]
      rfl
    rw [iterThisindSentinel s (stringNcodeunits s) (Or.inl (by
      rw [stringNcodeunits_val, hz]
      rfl)), hnzero]
  · obtain ⟨start, c, next, hm, hle, hlt, hthree, hthis⟩ :=
      iterThisindRow s rows ht hstarts (stringNcodeunits s)
        (by rw [stringNcodeunits_val]; omega) (by rw [stringNcodeunits_val]; exact Int.le_refl _)
    have hv := (hstarts start).mp ((iterHasStartIff rows start).mpr ⟨c, next, hm⟩)
    have hstep := iterRowStep stringIterate s ht hm
    have hbound := (iterStepFacts s start next c hv hstep).2.1
    have hend : next.val = s.bytes.length + 1 := by
      rw [stringNcodeunits_val] at hlt
      omega
    have hlast := iterFinalRow s ht hm hend
    rw [hthis, hlast]
    rfl


theorem iterBetweenBounds (s : JString) (i : Index)
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ s.bytes.length) :
    stringBetweenIndex i (JuliaLean.Strings.ix 1) (stringNcodeunits s) = true := by
  simp only [stringBetweenIndex, between, Bool.and_eq_true, decide_eq_true_eq,
    stringNcodeunits_val, show (JuliaLean.Strings.ix 1).val = 1 by decide]
  exact ⟨hlo, hhi⟩

theorem iterNextindContinuation (s : JString) (i start : Index)
    (hi1 : 1 ≤ i.val) (hin : i.val ≤ s.bytes.length)
    (hs1 : 1 ≤ start.val) (hsi : start.val < i.val)
    (hthis : stringThisind s i = .ok start)
    (hcont : contB (parentByte s i.val) = true)
    (hlead : 192 ≤ (parentByte s start.val).toNat ∧
      (parentByte s start.val).toNat ≤ 247) :
    stringNextind s i = stringNextind s start := by
  have hizero : (i.val == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    omega
  have hszero : (start.val == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    omega
  have hiBetween := iterBetweenBounds s i hi1 hin
  have hsBetween := iterBetweenBounds s start hs1 (by omega)
  have hci := (contB_iff (parentByte s i.val)).mp hcont
  have hiByte : stringBetweenByte (parentByte s i.val) 0x80 0xf7 = true := by
    rw [btw80_iff]
    omega
  have hiLt : parentByte s i.val < 0xc0 := (lt192_iff _).mpr (by omega)
  have hsByte : stringBetweenByte (parentByte s start.val) 0x80 0xf7 = true := by
    rw [btw80_iff]
    omega
  have hsLt : ¬ parentByte s start.val < 0xc0 := by
    rw [lt192_iff]
    omega
  have hsLow : ¬ parentByte s start.val < 0x80 := by
    rw [lt128_iff]
    omega
  have hsHigh : ¬ 0xf8 ≤ parentByte s start.val := by
    rw [ge248_iff]
    omega
  have hsGe : parentByte s start.val ≥ 0xc0 := by
    rw [ge192_iff]
    exact hlead.1
  have hprev : ¬ start.val ≥ i.val := by omega
  have ht : thisindString stringNcodeunits stringBetweenIndex stringBetweenByte
      stringCodeunitAt s i = .ok start := hthis
  simp only [stringNextind, nextindString, nextindStr, hizero, hszero,
    hiBetween, hsBetween, stringCodeunitAt_unchecked, hiByte, hsByte,
    hiLt, hsLt, hsLow, hsHigh, hsGe, hprev, ht, Bool.false_eq_true,
    Bool.not_true, Bool.not_false, Bool.or_self, decide_true, decide_false,
    ite_true, ite_false, bind, Except.bind, pure, Except.pure]

theorem iterNextindSameStart (s : JString) (i start : Index)
    (hi1 : 1 ≤ i.val) (hin : i.val ≤ s.bytes.length)
    (hthis : stringThisind s i = .ok start)
    (hpure : start.val = thisindPure (parentByte s) i.val) :
    stringNextind s i = stringNextind s start := by
  have hs1 : 1 ≤ start.val := by
    rw [hpure]
    exact thisindPure_ge_one _ _ hi1
  rcases thisindPure_cases (parentByte s) i.val with h | h | h | h
  · have heq : start = i := Subtype.ext (hpure.trans h)
    rw [heq]
  all_goals
    apply iterNextindContinuation s i start hi1 hin hs1 (by omega) hthis
    · exact h.2.2.1
    · have hv := hpure.trans h.1
      rw [hv]
      first
      | exact (leadB_iff 1 _).mp h.2.2.2
      | (have hl := (leadB_iff 2 _).mp h.2.2.2.2
         change 224 ≤ _ ∧ _ ≤ 247 at hl
         omega)
      | (have hl := (leadB_iff 3 _).mp h.2.2.2.2.2
         change 240 ≤ _ ∧ _ ≤ 247 at hl
         omega)

theorem iterNextindZero (s : JString) (i : Index) (hi : i.val = 0) :
    stringNextind s i = .ok (JuliaLean.Strings.ix 1) := by
  simp only [stringNextind, nextindString, nextindStr, hi,
    beq_self_eq_true, ite_true, pure, Except.pure]

theorem iterNextindOutside (s : JString) (i : Index)
    (hi : i.val < 0 ∨ (stringNcodeunits s).val < i.val) :
    stringNextind s i = .error (.jl .boundsError) := by
  rw [stringNcodeunits_val] at hi
  have hizero : (i.val == 0) = false := by
    apply beq_eq_false_iff_ne.mpr
    omega
  have hbetween : stringBetweenIndex i (JuliaLean.Strings.ix 1) (stringNcodeunits s) = false := by
    simp only [stringBetweenIndex, between, stringNcodeunits_val,
      show (JuliaLean.Strings.ix 1).val = 1 by decide, Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    omega
  simp only [stringNextind, nextindString, nextindStr, hizero,
    Bool.false_eq_true, ite_false, hbetween, Bool.not_false, ite_true,
    throw_bind']

theorem iterStepNextFour (s : JString) (i next : Index) (c : UInt32)
    (hv : stringIsvalidIndex s i = true) (hit : stringIterate s i = some (c, next)) :
    stringNextind s i = .ok next ∧ next.val ≤ i.val + 4 := by
  obtain ⟨d, following, hiter, hnext⟩ := iterationNextBridge s i hv
  have heq := Option.some.inj (hit.symm.trans hiter)
  cases heq
  refine ⟨hnext, ?_⟩
  obtain ⟨hlo, hhi⟩ := iterationValidBounds s i hv
  have hpure := (stringIsvalid_iff_pure s i hlo hhi).mp hv
  have hnot := (thisindPure_eq_iff (parentByte s) i.val).mp hpure
  have hsmall := s.small
  have hcu : ∀ k : Index, stringCodeunitAt false s k =
      if 1 ≤ k.val ∧ k.val ≤ (stringNcodeunits s).val then .ok (parentByte s k.val)
      else .ok (parentByte s k.val) := by
    intro k
    rw [stringCodeunitAt_unchecked]
    split <;> rfl
  obtain ⟨m, hm, _, _, hfour, _⟩ := nextindStr_next stringNcodeunits
    stringCodeunitAt s (parentByte s) i (fun k => .ok (parentByte s k.val)) hcu hlo
    (by rw [stringNcodeunits_val]; exact hhi)
    (by rw [stringNcodeunits_val]; omega) hnot
  have hm' : stringNextind s i = .ok m := hm
  have heq' := Except.ok.inj (hnext.symm.trans hm')
  rw [heq']
  exact hfour

theorem StringscovaStringNextindDispatchRebuilt_proven :
    JuliaLean.Proofs.base.strings.string.Round3.NextindLocatesFollowingCharacter := by
  intro s
  obtain ⟨rows, ht, hstarts⟩ := iterationComplete s
  refine ⟨rows, ht, ?_⟩
  intro i
  refine ⟨iterNextindZero s i, ?_, iterNextindOutside s i⟩
  rintro ⟨hi1, hin⟩
  rw [stringNcodeunits_val] at hin
  obtain ⟨start, c, next, hm, hle, hlt, hthree, hthis⟩ :=
    iterThisindRow s rows ht hstarts i hi1 hin
  obtain ⟨r, hr, hpure⟩ := iterThisindPure s i hi1 hin
  have hre : r = start := Except.ok.inj (hr.symm.trans hthis)
  subst r
  have hvalid := (hstarts start).mp ((iterHasStartIff rows start).mpr ⟨c, next, hm⟩)
  have hstep := iterRowStep stringIterate s ht hm
  have hnhi := (iterStepFacts s start next c hvalid hstep).2.1
  obtain ⟨hnext, hfour⟩ := iterStepNextFour s start next c hvalid hstep
  refine ⟨start, c, next, hm, hle, hlt, by omega, ?_, ?_⟩
  · rw [stringNcodeunits_val]
    exact hnhi
  · rw [iterNextindSameStart s i start hi1 hin hthis hpure]
    exact hnext

theorem iterTraceLayout (s : JString) {i : Index}
    {rows : List (Index × UInt32 × Index)} (ht : IterTrace stringIterate s i rows)
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ s.bytes.length + 1)
    (hv : i.val ≤ s.bytes.length → stringIsvalidIndex s i = true) :
    (∀ row ∈ rows, i.val ≤ row.1.val) ∧
      (rows.map (fun row => row.1)).Pairwise (fun a b => a.val < b.val) := by
  induction ht with
  | stop h =>
    exact ⟨fun row hmem => (List.not_mem_nil hmem).elim, .nil⟩
  | @step i c next rows hstep tail ih =>
    have hin : i.val ≤ s.bytes.length := by
      by_cases hin : i.val ≤ s.bytes.length
      · exact hin
      · have hend : i.val = s.bytes.length + 1 := by omega
        rw [iterationEnd s i hend] at hstep
        cases hstep
    have hvi := hv hin
    obtain ⟨hgt, hn, hnvalid, hgap⟩ := iterStepFacts s i next c hvi hstep
    have htLayout := ih (by omega) hn hnvalid
    refine ⟨?_, ?_⟩
    · intro row hmem
      rcases List.mem_cons.mp hmem with heq | hmem
      · cases heq
        exact Int.le_refl _
      · have hlow := htLayout.1 row hmem
        omega
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, htLayout.2⟩
      intro b hb
      obtain ⟨row, hm, heq⟩ := List.mem_map.mp hb
      subst b
      have hlow := htLayout.1 row hm
      change i.val < row.1.val
      omega

theorem iterRangeIndexVal (s : JString) (k : Nat) (hk : k ≤ s.bytes.length) :
    (JuliaLean.Strings.ix (Int.ofNat (k + 1))).val = (k : Int) + 1 := by
  have hs := s.small
  change wrapInt .i64 (Int.ofNat (k + 1)) = _
  simp only [Int.ofNat_eq_coe]
  rw [wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)]
  omega

theorem iterValidIndicesOrdered (s : JString) :
    (validByteIndices stringNcodeunits stringIsvalidIndex s).Pairwise
      (fun a b => a.val < b.val) := by
  unfold validByteIndices
  apply List.Pairwise.filter
  rw [List.pairwise_map, stringNcodeunits_val, Int.toNat_natCast]
  refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
  intro a b ha hb hab
  have hal := List.mem_range.mp ha
  have hbl := List.mem_range.mp hb
  rw [iterRangeIndexVal s a (by omega), iterRangeIndexVal s b (by omega)]
  omega

theorem iterValidIndicesMem (s : JString) (i : Index) :
    i ∈ validByteIndices stringNcodeunits stringIsvalidIndex s ↔
      stringIsvalidIndex s i = true := by
  unfold validByteIndices
  rw [List.mem_filter]
  constructor
  · exact And.right
  · intro hi
    obtain ⟨hlo, hhi⟩ := iterationValidBounds s i hi
    let k := (i.val - 1).toNat
    have hk : k < (stringNcodeunits s).val.toNat := by
      rw [stringNcodeunits_val, Int.toNat_natCast]
      dsimp only [k]
      omega
    have hie : JuliaLean.Strings.ix (Int.ofNat (k + 1)) = i := by
      apply Subtype.ext
      rw [iterRangeIndexVal s k (by
        rw [stringNcodeunits_val, Int.toNat_natCast] at hk
        omega)]
      dsimp only [k]
      omega
    exact ⟨List.mem_map.mpr ⟨k, List.mem_range.mpr hk, hie⟩, hi⟩

theorem iterOrderedExt (xs ys : List Index)
    (hx : xs.Pairwise (fun a b => a.val < b.val))
    (hy : ys.Pairwise (fun a b => a.val < b.val))
    (hmem : ∀ i, i ∈ xs ↔ i ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have h := (hmem y).mpr (List.mem_cons_self)
      exact (List.not_mem_nil h).elim
  | cons x xs ih =>
    cases ys with
    | nil =>
      have h := (hmem x).mp (List.mem_cons_self)
      exact (List.not_mem_nil h).elim
    | cons y ys =>
      rw [List.pairwise_cons] at hx hy
      have hxy : x = y := by
        have hxm := List.mem_cons.mp ((hmem x).mp (List.mem_cons_self))
        have hym := List.mem_cons.mp ((hmem y).mpr (List.mem_cons_self))
        rcases hxm with heq | hxm
        · exact heq
        rcases hym with heq | hym
        · exact heq.symm
        have h1 := hx.1 y hym
        have h2 := hy.1 x hxm
        omega
      subst y
      have htail : ∀ i, i ∈ xs ↔ i ∈ ys := by
        intro i
        constructor
        · intro hi
          have hin := List.mem_cons.mp ((hmem i).mp (List.mem_cons_of_mem x hi))
          rcases hin with heq | hi'
          · subst i
            have h := hx.1 x hi
            omega
          · exact hi'
        · intro hi
          have hin := List.mem_cons.mp ((hmem i).mpr (List.mem_cons_of_mem x hi))
          rcases hin with heq | hi'
          · subst i
            have h := hy.1 x hi
            omega
          · exact hi'
      rw [ih ys hx.2 hy.2 htail]

theorem iterStartsMem (rows : List (Index × UInt32 × Index)) (i : Index) :
    i ∈ rows.map (fun row => row.1) ↔ Round1.traceHasStart rows i = true := by
  rw [iterHasStartIff]
  constructor
  · intro hi
    obtain ⟨⟨start, c, next⟩, hm, heq⟩ := List.mem_map.mp hi
    change start = i at heq
    subst start
    exact ⟨c, next, hm⟩
  · rintro ⟨c, next, hm⟩
    exact List.mem_map.mpr ⟨(i, c, next), hm, rfl⟩

/-- The unchanged String conjunct of the frozen iteration target. -/
theorem iterStringVisitsAllValid (s : JString) (rows : List (Index × UInt32 × Index))
    (ht : IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows) :
    rows.map (fun row => row.1) = validByteIndices stringNcodeunits stringIsvalidIndex s := by
  obtain ⟨complete, hcomplete, hstarts⟩ := iterationComplete s
  have heq := iterationTraceUnique stringIterate s ht hcomplete
  subst rows
  apply iterOrderedExt
  · exact (iterTraceLayout s hcomplete
      (by decide) (by change (1 : Int) ≤ (s.bytes.length : Int) + 1; omega)
      (fun hn => iterationFirstValid s hn)).2
  · exact iterValidIndicesOrdered s
  · intro i
    rw [iterStartsMem, hstarts, iterValidIndicesMem]


/-- Existence and exact ordered enumeration for the String half of the frozen target. -/
theorem iterStringVisitsValidConjunct :
    ∀ s : JString, ∃ rows,
      IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows ∧
      rows.map (fun row => row.1) =
        validByteIndices stringNcodeunits stringIsvalidIndex s := by
  intro s
  obtain ⟨rows, ht, _⟩ := iterationComplete s
  exact ⟨rows, ht, iterStringVisitsAllValid s rows ht⟩


/-- The two concrete iterators share exactly the same byte decoder. -/
theorem iterViewStepAsString (s : JString) (i : Index) :
    stringViewIterate ⟨s.bytes⟩ i = stringIterate s i := by
  rfl

theorem iterViewTraceAsString (s : JString) (i : Index)
    (rows : List (Index × UInt32 × Index)) :
    IterTrace stringViewIterate ⟨s.bytes⟩ i rows ↔ IterTrace stringIterate s i rows := by
  constructor
  · intro ht
    induction ht with
    | stop h => exact .stop h
    | step h tail ih => exact .step h ih
  · intro ht
    induction ht with
    | stop h => exact .stop h
    | step h tail ih => exact .step h ih

/-- A bounded view visits the actual character starts of the same stored bytes. -/
theorem iterViewVisitsActualValid (s : JString) (rows : List (Index × UInt32 × Index))
    (ht : IterTrace stringViewIterate ⟨s.bytes⟩ (JuliaLean.Strings.ix 1) rows) :
    rows.map (fun row => row.1) = validByteIndices stringNcodeunits stringIsvalidIndex s := by
  exact iterStringVisitsAllValid s rows
    ((iterViewTraceAsString s (JuliaLean.Strings.ix 1) rows).mp ht)


/-- The unsigned one-based bound check is exact for representable string storage. -/
theorem iterUnsignedBounds (n : Nat) (hn : n < 2 ^ 62) (i : Index) :
    (JInt.rem .u64 i - JInt.lit .u64 1).val < (n : Int) ↔
      1 ≤ i.val ∧ i.val ≤ (n : Int) := by
  have hi := i.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hi
  change ((i.val % (2 ^ 64) - 1) % (2 ^ 64) < (n : Int)) ↔ _
  omega

theorem iterStringNonemptyIff (s : JString) (i : Index) :
    stringIterate s i ≠ none ↔ 1 ≤ i.val ∧ i.val ≤ (s.bytes.length : Int) := by
  constructor
  · intro hit
    have hc : (JInt.rem .u64 i - JInt.lit .u64 1).val < (stringNcodeunits s).val := by
      by_cases hc : (JInt.rem .u64 i - JInt.lit .u64 1).val < (stringNcodeunits s).val
      · exact hc
      · have hnone : stringIterate s i = none := by
          simp only [stringIterate, iterateString, hc, decide_false,
            Bool.not_false, ite_true]
        exact (hit hnone).elim
    rw [stringNcodeunits_val] at hc
    exact (iterUnsignedBounds s.bytes.length s.small i).mp hc
  · rintro ⟨hlo, hhi⟩
    rw [iterationInBounds s i hlo hhi]
    split <;> (intro h; cases h)

/-- Useful bounded-storage part of the frozen view-access contract. -/
theorem iterBoundedViewNonemptyIff (view : StringView (List UInt8))
    (hsmall : view.data.length < 2 ^ 62) (i : Index) :
    stringViewIterate view i ≠ none ↔
      1 ≤ i.val ∧ i.val ≤ Int.ofNat view.data.length := by
  exact iterStringNonemptyIff ⟨view.data, hsmall⟩ i

/-- One-byte advancement does not wrap inside a representable String. -/
theorem iterWalkAdvanceVal (s : JString) (i : Index)
    (hlo : 0 ≤ i.val) (hhi : i.val ≤ s.bytes.length + 1) :
    (i + JuliaLean.Strings.ix 1).val = i.val + 1 := by
  have hs := s.small
  change wrapInt .i64 (i.val + (JuliaLean.Strings.ix 1).val) = _
  rw [show (JuliaLean.Strings.ix 1).val = 1 by decide]
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

/-- Exact membership for a recursive byte-index walk using the installed validity predicate. -/
theorem iterWalkMem (s : JString) (walk : Nat → Index → List Index)
    (hzero : ∀ i, walk 0 i = [])
    (hsucc : ∀ k i, walk (k + 1) i =
      if stringIsvalidIndex s i then i :: walk k (i + JuliaLean.Strings.ix 1)
      else walk k (i + JuliaLean.Strings.ix 1)) :
    ∀ (k : Nat) (i : Index), 1 ≤ i.val → i.val + (k : Int) ≤ s.bytes.length + 1 →
      ∀ j, j ∈ walk k i ↔
        i.val ≤ j.val ∧ j.val < i.val + (k : Int) ∧ stringIsvalidIndex s j = true := by
  intro k
  induction k with
  | zero =>
    intro i hlo hhi j
    rw [hzero]
    constructor
    · intro h
      exact (List.not_mem_nil h).elim
    · rintro ⟨hlo, hhi, hv⟩
      omega
  | succ k ih =>
    intro i hlo hhi j
    have hnval := iterWalkAdvanceVal s i (by omega) (by omega)
    have hnext := ih (i + JuliaLean.Strings.ix 1) (by omega) (by omega) j
    rw [hsucc]
    by_cases hv : stringIsvalidIndex s i = true
    · rw [if_pos hv, List.mem_cons, hnext]
      constructor
      · rintro (heq | ⟨hl, hh, hj⟩)
        · subst j
          exact ⟨Int.le_refl _, by omega, hv⟩
        · exact ⟨by omega, by omega, hj⟩
      · rintro ⟨hl, hh, hj⟩
        by_cases heq : j.val = i.val
        · exact Or.inl (Subtype.ext heq)
        · exact Or.inr ⟨by omega, by omega, hj⟩
    · rw [if_neg hv, hnext]
      constructor
      · rintro ⟨hl, hh, hj⟩
        exact ⟨by omega, by omega, hj⟩
      · rintro ⟨hl, hh, hj⟩
        have hne : j.val ≠ i.val := by
          intro heq
          have hji : j = i := Subtype.ext heq
          subst j
          exact hv hj
        exact ⟨by omega, by omega, hj⟩

theorem iterWalkOrdered (s : JString) (walk : Nat → Index → List Index)
    (hzero : ∀ i, walk 0 i = [])
    (hsucc : ∀ k i, walk (k + 1) i =
      if stringIsvalidIndex s i then i :: walk k (i + JuliaLean.Strings.ix 1)
      else walk k (i + JuliaLean.Strings.ix 1)) :
    ∀ (k : Nat) (i : Index), 1 ≤ i.val → i.val + (k : Int) ≤ s.bytes.length + 1 →
      (walk k i).Pairwise (fun a b => a.val < b.val) := by
  intro k
  induction k with
  | zero =>
    intro i hlo hhi
    rw [hzero]
    exact .nil
  | succ k ih =>
    intro i hlo hhi
    have hnval := iterWalkAdvanceVal s i (by omega) (by omega)
    have hnext := ih (i + JuliaLean.Strings.ix 1) (by omega) (by omega)
    rw [hsucc]
    by_cases hv : stringIsvalidIndex s i = true
    · rw [if_pos hv, List.pairwise_cons]
      refine ⟨?_, hnext⟩
      intro j hj
      have hm := (iterWalkMem s walk hzero hsucc k (i + JuliaLean.Strings.ix 1)
        (by omega) (by omega) j).mp hj
      omega
    · rw [if_neg hv]
      exact hnext

/-- A recursive count-valid-indices walk equals the frozen filtered enumeration. -/
theorem iterWalkValidIndices (s : JString) (walk : Nat → Index → List Index)
    (hzero : ∀ i, walk 0 i = [])
    (hsucc : ∀ k i, walk (k + 1) i =
      if stringIsvalidIndex s i then i :: walk k (i + JuliaLean.Strings.ix 1)
      else walk k (i + JuliaLean.Strings.ix 1)) :
    walk s.bytes.length (JuliaLean.Strings.ix 1) =
      validByteIndices stringNcodeunits stringIsvalidIndex s := by
  have h1 : (JuliaLean.Strings.ix 1).val = 1 := by decide
  apply iterOrderedExt
  · exact iterWalkOrdered s walk hzero hsucc s.bytes.length (JuliaLean.Strings.ix 1)
      (by rw [h1]; exact Int.le_refl _) (by rw [h1]; omega)
  · exact iterValidIndicesOrdered s
  · intro j
    rw [iterWalkMem s walk hzero hsucc s.bytes.length (JuliaLean.Strings.ix 1)
      (by rw [h1]; exact Int.le_refl _) (by rw [h1]; omega), iterValidIndicesMem]
    constructor
    · exact fun h => h.2.2
    · intro hv
      obtain ⟨hlo, hhi⟩ := iterationValidBounds s j hv
      exact ⟨by rw [h1]; exact hlo, by rw [h1]; omega, hv⟩

/-- Complete actual iteration has the length of any recursive walk satisfying these equations. -/
theorem iterTraceLengthWalk (s : JString) (walk : Nat → Index → List Index)
    (hzero : ∀ i, walk 0 i = [])
    (hsucc : ∀ k i, walk (k + 1) i =
      if stringIsvalidIndex s i then i :: walk k (i + JuliaLean.Strings.ix 1)
      else walk k (i + JuliaLean.Strings.ix 1))
    (rows : List (Index × UInt32 × Index))
    (ht : IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows) :
    rows.length = (walk s.bytes.length (JuliaLean.Strings.ix 1)).length := by
  have hlen := congrArg List.length (iterStringVisitsAllValid s rows ht)
  rw [List.length_map] at hlen
  rw [iterWalkValidIndices s walk hzero hsucc]
  exact hlen

/-- On a nonempty in-bounds interval, the recursive walk lists exactly the actual iteration starts. -/
theorem iterWalkTraceInterval (s : JString) (walk : Nat → Index → List Index)
    (hzero : ∀ i, walk 0 i = [])
    (hsucc : ∀ k i, walk (k + 1) i =
      if stringIsvalidIndex s i then i :: walk k (i + JuliaLean.Strings.ix 1)
      else walk k (i + JuliaLean.Strings.ix 1))
    (rows : List (Index × UInt32 × Index))
    (ht : IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows)
    (i j : Index) (hlo : 1 ≤ i.val) (hij : i.val ≤ j.val)
    (hhi : j.val ≤ s.bytes.length) :
    walk (j.val - i.val + 1).toNat i =
      (Round3.traceStarts rows).filter
        (fun start => decide (i.val ≤ start.val ∧ start.val ≤ j.val)) := by
  have hk : ((j.val - i.val + 1).toNat : Int) = j.val - i.val + 1 :=
    Int.toNat_of_nonneg (by omega)
  have hrows : Round3.traceStarts rows =
      validByteIndices stringNcodeunits stringIsvalidIndex s :=
    iterStringVisitsAllValid s rows ht
  rw [hrows]
  apply iterOrderedExt
  · exact iterWalkOrdered s walk hzero hsucc (j.val - i.val + 1).toNat i hlo (by omega)
  · exact List.Pairwise.filter _ (iterValidIndicesOrdered s)
  · intro k
    rw [iterWalkMem s walk hzero hsucc (j.val - i.val + 1).toNat i hlo (by omega),
      List.mem_filter, iterValidIndicesMem]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨hkl, hkh, hv⟩
      exact ⟨hv, hkl, by omega⟩
    · rintro ⟨hv, hkl, hkh⟩
      exact ⟨hkl, by omega, hv⟩

theorem iterTraceFilterEmpty (rows : List (Index × UInt32 × Index)) (i j : Index)
    (hji : j.val < i.val) :
    (Round3.traceStarts rows).filter
      (fun start => decide (i.val ≤ start.val ∧ start.val ≤ j.val)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro start hmem hgood
  have h := of_decide_eq_true hgood
  omega

/-- Adding an enumerated byte offset is exact throughout a representable String interval. -/
theorem iterWalkOffsetVal (s : JString) (i : Index) (offset : Nat)
    (hlo : 1 ≤ i.val) (hhi : i.val + (offset : Int) ≤ s.bytes.length + 1) :
    (i + JuliaLean.Strings.ix (Int.ofNat offset)).val = i.val + (offset : Int) := by
  have hs := s.small
  have hoff : (JuliaLean.Strings.ix (Int.ofNat offset)).val = (offset : Int) := by
    change wrapInt .i64 (Int.ofNat offset) = _
    simp only [Int.ofNat_eq_coe]
    exact wrapInt_of_inRange .i64 _ (by
      simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
      omega)
  change wrapInt .i64 (i.val + (JuliaLean.Strings.ix (Int.ofNat offset)).val) = _
  rw [hoff]
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

/-- Recursive validity counting agrees with the frozen offset-filter specification. -/
theorem iterWalkOffsetCount (s : JString) (walk : Nat → Index → List Index)
    (hzero : ∀ i, walk 0 i = [])
    (hsucc : ∀ k i, walk (k + 1) i =
      if stringIsvalidIndex s i then i :: walk k (i + JuliaLean.Strings.ix 1)
      else walk k (i + JuliaLean.Strings.ix 1))
    (i j : Index) (hlo : 1 ≤ i.val) (hij : i.val ≤ j.val)
    (hhi : j.val ≤ s.bytes.length) :
    (walk (j.val - i.val + 1).toNat i).length =
      Round1.validIndexCount stringIsvalidIndex s i j := by
  let k := (j.val - i.val + 1).toNat
  let atOffset := fun offset : Nat => i + JuliaLean.Strings.ix (Int.ofNat offset)
  have hk : (k : Int) = j.val - i.val + 1 := Int.toNat_of_nonneg (by omega)
  have hvalue : ∀ offset, offset < k →
      (atOffset offset).val = i.val + (offset : Int) := by
    intro offset hoff
    exact iterWalkOffsetVal s i offset hlo (by omega)
  have heq : walk k i =
      ((List.range k).filter (fun offset => stringIsvalidIndex s (atOffset offset))).map
        atOffset := by
    apply iterOrderedExt
    · exact iterWalkOrdered s walk hzero hsucc k i hlo (by omega)
    · rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.filter _ (List.pairwise_lt_range (n := k)))
      intro a b ha hb hab
      have hal := List.mem_range.mp (List.mem_filter.mp ha).1
      have hbl := List.mem_range.mp (List.mem_filter.mp hb).1
      rw [hvalue a hal, hvalue b hbl]
      omega
    · intro x
      rw [iterWalkMem s walk hzero hsucc k i hlo (by omega)]
      simp only [List.mem_map, List.mem_filter, List.mem_range]
      constructor
      · rintro ⟨hxl, hxh, hv⟩
        let offset := (x.val - i.val).toNat
        have hoff : offset < k := by
          dsimp only [offset]
          omega
        have hindex : atOffset offset = x := by
          apply Subtype.ext
          rw [hvalue offset hoff]
          dsimp only [offset]
          omega
        refine ⟨offset, ⟨hoff, ?_⟩, hindex⟩
        rw [hindex]
        exact hv
      · rintro ⟨offset, ⟨hoff, hv⟩, hindex⟩
        subst x
        refine ⟨?_, ?_, hv⟩
        · rw [hvalue offset hoff]
          omega
        · rw [hvalue offset hoff]
          omega
  unfold Round1.validIndexCount
  rw [if_neg (by omega : ¬ j.val < i.val)]
  change (walk k i).length = _
  rw [heq, List.length_map]

end JuliaLean.ChatGPT.Batch4.Group11


namespace JuliaLean.ChatGPT.Batch4.Group11

open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string
open _root_.JuliaLean.Proofs.base.strings.string
open _root_.JuliaLean.Proofs.base.strings.util.Round6
open _root_.JuliaLean.Proofs.base.strings.string.JuliaLean.ChatGPT.Batch2.Group2.Indexing

/-- The documented native-index domain of a String range-length call. -/
def countRangeDomain (s : JString) (i j : Index) : Prop :=
  0 < i.val ∧ i.val ≤ (stringNcodeunits s).val + 1 ∧
    0 ≤ j.val ∧ j.val ≤ (stringNcodeunits s).val

/-- The first two source checks have exactly the documented native-index domain. -/
theorem countRangeDomainChecks (s : JString) (i j : Index) :
    countRangeDomain s i j ↔
      (0 < i.val ∧ i.val ≤ (stringNcodeunits s + JuliaLean.Strings.ix 1).val) ∧
      (0 ≤ j.val ∧ j.val < (stringNcodeunits s + JuliaLean.Strings.ix 1).val) := by
  unfold countRangeDomain
  rw [addOneNcodeunits, stringNcodeunits_val]
  omega

/-- Every failed range-domain check raises the exact source BoundsError. -/
theorem countRangeOutside (s : JString) (i j : Index)
    (outside : ¬ countRangeDomain s i j) :
    stringLengthRange s i j = .error (.jl .boundsError) := by
  have checks := mt (countRangeDomainChecks s i j).mpr outside
  unfold stringLengthRange lengthStringRange lengthRange
  by_cases first : 0 < i.val ∧
      i.val ≤ (stringNcodeunits s + JuliaLean.Strings.ix 1).val
  · have last : ¬ (0 ≤ j.val ∧
        j.val < (stringNcodeunits s + JuliaLean.Strings.ix 1).val) :=
      fun h => checks ⟨first, h⟩
    have firstBool : (0 < i.val &&
        i.val ≤ (stringNcodeunits s + JuliaLean.Strings.ix 1).val) = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using first
    have lastBool : (0 ≤ j.val &&
        j.val < (stringNcodeunits s + JuliaLean.Strings.ix 1).val) = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hb := Bool.and_eq_true_iff.mp htrue
      exact last ⟨of_decide_eq_true hb.1, of_decide_eq_true hb.2⟩
    simp only [firstBool, lastBool, Bool.not_true, Bool.false_eq_true, ite_false,
      Bool.not_false, ite_true, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · have firstBool : (0 < i.val &&
        i.val ≤ (stringNcodeunits s + JuliaLean.Strings.ix 1).val) = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hb := Bool.and_eq_true_iff.mp htrue
      exact first ⟨of_decide_eq_true hb.1, of_decide_eq_true hb.2⟩
    simp only [firstBool, Bool.not_false, ite_true,
      throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- An accepted empty span has zero characters, including both sentinel endpoints. -/
theorem countRangeEmpty (s : JString) (i j : Index)
    (inside : countRangeDomain s i j) (empty : j.val < i.val) :
    stringLengthRange s i j = .ok (JuliaLean.Strings.ix 0) := by
  obtain ⟨first, last⟩ := (countRangeDomainChecks s i j).mp inside
  have firstBool : (0 < i.val &&
      i.val ≤ (stringNcodeunits s + JuliaLean.Strings.ix 1).val) = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using first
  have lastBool : (0 ≤ j.val &&
      j.val < (stringNcodeunits s + JuliaLean.Strings.ix 1).val) = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using last
  simp only [stringLengthRange, lengthStringRange, lengthRange,
    firstBool, lastBool, Bool.not_true, Bool.false_eq_true, ite_false,
    empty, ite_true, pure, Except.pure, bind, Except.bind]

/-- An accepted nonempty span normalizes its first byte to an existing character start. -/
theorem countRangeNonempty (s : JString) (i j : Index)
    (inside : countRangeDomain s i j) (nonempty : i.val ≤ j.val) :
    ∃ first,
      stringThisind s i = .ok first ∧
      first.val = thisindPure (parentByte s) i.val ∧
      stringLengthRange s i j = .ok
        (stringLengthContinued s first j
          (j - first + stringIndexBool (first.val == i.val))) := by
  obtain ⟨firstCheck, lastCheck⟩ := (countRangeDomainChecks s i j).mp inside
  have ilo : 1 ≤ i.val := by have := inside.1; omega
  have ihi : i.val ≤ (s.bytes.length : Int) := by
    have hj := inside.2.2.2
    rw [stringNcodeunits_val] at hj
    omega
  obtain ⟨first, normalized, value⟩ := thisindPureResult s i ilo ihi
  refine ⟨first, normalized, value, ?_⟩
  have firstBool : (0 < i.val &&
      i.val ≤ (stringNcodeunits s + JuliaLean.Strings.ix 1).val) = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using firstCheck
  have lastBool : (0 ≤ j.val &&
      j.val < (stringNcodeunits s + JuliaLean.Strings.ix 1).val) = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using lastCheck
  simp only [stringLengthRange, lengthStringRange, lengthRange,
    firstBool, lastBool, Bool.not_true, Bool.false_eq_true, ite_false,
    show ¬ j.val < i.val by omega, normalized, pure, Except.pure, bind, Except.bind]

/-- Range length succeeds at every point in its documented domain. -/
theorem countRangeInside (s : JString) (i j : Index)
    (inside : countRangeDomain s i j) :
    ∃ count, stringLengthRange s i j = .ok count := by
  by_cases empty : j.val < i.val
  · exact ⟨_, countRangeEmpty s i j inside empty⟩
  · obtain ⟨first, _, _, result⟩ := countRangeNonempty s i j inside (by omega)
    exact ⟨_, result⟩

/-- The success/error domain of the frozen range-length model is completely settled. -/
theorem countRangeErrorIff (s : JString) (i j : Index) :
    stringLengthRange s i j = .error (.jl .boundsError) ↔
      ¬ countRangeDomain s i j := by
  constructor
  · intro result inside
    obtain ⟨count, successful⟩ := countRangeInside s i j inside
    rw [successful] at result
    cases result
  · exact countRangeOutside s i j

/-- Leading bytes that can absorb one or more continuation bytes in Julia iteration. -/
def countByteIsLead (b : UInt8) : Bool := 0xc0 ≤ b && b ≤ 0xf7

local macro "countOriginalSeek" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JuliaLean.base.strings.string
    `JuliaLean.base.strings.string.lengthSeekLead))
local macro "countOriginalLoop" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JuliaLean.base.strings.string
    `JuliaLean.base.strings.string.lengthCountLoop))

abbrev countSeekModel {S : Type} (read : S → Index → UInt8)
    (s : S) (last : Index) (fuel : Nat) (i : Index) (b : UInt8) :=
  countOriginalSeek read s last fuel i b
abbrev countLoopModel {S : Type} (read : S → Index → UInt8)
    (s : S) (last : Index) (fuel : Nat) (i : Index) (b : UInt8) (count : Index) :=
  countOriginalLoop read s last fuel i b count

/-- The seeking loop terminates without a candidate when every inspected byte is a nonlead. -/
theorem countSeekWithoutLeads {S : Type} (read : S → Index → UInt8) (s : S)
    (noneLead : ∀ k, countByteIsLead (read s k) = false)
    (last : Index) (fuel : Nat) (i : Index) (b : UInt8)
    (firstNotLead : countByteIsLead b = false) :
    countSeekModel read s last fuel i b = none := by
  induction fuel generalizing i b with
  | zero => rfl
  | succ fuel ih =>
    change (if (i + JuliaLean.Strings.ix 1).val > last.val then none
      else if countByteIsLead b then some (i + JuliaLean.Strings.ix 1, b)
      else countSeekModel read s last fuel (i + JuliaLean.Strings.ix 1)
        (read s (i + JuliaLean.Strings.ix 1))) = none
    rw [firstNotLead]
    simp only [Bool.false_eq_true, ite_false]
    split
    · rfl
    · exact ih _ _ (noneLead _)

/-- No count subtraction occurs when the scan encounters no leading byte. -/
theorem countLoopWithoutLeads {S : Type} (read : S → Index → UInt8) (s : S)
    (noneLead : ∀ k, countByteIsLead (read s k) = false)
    (last : Index) (fuel : Nat) (i : Index) (b : UInt8) (count : Index)
    (firstNotLead : countByteIsLead b = false) :
    countLoopModel read s last fuel i b count = count := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have noCandidate := countSeekWithoutLeads read s noneLead last fuel i b firstNotLead
    unfold countLoopModel
    change (match countSeekModel read s last fuel i b with
      | none => count
      | some (next, lead) => _) = count
    rw [noCandidate]

/-- Default list lookup preserves the absence of multibyte lead bytes. -/
theorem countGetDWithoutLeads (bytes : List UInt8)
    (noneLead : ∀ b ∈ bytes, countByteIsLead b = false) (n : Nat) :
    countByteIsLead (bytes.getD n 0) = false := by
  induction bytes generalizing n with
  | nil => simp only [List.getD_nil]; decide
  | cons b bytes ih =>
    cases n with
    | zero =>
      rw [List.getD_cons_zero]
      exact noneLead b (by simp only [List.mem_cons, true_or])
    | succ n =>
      rw [List.getD_cons_succ]
      exact ih (fun b hb => noneLead b (List.mem_cons_of_mem _ hb)) n

/-- All strings without multibyte leads have one counted character per stored byte.
This includes ASCII strings and arbitrary isolated continuation-byte sequences. -/
theorem countStringWithoutLeads (s : JString)
    (noneLead : ∀ b ∈ s.bytes, countByteIsLead b = false) :
    stringLength s = stringNcodeunits s := by
  have reads : ∀ k, countByteIsLead (stringByteAt s k) = false := by
    intro k
    exact countGetDWithoutLeads s.bytes noneLead _
  unfold stringLength lengthString lengthContinuedString lengthContinuedInternal
  split
  · rfl
  · exact countLoopWithoutLeads stringByteAt s reads _ _ _ _ _ (reads _)


/-- The source body after its inner scan has found a leading byte. -/
def countAfterLead (s : JString) (last : Index) (fuel : Nat)
    (i : Index) (lead : UInt8) (count : Index) : Index :=
  let b := stringByteAt s i
  let firstIsContinuation := isValidContinuation b
  let count := count - stringIndexBool firstIsContinuation
  if !(firstIsContinuation && lead ≥ 0xe0) then
    countLoopModel stringByteAt s last fuel i b count
  else
    let i := i + JuliaLean.Strings.ix 1
    if i.val > last.val then count
    else
      let b := stringByteAt s i
      let secondIsContinuation := isValidContinuation b
      let count := count - stringIndexBool secondIsContinuation
      if !(secondIsContinuation && lead ≥ 0xf0) then
        countLoopModel stringByteAt s last fuel i b count
      else
        let i := i + JuliaLean.Strings.ix 1
        if i.val > last.val then count
        else
          let b := stringByteAt s i
          countLoopModel stringByteAt s last fuel i b
            (count - stringIndexBool (isValidContinuation b))

theorem countSeekStep (s : JString) (last : Index) (fuel : Nat) (i : Index) (b : UInt8) :
    countSeekModel stringByteAt s last (fuel + 1) i b =
      (if (i + JuliaLean.Strings.ix 1).val > last.val then none
       else if countByteIsLead b then some (i + JuliaLean.Strings.ix 1, b)
       else countSeekModel stringByteAt s last fuel (i + JuliaLean.Strings.ix 1)
         (stringByteAt s (i + JuliaLean.Strings.ix 1))) := rfl

theorem countLoopStep (s : JString) (last : Index) (fuel : Nat) (i : Index)
    (b : UInt8) (count : Index) :
    countLoopModel stringByteAt s last (fuel + 1) i b count =
      match countSeekModel stringByteAt s last fuel i b with
      | none => count
      | some (next, lead) => countAfterLead s last fuel next lead count := rfl

theorem countAdvanceVal (i : Index) (lo : 0 ≤ i.val) (hi : i.val ≤ 2 ^ 62 + 8) :
    (i + JuliaLean.Strings.ix 1).val = i.val + 1 := by
  change wrapInt .i64 (i.val + (JuliaLean.Strings.ix 1).val) = _
  rw [show (JuliaLean.Strings.ix 1).val = 1 by decide]
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega)

/-- The separate source scan has enough fuel to agree with the byte-counted loop.
Both loops here are existing supplied models; no statement or model is changed. -/
theorem countLoopMatchesByteLoop (s : JString) (last : Index) (fuel : Nat) :
    ∀ (remaining : Nat) (i : Index) (b : UInt8) (count : Index),
      remaining < fuel → 0 ≤ i.val → i.val + remaining = last.val →
      last.val ≤ 2 ^ 62 →
      countLoopModel stringByteAt s last fuel i b count =
        JuliaLean.Strings.lenLoop s last remaining i b count := by
  induction fuel with
  | zero => intro remaining i b count small; omega
  | succ fuel ih =>
    intro remaining i b count small lo distance lastSmall
    have scan : ∀ budget : Nat, budget ≤ fuel →
        ∀ (remaining : Nat) (i : Index) (b : UInt8) (count : Index),
        remaining ≤ budget → 0 ≤ i.val → i.val + remaining = last.val →
        (match countSeekModel stringByteAt s last budget i b with
        | none => count
        | some (next, lead) => countAfterLead s last fuel next lead count) =
          JuliaLean.Strings.lenLoop s last remaining i b count := by
      intro budget
      induction budget with
      | zero =>
        intro budgetBound remaining i b count small lo distance
        have rz : remaining = 0 := by omega
        subst remaining
        rfl
      | succ budget scanIH =>
        intro budgetBound remaining i b count small lo distance
        have nextVal := countAdvanceVal i lo (by omega)
        cases remaining with
        | zero =>
          rw [countSeekStep]
          have ended : (i + JuliaLean.Strings.ix 1).val > last.val := by omega
          rw [if_pos ended]
          rfl
        | succ remaining =>
          rw [countSeekStep]
          have inside : ¬ (i + JuliaLean.Strings.ix 1).val > last.val := by omega
          rw [if_neg inside]
          cases lead : countByteIsLead b with
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            have oldNotLead :
                (!(decide ((0xc0 : UInt8) ≤ b) && decide (b ≤ (0xf7 : UInt8)))) = true := by
              change Bool.not (countByteIsLead b) = true
              rw [lead]
              rfl
            rw [JuliaLean.Strings.lenLoop, if_pos oldNotLead]
            exact scanIH (by omega) remaining (i + JuliaLean.Strings.ix 1)
              (stringByteAt s (i + JuliaLean.Strings.ix 1)) count
              (by omega) (by omega) (by omega)
          | true =>
            simp only [ite_true]
            have oldLead :
                ¬ (!(decide ((0xc0 : UInt8) ≤ b) && decide (b ≤ (0xf7 : UInt8)))) = true := by
              change ¬ Bool.not (countByteIsLead b) = true
              rw [lead]
              exact Bool.false_ne_true
            rw [JuliaLean.Strings.lenLoop, if_neg oldLead]
            change countAfterLead s last fuel (i + JuliaLean.Strings.ix 1) b count = _
            unfold countAfterLead
            dsimp only
            by_cases stop1 :
                (!(isValidContinuation (stringByteAt s (i + JuliaLean.Strings.ix 1)) && b ≥ 0xe0)) = true
            · have oldStop1 :
                  (!(JuliaLean.Strings.isCont (JuliaLean.Strings.cu s (i + JuliaLean.Strings.ix 1)) &&
                    b ≥ 0xe0)) = true := stop1
              rw [if_pos stop1, if_pos oldStop1]
              exact ih remaining _ _ _ (by omega) (by omega) (by omega) lastSmall
            · have oldStop1 : ¬
                  (!(JuliaLean.Strings.isCont (JuliaLean.Strings.cu s (i + JuliaLean.Strings.ix 1)) &&
                    b ≥ 0xe0)) = true := stop1
              rw [if_neg stop1, if_neg oldStop1]
              have next2Val := countAdvanceVal (i + JuliaLean.Strings.ix 1)
                (by omega) (by omega)
              cases remaining with
              | zero =>
                have ended : (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1).val > last.val := by
                  omega
                rw [if_pos ended]
                rfl
              | succ remaining =>
                have inside2 : ¬ (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1).val > last.val := by
                  omega
                rw [if_neg inside2]
                dsimp only
                by_cases stop2 :
                    (!(isValidContinuation (stringByteAt s
                      (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)) && b ≥ 0xf0)) = true
                · have oldStop2 :
                      (!(JuliaLean.Strings.isCont (JuliaLean.Strings.cu s
                        (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)) && b ≥ 0xf0)) = true := stop2
                  rw [if_pos stop2, if_pos oldStop2]
                  exact ih remaining _ _ _ (by omega) (by omega) (by omega) lastSmall
                · have oldStop2 : ¬
                      (!(JuliaLean.Strings.isCont (JuliaLean.Strings.cu s
                        (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)) && b ≥ 0xf0)) = true := stop2
                  rw [if_neg stop2, if_neg oldStop2]
                  have next3Val := countAdvanceVal
                    (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1) (by omega) (by omega)
                  cases remaining with
                  | zero =>
                    have ended :
                        (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1).val >
                          last.val := by omega
                    rw [if_pos ended]
                    rfl
                  | succ remaining =>
                    have inside3 : ¬
                        (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1).val >
                          last.val := by omega
                    rw [if_neg inside3]
                    exact ih remaining _ _ _ (by omega) (by omega) (by omega) lastSmall
    rw [countLoopStep]
    exact scan fuel (Nat.le_refl _) remaining i b count (by omega) lo distance

/-- The source-mirrored whole-String length agrees with the installed byte-counted loop. -/
theorem countLengthMatchesByteLoop (s : JString) :
    stringLength s = JuliaLean.Strings.length s := by
  have sizeVal := stringNcodeunits_val s
  have small := s.small
  unfold stringLength lengthString lengthContinuedString lengthContinuedInternal
    JuliaLean.Strings.length JuliaLean.Strings.lengthContinued
  change (if !((JuliaLean.Strings.ix 1).val < (stringNcodeunits s).val) then stringNcodeunits s
    else countLoopModel stringByteAt s (stringNcodeunits s)
      ((stringNcodeunits s).val - (JuliaLean.Strings.ix 1).val + 1).toNat
      (JuliaLean.Strings.ix 1) (stringByteAt s (JuliaLean.Strings.ix 1)) (stringNcodeunits s)) =
    (if !((JuliaLean.Strings.ix 1).val < (stringNcodeunits s).val) then stringNcodeunits s
    else JuliaLean.Strings.lenLoop s (stringNcodeunits s)
      ((stringNcodeunits s).val - (JuliaLean.Strings.ix 1).val).toNat
      (JuliaLean.Strings.ix 1) (stringByteAt s (JuliaLean.Strings.ix 1)) (stringNcodeunits s))
  split
  · rfl
  · rename_i runningBool
    have one : (JuliaLean.Strings.ix 1).val = 1 := by decide
    have running : (JuliaLean.Strings.ix 1).val < (stringNcodeunits s).val := by
      by_cases h : (JuliaLean.Strings.ix 1).val < (stringNcodeunits s).val
      · exact h
      · exact (runningBool (by simp only [h, decide_false, Bool.not_false])).elim
    rw [one, sizeVal] at running
    apply countLoopMatchesByteLoop
    · simp only [one, sizeVal]
      omega
    · rw [one]; decide
    · rw [one, sizeVal]; omega
    · rw [sizeVal]; omega

/-- Mathematical character normalization used only as an invariant for the existing loop. -/
abbrev countThis (s : JString) (p : Int) : Int := thisindPure (parentByte s) p
abbrev countBv (s : JString) (p : Int) : Nat := (parentByte s p).toNat

/-- Scan valid starts over a consecutive, explicitly bounded byte interval. -/
def countValidFrom (s : JString) : Nat → Index → List Index
  | 0, _ => []
  | k + 1, i => if stringIsvalidIndex s i then
      i :: countValidFrom s k (i + JuliaLean.Strings.ix 1)
    else countValidFrom s k (i + JuliaLean.Strings.ix 1)

/-- The number of absorbed continuation positions in a consecutive interval. -/
def countAbsCnt (s : JString) : Nat → Int → Nat
  | 0, _ => 0
  | k + 1, p => (if countThis s p < p then 1 else 0) + countAbsCnt s k (p + 1)

theorem countSmall (s : JString) : (s.bytes.length : Int) < 2 ^ 62 := by
  have := s.small
  omega

theorem countSubVal (a b : Index) (lo : -(2 ^ 63) ≤ a.val - b.val)
    (hi : a.val - b.val < 2 ^ 63) : (a - b).val = a.val - b.val := by
  change wrapInt .i64 (a.val - b.val) = _
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ a.val - b.val ∧
    a.val - b.val ≤ 9223372036854775807
  omega

theorem countIxVal (x : Int) (lo : -(2 ^ 63) ≤ x) (hi : x < 2 ^ 63) :
    (JuliaLean.Strings.ix x).val = x := by
  change wrapInt .i64 x = _
  apply wrapInt_of_inRange
  change -9223372036854775808 ≤ x ∧ x ≤ 9223372036854775807
  omega

theorem countBoolVal (b : Bool) :
    (JuliaLean.Strings.bInt b).val = if b then 1 else 0 := by
  cases b <;> rfl

theorem countCuNat (s : JString) (i : Index) :
    (JuliaLean.Strings.cu s i).toNat = countBv s i.val := by
  unfold JuliaLean.Strings.cu countBv parentByte
  congr 2
  omega

theorem countThisCases (s : JString) (r : Int) :
    countThis s r = r ∨
    (countThis s r = r - 1 ∧ r - 1 > 0 ∧ 128 ≤ countBv s r ∧ countBv s r < 192 ∧
      192 ≤ countBv s (r - 1) ∧ countBv s (r - 1) ≤ 247) ∨
    (countThis s r = r - 2 ∧ r - 2 > 0 ∧ 128 ≤ countBv s r ∧ countBv s r < 192 ∧
      128 ≤ countBv s (r - 1) ∧ countBv s (r - 1) < 192 ∧
      224 ≤ countBv s (r - 2) ∧ countBv s (r - 2) ≤ 247) ∨
    (countThis s r = r - 3 ∧ r - 3 > 0 ∧ 128 ≤ countBv s r ∧ countBv s r < 192 ∧
      128 ≤ countBv s (r - 1) ∧ countBv s (r - 1) < 192 ∧
      128 ≤ countBv s (r - 2) ∧ countBv s (r - 2) < 192 ∧
      240 ≤ countBv s (r - 3) ∧ countBv s (r - 3) ≤ 247) := by
  simpa only [countThis, countBv, contB_iff, lead1_iff, lead2_iff, lead3_iff, and_assoc]
    using thisindPure_cases (parentByte s) r

theorem countThisLe (s : JString) (r : Int) :
    countThis s r ≤ r ∧ r - 3 ≤ countThis s r := by
  rcases countThisCases s r with h | h | h | h <;> omega

theorem countThisPos (s : JString) (r : Int) (lo : 1 ≤ r) : 1 ≤ countThis s r := by
  rcases countThisCases s r with h | h | h | h <;> omega

theorem countThisOne (s : JString) : countThis s 1 = 1 := by
  rcases countThisCases s 1 with h | h | h | h <;> omega

theorem countThisLead1 (s : JString) (p r : Int) (hr : r = p + 1) (hp : 1 ≤ p)
    (hl : 192 ≤ countBv s p ∧ countBv s p ≤ 247)
    (hc : 128 ≤ countBv s r ∧ countBv s r < 192) : countThis s r = p := by
  subst r
  have e1 : p + 1 - 1 = p := by omega
  have joinedHere : joined (parentByte s) (p + 1) := by
    left
    refine ⟨by omega, (contB_iff _).mpr hc, ?_⟩
    rw [e1]
    exact (lead1_iff _).mpr hl
  have ne : countThis s (p + 1) ≠ p + 1 :=
    fun h => (thisindPure_eq_iff _ _).mp h joinedHere
  rcases countThisCases s (p + 1) with h | h | h | h
  · exact (ne h).elim
  all_goals simp only [e1] at h; omega

theorem countThisLead2 (s : JString) (p r : Int) (hr : r = p + 2) (hp : 1 ≤ p)
    (hl : 224 ≤ countBv s p ∧ countBv s p ≤ 247)
    (hc1 : 128 ≤ countBv s (p + 1) ∧ countBv s (p + 1) < 192)
    (hc : 128 ≤ countBv s r ∧ countBv s r < 192) : countThis s r = p := by
  subst r
  have e1 : p + 2 - 1 = p + 1 := by omega
  have e2 : p + 2 - 2 = p := by omega
  have joinedHere : joined (parentByte s) (p + 2) := by
    right
    left
    refine ⟨by omega, (contB_iff _).mpr hc, ?_, ?_⟩
    · rw [e1]
      exact (contB_iff _).mpr hc1
    · rw [e2]
      exact (lead2_iff _).mpr hl
  have ne : countThis s (p + 2) ≠ p + 2 :=
    fun h => (thisindPure_eq_iff _ _).mp h joinedHere
  rcases countThisCases s (p + 2) with h | h | h | h
  · exact (ne h).elim
  all_goals simp only [e1, e2] at h; omega

theorem countThisLead3 (s : JString) (p r : Int) (hr : r = p + 3) (hp : 1 ≤ p)
    (hl : 240 ≤ countBv s p ∧ countBv s p ≤ 247)
    (hc1 : 128 ≤ countBv s (p + 1) ∧ countBv s (p + 1) < 192)
    (hc2 : 128 ≤ countBv s (p + 2) ∧ countBv s (p + 2) < 192)
    (hc : 128 ≤ countBv s r ∧ countBv s r < 192) : countThis s r = p := by
  subst r
  have e1 : p + 3 - 1 = p + 2 := by omega
  have e2 : p + 3 - 2 = p + 1 := by omega
  have e3 : p + 3 - 3 = p := by omega
  have joinedHere : joined (parentByte s) (p + 3) := by
    right
    right
    refine ⟨by omega, (contB_iff _).mpr hc, ?_, ?_, ?_⟩
    · rw [e1]
      exact (contB_iff _).mpr hc2
    · rw [e2]
      exact (contB_iff _).mpr hc1
    · rw [e3]
      exact (lead3_iff _).mpr hl
  have ne : countThis s (p + 3) ≠ p + 3 :=
    fun h => (thisindPure_eq_iff _ _).mp h joinedHere
  rcases countThisCases s (p + 3) with h | h | h | h
  · exact (ne h).elim
  all_goals simp only [e1, e2, e3] at h; omega

/-- Each byte is either a valid start or is absorbed into a preceding character. -/
theorem countValidFromAbsorbed (s : JString) : ∀ (k : Nat) (i : Index), 1 ≤ i.val →
    i.val + k ≤ s.bytes.length + 1 →
    (countValidFrom s k i).length + countAbsCnt s k i.val = k := by
  intro k
  induction k with
  | zero => intro i _ _; rfl
  | succ k ih =>
    intro i lo hi
    have small := countSmall s
    have nextVal := countAdvanceVal i (by omega) (by omega)
    have remaining := ih (i + JuliaLean.Strings.ix 1) (by omega) (by omega)
    rw [nextVal] at remaining
    simp only [countValidFrom, countAbsCnt]
    have hle := (countThisLe s i.val).1
    have valid := stringIsvalid_iff_pure s i lo (by omega)
    by_cases start : countThis s i.val = i.val
    · have isStart : stringIsvalidIndex s i = true := valid.mpr start
      have notAbsorbed : ¬ countThis s i.val < i.val := by omega
      rw [if_pos isStart, if_neg notAbsorbed, List.length_cons]
      omega
    · have notStart : stringIsvalidIndex s i ≠ true := fun h => start (valid.mp h)
      have absorbed : countThis s i.val < i.val := by omega
      rw [if_neg notStart, if_pos absorbed]
      omega
/-- Structure of an absorbed position `r`: its character starts at a lead byte
`q = countThis s r` at most three bytes back, and the bytes in between are
continuation bytes allowed by the lead byte. -/
theorem countAbsorbedStructure (s : JString) (r : Int) (h : countThis s r < r) :
    1 ≤ countThis s r ∧ r - 3 ≤ countThis s r ∧ 192 ≤ countBv s (countThis s r) ∧ countBv s (countThis s r) ≤ 247 ∧
    (128 ≤ countBv s r ∧ countBv s r < 192) ∧
    (countThis s r + 1 < r →
      (128 ≤ countBv s (countThis s r + 1) ∧ countBv s (countThis s r + 1) < 192) ∧ 224 ≤ countBv s (countThis s r)) ∧
    (countThis s r + 2 < r →
      (128 ≤ countBv s (countThis s r + 2) ∧ countBv s (countThis s r + 2) < 192) ∧ 240 ≤ countBv s (countThis s r)) := by
  rcases countThisCases s r with h' | h' | h' | h'
  · omega
  · rw [h'.1]
    exact ⟨by omega, by omega, by omega, by omega, ⟨by omega, by omega⟩,
      fun _ => by omega, fun _ => by omega⟩
  · rw [h'.1]
    have e1 : r - 2 + 1 = r - 1 := by omega
    rw [e1]
    exact ⟨by omega, by omega, by omega, by omega, ⟨by omega, by omega⟩,
      fun _ => ⟨⟨by omega, by omega⟩, by omega⟩, fun _ => by omega⟩
  · rw [h'.1]
    have e1 : r - 3 + 1 = r - 2 := by omega
    have e2 : r - 3 + 2 = r - 1 := by omega
    rw [e1, e2]
    exact ⟨by omega, by omega, by omega, by omega, ⟨by omega, by omega⟩,
      fun _ => ⟨⟨by omega, by omega⟩, by omega⟩, fun _ => ⟨⟨by omega, by omega⟩, by omega⟩⟩

/-- Every absorbed position after `p` belongs to a character starting at `p` or later. -/
abbrev countLenInv (s : JString) (p : Int) : Prop := ∀ r, p < r → countThis s r < r → p ≤ countThis s r

theorem countInvNonlead (s : JString) (p : Int) (hI : countLenInv s p)
    (hl : ¬ (192 ≤ countBv s p ∧ countBv s p ≤ 247)) :
    ¬ countThis s (p + 1) < p + 1 ∧ countLenInv s (p + 1) := by
  constructor
  · intro ha
    have h1 := hI (p + 1) (by omega) ha
    obtain ⟨_, s2, s3, s4, -⟩ := countAbsorbedStructure s (p + 1) ha
    have hq : countThis s (p + 1) = p := by omega
    rw [hq] at s3 s4; omega
  · intro r hr ha
    have h1 := hI r (by omega) ha
    obtain ⟨_, s2, s3, s4, -⟩ := countAbsorbedStructure s r ha
    refine Classical.byContradiction fun hc => ?_
    have hq : countThis s r = p := by omega
    rw [hq] at s3 s4; omega

theorem countInvLead1 (s : JString) (p : Int) (hI : countLenInv s p)
    (hstop : ¬ ((128 ≤ countBv s (p + 1) ∧ countBv s (p + 1) < 192) ∧ 224 ≤ countBv s p)) :
    countLenInv s (p + 1) := by
  intro r hr ha
  have h1 := hI r (by omega) ha
  obtain ⟨_, s2, _, _, _, s6, _⟩ := countAbsorbedStructure s r ha
  refine Classical.byContradiction fun hc => ?_
  have hq : countThis s r = p := by omega
  rw [hq] at s6
  exact hstop (s6 (by omega))

theorem countInvLead2 (s : JString) (p : Int) (hI : countLenInv s p)
    (hc1 : 128 ≤ countBv s (p + 1) ∧ countBv s (p + 1) < 192)
    (hstop : ¬ ((128 ≤ countBv s (p + 2) ∧ countBv s (p + 2) < 192) ∧ 240 ≤ countBv s p)) :
    countLenInv s (p + 2) := by
  intro r hr ha
  have h1 := hI r (by omega) ha
  obtain ⟨_, s2, s3, _, _, _, s7⟩ := countAbsorbedStructure s r ha
  refine Classical.byContradiction fun hc => ?_
  by_cases hq : countThis s r = p
  · rw [hq] at s7
    exact hstop (s7 (by omega))
  · have hq' : countThis s r = p + 1 := by omega
    rw [hq'] at s3; omega

theorem countInvLead3 (s : JString) (p : Int)
    (hc1 : 128 ≤ countBv s (p + 1) ∧ countBv s (p + 1) < 192)
    (hc2 : 128 ≤ countBv s (p + 2) ∧ countBv s (p + 2) < 192) :
    countLenInv s (p + 3) := by
  intro r hr ha
  obtain ⟨_, s2, s3, _, _, _, _⟩ := countAbsorbedStructure s r ha
  refine Classical.byContradiction fun hc => ?_
  by_cases hq : countThis s r = p + 1
  · rw [hq] at s3; omega
  · have hq' : countThis s r = p + 2 := by omega
    rw [hq'] at s3; omega

theorem countAbsorbedIffContinuation (s : JString) (r : Int) (hc : (128 ≤ countBv s r ∧ countBv s r < 192) → countThis s r < r) :
    (countThis s r < r ↔ (128 ≤ countBv s r ∧ countBv s r < 192)) :=
  ⟨fun ha => (countAbsorbedStructure s r ha).2.2.2.2.1, hc⟩

theorem countLeadCondIff (b : UInt8) :
    (!(decide (0xc0 ≤ b) && decide (b ≤ 0xf7))) = true ↔ ¬ (192 ≤ b.toNat ∧ b.toNat ≤ 247) := by
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    UInt8.le_iff_toNat_le]
  have : (0xc0 : UInt8).toNat = 192 := rfl
  have : (0xf7 : UInt8).toNat = 247 := rfl
  omega

theorem countStopCondIff (x : Bool) (l m : UInt8) :
    (!(x && decide (l ≥ m))) = true ↔ ¬ (x = true ∧ m.toNat ≤ l.toNat) := by
  cases x <;> simp [UInt8.le_iff_toNat_le]

theorem countIsContCu (s : JString) (i : Index) :
    JuliaLean.Strings.isCont (JuliaLean.Strings.cu s i) = true ↔ (128 ≤ countBv s i.val ∧ countBv s i.val < 192) := by
  change contB (JuliaLean.Strings.cu s i) = true ↔ _
  rw [contB_iff, countCuNat]

theorem countAbsCntAbsorbed (s : JString) (k : Nat) (p : Int) (h : countThis s p < p) :
    countAbsCnt s (k + 1) p = 1 + countAbsCnt s k (p + 1) := by
  simp [countAbsCnt, h]

theorem countAbsCntNotAbsorbed (s : JString) (k : Nat) (p : Int) (h : ¬ countThis s p < p) :
    countAbsCnt s (k + 1) p = countAbsCnt s k (p + 1) := by
  simp [countAbsCnt, h]

theorem countSubBoolVal (c : Index) (b : Bool) (h1 : 0 ≤ c.val) (h2 : c.val ≤ 2 ^ 62) :
    (c - JuliaLean.Strings.bInt b).val = c.val - (if b then 1 else 0) := by
  rw [countSubVal _ _ (by rw [countBoolVal]; split <;> omega) (by rw [countBoolVal]; split <;> omega), countBoolVal]

theorem countNoncontNotAbsorbed (s : JString) (r : Int) (hc : ¬ (128 ≤ countBv s r ∧ countBv s r < 192)) :
    ¬ countThis s r < r := fun h => hc (countAbsorbedStructure s r h).2.2.2.2.1

theorem countE224 : (0xe0 : UInt8).toNat = 224 := rfl
theorem countE240 : (0xf0 : UInt8).toNat = 240 := rfl
theorem countE192 : (0xc0 : UInt8).toNat = 192 := rfl
theorem countE247 : (0xf7 : UInt8).toNat = 247 := rfl

theorem countByteLoopSpec (s : JString) (last : Index)
    (lastWithin : last.val ≤ s.bytes.length) : ∀ (k : Nat) (i c : Index), 1 ≤ i.val →
    i.val + k = last.val → countLenInv s i.val →
    countAbsCnt s k (i.val + 1) ≤ c.val → c.val ≤ 2 ^ 62 →
    (JuliaLean.Strings.lenLoop s last k i (JuliaLean.Strings.cu s i) c).val = c.val - countAbsCnt s k (i.val + 1) := by
  have hs := countSmall s
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro i c hi1 hk hI hc1 hc2
    cases k with
    | zero => simp [JuliaLean.Strings.lenLoop, countAbsCnt]
    | succ k =>
      have e1 : (i + JuliaLean.Strings.ix 1).val = i.val + 1 := countAdvanceVal _ (by omega) (by omega)
      simp only [JuliaLean.Strings.lenLoop]
      split
      · rename_i hcnd
        rw [countLeadCondIff, countCuNat] at hcnd
        obtain ⟨hna, hI1⟩ := countInvNonlead s i.val hI hcnd
        have hcnt := countAbsCntNotAbsorbed s k (i.val + 1) hna
        rw [hcnt] at hc1
        rw [ih k (by omega) _ _ (by rw [e1]; omega) (by rw [e1]; omega) (by rw [e1]; exact hI1)
          (by rw [e1]; exact hc1) hc2, e1, hcnt]
      · rename_i hcnd
        rw [countLeadCondIff, countCuNat] at hcnd
        have hl : 192 ≤ countBv s i.val ∧ countBv s i.val ≤ 247 := Classical.byContradiction hcnd
        have hx := countIsContCu s (i + JuliaLean.Strings.ix 1)
        rw [e1] at hx
        by_cases hc : 128 ≤ countBv s (i.val + 1) ∧ countBv s (i.val + 1) < 192
        · have hcnt := countAbsCntAbsorbed s k (i.val + 1)
            (by rw [countThisLead1 s i.val (i.val + 1) rfl hi1 hl hc]; omega)
          rw [hcnt] at hc1
          rw [hx.2 hc]
          have ec := countSubBoolVal c true (by omega) hc2
          simp only [ite_true] at ec
          split
          · rename_i hcnd2
            rw [countStopCondIff, countCuNat, countE224] at hcnd2
            have hstop : ¬ ((128 ≤ countBv s (i.val + 1) ∧ countBv s (i.val + 1) < 192) ∧ 224 ≤ countBv s i.val) :=
              fun h => hcnd2 ⟨rfl, h.2⟩
            rw [ih k (by omega) _ _ (by rw [e1]; omega) (by rw [e1]; omega)
              (by rw [e1]; exact countInvLead1 s i.val hI hstop) (by rw [ec, e1]; omega) (by rw [ec]; omega)]
            rw [ec, e1, hcnt]; omega
          · rename_i hcnd2
            rw [countStopCondIff, countCuNat, countE224] at hcnd2
            have h224 : 224 ≤ countBv s i.val := Classical.byContradiction fun h => hcnd2 fun h' => h h'.2
            cases k with
            | zero =>
              dsimp only
              rw [ec, hcnt]; simp [countAbsCnt]
            | succ k =>
              dsimp only
              have e2 : (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1).val = i.val + 2 := by
                rw [countAdvanceVal _ (by rw [e1]; omega) (by rw [e1]; omega), e1]; omega
              have ei : i.val + 1 + 1 = i.val + 2 := by omega
              rw [ei] at hcnt hc1
              have hx2 := countIsContCu s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)
              rw [e2] at hx2
              by_cases hc2' : 128 ≤ countBv s (i.val + 2) ∧ countBv s (i.val + 2) < 192
              · have hcnt2 := countAbsCntAbsorbed s k (i.val + 2)
                  (by rw [countThisLead2 s i.val (i.val + 2) rfl hi1 ⟨h224, hl.2⟩ hc hc2']; omega)
                rw [hcnt2] at hc1
                rw [hx2.2 hc2']
                have ec2 := countSubBoolVal (c - JuliaLean.Strings.bInt true) true (by rw [ec]; omega) (by rw [ec]; omega)
                simp only [ite_true] at ec2
                split
                · rename_i hcnd3
                  rw [countStopCondIff, countCuNat, countE240] at hcnd3
                  rw [ih k (by omega) _ _ (by rw [e2]; omega) (by rw [e2]; omega)
                    (by rw [e2]; exact countInvLead2 s i.val hI hc (fun h => hcnd3 ⟨rfl, h.2⟩))
                    (by rw [ec2, ec, e2]; omega) (by rw [ec2, ec]; omega)]
                  rw [ec2, ec, e2, hcnt, hcnt2]; omega
                · rename_i hcnd3
                  rw [countStopCondIff, countCuNat, countE240] at hcnd3
                  have h240 : 240 ≤ countBv s i.val :=
                    Classical.byContradiction fun h => hcnd3 fun h' => h h'.2
                  cases k with
                  | zero =>
                    dsimp only
                    rw [ec2, ec, hcnt, hcnt2]; simp [countAbsCnt]; omega
                  | succ k =>
                    dsimp only
                    have e3 : (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1).val = i.val + 3 := by
                      rw [countAdvanceVal _ (by rw [e2]; omega) (by rw [e2]; omega), e2]; omega
                    have ej : i.val + 2 + 1 = i.val + 3 := by omega
                    rw [ej] at hcnt2 hc1
                    have hx3 := countIsContCu s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)
                    rw [e3] at hx3
                    have hI3 : countLenInv s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1).val := by
                      rw [e3]; exact countInvLead3 s i.val hc hc2'
                    by_cases hc3 : 128 ≤ countBv s (i.val + 3) ∧ countBv s (i.val + 3) < 192
                    · have hcnt3 := countAbsCntAbsorbed s k (i.val + 3)
                        (by rw [countThisLead3 s i.val (i.val + 3) rfl hi1 ⟨h240, hl.2⟩ hc hc2' hc3]; omega)
                      rw [hcnt3] at hc1
                      rw [hx3.2 hc3]
                      have ec3 := countSubBoolVal (c - JuliaLean.Strings.bInt true - JuliaLean.Strings.bInt true) true (by rw [ec2, ec]; omega)
                        (by rw [ec2, ec]; omega)
                      simp only [ite_true] at ec3
                      rw [ih k (by omega) _ _ (by rw [e3]; omega) (by rw [e3]; omega) hI3
                        (by rw [ec3, ec2, ec, e3]; omega) (by rw [ec3, ec2, ec]; omega)]
                      rw [ec3, ec2, ec, e3, hcnt, hcnt2, hcnt3]; omega
                    · have hcnt3 := countAbsCntNotAbsorbed s k (i.val + 3) (countNoncontNotAbsorbed s _ hc3)
                      rw [hcnt3] at hc1
                      have hf : JuliaLean.Strings.isCont (JuliaLean.Strings.cu s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)) = false := by
                        cases h : JuliaLean.Strings.isCont (JuliaLean.Strings.cu s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1))
                        · rfl
                        · exact absurd (hx3.1 h) hc3
                      rw [hf]
                      have ec3 := countSubBoolVal (c - JuliaLean.Strings.bInt true - JuliaLean.Strings.bInt true) false (by rw [ec2, ec]; omega)
                        (by rw [ec2, ec]; omega)
                      simp only [Bool.false_eq_true, ite_false] at ec3
                      rw [ih k (by omega) _ _ (by rw [e3]; omega) (by rw [e3]; omega) hI3
                        (by rw [ec3, ec2, ec, e3]; omega) (by rw [ec3, ec2, ec]; omega)]
                      rw [ec3, ec2, ec, e3, hcnt, hcnt2, hcnt3]; omega
              · have hcnt2 := countAbsCntNotAbsorbed s k (i.val + 2) (countNoncontNotAbsorbed s _ hc2')
                rw [hcnt2] at hc1
                have hf : JuliaLean.Strings.isCont (JuliaLean.Strings.cu s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1)) = false := by
                  cases h : JuliaLean.Strings.isCont (JuliaLean.Strings.cu s (i + JuliaLean.Strings.ix 1 + JuliaLean.Strings.ix 1))
                  · rfl
                  · exact absurd (hx2.1 h) hc2'
                rw [hf]
                have ec2 := countSubBoolVal (c - JuliaLean.Strings.bInt true) false (by rw [ec]; omega) (by rw [ec]; omega)
                simp only [Bool.false_eq_true, ite_false] at ec2
                simp only [Bool.false_and, Bool.not_false, ite_true]
                rw [ih k (by omega) _ _ (by rw [e2]; omega) (by rw [e2]; omega)
                  (by rw [e2]; exact countInvLead2 s i.val hI hc (fun h => hc2' h.1))
                  (by rw [ec2, ec, e2]; omega) (by rw [ec2, ec]; omega)]
                rw [ec2, ec, e2, hcnt, hcnt2]; omega
        · have hcnt := countAbsCntNotAbsorbed s k (i.val + 1) (countNoncontNotAbsorbed s _ hc)
          rw [hcnt] at hc1
          have hf : JuliaLean.Strings.isCont (JuliaLean.Strings.cu s (i + JuliaLean.Strings.ix 1)) = false := by
            cases h : JuliaLean.Strings.isCont (JuliaLean.Strings.cu s (i + JuliaLean.Strings.ix 1))
            · rfl
            · exact absurd (hx.1 h) hc
          rw [hf]
          have ec := countSubBoolVal c false (by omega) hc2
          simp only [Bool.false_eq_true, ite_false] at ec
          simp only [Bool.false_and, Bool.not_false, ite_true]
          rw [ih k (by omega) _ _ (by rw [e1]; omega) (by rw [e1]; omega)
            (by rw [e1]; exact countInvLead1 s i.val hI (fun h => hc h.1))
            (by rw [ec, e1]; omega) (by rw [ec]; omega)]
          rw [ec, e1, hcnt]; omega


theorem countNcuVal (s : JString) :
    (JuliaLean.Strings.ncodeunits s).val = (s.bytes.length : Int) := stringNcodeunits_val s

theorem countOneVal : (JuliaLean.Strings.ix 1).val = 1 := rfl

/-- The byte-counted length is the number of valid starts, including malformed bytes. -/
theorem countByteLengthValidStarts (s : JString) :
    (JuliaLean.Strings.length s).val =
      (countValidFrom s s.bytes.length (JuliaLean.Strings.ix 1)).length := by
  have hs := countSmall s
  have hv := countValidFromAbsorbed s s.bytes.length (JuliaLean.Strings.ix 1)
    (by rw [countOneVal]; omega) (by rw [countOneVal]; omega)
  rw [countOneVal] at hv
  unfold JuliaLean.Strings.length JuliaLean.Strings.lengthContinued
  rw [countNcuVal, countOneVal]
  by_cases h1 : 1 < s.bytes.length
  · simp only [show decide ((1 : Int) < s.bytes.length) = true from decide_eq_true (by omega),
      Bool.not_true, Bool.false_eq_true, ite_false]
    obtain ⟨m, hm⟩ : ∃ m, s.bytes.length = m + 1 := ⟨s.bytes.length - 1, by omega⟩
    have hc0 := countAbsCntNotAbsorbed s m 1 (by rw [countThisOne]; omega)
    rw [hm] at hv
    rw [hc0] at hv
    have e : ((s.bytes.length : Int) - 1).toNat = m := by omega
    rw [e]
    have hI : countLenInv s (JuliaLean.Strings.ix 1).val := by
      intro r hr absorbed
      rw [countOneVal] at hr ⊢
      exact countThisPos s r (by omega)
    have result := countByteLoopSpec s (JuliaLean.Strings.ncodeunits s)
      (by rw [countNcuVal]; exact Int.le_refl _) m
      (JuliaLean.Strings.ix 1) (JuliaLean.Strings.ncodeunits s)
      (by rw [countOneVal]; omega) (by rw [countOneVal, countNcuVal]; omega) hI
      (by rw [countOneVal, countNcuVal]; omega) (by rw [countNcuVal]; omega)
    rw [countOneVal, countNcuVal] at result
    rw [result, hm]
    omega
  · simp only [show decide ((1 : Int) < s.bytes.length) = false from decide_eq_false (by omega),
      Bool.not_false, ite_true]
    rw [countNcuVal]
    have : countAbsCnt s s.bytes.length 1 = 0 := by
      rcases (show s.bytes.length = 0 ∨ s.bytes.length = 1 by omega) with h | h <;> rw [h]
      · rfl
      · simp only [countAbsCnt, countThisOne, Int.lt_irrefl, ite_false, Nat.zero_add]
    omega

/-- The frozen whole-String length is the count of valid starts in its storage interval. -/
theorem countSourceLengthValidStarts (s : JString) :
    stringLength s = JuliaLean.Strings.ix
      (Int.ofNat (countValidFrom s s.bytes.length (JuliaLean.Strings.ix 1)).length) := by
  have value := countByteLengthValidStarts s
  have bounds := countValidFromAbsorbed s s.bytes.length (JuliaLean.Strings.ix 1)
    (by rw [countOneVal]; omega) (by rw [countOneVal]; omega)
  have small := s.small
  simp only [Int.ofNat_eq_coe]
  apply Subtype.ext
  rw [countLengthMatchesByteLoop, value,
    countIxVal ((countValidFrom s s.bytes.length (JuliaLean.Strings.ix 1)).length : Int)
      (by omega) (by omega)]

/-- At most one absorbed position is charged per byte. -/
theorem countAbsCntLe (s : JString) (k : Nat) (p : Int) : countAbsCnt s k p ≤ k := by
  induction k generalizing p with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    rw [countAbsCnt]
    have tail := ih (p + 1)
    split <;> omega

/-- Absorption counts add over consecutive byte intervals. -/
theorem countAbsCntAdd (s : JString) (a b : Nat) (p : Int) :
    countAbsCnt s (a + b) p =
      countAbsCnt s a p + countAbsCnt s b (p + (a : Int)) := by
  induction a generalizing p with
  | zero => simp only [Nat.zero_add, countAbsCnt, Int.natCast_zero, Int.add_zero]
  | succ a ih =>
    rw [Nat.succ_add, countAbsCnt, ih, countAbsCnt]
    rw [show p + 1 + (a : Int) = p + ((a + 1 : Nat) : Int) by omega]
    omega

/-- An interval entirely inside previously started characters is fully absorbed. -/
theorem countAbsCntAll (s : JString) (k : Nat) (p : Int)
    (allAbsorbed : ∀ r, p ≤ r → r < p + (k : Int) → countThis s r < r) :
    countAbsCnt s k p = k := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [countAbsCnt, if_pos (allAbsorbed p (Int.le_refl _) (by omega))]
    rw [ih (p + 1) (fun r lo hi => allAbsorbed r (by omega) (by omega))]
    omega

/-- A normalized start satisfies the no-overlap invariant used by the counting loop. -/
theorem countStartInvariant (s : JString) (p : Int) (start : countThis s p = p) :
    countLenInv s p := by
  intro r after absorbed
  exact thisindPure_ge_valid (parentByte s) r p
    ((thisindPure_eq_iff _ _).mp start) (by omega)

/-- The continued source count subtracts exactly the absorbed bytes in the selected suffix. -/
theorem countContinuedSpec (s : JString) (first last count : Index)
    (firstPositive : 1 ≤ first.val) (ordered : first.val ≤ last.val)
    (lastWithin : last.val ≤ s.bytes.length) (invariant : countLenInv s first.val)
    (enough : (countAbsCnt s (last.val - first.val).toNat (first.val + 1) : Int) ≤ count.val)
    (counterBound : count.val ≤ 2 ^ 62) :
    (stringLengthContinued s first last count).val =
      count.val - countAbsCnt s (last.val - first.val).toNat (first.val + 1) := by
  have small := s.small
  unfold stringLengthContinued lengthContinuedString lengthContinuedInternal
  by_cases short : first.val < last.val
  · rw [show (!(first.val < last.val)) = false by simp only [short, decide_true, Bool.not_true]]
    simp only [Bool.false_eq_true, ite_false]
    change (countLoopModel stringByteAt s last (last.val - first.val + 1).toNat first
      (stringByteAt s first) count).val = _
    rw [countLoopMatchesByteLoop s last (last.val - first.val + 1).toNat
      (last.val - first.val).toNat first
      (stringByteAt s first) count (by omega) (by omega) (by omega) (by omega)]
    exact countByteLoopSpec s last lastWithin _ first count firstPositive
      (by omega) invariant enough counterBound
  · have same : last.val = first.val := by omega
    rw [same]
    simp only [Int.lt_irrefl, decide_false, Bool.not_false, ite_true, Int.sub_self,
      Int.toNat_zero, countAbsCnt, Int.natCast_zero, Int.sub_zero]

/-- Arithmetic in the source's initial range counter does not wrap on its storage domain. -/
theorem countRangeInitialVal (s : JString) (first i j : Index)
    (firstPositive : 1 ≤ first.val) (firstBefore : first.val ≤ i.val)
    (ordered : i.val ≤ j.val) (lastWithin : j.val ≤ s.bytes.length) :
    (j - first + stringIndexBool (first.val == i.val)).val =
      j.val - first.val + (if first.val == i.val then (1 : Int) else 0) := by
  have small := s.small
  have difference := countSubVal j first (by omega) (by omega)
  have bitValue : (stringIndexBool (first.val == i.val)).val =
      (if first.val == i.val then (1 : Int) else 0) := by
    exact countBoolVal _
  change wrapInt .i64 ((j - first).val + (stringIndexBool (first.val == i.val)).val) = _
  rw [difference, bitValue]
  exact wrapInt_of_inRange .i64 _ (by
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    split <;> omega)

/-- The accepted nonempty range count is exactly the count of actual valid byte starts. -/
theorem countSourceRangeValidStarts (s : JString) (i j : Index)
    (inside : countRangeDomain s i j) (ordered : i.val ≤ j.val) :
    stringLengthRange s i j = .ok (JuliaLean.Strings.ix
      (Int.ofNat (countValidFrom s (j.val - i.val + 1).toNat i).length)) := by
  obtain ⟨first, normalized, firstValue, result⟩ := countRangeNonempty s i j inside ordered
  have ilo : 1 ≤ i.val := by have := inside.1; omega
  have jhi : j.val ≤ (s.bytes.length : Int) := by
    have h := inside.2.2.2
    rwa [stringNcodeunits_val] at h
  have firstPositive : 1 ≤ first.val := by
    rw [firstValue]
    exact thisindPure_ge_one _ _ ilo
  have firstBefore : first.val ≤ i.val := by
    rw [firstValue]
    exact thisindPure_le _ _
  have isStart : countThis s first.val = first.val := by
    rw [firstValue]
    exact thisindPure_idem _ _
  have initial := countRangeInitialVal s first i j firstPositive firstBefore ordered jhi
  have absorbedBound := countAbsCntLe s (j.val - first.val).toNat (first.val + 1)
  have finite := s.small
  have value := countContinuedSpec s first j
    (j - first + stringIndexBool (first.val == i.val))
    firstPositive (by omega) jhi (countStartInvariant s first.val isStart)
    (by rw [initial]; split <;> omega)
    (by rw [initial]; split <;> omega)
  rw [initial] at value
  have partition := countValidFromAbsorbed s (j.val - i.val + 1).toNat i ilo (by omega)
  have countBound :
      (countValidFrom s (j.val - i.val + 1).toNat i).length ≤ (j.val - i.val + 1).toNat := by
    omega
  rw [result]
  apply congrArg (fun n : Index => (Except.ok n : StringResult Index))
  apply Subtype.ext
  simp only [Int.ofNat_eq_coe]
  rw [value, countIxVal ((countValidFrom s (j.val - i.val + 1).toNat i).length : Int)
    (by omega) (by omega)]
  by_cases same : first.val = i.val
  · have bit : (first.val == i.val) = true := beq_iff_eq.mpr same
    rw [bit, ite_eq_left (show true = true from rfl)]
    have noAbsorbed : ¬ countThis s i.val < i.val := by rw [← same, isStart]; omega
    have startCount := countAbsCntNotAbsorbed s (j.val - i.val).toNat i.val noAbsorbed
    have span : (j.val - i.val + 1).toNat = (j.val - i.val).toNat + 1 := by omega
    have absorbedSpan : countAbsCnt s (j.val - i.val + 1).toNat i.val =
        countAbsCnt s (j.val - i.val).toNat (i.val + 1) := by
      rw [span, startCount]
    rw [absorbedSpan] at partition
    rw [same]
    omega
  · have bit : (first.val == i.val) = false := beq_eq_false_iff_ne.mpr same
    rw [bit, ite_eq_right (show ¬ false = true by decide), Int.add_zero]
    let prefixLen : Nat := (i.val - first.val - 1).toNat
    let selected : Nat := (j.val - i.val + 1).toNat
    have prefixValue : (prefixLen : Int) = i.val - first.val - 1 := by
      dsimp only [prefixLen]
      omega
    have selectedValue : (selected : Int) = j.val - i.val + 1 := by
      dsimp only [selected]
      omega
    have prefixAll : countAbsCnt s prefixLen (first.val + 1) = prefixLen := by
      apply countAbsCntAll
      intro r after before
      have joinedHere := thisindPure_gap (parentByte s) i.val r
        (by rw [← firstValue]; omega) (by omega)
      have le := thisindPure_le (parentByte s) r
      change countThis s r ≤ r at le
      have ne : countThis s r ≠ r :=
        fun h => (thisindPure_eq_iff _ _).mp h joinedHere
      omega
    have sumSpan : (j.val - first.val).toNat = prefixLen + selected := by omega
    have sumCount := countAbsCntAdd s prefixLen selected (first.val + 1)
    rw [show first.val + 1 + (prefixLen : Int) = i.val by omega, prefixAll] at sumCount
    rw [sumSpan, sumCount]
    dsimp only [selected] at *
    omega

end JuliaLean.ChatGPT.Batch4.Group11


namespace JuliaLean.ChatGPT.Batch4.Group11
open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string
open _root_.JuliaLean.Proofs.base.strings.string

/-- Whole String length counts the steps of its actual complete iteration trace. -/
theorem StringsLengthIterateSteps_proven :
    JuliaLean.Proofs.base.strings.string.Round1.StringLengthIterationCount := by
  intro s
  obtain ⟨rows, trace, _⟩ :=
    JuliaLean.Proofs.base.strings.string.JuliaLean.ChatGPT.Batch2.Group5.iterationComplete s
  refine ⟨rows, trace, ?_⟩
  rw [countSourceLengthValidStarts]
  rw [iterTraceLengthWalk s (countValidFrom s) (fun _ => rfl) (fun _ _ => rfl) rows trace]

/-- Accepted String range length counts its actual valid byte indices. -/
theorem StringCharacterLengthRangeStringOnly_proven :
    JuliaLean.Proofs.base.strings.string.Round1.StringCharacterLengthRangeCountsValidIndices := by
  intro s i j firstPositive firstBound lastPositive lastBound
  have inside : countRangeDomain s i j :=
    (countRangeDomainChecks s i j).mpr ⟨⟨firstPositive, firstBound⟩, ⟨lastPositive, lastBound⟩⟩
  by_cases empty : j.val < i.val
  · rw [countRangeEmpty s i j inside empty]
    simp only [Round1.validIndexCount, empty, ite_true, Int.ofNat_eq_coe, Int.natCast_zero]
  · rw [countSourceRangeValidStarts s i j inside (by omega)]
    have lastWithin : j.val ≤ s.bytes.length := by
      have h := inside.2.2.2
      rwa [_root_.JuliaLean.Proofs.base.strings.util.Round6.stringNcodeunits_val] at h
    rw [iterWalkOffsetCount s (countValidFrom s) (fun _ => rfl) (fun _ _ => rfl)
      i j (by omega) (by omega) lastWithin]

/-- String range length has exactly its native endpoint domain and counts iteration starts. -/
theorem StringsRangeLengthNativeDomain_proven :
    JuliaLean.Proofs.base.strings.string.Round3.RangeLengthHasExactlyCharacterDomain := by
  intro s
  obtain ⟨rows, trace, _⟩ :=
    JuliaLean.Proofs.base.strings.string.JuliaLean.ChatGPT.Batch2.Group5.iterationComplete s
  refine ⟨rows, trace, ?_⟩
  intro i j
  by_cases inside : countRangeDomain s i j
  · unfold countRangeDomain at inside
    rw [if_pos inside]
    by_cases empty : j.val < i.val
    · rw [countRangeEmpty s i j inside empty, iterTraceFilterEmpty rows i j empty]
      rfl
    · rw [countSourceRangeValidStarts s i j inside (by omega)]
      have firstPositive := inside.1
      have lastWithin : j.val ≤ s.bytes.length := by
        have h := inside.2.2.2
        rwa [_root_.JuliaLean.Proofs.base.strings.util.Round6.stringNcodeunits_val] at h
      rw [iterWalkTraceInterval s (countValidFrom s) (fun _ => rfl) (fun _ _ => rfl)
        rows trace i j (by omega) (by omega) lastWithin]
  · unfold countRangeDomain at inside
    rw [if_neg inside, countRangeOutside s i j inside]

end JuliaLean.ChatGPT.Batch4.Group11


namespace JuliaLean.ChatGPT.Batch4.Group11
open JuliaLean
open JuliaLean.base.strings.string
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

/-! A helper language and classifier proof over the unchanged source model. -/

inductive Utf8Language : List UInt8 → Prop where
  | empty : Utf8Language []
  | ascii {b rest} (lead : b.toNat < 0x80) (tail : Utf8Language rest) :
      Utf8Language (b :: rest)
  | twoByte {b1 b2 rest} (lead : 0xc2 ≤ b1 ∧ b1 ≤ 0xdf)
      (continuation : 0x80 ≤ b2 ∧ b2 ≤ 0xbf) (tail : Utf8Language rest) :
      Utf8Language (b1 :: b2 :: rest)
  | threeE0 {b2 b3 rest} (second : 0xa0 ≤ b2 ∧ b2 ≤ 0xbf)
      (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf) (tail : Utf8Language rest) :
      Utf8Language (0xe0 :: b2 :: b3 :: rest)
  | threeNormal {b1 b2 b3 rest}
      (lead : (0xe1 ≤ b1 ∧ b1 ≤ 0xec) ∨ (0xee ≤ b1 ∧ b1 ≤ 0xef))
      (second : 0x80 ≤ b2 ∧ b2 ≤ 0xbf) (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf)
      (tail : Utf8Language rest) : Utf8Language (b1 :: b2 :: b3 :: rest)
  | threeEd {b2 b3 rest} (second : 0x80 ≤ b2 ∧ b2 ≤ 0x9f)
      (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf) (tail : Utf8Language rest) :
      Utf8Language (0xed :: b2 :: b3 :: rest)
  | fourF0 {b2 b3 b4 rest} (second : 0x90 ≤ b2 ∧ b2 ≤ 0xbf)
      (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf) (fourth : 0x80 ≤ b4 ∧ b4 ≤ 0xbf)
      (tail : Utf8Language rest) : Utf8Language (0xf0 :: b2 :: b3 :: b4 :: rest)
  | fourNormal {b1 b2 b3 b4 rest} (lead : 0xf1 ≤ b1 ∧ b1 ≤ 0xf3)
      (second : 0x80 ≤ b2 ∧ b2 ≤ 0xbf) (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf)
      (fourth : 0x80 ≤ b4 ∧ b4 ≤ 0xbf) (tail : Utf8Language rest) :
      Utf8Language (b1 :: b2 :: b3 :: b4 :: rest)
  | fourF4 {b2 b3 b4 rest} (second : 0x80 ≤ b2 ∧ b2 ≤ 0x8f)
      (third : 0x80 ≤ b3 ∧ b3 ≤ 0xbf) (fourth : 0x80 ≤ b4 ∧ b4 ≤ 0xbf)
      (tail : Utf8Language rest) : Utf8Language (0xf4 :: b2 :: b3 :: b4 :: rest)

def u8mVectorBytes {V : Type} (length : V → Int) (getByte : V → Int → UInt8)
    (bytes : V) : List UInt8 :=
  (List.range (length bytes).toNat).map
    (fun i => getByte bytes (Int.ofNat (i + 1)))

def Utf8LanguageValidity : Prop :=
  (∀ {V : Type} (length : V → Int) (getByte : V → Int → UInt8)
      (firstindex lastindex : V → Int) (isAscii : V → Int → Int → Bool) (bytes : V),
    0 ≤ length bytes →
    (∀ first last, isAscii bytes first last =
      byteListIsAscii (u8mVectorBytes length getByte bytes) first last) →
    let values := u8mVectorBytes length getByte bytes
    (byteStringClassifyVector length getByte firstindex lastindex isAscii bytes = 1 ↔
      byteListIsAscii values 1 (Int.ofNat values.length) = true) ∧
    (byteStringClassifyVector length getByte firstindex lastindex isAscii bytes = 2 ↔
      byteListIsAscii values 1 (Int.ofNat values.length) = false ∧ Utf8Language values) ∧
    (byteStringClassifyVector length getByte firstindex lastindex isAscii bytes = 0 ↔
      ¬ Utf8Language values) ∧
    (isvalidStringBytes length getByte firstindex lastindex isAscii bytes = true ↔
      Utf8Language values)) ∧
  (∀ {S V : Type} (codeunits : S → V) (length : V → Int)
      (getByte : V → Int → UInt8) (firstindex lastindex : V → Int)
      (isAscii : V → Int → Int → Bool) (s : S),
    (∀ values first last, isAscii values first last =
      byteListIsAscii (u8mVectorBytes length getByte values) first last) →
    let values := u8mVectorBytes length getByte (codeunits s)
    (isvalidStringAbstract codeunits length getByte firstindex lastindex isAscii s = true
      ↔ Utf8Language values) ∧
    (isvalidAbstractString codeunits length getByte firstindex lastindex isAscii s = true
      ↔ Utf8Language values))

 theorem u8mDfaStepRow (state : UInt32) (b : UInt8) :
    utfDfaStep state b = (utf8DfaClassRow (utf8DfaClass b) >>> state) &&& 0x0000001e := by
  have hb : b.toNat < 256 := UInt8.toNat_lt b
  unfold utfDfaStep utf8DfaTable
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa only [List.length_range] using hb)]
  simp only [List.getElem_range, Option.map_some, Option.getD_some, UInt8.ofNat_toNat]

 theorem u8mDfaAsciiStep (b : UInt8) (hb : b.toNat < 128) :
    utfDfaStep utf8DfaAccept b = utf8DfaAccept := by
  rw [u8mDfaStepRow]
  simp only [utf8DfaClass, hb, ite_eq_left]
  rfl

 theorem u8mDfaClassLt (b : UInt8) : utf8DfaClass b < 12 := by
  unfold utf8DfaClass
  simp only [beq_iff_eq]
  by_cases hc0 : b.toNat < 128
  · rw [ite_eq_left hc0]
    decide
  rw [ite_eq_right hc0]
  by_cases hc1 : b.toNat < 144
  · rw [ite_eq_left hc1]
    decide
  rw [ite_eq_right hc1]
  by_cases hc2 : b.toNat < 160
  · rw [ite_eq_left hc2]
    decide
  rw [ite_eq_right hc2]
  by_cases hc3 : b.toNat < 192
  · rw [ite_eq_left hc3]
    decide
  rw [ite_eq_right hc3]
  by_cases hc4 : b.toNat < 194
  · rw [ite_eq_left hc4]
    decide
  rw [ite_eq_right hc4]
  by_cases hc5 : b.toNat < 224
  · rw [ite_eq_left hc5]
    decide
  rw [ite_eq_right hc5]
  by_cases hc6 : b.toNat = 224
  · rw [ite_eq_left hc6]
    decide
  rw [ite_eq_right hc6]
  by_cases hc7 : b.toNat < 237
  · rw [ite_eq_left hc7]
    decide
  rw [ite_eq_right hc7]
  by_cases hc8 : b.toNat = 237
  · rw [ite_eq_left hc8]
    decide
  rw [ite_eq_right hc8]
  by_cases hc9 : b.toNat < 240
  · rw [ite_eq_left hc9]
    decide
  rw [ite_eq_right hc9]
  by_cases hc10 : b.toNat = 240
  · rw [ite_eq_left hc10]
    decide
  rw [ite_eq_right hc10]
  by_cases hc11 : b.toNat < 244
  · rw [ite_eq_left hc11]
    decide
  rw [ite_eq_right hc11]
  by_cases hc12 : b.toNat = 244
  · rw [ite_eq_left hc12]
    decide
  rw [ite_eq_right hc12]
  decide

 theorem u8mDfaInvalidStep (b : UInt8) :
    utfDfaStep utf8DfaInvalid b = utf8DfaInvalid := by
  rw [u8mDfaStepRow]
  have h := u8mDfaClassLt b
  generalize utf8DfaClass b = k at *
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem u8mDfaInvalidFold (bs : List UInt8) :
    bs.foldl utfDfaStep utf8DfaInvalid = utf8DfaInvalid := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rw [List.foldl_cons, u8mDfaInvalidStep, ih]


local macro "u8mOriginalDfaRun" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JuliaLean.base.strings.string
    `JuliaLean.base.strings.string.utfDfaRunLoop))
local macro "u8mOriginalFind" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JuliaLean.base.strings.string
    `JuliaLean.base.strings.string.findNonasciiLoop))
local macro "u8mOriginalSkip" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JuliaLean.base.strings.string
    `JuliaLean.base.strings.string.skipAsciiChunks))
local macro "u8mOriginalClassify" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `JuliaLean.base.strings.string
    `JuliaLean.base.strings.string.classifyNonasciiLoop))

abbrev u8mDfaRun {V : Type} (rd : V → Int → UInt8) (bs : V)
    (last : Int) (fuel : Nat) (i : Int) (st : UInt32) :=
  u8mOriginalDfaRun rd bs last fuel i st
abbrev u8mFind {V : Type} (ascii : V → Int → Int → Bool) (bs : V)
    (last chunk : Int) (fuel : Nat) (i : Int) :=
  u8mOriginalFind ascii bs last chunk fuel i
abbrev u8mSkip {V : Type} (ascii : V → Int → Int → Bool) (bs : V)
    (chunk last : Int) (fuel : Nat) (first stop : Int) (st : UInt32) :=
  u8mOriginalSkip ascii bs chunk last fuel first stop st
abbrev u8mClassify {V : Type} (rd : V → Int → UInt8)
    (fi li : V → Int) (ascii : V → Int → Int → Bool) (bs : V)
    (chunk last : Int) (fuel : Nat) (first stop : Int) (st : UInt32) :=
  u8mOriginalClassify rd fi li ascii bs chunk last fuel first stop st

def u8mDfaRange (rd : Int → UInt8) : Int → Nat → UInt32 → UInt32
  | _, 0, st => st
  | first, n+1, st => u8mDfaRange rd (first+1) n (utfDfaStep st (rd first))

theorem u8mDfaRange_append (rd : Int → UInt8) (first : Int) (n m : Nat) (st : UInt32) :
    u8mDfaRange rd first (n+m) st =
      u8mDfaRange rd (first + n) m (u8mDfaRange rd first n st) := by
  induction n generalizing first st with
  | zero => simp only [Nat.zero_add, Int.natCast_zero, Int.add_zero, u8mDfaRange]
  | succ n ih =>
      rw [Nat.succ_add]
      simp only [u8mDfaRange]
      rw [ih]
      congr 1
      omega

theorem u8mDfaRun_eq {V : Type} (getByte : V → Int → UInt8) (bs : V)
    (last first : Int) (fuel : Nat) (st : UInt32)
    (hf : (last-first+1).toNat ≤ fuel) :
    u8mDfaRun getByte bs last fuel first st =
      u8mDfaRange (getByte bs) first (last-first+1).toNat st := by
  induction fuel generalizing first st with
  | zero =>
      have h : (last-first+1).toNat = 0 := by omega
      rw [h]
      rfl
  | succ fuel ih =>
      change (if first ≤ last then
        u8mDfaRun getByte bs last fuel (first+1) (utfDfaStep st (getByte bs first))
        else st) = _
      by_cases hi : first ≤ last
      · rw [ite_eq_left hi, ih (first+1) (utfDfaStep st (getByte bs first)) (by omega)]
        have he : (last-first+1).toNat = (last-(first+1)+1).toNat + 1 := by omega
        rw [he]
        rfl
      · rw [ite_eq_right hi]
        have hz : (last-first+1).toNat = 0 := by omega
        rw [hz]
        rfl


def u8mDfaWindow (rd : Int → UInt8) (first last : Int) (st : UInt32) : UInt32 :=
  u8mDfaRange rd first (last-first+1).toNat st

theorem u8mDfaWindow_empty (rd : Int → UInt8) (first last : Int) (st : UInt32)
    (h : last < first) : u8mDfaWindow rd first last st = st := by
  have hz : (last-first+1).toNat = 0 := by omega
  simp only [u8mDfaWindow, hz, u8mDfaRange]

theorem u8mDfaWindow_split (rd : Int → UInt8) (first mid last : Int) (st : UInt32)
    (h1 : first ≤ mid) (h2 : mid ≤ last+1) :
    u8mDfaWindow rd first last st =
      u8mDfaWindow rd mid last (u8mDfaWindow rd first (mid-1) st) := by
  have hn : (last-first+1).toNat = (mid-1-first+1).toNat + (last-mid+1).toNat := by omega
  have hi : first + ((mid-1-first+1).toNat : Int) = mid := by omega
  simp only [u8mDfaWindow]
  rw [hn, u8mDfaRange_append, hi]

theorem u8mDfaWindow_advance (rd : Int → UInt8) (first last chunk : Int) (st : UInt32)
    (_hf : first ≤ last) (hc : 0 < chunk) :
    u8mDfaWindow rd first last st =
      u8mDfaWindow rd (first+chunk) last
        (u8mDfaWindow rd first (min last (first+chunk-1)) st) := by
  by_cases h : first+chunk ≤ last
  · rw [Int.min_eq_right (by omega)]
    exact u8mDfaWindow_split rd first (first+chunk) last st (by omega) (by omega)
  · rw [Int.min_eq_left (by omega), u8mDfaWindow_empty rd (first+chunk) last _ (by omega)]

theorem u8mDfaRange_ascii (asciiStep : ∀ b : UInt8, b.toNat < 128 →
      utfDfaStep utf8DfaAccept b = utf8DfaAccept)
    (rd : Int → UInt8) (first : Int) (n : Nat)
    (h : ∀ k : Int, first ≤ k → k < first+n → (rd k).toNat < 128) :
    u8mDfaRange rd first n utf8DfaAccept = utf8DfaAccept := by
  induction n generalizing first with
  | zero => rfl
  | succ n ih =>
      simp only [u8mDfaRange, asciiStep _ (h first (Int.le_refl _) (by omega))]
      exact ih (first+1) (fun k hk1 hk2 => h k (by omega) (by omega))

theorem u8mDfaWindow_ascii (asciiStep : ∀ b : UInt8, b.toNat < 128 →
      utfDfaStep utf8DfaAccept b = utf8DfaAccept)
    (rd : Int → UInt8) (first last : Int)
    (h : ∀ k : Int, first ≤ k → k ≤ last → (rd k).toNat < 128) :
    u8mDfaWindow rd first last utf8DfaAccept = utf8DfaAccept := by
  apply u8mDfaRange_ascii asciiStep
  intro k h1 h2
  exact h k h1 (by omega)

theorem u8mByteAscii (bs : List UInt8) (first last k : Int)
    (ha : byteListIsAscii bs first last = true)
    (h1 : first ≤ k) (h2 : k ≤ last) : (byteListGet bs k).toNat < 128 := by
  have hf : ¬ first > last := by omega
  simp only [byteListIsAscii, hf, ite_false, List.all_eq_true] at ha
  have hk : (k-first).toNat ∈ List.range (last-first+1).toNat := by
    rw [List.mem_range]
    omega
  have h := ha (k-first).toNat hk
  have he : first + ((k-first).toNat : Int) = k := by omega
  have hh : (byteListGet bs (first + ((k-first).toNat : Int))).toNat < 128 :=
    of_decide_eq_true h
  rw [he] at hh
  exact hh

theorem u8mIsvalidDfa_eq {V : Type} (rd : V → Int → UInt8) (bs : V)
    (fi li : V → Int) (first last : Int) (st : UInt32) :
    isvalidUtf8Dfa rd fi li st bs first last =
      u8mDfaWindow (rd bs) first last st := by
  unfold isvalidUtf8Dfa
  change u8mDfaRun rd bs last
    (if first ≤ last then (last-first+1).toNat else 0) first st = _
  apply u8mDfaRun_eq
  split <;> omega

theorem u8mSkip_step {V : Type} (ascii : V → Int → Int → Bool) (bs : V)
    (chunk last : Int) (fuel : Nat) (first stop : Int) (st : UInt32) :
    u8mSkip ascii bs chunk last (fuel+1) first stop st =
      (if st == utf8DfaAccept && ascii bs first stop then
        let next := first+chunk
        if next ≤ last then u8mSkip ascii bs chunk last fuel next (min last (stop+chunk)) st
        else (first,stop,st)
      else (first,stop,st)) := by rfl

theorem u8mSkip_spec {V : Type}
    (asciiStep : ∀ b : UInt8, b.toNat < 128 → utfDfaStep utf8DfaAccept b = utf8DfaAccept)
    (ascii : V → Int → Int → Bool) (bs : V) (rd : Int → UInt8)
    (asciiLaw : ∀ a b k, ascii bs a b = true → a ≤ k → k ≤ b → (rd k).toNat < 128)
    (chunk last : Int) (hc : 0 < chunk) (fuel : Nat) (first stop : Int) (st : UInt32)
    (hs : stop = min last (first+chunk-1)) (hfirst : first ≤ last) :
    let r := u8mSkip ascii bs chunk last fuel first stop st
    first ≤ r.1 ∧ r.1 ≤ last ∧ r.2.1 = min last (r.1+chunk-1) ∧ r.2.2 = st ∧
      u8mDfaWindow rd first last st = u8mDfaWindow rd r.1 last r.2.2 := by
  induction fuel generalizing first stop with
  | zero => exact ⟨Int.le_refl _, hfirst, hs, rfl, rfl⟩
  | succ fuel ih =>
      rw [u8mSkip_step]
      by_cases hcond : (st == utf8DfaAccept && ascii bs first stop) = true
      · rw [ite_eq_left hcond]
        by_cases hnext : first+chunk ≤ last
        · rw [ite_eq_left hnext]
          have stopEq : stop = first+chunk-1 := by rw [hs, Int.min_eq_right (by omega)]
          have newStop : min last (stop+chunk) = min last (first+chunk+chunk-1) := by
            rw [stopEq]
            congr 1 <;> omega
          obtain ⟨hlo, hhi, hstop, hst, hwindow⟩ := ih (first+chunk) (min last (stop+chunk)) newStop hnext
          refine ⟨by omega, hhi, hstop, hst, ?_⟩
          rw [← hwindow]
          have hbits : (st == utf8DfaAccept) = true ∧ ascii bs first stop = true := by
            simpa only [Bool.and_eq_true] using hcond
          have heq : st = utf8DfaAccept := beq_iff_eq.mp hbits.1
          rw [heq, u8mDfaWindow_split rd first (first+chunk) last _ (by omega) (by omega)]
          congr 1
          apply u8mDfaWindow_ascii asciiStep
          intro k h1 h2
          exact asciiLaw first stop k hbits.2 h1 (by omega)
        · rw [ite_eq_right hnext]
          exact ⟨Int.le_refl _, hfirst, hs, rfl, rfl⟩
      · rw [ite_eq_right hcond]
        exact ⟨Int.le_refl _, hfirst, hs, rfl, rfl⟩


theorem u8mClassify_step {V : Type} (rd : V → Int → UInt8)
    (fi li : V → Int) (ascii : V → Int → Int → Bool) (bs : V)
    (chunk last : Int) (fuel : Nat) (first stop : Int) (st : UInt32) :
    u8mClassify rd fi li ascii bs chunk last (fuel+1) first stop st =
      (if first ≤ last then
        let r := u8mSkip ascii bs chunk last fuel first stop st
        let nextState := isvalidUtf8Dfa rd fi li r.2.2 bs r.1 r.2.1
        if nextState == utf8DfaInvalid then 0
        else u8mClassify rd fi li ascii bs chunk last fuel
          (r.1+chunk) (min last (r.2.1+chunk)) nextState
      else if st == utf8DfaAccept then 2 else 0) := by rfl

theorem u8mClassify_sound {V : Type}
    (asciiStep : ∀ b : UInt8, b.toNat < 128 → utfDfaStep utf8DfaAccept b = utf8DfaAccept)
    (rd : V → Int → UInt8) (fi li : V → Int)
    (ascii : V → Int → Int → Bool) (bs : V)
    (asciiLaw : ∀ a b k, ascii bs a b = true → a ≤ k → k ≤ b → (rd bs k).toNat < 128)
    (chunk last : Int) (hc : 0 < chunk) (fuel : Nat) (first stop : Int) (st : UInt32)
    (hs : stop = min last (first+chunk-1))
    (hrun : u8mClassify rd fi li ascii bs chunk last fuel first stop st ≠ 0) :
    u8mDfaWindow (rd bs) first last st = utf8DfaAccept := by
  induction fuel generalizing first stop st with
  | zero =>
      change (if first ≤ last then 0 else if st == utf8DfaAccept then 2 else 0) ≠ 0 at hrun
      by_cases hf : first ≤ last
      · rw [ite_eq_left hf] at hrun
        exact False.elim (hrun rfl)
      · rw [ite_eq_right hf] at hrun
        have he : st = utf8DfaAccept := by
          by_cases he : st == utf8DfaAccept
          · exact beq_iff_eq.mp he
          · rw [ite_eq_right he] at hrun
            exact False.elim (hrun rfl)
        rw [u8mDfaWindow_empty _ _ _ _ (by omega), he]
  | succ fuel ih =>
      rw [u8mClassify_step] at hrun
      by_cases hf : first ≤ last
      · rw [ite_eq_left hf] at hrun
        obtain ⟨hlo, hhi, ht, hv, hw⟩ :=
          u8mSkip_spec asciiStep ascii bs (rd bs) asciiLaw chunk last hc fuel first stop st hs hf
        cases heq : u8mSkip ascii bs chunk last fuel first stop st with
        | mk f p =>
          cases p with
          | mk t v =>
              rw [heq] at hrun hlo hhi ht hv hw
              dsimp only at hrun hlo hhi ht hv hw
              have hstate : isvalidUtf8Dfa rd fi li v bs f t =
                  u8mDfaWindow (rd bs) f t v := by
                exact u8mIsvalidDfa_eq rd bs fi li f t v
              rw [hstate] at hrun
              by_cases herr : u8mDfaWindow (rd bs) f t v == utf8DfaInvalid
              · rw [ite_eq_left herr] at hrun
                exact False.elim (hrun rfl)
              · rw [ite_eq_right herr] at hrun
                have hstop : min last (t+chunk) = min last (f+chunk+chunk-1) := by
                  rw [ht]
                  omega
                have hind := ih (f+chunk) (min last (t+chunk))
                  (u8mDfaWindow (rd bs) f t v) hstop hrun
                rw [hw, u8mDfaWindow_advance (rd bs) f last chunk v (by omega) hc]
                rw [← ht]
                exact hind
      · rw [ite_eq_right hf] at hrun
        have he : st = utf8DfaAccept := by
          by_cases he : st == utf8DfaAccept
          · exact beq_iff_eq.mp he
          · rw [ite_eq_right he] at hrun
            exact False.elim (hrun rfl)
        rw [u8mDfaWindow_empty _ _ _ _ (by omega), he]


theorem u8mFind_step {V : Type} (ascii : V → Int → Int → Bool) (bs : V)
    (last chunk : Int) (fuel : Nat) (first : Int) :
    u8mFind ascii bs last chunk (fuel+1) first =
      (if first ≤ last-chunk then
        if !ascii bs first (first+chunk-1) then some first
        else u8mFind ascii bs last chunk fuel (first+chunk)
      else none) := by rfl

theorem u8mFind_spec {V : Type} (ascii : V → Int → Int → Bool) (bs : V)
    (rd : Int → UInt8)
    (asciiLaw : ∀ a b k, ascii bs a b = true → a ≤ k → k ≤ b → (rd k).toNat < 128)
    (last chunk : Int) (hc : 0 < chunk) (fuel : Nat) (first : Int)
    (hf : (last-first+1).toNat ≤ fuel) :
    match u8mFind ascii bs last chunk fuel first with
    | some start => first ≤ start ∧ start ≤ last ∧
        ∀ k, first ≤ k → k < start → (rd k).toNat < 128
    | none => ∀ k, first ≤ k → k ≤ last-chunk → (rd k).toNat < 128 := by
  induction fuel generalizing first with
  | zero =>
      change ∀ k, first ≤ k → k ≤ last-chunk → _
      intro k h1 h2
      omega
  | succ fuel ih =>
      rw [u8mFind_step]
      by_cases hscan : first ≤ last-chunk
      · rw [ite_eq_left hscan]
        cases ha : ascii bs first (first+chunk-1) with
        | false =>
            simp only [Bool.not_false, ite_true]
            exact ⟨Int.le_refl _, by omega, fun k h1 h2 => by omega⟩
        | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            have hs := ih (first+chunk) (by omega)
            cases hr : u8mFind ascii bs last chunk fuel (first+chunk) with
            | none =>
                rw [hr] at hs
                intro k hk1 hk2
                by_cases hk : k < first+chunk
                · exact asciiLaw first (first+chunk-1) k ha hk1 (by omega)
                · exact hs k (by omega) hk2
            | some start =>
                rw [hr] at hs
                refine ⟨by omega, hs.2.1, ?_⟩
                intro k hk1 hk2
                by_cases hk : k < first+chunk
                · exact asciiLaw first (first+chunk-1) k ha hk1 (by omega)
                · exact hs.2.2 k (by omega) hk2
      · rw [ite_eq_right hscan]
        intro k h1 h2
        omega

theorem u8mFindChunk_spec {V : Type} (ascii : V → Int → Int → Bool) (bs : V)
    (rd : Int → UInt8)
    (asciiLaw : ∀ a b k, ascii bs a b = true → a ≤ k → k ≤ b → (rd k).toNat < 128)
    (last chunk first : Int) (hc : 0 < chunk) (hsize : first+chunk-1 ≤ last) :
    match findNonasciiChunk ascii chunk bs first last with
    | some start => first ≤ start ∧ start ≤ last ∧
        ∀ k, first ≤ k → k < start → (rd k).toNat < 128
    | none => ∀ k, first ≤ k → k ≤ last → (rd k).toNat < 128 := by
  have hfl : first ≤ last := by omega
  change (match (match u8mFind ascii bs last chunk
      (if first ≤ last then (last-first+1).toNat+1 else 1) first with
    | some i => some i
    | none => if !ascii bs (last-chunk+1) last then some (last-chunk+1) else none) with
    | some start => first ≤ start ∧ start ≤ last ∧
        ∀ k, first ≤ k → k < start → (rd k).toNat < 128
    | none => ∀ k, first ≤ k → k ≤ last → (rd k).toNat < 128)
  rw [ite_eq_left hfl]
  have hs := u8mFind_spec ascii bs rd asciiLaw last chunk hc
    ((last-first+1).toNat+1) first (by omega)
  cases hr : u8mFind ascii bs last chunk ((last-first+1).toNat+1) first with
  | some start =>
      rw [hr] at hs
      exact hs
  | none =>
      rw [hr] at hs
      cases ha : ascii bs (last-chunk+1) last with
      | false =>
          simp only [Bool.not_false, ite_true]
          exact ⟨by omega, by omega, fun k h1 h2 => hs k h1 (by omega)⟩
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          intro k h1 h2
          by_cases hk : k ≤ last-chunk
          · exact hs k h1 hk
          · exact asciiLaw (last-chunk+1) last k ha (by omega) h2


theorem u8mNonascii_sound (bs : List UInt8) (first last : Int)
    (h : byteStringClassifyNonascii byteListGet byteListFirstindex byteListLastindex
      byteListIsAscii bs first last ≠ 0) :
    u8mDfaWindow (byteListGet bs) first last utf8DfaAccept = utf8DfaAccept := by
  exact u8mClassify_sound u8mDfaAsciiStep byteListGet byteListFirstindex byteListLastindex
    byteListIsAscii bs (fun a b k ha h1 h2 => u8mByteAscii bs a b k ha h1 h2)
    256 last (by decide) _ first (min last (first+256-1)) utf8DfaAccept rfl h

theorem u8mValid_window (bs : List UInt8) (h : stringBytesAreValidUtf8 bs = true) :
    u8mDfaWindow (byteListGet bs) 1 bs.length utf8DfaAccept = utf8DfaAccept := by
  have hclass : byteStringClassifyVector byteListLength byteListGet byteListFirstindex
      byteListLastindex byteListIsAscii bs ≠ 0 := by
    simpa only [stringBytesAreValidUtf8, isvalidStringBytes, bne_iff_ne] using h
  change (if (bs.length : Int) > 1536 then
      (match findNonasciiChunk byteListIsAscii 1024 bs 1 bs.length with
      | none => 1
      | some start => byteStringClassifyNonascii byteListGet byteListFirstindex
          byteListLastindex byteListIsAscii bs start bs.length)
    else if byteListIsAscii bs 1 bs.length then 1
    else byteStringClassifyNonascii byteListGet byteListFirstindex byteListLastindex
      byteListIsAscii bs 1 bs.length) ≠ 0 at hclass
  by_cases hlong : (bs.length : Int) > 1536
  · rw [ite_eq_left hlong] at hclass
    have hspec := u8mFindChunk_spec byteListIsAscii bs (byteListGet bs)
      (fun a b k ha h1 h2 => u8mByteAscii bs a b k ha h1 h2)
      bs.length 1024 1 (by decide) (by omega)
    cases hfind : findNonasciiChunk byteListIsAscii 1024 bs 1 bs.length with
    | none =>
        rw [hfind] at hspec
        exact u8mDfaWindow_ascii u8mDfaAsciiStep _ _ _ hspec
    | some start =>
        rw [hfind] at hspec hclass
        have hprefix := u8mDfaWindow_ascii u8mDfaAsciiStep (byteListGet bs) 1 (start-1)
          (fun k h1 h2 => hspec.2.2 k h1 (by omega))
        rw [u8mDfaWindow_split (byteListGet bs) 1 start bs.length _ hspec.1 (by omega), hprefix]
        exact u8mNonascii_sound bs start bs.length hclass
  · rw [ite_eq_right hlong] at hclass
    cases ha : byteListIsAscii bs 1 bs.length with
    | false =>
        rw [ha] at hclass
        exact u8mNonascii_sound bs 1 bs.length hclass
    | true =>
        exact u8mDfaWindow_ascii u8mDfaAsciiStep _ _ _
          (fun k h1 h2 => u8mByteAscii bs 1 bs.length k ha h1 h2)

theorem u8mDfaRange_list (rd : Int → UInt8) (xs : List UInt8)
    (first : Int) (st : UInt32)
    (h : ∀ k : Nat, k < xs.length → rd (first+k) = xs.getD k 0) :
    u8mDfaRange rd first xs.length st = xs.foldl utfDfaStep st := by
  induction xs generalizing first st with
  | nil => rfl
  | cons b xs ih =>
      have hb : rd first = b := by
        have hh := h 0 (by simp only [List.length_cons]; omega)
        simpa only [Int.natCast_zero, Int.add_zero, List.getD_cons_zero] using hh
      simp only [List.length_cons, u8mDfaRange, List.foldl_cons, hb]
      apply ih
      intro k hk
      have hh := h (k+1) (by simp only [List.length_cons]; omega)
      have hp : first + ((k+1 : Nat) : Int) = first+1+k := by omega
      rw [hp] at hh
      exact hh

theorem u8mDfaWindow_bytes (bs : List UInt8) (st : UInt32) :
    u8mDfaWindow (byteListGet bs) 1 bs.length st = bs.foldl utfDfaStep st := by
  unfold u8mDfaWindow
  have hn : ((bs.length : Int)-1+1).toNat = bs.length := by omega
  rw [hn]
  apply u8mDfaRange_list
  intro k hk
  unfold byteListGet
  have hi : ((1 : Int)+k).toNat - 1 = k := by omega
  rw [hi]

theorem u8mDfaAccept_of_valid (bs : List UInt8) (h : stringBytesAreValidUtf8 bs = true) :
    bs.foldl utfDfaStep utf8DfaAccept = utf8DfaAccept := by
  rw [← u8mDfaWindow_bytes]
  exact u8mValid_window bs h

theorem u8mStepOne (b : UInt8) :
    utfDfaStep 14 b = if 128 ≤ b.toNat ∧ b.toNat < 192 then utf8DfaAccept else utf8DfaInvalid := by
  rw [u8mDfaStepRow]
  unfold utf8DfaClass
  simp only [beq_iff_eq]
  by_cases hc0 : b.toNat < 128
  · rw [ite_eq_left hc0]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc0]
  by_cases hc1 : b.toNat < 144
  · rw [ite_eq_left hc1]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc1]
  by_cases hc2 : b.toNat < 160
  · rw [ite_eq_left hc2]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc2]
  by_cases hc3 : b.toNat < 192
  · rw [ite_eq_left hc3]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc3]
  by_cases hc4 : b.toNat < 194
  · rw [ite_eq_left hc4]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc4]
  by_cases hc5 : b.toNat < 224
  · rw [ite_eq_left hc5]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc5]
  by_cases hc6 : b.toNat = 224
  · rw [ite_eq_left hc6]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc6]
  by_cases hc7 : b.toNat < 237
  · rw [ite_eq_left hc7]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc7]
  by_cases hc8 : b.toNat = 237
  · rw [ite_eq_left hc8]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc8]
  by_cases hc9 : b.toNat < 240
  · rw [ite_eq_left hc9]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc9]
  by_cases hc10 : b.toNat = 240
  · rw [ite_eq_left hc10]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc10]
  by_cases hc11 : b.toNat < 244
  · rw [ite_eq_left hc11]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc11]
  by_cases hc12 : b.toNat = 244
  · rw [ite_eq_left hc12]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc12]
  rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
  all_goals rfl

theorem u8mStepTwo (b : UInt8) :
    utfDfaStep 18 b = if 128 ≤ b.toNat ∧ b.toNat < 192 then 14 else utf8DfaInvalid := by
  rw [u8mDfaStepRow]
  unfold utf8DfaClass
  simp only [beq_iff_eq]
  by_cases hc0 : b.toNat < 128
  · rw [ite_eq_left hc0]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc0]
  by_cases hc1 : b.toNat < 144
  · rw [ite_eq_left hc1]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc1]
  by_cases hc2 : b.toNat < 160
  · rw [ite_eq_left hc2]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc2]
  by_cases hc3 : b.toNat < 192
  · rw [ite_eq_left hc3]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc3]
  by_cases hc4 : b.toNat < 194
  · rw [ite_eq_left hc4]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc4]
  by_cases hc5 : b.toNat < 224
  · rw [ite_eq_left hc5]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc5]
  by_cases hc6 : b.toNat = 224
  · rw [ite_eq_left hc6]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc6]
  by_cases hc7 : b.toNat < 237
  · rw [ite_eq_left hc7]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc7]
  by_cases hc8 : b.toNat = 237
  · rw [ite_eq_left hc8]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc8]
  by_cases hc9 : b.toNat < 240
  · rw [ite_eq_left hc9]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc9]
  by_cases hc10 : b.toNat = 240
  · rw [ite_eq_left hc10]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc10]
  by_cases hc11 : b.toNat < 244
  · rw [ite_eq_left hc11]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc11]
  by_cases hc12 : b.toNat = 244
  · rw [ite_eq_left hc12]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc12]
  rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
  all_goals rfl

theorem u8mStepE0 (b : UInt8) :
    utfDfaStep 24 b = if 160 ≤ b.toNat ∧ b.toNat < 192 then 14 else utf8DfaInvalid := by
  rw [u8mDfaStepRow]
  unfold utf8DfaClass
  simp only [beq_iff_eq]
  by_cases hc0 : b.toNat < 128
  · rw [ite_eq_left hc0]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc0]
  by_cases hc1 : b.toNat < 144
  · rw [ite_eq_left hc1]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc1]
  by_cases hc2 : b.toNat < 160
  · rw [ite_eq_left hc2]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc2]
  by_cases hc3 : b.toNat < 192
  · rw [ite_eq_left hc3]
    rw [ite_eq_left (show 160 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc3]
  by_cases hc4 : b.toNat < 194
  · rw [ite_eq_left hc4]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc4]
  by_cases hc5 : b.toNat < 224
  · rw [ite_eq_left hc5]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc5]
  by_cases hc6 : b.toNat = 224
  · rw [ite_eq_left hc6]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc6]
  by_cases hc7 : b.toNat < 237
  · rw [ite_eq_left hc7]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc7]
  by_cases hc8 : b.toNat = 237
  · rw [ite_eq_left hc8]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc8]
  by_cases hc9 : b.toNat < 240
  · rw [ite_eq_left hc9]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc9]
  by_cases hc10 : b.toNat = 240
  · rw [ite_eq_left hc10]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc10]
  by_cases hc11 : b.toNat < 244
  · rw [ite_eq_left hc11]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc11]
  by_cases hc12 : b.toNat = 244
  · rw [ite_eq_left hc12]
    rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc12]
  rw [ite_eq_right (show ¬ (160 ≤ b.toNat ∧ b.toNat < 192) by omega)]
  all_goals rfl

theorem u8mStepED (b : UInt8) :
    utfDfaStep 8 b = if 128 ≤ b.toNat ∧ b.toNat < 160 then 14 else utf8DfaInvalid := by
  rw [u8mDfaStepRow]
  unfold utf8DfaClass
  simp only [beq_iff_eq]
  by_cases hc0 : b.toNat < 128
  · rw [ite_eq_left hc0]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
    all_goals rfl
  rw [ite_eq_right hc0]
  by_cases hc1 : b.toNat < 144
  · rw [ite_eq_left hc1]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 160 by omega)]
    all_goals rfl
  rw [ite_eq_right hc1]
  by_cases hc2 : b.toNat < 160
  · rw [ite_eq_left hc2]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 160 by omega)]
    all_goals rfl
  rw [ite_eq_right hc2]
  by_cases hc3 : b.toNat < 192
  · rw [ite_eq_left hc3]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
    all_goals rfl
  rw [ite_eq_right hc3]
  by_cases hc4 : b.toNat < 194
  · rw [ite_eq_left hc4]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
    all_goals rfl
  rw [ite_eq_right hc4]
  by_cases hc5 : b.toNat < 224
  · rw [ite_eq_left hc5]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
    all_goals rfl
  rw [ite_eq_right hc5]
  by_cases hc6 : b.toNat = 224
  · rw [ite_eq_left hc6]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
    all_goals rfl
  rw [ite_eq_right hc6]
  by_cases hc7 : b.toNat < 237
  · rw [ite_eq_left hc7]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
    all_goals rfl
  rw [ite_eq_right hc7]
  by_cases hc8 : b.toNat = 237
  · rw [ite_eq_left hc8]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
    all_goals rfl
  rw [ite_eq_right hc8]
  by_cases hc9 : b.toNat < 240
  · rw [ite_eq_left hc9]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
    all_goals rfl
  rw [ite_eq_right hc9]
  by_cases hc10 : b.toNat = 240
  · rw [ite_eq_left hc10]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
    all_goals rfl
  rw [ite_eq_right hc10]
  by_cases hc11 : b.toNat < 244
  · rw [ite_eq_left hc11]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
    all_goals rfl
  rw [ite_eq_right hc11]
  by_cases hc12 : b.toNat = 244
  · rw [ite_eq_left hc12]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
    all_goals rfl
  rw [ite_eq_right hc12]
  rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 160) by omega)]
  all_goals rfl

theorem u8mStepThree (b : UInt8) :
    utfDfaStep 12 b = if 128 ≤ b.toNat ∧ b.toNat < 192 then 18 else utf8DfaInvalid := by
  rw [u8mDfaStepRow]
  unfold utf8DfaClass
  simp only [beq_iff_eq]
  by_cases hc0 : b.toNat < 128
  · rw [ite_eq_left hc0]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc0]
  by_cases hc1 : b.toNat < 144
  · rw [ite_eq_left hc1]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc1]
  by_cases hc2 : b.toNat < 160
  · rw [ite_eq_left hc2]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc2]
  by_cases hc3 : b.toNat < 192
  · rw [ite_eq_left hc3]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc3]
  by_cases hc4 : b.toNat < 194
  · rw [ite_eq_left hc4]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc4]
  by_cases hc5 : b.toNat < 224
  · rw [ite_eq_left hc5]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc5]
  by_cases hc6 : b.toNat = 224
  · rw [ite_eq_left hc6]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc6]
  by_cases hc7 : b.toNat < 237
  · rw [ite_eq_left hc7]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc7]
  by_cases hc8 : b.toNat = 237
  · rw [ite_eq_left hc8]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc8]
  by_cases hc9 : b.toNat < 240
  · rw [ite_eq_left hc9]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc9]
  by_cases hc10 : b.toNat = 240
  · rw [ite_eq_left hc10]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc10]
  by_cases hc11 : b.toNat < 244
  · rw [ite_eq_left hc11]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc11]
  by_cases hc12 : b.toNat = 244
  · rw [ite_eq_left hc12]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc12]
  rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 192) by omega)]
  all_goals rfl

theorem u8mStepF0 (b : UInt8) :
    utfDfaStep 20 b = if 144 ≤ b.toNat ∧ b.toNat < 192 then 18 else utf8DfaInvalid := by
  rw [u8mDfaStepRow]
  unfold utf8DfaClass
  simp only [beq_iff_eq]
  by_cases hc0 : b.toNat < 128
  · rw [ite_eq_left hc0]
    rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc0]
  by_cases hc1 : b.toNat < 144
  · rw [ite_eq_left hc1]
    rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc1]
  by_cases hc2 : b.toNat < 160
  · rw [ite_eq_left hc2]
    rw [ite_eq_left (show 144 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc2]
  by_cases hc3 : b.toNat < 192
  · rw [ite_eq_left hc3]
    rw [ite_eq_left (show 144 ≤ b.toNat ∧ b.toNat < 192 by omega)]
    all_goals rfl
  rw [ite_eq_right hc3]
  by_cases hc4 : b.toNat < 194
  · rw [ite_eq_left hc4]
    rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc4]
  by_cases hc5 : b.toNat < 224
  · rw [ite_eq_left hc5]
    rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc5]
  by_cases hc6 : b.toNat = 224
  · rw [ite_eq_left hc6]
    rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc6]
  by_cases hc7 : b.toNat < 237
  · rw [ite_eq_left hc7]
    rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc7]
  by_cases hc8 : b.toNat = 237
  · rw [ite_eq_left hc8]
    rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc8]
  by_cases hc9 : b.toNat < 240
  · rw [ite_eq_left hc9]
    rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc9]
  by_cases hc10 : b.toNat = 240
  · rw [ite_eq_left hc10]
    rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc10]
  by_cases hc11 : b.toNat < 244
  · rw [ite_eq_left hc11]
    rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc11]
  by_cases hc12 : b.toNat = 244
  · rw [ite_eq_left hc12]
    rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
    all_goals rfl
  rw [ite_eq_right hc12]
  rw [ite_eq_right (show ¬ (144 ≤ b.toNat ∧ b.toNat < 192) by omega)]
  all_goals rfl

theorem u8mStepF4 (b : UInt8) :
    utfDfaStep 26 b = if 128 ≤ b.toNat ∧ b.toNat < 144 then 18 else utf8DfaInvalid := by
  rw [u8mDfaStepRow]
  unfold utf8DfaClass
  simp only [beq_iff_eq]
  by_cases hc0 : b.toNat < 128
  · rw [ite_eq_left hc0]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc0]
  by_cases hc1 : b.toNat < 144
  · rw [ite_eq_left hc1]
    rw [ite_eq_left (show 128 ≤ b.toNat ∧ b.toNat < 144 by omega)]
    all_goals rfl
  rw [ite_eq_right hc1]
  by_cases hc2 : b.toNat < 160
  · rw [ite_eq_left hc2]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc2]
  by_cases hc3 : b.toNat < 192
  · rw [ite_eq_left hc3]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc3]
  by_cases hc4 : b.toNat < 194
  · rw [ite_eq_left hc4]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc4]
  by_cases hc5 : b.toNat < 224
  · rw [ite_eq_left hc5]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc5]
  by_cases hc6 : b.toNat = 224
  · rw [ite_eq_left hc6]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc6]
  by_cases hc7 : b.toNat < 237
  · rw [ite_eq_left hc7]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc7]
  by_cases hc8 : b.toNat = 237
  · rw [ite_eq_left hc8]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc8]
  by_cases hc9 : b.toNat < 240
  · rw [ite_eq_left hc9]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc9]
  by_cases hc10 : b.toNat = 240
  · rw [ite_eq_left hc10]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc10]
  by_cases hc11 : b.toNat < 244
  · rw [ite_eq_left hc11]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc11]
  by_cases hc12 : b.toNat = 244
  · rw [ite_eq_left hc12]
    rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
    all_goals rfl
  rw [ite_eq_right hc12]
  rw [ite_eq_right (show ¬ (128 ≤ b.toNat ∧ b.toNat < 144) by omega)]
  all_goals rfl

theorem u8mStepAccept (b : UInt8) :
    utfDfaStep utf8DfaAccept b =
      if b.toNat < 128 then utf8DfaAccept
      else if b.toNat < 194 then utf8DfaInvalid
      else if b.toNat < 224 then 14
      else if b.toNat = 224 then 24
      else if b.toNat < 237 then 18
      else if b.toNat = 237 then 8
      else if b.toNat < 240 then 18
      else if b.toNat = 240 then 20
      else if b.toNat < 244 then 12
      else if b.toNat = 244 then 26
      else utf8DfaInvalid := by
  rw [u8mDfaStepRow]
  unfold utf8DfaClass
  simp only [beq_iff_eq]
  by_cases hc0 : b.toNat < 128
  · rw [ite_eq_left hc0]
    rw [ite_eq_left (show b.toNat < 128 by omega)]
    all_goals rfl
  rw [ite_eq_right hc0]
  by_cases hc1 : b.toNat < 144
  · rw [ite_eq_left hc1]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_left (show b.toNat < 194 by omega)]
    all_goals rfl
  rw [ite_eq_right hc1]
  by_cases hc2 : b.toNat < 160
  · rw [ite_eq_left hc2]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_left (show b.toNat < 194 by omega)]
    all_goals rfl
  rw [ite_eq_right hc2]
  by_cases hc3 : b.toNat < 192
  · rw [ite_eq_left hc3]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_left (show b.toNat < 194 by omega)]
    all_goals rfl
  rw [ite_eq_right hc3]
  by_cases hc4 : b.toNat < 194
  · rw [ite_eq_left hc4]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_left (show b.toNat < 194 by omega)]
    all_goals rfl
  rw [ite_eq_right hc4]
  by_cases hc5 : b.toNat < 224
  · rw [ite_eq_left hc5]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 194) by omega)]
    rw [ite_eq_left (show b.toNat < 224 by omega)]
    all_goals rfl
  rw [ite_eq_right hc5]
  by_cases hc6 : b.toNat = 224
  · rw [ite_eq_left hc6]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 194) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 224) by omega)]
    rw [ite_eq_left (show b.toNat = 224 by omega)]
    all_goals rfl
  rw [ite_eq_right hc6]
  by_cases hc7 : b.toNat < 237
  · rw [ite_eq_left hc7]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 194) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 224) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 224) by omega)]
    rw [ite_eq_left (show b.toNat < 237 by omega)]
    all_goals rfl
  rw [ite_eq_right hc7]
  by_cases hc8 : b.toNat = 237
  · rw [ite_eq_left hc8]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 194) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 224) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 224) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 237) by omega)]
    rw [ite_eq_left (show b.toNat = 237 by omega)]
    all_goals rfl
  rw [ite_eq_right hc8]
  by_cases hc9 : b.toNat < 240
  · rw [ite_eq_left hc9]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 194) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 224) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 224) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 237) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 237) by omega)]
    rw [ite_eq_left (show b.toNat < 240 by omega)]
    all_goals rfl
  rw [ite_eq_right hc9]
  by_cases hc10 : b.toNat = 240
  · rw [ite_eq_left hc10]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 194) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 224) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 224) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 237) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 237) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 240) by omega)]
    rw [ite_eq_left (show b.toNat = 240 by omega)]
    all_goals rfl
  rw [ite_eq_right hc10]
  by_cases hc11 : b.toNat < 244
  · rw [ite_eq_left hc11]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 194) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 224) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 224) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 237) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 237) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 240) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 240) by omega)]
    rw [ite_eq_left (show b.toNat < 244 by omega)]
    all_goals rfl
  rw [ite_eq_right hc11]
  by_cases hc12 : b.toNat = 244
  · rw [ite_eq_left hc12]
    rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 194) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 224) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 224) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 237) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 237) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 240) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat = 240) by omega)]
    rw [ite_eq_right (show ¬ (b.toNat < 244) by omega)]
    rw [ite_eq_left (show b.toNat = 244 by omega)]
    all_goals rfl
  rw [ite_eq_right hc12]
  rw [ite_eq_right (show ¬ (b.toNat < 128) by omega)]
  rw [ite_eq_right (show ¬ (b.toNat < 194) by omega)]
  rw [ite_eq_right (show ¬ (b.toNat < 224) by omega)]
  rw [ite_eq_right (show ¬ (b.toNat = 224) by omega)]
  rw [ite_eq_right (show ¬ (b.toNat < 237) by omega)]
  rw [ite_eq_right (show ¬ (b.toNat = 237) by omega)]
  rw [ite_eq_right (show ¬ (b.toNat < 240) by omega)]
  rw [ite_eq_right (show ¬ (b.toNat = 240) by omega)]
  rw [ite_eq_right (show ¬ (b.toNat < 244) by omega)]
  rw [ite_eq_right (show ¬ (b.toNat = 244) by omega)]
  all_goals rfl

theorem u8mNat128 : (128 : UInt8).toNat = 128 := by rfl
theorem u8mNat143 : (143 : UInt8).toNat = 143 := by rfl
theorem u8mNat144 : (144 : UInt8).toNat = 144 := by rfl
theorem u8mNat159 : (159 : UInt8).toNat = 159 := by rfl
theorem u8mNat160 : (160 : UInt8).toNat = 160 := by rfl
theorem u8mNat191 : (191 : UInt8).toNat = 191 := by rfl
theorem u8mNat194 : (194 : UInt8).toNat = 194 := by rfl
theorem u8mNat223 : (223 : UInt8).toNat = 223 := by rfl
theorem u8mNat224 : (224 : UInt8).toNat = 224 := by rfl
theorem u8mNat225 : (225 : UInt8).toNat = 225 := by rfl
theorem u8mNat236 : (236 : UInt8).toNat = 236 := by rfl
theorem u8mNat237 : (237 : UInt8).toNat = 237 := by rfl
theorem u8mNat238 : (238 : UInt8).toNat = 238 := by rfl
theorem u8mNat239 : (239 : UInt8).toNat = 239 := by rfl
theorem u8mNat240 : (240 : UInt8).toNat = 240 := by rfl
theorem u8mNat241 : (241 : UInt8).toNat = 241 := by rfl
theorem u8mNat243 : (243 : UInt8).toNat = 243 := by rfl
theorem u8mNat244 : (244 : UInt8).toNat = 244 := by rfl

theorem u8mWellFormed_dfa_accept (bs : List UInt8) (h : Utf8Language bs) :
    bs.foldl utfDfaStep utf8DfaAccept = utf8DfaAccept := by
  induction h with
  | empty => rfl
  | ascii lead tail ih =>
      rw [List.foldl_cons, u8mDfaAsciiStep _ lead, ih]
  | @twoByte b1 b2 rest lead continuation tail ih =>
      simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244] at lead continuation
      have hs : utfDfaStep utf8DfaAccept b1 = 14 := by
        rw [u8mStepAccept]
        repeat' split
        all_goals first | rfl | omega
      have hc : 128 ≤ b2.toNat ∧ b2.toNat < 192 := by omega
      rw [List.foldl_cons, hs, List.foldl_cons, u8mStepOne, ite_eq_left hc, ih]
  | @threeE0 b2 b3 rest second third tail ih =>
      simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244] at second third
      have h2 : 160 ≤ b2.toNat ∧ b2.toNat < 192 := by omega
      have h3 : 128 ≤ b3.toNat ∧ b3.toNat < 192 := by omega
      rw [List.foldl_cons, show utfDfaStep utf8DfaAccept 0xe0 = 24 by decide,
        List.foldl_cons, u8mStepE0, ite_eq_left h2,
        List.foldl_cons, u8mStepOne, ite_eq_left h3, ih]
  | @threeNormal b1 b2 b3 rest lead second third tail ih =>
      simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244] at lead second third
      have hs : utfDfaStep utf8DfaAccept b1 = 18 := by
        rw [u8mStepAccept]
        repeat' split
        all_goals first | rfl | omega
      have h2 : 128 ≤ b2.toNat ∧ b2.toNat < 192 := by omega
      have h3 : 128 ≤ b3.toNat ∧ b3.toNat < 192 := by omega
      rw [List.foldl_cons, hs, List.foldl_cons, u8mStepTwo, ite_eq_left h2,
        List.foldl_cons, u8mStepOne, ite_eq_left h3, ih]
  | @threeEd b2 b3 rest second third tail ih =>
      simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244] at second third
      have h2 : 128 ≤ b2.toNat ∧ b2.toNat < 160 := by omega
      have h3 : 128 ≤ b3.toNat ∧ b3.toNat < 192 := by omega
      rw [List.foldl_cons, show utfDfaStep utf8DfaAccept 0xed = 8 by decide,
        List.foldl_cons, u8mStepED, ite_eq_left h2,
        List.foldl_cons, u8mStepOne, ite_eq_left h3, ih]
  | @fourF0 b2 b3 b4 rest second third fourth tail ih =>
      simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244] at second third fourth
      have h2 : 144 ≤ b2.toNat ∧ b2.toNat < 192 := by omega
      have h3 : 128 ≤ b3.toNat ∧ b3.toNat < 192 := by omega
      have h4 : 128 ≤ b4.toNat ∧ b4.toNat < 192 := by omega
      rw [List.foldl_cons, show utfDfaStep utf8DfaAccept 0xf0 = 20 by decide,
        List.foldl_cons, u8mStepF0, ite_eq_left h2,
        List.foldl_cons, u8mStepTwo, ite_eq_left h3,
        List.foldl_cons, u8mStepOne, ite_eq_left h4, ih]
  | @fourNormal b1 b2 b3 b4 rest lead second third fourth tail ih =>
      simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244] at lead second third fourth
      have hs : utfDfaStep utf8DfaAccept b1 = 12 := by
        rw [u8mStepAccept]
        repeat' split
        all_goals first | rfl | omega
      have h2 : 128 ≤ b2.toNat ∧ b2.toNat < 192 := by omega
      have h3 : 128 ≤ b3.toNat ∧ b3.toNat < 192 := by omega
      have h4 : 128 ≤ b4.toNat ∧ b4.toNat < 192 := by omega
      rw [List.foldl_cons, hs, List.foldl_cons, u8mStepThree, ite_eq_left h2,
        List.foldl_cons, u8mStepTwo, ite_eq_left h3,
        List.foldl_cons, u8mStepOne, ite_eq_left h4, ih]
  | @fourF4 b2 b3 b4 rest second third fourth tail ih =>
      simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244] at second third fourth
      have h2 : 128 ≤ b2.toNat ∧ b2.toNat < 144 := by omega
      have h3 : 128 ≤ b3.toNat ∧ b3.toNat < 192 := by omega
      have h4 : 128 ≤ b4.toNat ∧ b4.toNat < 192 := by omega
      rw [List.foldl_cons, show utfDfaStep utf8DfaAccept 0xf4 = 26 by decide,
        List.foldl_cons, u8mStepF4, ite_eq_left h2,
        List.foldl_cons, u8mStepTwo, ite_eq_left h3,
        List.foldl_cons, u8mStepOne, ite_eq_left h4, ih]


theorem u8mAcceptedPending (st next : UInt32) (lo hi : Nat)
    (hne : st ≠ utf8DfaAccept)
    (hstep : ∀ b : UInt8, utfDfaStep st b =
      if lo ≤ b.toNat ∧ b.toNat < hi then next else utf8DfaInvalid)
    (bs : List UInt8) :
    bs.foldl utfDfaStep st = utf8DfaAccept ↔
      ∃ b rest, bs = b :: rest ∧ (lo ≤ b.toNat ∧ b.toNat < hi) ∧
        rest.foldl utfDfaStep next = utf8DfaAccept := by
  cases bs with
  | nil =>
      constructor
      · intro h
        exact False.elim (hne h)
      · rintro ⟨b, rest, h, _, _⟩
        cases h
  | cons b rest =>
      constructor
      · intro h
        rw [List.foldl_cons, hstep] at h
        split at h
        next hb => exact ⟨b, rest, rfl, hb, h⟩
        next hb =>
          rw [u8mDfaInvalidFold] at h
          exact False.elim ((by decide : utf8DfaInvalid ≠ utf8DfaAccept) h)
      · rintro ⟨c, tail, hshape, hc, ht⟩
        cases hshape
        rw [List.foldl_cons, hstep, ite_eq_left hc]
        exact ht

theorem u8mDfaAccept_wellFormed (bs : List UInt8)
    (h : bs.foldl utfDfaStep utf8DfaAccept = utf8DfaAccept) : Utf8Language bs := by
  cases bs with
  | nil => exact .empty
  | cons b rest =>
      rw [List.foldl_cons, u8mStepAccept] at h
      by_cases ha : b.toNat < 128
      · rw [ite_eq_left ha] at h
        exact .ascii ha (u8mDfaAccept_wellFormed rest h)
      rw [ite_eq_right ha] at h
      by_cases hx : b.toNat < 194
      · rw [ite_eq_left hx, u8mDfaInvalidFold] at h
        exact False.elim ((by decide : utf8DfaInvalid ≠ utf8DfaAccept) h)
      rw [ite_eq_right hx] at h
      by_cases h2 : b.toNat < 224
      · rw [ite_eq_left h2] at h
        obtain ⟨b2, rest, rfl, hb2, ht⟩ :=
          (u8mAcceptedPending 14 utf8DfaAccept 128 192 (by decide) u8mStepOne rest).mp h
        exact .twoByte (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (u8mDfaAccept_wellFormed rest ht)
      rw [ite_eq_right h2] at h
      by_cases he0 : b.toNat = 224
      · rw [ite_eq_left he0] at h
        have hb : b = 0xe0 := UInt8.toNat_inj.mp he0
        subst b
        obtain ⟨b2, rest, rfl, hb2, ht⟩ :=
          (u8mAcceptedPending 24 14 160 192 (by decide) u8mStepE0 rest).mp h
        obtain ⟨b3, rest, rfl, hb3, ht⟩ :=
          (u8mAcceptedPending 14 utf8DfaAccept 128 192 (by decide) u8mStepOne rest).mp ht
        exact .threeE0 (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (u8mDfaAccept_wellFormed rest ht)
      rw [ite_eq_right he0] at h
      by_cases hn1 : b.toNat < 237
      · rw [ite_eq_left hn1] at h
        obtain ⟨b2, rest, rfl, hb2, ht⟩ :=
          (u8mAcceptedPending 18 14 128 192 (by decide) u8mStepTwo rest).mp h
        obtain ⟨b3, rest, rfl, hb3, ht⟩ :=
          (u8mAcceptedPending 14 utf8DfaAccept 128 192 (by decide) u8mStepOne rest).mp ht
        exact .threeNormal (by left; simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (u8mDfaAccept_wellFormed rest ht)
      rw [ite_eq_right hn1] at h
      by_cases hed : b.toNat = 237
      · rw [ite_eq_left hed] at h
        have hb : b = 0xed := UInt8.toNat_inj.mp hed
        subst b
        obtain ⟨b2, rest, rfl, hb2, ht⟩ :=
          (u8mAcceptedPending 8 14 128 160 (by decide) u8mStepED rest).mp h
        obtain ⟨b3, rest, rfl, hb3, ht⟩ :=
          (u8mAcceptedPending 14 utf8DfaAccept 128 192 (by decide) u8mStepOne rest).mp ht
        exact .threeEd (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (u8mDfaAccept_wellFormed rest ht)
      rw [ite_eq_right hed] at h
      by_cases hn2 : b.toNat < 240
      · rw [ite_eq_left hn2] at h
        obtain ⟨b2, rest, rfl, hb2, ht⟩ :=
          (u8mAcceptedPending 18 14 128 192 (by decide) u8mStepTwo rest).mp h
        obtain ⟨b3, rest, rfl, hb3, ht⟩ :=
          (u8mAcceptedPending 14 utf8DfaAccept 128 192 (by decide) u8mStepOne rest).mp ht
        exact .threeNormal (by right; simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (u8mDfaAccept_wellFormed rest ht)
      rw [ite_eq_right hn2] at h
      by_cases hf0 : b.toNat = 240
      · rw [ite_eq_left hf0] at h
        have hb : b = 0xf0 := UInt8.toNat_inj.mp hf0
        subst b
        obtain ⟨b2, rest, rfl, hb2, ht⟩ :=
          (u8mAcceptedPending 20 18 144 192 (by decide) u8mStepF0 rest).mp h
        obtain ⟨b3, rest, rfl, hb3, ht⟩ :=
          (u8mAcceptedPending 18 14 128 192 (by decide) u8mStepTwo rest).mp ht
        obtain ⟨b4, rest, rfl, hb4, ht⟩ :=
          (u8mAcceptedPending 14 utf8DfaAccept 128 192 (by decide) u8mStepOne rest).mp ht
        exact .fourF0 (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (u8mDfaAccept_wellFormed rest ht)
      rw [ite_eq_right hf0] at h
      by_cases hn3 : b.toNat < 244
      · rw [ite_eq_left hn3] at h
        obtain ⟨b2, rest, rfl, hb2, ht⟩ :=
          (u8mAcceptedPending 12 18 128 192 (by decide) u8mStepThree rest).mp h
        obtain ⟨b3, rest, rfl, hb3, ht⟩ :=
          (u8mAcceptedPending 18 14 128 192 (by decide) u8mStepTwo rest).mp ht
        obtain ⟨b4, rest, rfl, hb4, ht⟩ :=
          (u8mAcceptedPending 14 utf8DfaAccept 128 192 (by decide) u8mStepOne rest).mp ht
        exact .fourNormal (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (u8mDfaAccept_wellFormed rest ht)
      rw [ite_eq_right hn3] at h
      by_cases hf4 : b.toNat = 244
      · rw [ite_eq_left hf4] at h
        have hb : b = 0xf4 := UInt8.toNat_inj.mp hf4
        subst b
        obtain ⟨b2, rest, rfl, hb2, ht⟩ :=
          (u8mAcceptedPending 26 18 128 144 (by decide) u8mStepF4 rest).mp h
        obtain ⟨b3, rest, rfl, hb3, ht⟩ :=
          (u8mAcceptedPending 18 14 128 192 (by decide) u8mStepTwo rest).mp ht
        obtain ⟨b4, rest, rfl, hb4, ht⟩ :=
          (u8mAcceptedPending 14 utf8DfaAccept 128 192 (by decide) u8mStepOne rest).mp ht
        exact .fourF4 (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (by simp only [UInt8.le_iff_toNat_le, u8mNat128, u8mNat143, u8mNat144, u8mNat159, u8mNat160, u8mNat191, u8mNat194, u8mNat223, u8mNat224, u8mNat225, u8mNat236, u8mNat237, u8mNat238, u8mNat239, u8mNat240, u8mNat241, u8mNat243, u8mNat244]; omega)
          (u8mDfaAccept_wellFormed rest ht)
      rw [ite_eq_right hf4, u8mDfaInvalidFold] at h
      exact False.elim ((by decide : utf8DfaInvalid ≠ utf8DfaAccept) h)
termination_by bs.length

theorem u8mDfaAccept_iff_wellFormed (bs : List UInt8) :
    bs.foldl utfDfaStep utf8DfaAccept = utf8DfaAccept ↔ Utf8Language bs :=
  ⟨u8mDfaAccept_wellFormed bs, u8mWellFormed_dfa_accept bs⟩

theorem u8mByteValidity_sound (bs : List UInt8) (h : stringBytesAreValidUtf8 bs = true) :
    Utf8Language bs :=
  u8mDfaAccept_wellFormed bs (u8mDfaAccept_of_valid bs h)


theorem u8mDfaRange_invalid (rd : Int → UInt8) (first : Int) (n : Nat) :
    u8mDfaRange rd first n utf8DfaInvalid = utf8DfaInvalid := by
  induction n generalizing first with
  | zero => rfl
  | succ n ih => rw [u8mDfaRange, u8mDfaInvalidStep, ih]

theorem u8mDfaWindow_invalid (rd : Int → UInt8) (first last : Int) :
    u8mDfaWindow rd first last utf8DfaInvalid = utf8DfaInvalid :=
  u8mDfaRange_invalid rd first _

theorem u8mClassifyExact {V : Type}
    (rd : V → Int → UInt8) (fi li : V → Int)
    (ascii : V → Int → Int → Bool) (bs : V)
    (asciiLaw : ∀ a b k, ascii bs a b = true → a ≤ k → k ≤ b → (rd bs k).toNat < 128)
    (chunk last : Int) (hc : 0 < chunk) (fuel : Nat) (first stop : Int) (st : UInt32)
    (hs : stop = min last (first+chunk-1))
    (hfuel : (last-first+1).toNat ≤ fuel) :
    u8mClassify rd fi li ascii bs chunk last fuel first stop st =
      if u8mDfaWindow (rd bs) first last st = utf8DfaAccept then 2 else 0 := by
  induction fuel generalizing first stop st with
  | zero =>
      have hf : ¬ first ≤ last := by omega
      change (if first ≤ last then 0 else if st == utf8DfaAccept then 2 else 0) = _
      rw [ite_eq_right hf, u8mDfaWindow_empty _ _ _ _ (by omega)]
      simp only [beq_iff_eq]
  | succ fuel ih =>
      rw [u8mClassify_step]
      by_cases hf : first ≤ last
      · rw [ite_eq_left hf]
        obtain ⟨hlo, hhi, ht, hv, hw⟩ :=
          u8mSkip_spec u8mDfaAsciiStep ascii bs (rd bs) asciiLaw chunk last hc fuel first stop st hs hf
        cases heq : u8mSkip ascii bs chunk last fuel first stop st with
        | mk f p =>
          cases p with
          | mk t v =>
              rw [heq] at hlo hhi ht hv hw
              dsimp only at hlo hhi ht hv hw
              dsimp only
              rw [u8mIsvalidDfa_eq]
              have hstop : min last (t+chunk) = min last (f+chunk+chunk-1) := by
                rw [ht]
                omega
              have hremaining : (last-(f+chunk)+1).toNat ≤ fuel := by omega
              have hwhole : u8mDfaWindow (rd bs) first last st =
                  u8mDfaWindow (rd bs) (f+chunk) last (u8mDfaWindow (rd bs) f t v) := by
                rw [hw, u8mDfaWindow_advance (rd bs) f last chunk v (by omega) hc, ← ht]
              by_cases herr : u8mDfaWindow (rd bs) f t v == utf8DfaInvalid
              · rw [ite_eq_left herr]
                have hstate : u8mDfaWindow (rd bs) f t v = utf8DfaInvalid := beq_iff_eq.mp herr
                rw [hwhole, hstate, u8mDfaWindow_invalid]
                decide
              · rw [ite_eq_right herr, ih (f+chunk) (min last (t+chunk))
                  (u8mDfaWindow (rd bs) f t v) hstop hremaining, hwhole]
      · rw [ite_eq_right hf, u8mDfaWindow_empty _ _ _ _ (by omega)]
        simp only [beq_iff_eq]

theorem u8mNonasciiExact (bs : List UInt8) (first last : Int) :
    byteStringClassifyNonascii byteListGet byteListFirstindex byteListLastindex
      byteListIsAscii bs first last =
      if u8mDfaWindow (byteListGet bs) first last utf8DfaAccept = utf8DfaAccept then 2 else 0 := by
  apply u8mClassifyExact byteListGet byteListFirstindex byteListLastindex byteListIsAscii bs
    (fun a b k ha h1 h2 => u8mByteAscii bs a b k ha h1 h2) 256 last (by decide)
    _ first (min last (first+256-1)) utf8DfaAccept rfl
  split <;> omega

theorem u8mAscii_iff (bs : List UInt8) (first last : Int) :
    byteListIsAscii bs first last = true ↔
      ∀ k, first ≤ k → k ≤ last → (byteListGet bs k).toNat < 128 := by
  constructor
  · exact fun ha k h1 h2 => u8mByteAscii bs first last k ha h1 h2
  · intro h
    unfold byteListIsAscii
    split
    next hnil => rfl
    next hn =>
      rw [List.all_eq_true]
      intro k hk
      have hlt : k < (last-first+1).toNat := List.mem_range.mp hk
      simp only [decide_eq_true_eq]
      exact h (first+k) (by omega) (by omega)

theorem u8mFindAscii {V : Type} (ascii : V → Int → Int → Bool) (bs : V)
    (last chunk : Int) (hc : 0 < chunk) (fuel : Nat) (first : Int)
    (h : ∀ a b, first ≤ a → b ≤ last → ascii bs a b = true) :
    u8mFind ascii bs last chunk fuel first = none := by
  induction fuel generalizing first with
  | zero => rfl
  | succ fuel ih =>
      rw [u8mFind_step]
      split
      next hscan =>
        rw [h first (first+chunk-1) (Int.le_refl _) (by omega)]
        simp only [Bool.not_true, Bool.false_eq_true, ite_false]
        apply ih
        intro a b h1 h2
        exact h a b (by omega) h2
      next hn => rfl

theorem u8mFindChunkNone_iff (bs : List UInt8) (first last chunk : Int)
    (hc : 0 < chunk) (hsize : first+chunk-1 ≤ last) :
    findNonasciiChunk byteListIsAscii chunk bs first last = none ↔
      byteListIsAscii bs first last = true := by
  constructor
  · intro h
    have hs := u8mFindChunk_spec byteListIsAscii bs (byteListGet bs)
      (fun a b k ha h1 h2 => u8mByteAscii bs a b k ha h1 h2)
      last chunk first hc hsize
    rw [h] at hs
    exact (u8mAscii_iff bs first last).mpr hs
  · intro h
    have hall : ∀ a b, first ≤ a → b ≤ last → byteListIsAscii bs a b = true := by
      intro a b ha hb
      apply (u8mAscii_iff bs a b).mpr
      intro k h1 h2
      exact u8mByteAscii bs first last k h (by omega) (by omega)
    change (match u8mFind byteListIsAscii bs last chunk
        (if first ≤ last then (last-first+1).toNat+1 else 1) first with
      | some i => some i
      | none => if !byteListIsAscii bs (last-chunk+1) last then some (last-chunk+1) else none) = none
    rw [u8mFindAscii byteListIsAscii bs last chunk hc _ first hall]
    rw [hall (last-chunk+1) last (by omega) (Int.le_refl _)]
    rfl


theorem u8mBytesClassifyExact (bs : List UInt8) :
    byteStringClassifyVector byteListLength byteListGet byteListFirstindex byteListLastindex
      byteListIsAscii bs =
      if byteListIsAscii bs 1 bs.length then 1
      else if bs.foldl utfDfaStep utf8DfaAccept = utf8DfaAccept then 2 else 0 := by
  change (if (bs.length : Int) > 1536 then
      (match findNonasciiChunk byteListIsAscii 1024 bs 1 bs.length with
      | none => 1
      | some start => byteStringClassifyNonascii byteListGet byteListFirstindex
          byteListLastindex byteListIsAscii bs start bs.length)
    else if byteListIsAscii bs 1 bs.length then 1
    else byteStringClassifyNonascii byteListGet byteListFirstindex byteListLastindex
      byteListIsAscii bs 1 bs.length) = _
  by_cases hlong : (bs.length : Int) > 1536
  · rw [ite_eq_left hlong]
    cases hfind : findNonasciiChunk byteListIsAscii 1024 bs 1 bs.length with
    | none =>
        have ha : byteListIsAscii bs 1 bs.length = true :=
          (u8mFindChunkNone_iff bs 1 bs.length 1024 (by decide) (by omega)).mp hfind
        rw [ha]
        rfl
    | some start =>
        have ha : byteListIsAscii bs 1 bs.length = false := by
          cases hh : byteListIsAscii bs 1 bs.length with
          | false => rfl
          | true =>
              have hn := (u8mFindChunkNone_iff bs 1 bs.length 1024 (by decide) (by omega)).mpr hh
              rw [hfind] at hn
              cases hn
        rw [ha]
        change byteStringClassifyNonascii byteListGet byteListFirstindex byteListLastindex
          byteListIsAscii bs start bs.length = _
        rw [u8mNonasciiExact]
        have hs := u8mFindChunk_spec byteListIsAscii bs (byteListGet bs)
          (fun a b k ha h1 h2 => u8mByteAscii bs a b k ha h1 h2)
          bs.length 1024 1 (by decide) (by omega)
        rw [hfind] at hs
        have hp := u8mDfaWindow_ascii u8mDfaAsciiStep (byteListGet bs) 1 (start-1)
          (fun k h1 h2 => hs.2.2 k h1 (by omega))
        have hw : u8mDfaWindow (byteListGet bs) 1 bs.length utf8DfaAccept =
            u8mDfaWindow (byteListGet bs) start bs.length utf8DfaAccept := by
          rw [u8mDfaWindow_split (byteListGet bs) 1 start bs.length _ hs.1 (by omega), hp]
        rw [← u8mDfaWindow_bytes, hw]
        rfl
  · rw [ite_eq_right hlong]
    cases ha : byteListIsAscii bs 1 bs.length with
    | false =>
        change byteStringClassifyNonascii byteListGet byteListFirstindex byteListLastindex
          byteListIsAscii bs 1 bs.length = _
        rw [u8mNonasciiExact, u8mDfaWindow_bytes]
        rfl
    | true => rfl

theorem u8mAsciiWellFormed (bs : List UInt8) (ha : byteListIsAscii bs 1 bs.length = true) :
    Utf8Language bs := by
  apply u8mDfaAccept_wellFormed
  rw [← u8mDfaWindow_bytes]
  apply u8mDfaWindow_ascii u8mDfaAsciiStep
  intro k h1 h2
  exact u8mByteAscii bs 1 bs.length k ha h1 h2

theorem u8mByteValidity_iff (bs : List UInt8) :
    stringBytesAreValidUtf8 bs = true ↔ Utf8Language bs := by
  unfold stringBytesAreValidUtf8 isvalidStringBytes
  rw [u8mBytesClassifyExact]
  cases ha : byteListIsAscii bs 1 bs.length with
  | true =>
      constructor
      · intro _
        exact u8mAsciiWellFormed bs ha
      · intro _
        rfl
  | false =>
      change ((if bs.foldl utfDfaStep utf8DfaAccept = utf8DfaAccept then 2 else 0) != 0) = true ↔ _
      by_cases hd : bs.foldl utfDfaStep utf8DfaAccept = utf8DfaAccept
      · rw [ite_eq_left hd]
        constructor
        · intro _
          exact u8mDfaAccept_wellFormed bs hd
        · intro _
          rfl
      · rw [ite_eq_right hd]
        constructor
        · intro h
          cases h
        · intro h
          exact False.elim (hd (u8mWellFormed_dfa_accept bs h))


theorem u8mDfaRangeCongr (rd₁ rd₂ : Int → UInt8) (first : Int) (n : Nat) (st : UInt32)
    (h : ∀ k, first ≤ k → k < first+n → rd₁ k = rd₂ k) :
    u8mDfaRange rd₁ first n st = u8mDfaRange rd₂ first n st := by
  induction n generalizing first st with
  | zero => rfl
  | succ n ih =>
      rw [u8mDfaRange, u8mDfaRange, h first (Int.le_refl _) (by omega)]
      apply ih
      intro k h1 h2
      exact h k (by omega) (by omega)

theorem u8mDfaWindowCongr (rd₁ rd₂ : Int → UInt8) (first last : Int) (st : UInt32)
    (h : ∀ k, first ≤ k → k ≤ last → rd₁ k = rd₂ k) :
    u8mDfaWindow rd₁ first last st = u8mDfaWindow rd₂ first last st := by
  apply u8mDfaRangeCongr
  intro k h1 h2
  exact h k h1 (by omega)

theorem u8mSkipCongr {V W : Type}
    (ascii₁ : V → Int → Int → Bool) (v : V)
    (ascii₂ : W → Int → Int → Bool) (w : W)
    (h : ∀ a b, ascii₁ v a b = ascii₂ w a b)
    (chunk last : Int) (fuel : Nat) (first stop : Int) (st : UInt32) :
    u8mSkip ascii₁ v chunk last fuel first stop st =
      u8mSkip ascii₂ w chunk last fuel first stop st := by
  induction fuel generalizing first stop with
  | zero => rfl
  | succ fuel ih =>
      rw [u8mSkip_step, u8mSkip_step, h]
      split
      next hc =>
        dsimp only
        split
        next hn => exact ih _ _
        next hn => rfl
      next hc => rfl

theorem u8mFindCongr {V W : Type}
    (ascii₁ : V → Int → Int → Bool) (v : V)
    (ascii₂ : W → Int → Int → Bool) (w : W)
    (h : ∀ a b, ascii₁ v a b = ascii₂ w a b)
    (last chunk : Int) (fuel : Nat) (first : Int) :
    u8mFind ascii₁ v last chunk fuel first = u8mFind ascii₂ w last chunk fuel first := by
  induction fuel generalizing first with
  | zero => rfl
  | succ fuel ih =>
      rw [u8mFind_step, u8mFind_step]
      split
      next hs =>
        rw [h]
        split
        next ha => rfl
        next ha => exact ih _
      next hs => rfl

theorem u8mFindChunkCongr {V W : Type}
    (ascii₁ : V → Int → Int → Bool) (v : V)
    (ascii₂ : W → Int → Int → Bool) (w : W)
    (h : ∀ a b, ascii₁ v a b = ascii₂ w a b)
    (chunk first last : Int) :
    findNonasciiChunk ascii₁ chunk v first last = findNonasciiChunk ascii₂ chunk w first last := by
  change (match u8mFind ascii₁ v last chunk
      (if first ≤ last then (last-first+1).toNat+1 else 1) first with
    | some i => some i
    | none => if !ascii₁ v (last-chunk+1) last then some (last-chunk+1) else none) =
    (match u8mFind ascii₂ w last chunk
      (if first ≤ last then (last-first+1).toNat+1 else 1) first with
    | some i => some i
    | none => if !ascii₂ w (last-chunk+1) last then some (last-chunk+1) else none)
  rw [u8mFindCongr ascii₁ v ascii₂ w h, h]

theorem u8mClassifyCongr {V W : Type}
    (rd₁ : V → Int → UInt8) (fi₁ li₁ : V → Int) (ascii₁ : V → Int → Int → Bool) (v : V)
    (rd₂ : W → Int → UInt8) (fi₂ li₂ : W → Int) (ascii₂ : W → Int → Int → Bool) (w : W)
    (ha : ∀ a b, ascii₁ v a b = ascii₂ w a b)
    (asciiLaw : ∀ a b k, ascii₂ w a b = true → a ≤ k → k ≤ b → (rd₂ w k).toNat < 128)
    (chunk last : Int) (hc : 0 < chunk) (fuel : Nat) (first stop : Int) (st : UInt32)
    (hs : stop = min last (first+chunk-1))
    (hrd : ∀ k, first ≤ k → k ≤ last → rd₁ v k = rd₂ w k) :
    u8mClassify rd₁ fi₁ li₁ ascii₁ v chunk last fuel first stop st =
      u8mClassify rd₂ fi₂ li₂ ascii₂ w chunk last fuel first stop st := by
  induction fuel generalizing first stop st with
  | zero => rfl
  | succ fuel ih =>
      rw [u8mClassify_step, u8mClassify_step]
      by_cases hf : first ≤ last
      · rw [ite_eq_left hf, ite_eq_left hf, u8mSkipCongr ascii₁ v ascii₂ w ha]
        obtain ⟨hlo, hhi, ht, hv, hw⟩ :=
          u8mSkip_spec u8mDfaAsciiStep ascii₂ w (rd₂ w) asciiLaw chunk last hc fuel first stop st hs hf
        cases heq : u8mSkip ascii₂ w chunk last fuel first stop st with
        | mk f p =>
          cases p with
          | mk t val =>
              rw [heq] at hlo hhi ht hv hw
              dsimp only at hlo hhi ht hv hw
              dsimp only
              have hr : isvalidUtf8Dfa rd₁ fi₁ li₁ val v f t =
                  isvalidUtf8Dfa rd₂ fi₂ li₂ val w f t := by
                rw [u8mIsvalidDfa_eq, u8mIsvalidDfa_eq]
                apply u8mDfaWindowCongr
                intro k h1 h2
                exact hrd k (by omega) (by rw [ht] at h2; omega)
              rw [hr]
              split
              next herr => rfl
              next herr =>
                apply ih
                · rw [ht]
                  omega
                · intro k h1 h2
                  exact hrd k (by omega) h2
      · rw [ite_eq_right hf, ite_eq_right hf]

theorem u8mVectorBytesLength {V : Type} (length : V → Int) (getByte : V → Int → UInt8)
    (bytes : V) : (u8mVectorBytes length getByte bytes).length = (length bytes).toNat := by
  simp only [u8mVectorBytes, List.length_map, List.length_range]

theorem u8mVectorByte {V : Type} (length : V → Int) (getByte : V → Int → UInt8)
    (bytes : V) (i : Int) (hlo : 1 ≤ i) (hhi : i ≤ length bytes) :
    getByte bytes i = byteListGet (u8mVectorBytes length getByte bytes) i := by
  unfold byteListGet u8mVectorBytes
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simp only [List.length_range]; omega)]
  simp only [List.getElem_range, Option.map_some, Option.getD_some]
  congr 1
  have hn : i.toNat - 1 + 1 = i.toNat := by omega
  rw [hn]
  exact (Int.toNat_of_nonneg (by omega)).symm

theorem u8mNonasciiCongr {V : Type}
    (length : V → Int) (rd : V → Int → UInt8) (fi li : V → Int)
    (ascii : V → Int → Int → Bool) (v : V)
    (ha : ∀ a b, ascii v a b = byteListIsAscii (u8mVectorBytes length rd v) a b)
    (first last : Int) (hfirst : 1 ≤ first) (hlast : last ≤ length v) :
    byteStringClassifyNonascii rd fi li ascii v first last =
      byteStringClassifyNonascii byteListGet byteListFirstindex byteListLastindex
        byteListIsAscii (u8mVectorBytes length rd v) first last := by
  apply u8mClassifyCongr rd fi li ascii v byteListGet byteListFirstindex byteListLastindex
    byteListIsAscii (u8mVectorBytes length rd v) ha
    (fun a b k hab h1 h2 => u8mByteAscii (u8mVectorBytes length rd v) a b k hab h1 h2)
    256 last (by decide) _ first (min last (first+256-1)) utf8DfaAccept rfl
  intro k h1 h2
  exact u8mVectorByte length rd v k (by omega) (by omega)


theorem u8mVectorClassifyEq {V : Type}
    (length : V → Int) (rd : V → Int → UInt8) (fi li : V → Int)
    (ascii : V → Int → Int → Bool) (v : V)
    (ha : ∀ a b, ascii v a b = byteListIsAscii (u8mVectorBytes length rd v) a b) :
    byteStringClassifyVector length rd fi li ascii v =
      byteStringClassifyVector byteListLength byteListGet byteListFirstindex byteListLastindex
        byteListIsAscii (u8mVectorBytes length rd v) := by
  by_cases hn : 0 ≤ length v
  · have hlen : ((u8mVectorBytes length rd v).length : Int) = length v := by
      rw [u8mVectorBytesLength]
      omega
    change (if length v > 1536 then
        (match findNonasciiChunk ascii 1024 v 1 (length v) with
        | none => 1
        | some start => byteStringClassifyNonascii rd fi li ascii v start (length v))
      else if ascii v 1 (length v) then 1
      else byteStringClassifyNonascii rd fi li ascii v 1 (length v)) =
      (if ((u8mVectorBytes length rd v).length : Int) > 1536 then
        (match findNonasciiChunk byteListIsAscii 1024 (u8mVectorBytes length rd v) 1
            (u8mVectorBytes length rd v).length with
        | none => 1
        | some start => byteStringClassifyNonascii byteListGet byteListFirstindex byteListLastindex
            byteListIsAscii (u8mVectorBytes length rd v) start (u8mVectorBytes length rd v).length)
      else if byteListIsAscii (u8mVectorBytes length rd v) 1 (u8mVectorBytes length rd v).length then 1
      else byteStringClassifyNonascii byteListGet byteListFirstindex byteListLastindex
        byteListIsAscii (u8mVectorBytes length rd v) 1 (u8mVectorBytes length rd v).length)
    rw [hlen]
    by_cases hlong : length v > 1536
    · rw [ite_eq_left hlong, ite_eq_left hlong, u8mFindChunkCongr ascii v byteListIsAscii
        (u8mVectorBytes length rd v) ha]
      cases hf : findNonasciiChunk byteListIsAscii 1024 (u8mVectorBytes length rd v) 1 (length v) with
      | none => rfl
      | some start =>
          have hs := u8mFindChunk_spec byteListIsAscii (u8mVectorBytes length rd v)
            (byteListGet (u8mVectorBytes length rd v))
            (fun a b k hab h1 h2 => u8mByteAscii (u8mVectorBytes length rd v) a b k hab h1 h2)
            (length v) 1024 1 (by decide) (by omega)
          rw [hf] at hs
          exact u8mNonasciiCongr length rd fi li ascii v ha start (length v) hs.1 (Int.le_refl _)
    · rw [ite_eq_right hlong, ite_eq_right hlong, ha]
      split
      next hASCII => rfl
      next hASCII =>
        exact u8mNonasciiCongr length rd fi li ascii v ha 1 (length v) (by decide) (Int.le_refl _)
  · have hzero : (length v).toNat = 0 := by omega
    have hv : u8mVectorBytes length rd v = [] := by
      simp only [u8mVectorBytes, hzero, List.range_zero, List.map_nil]
    have hascii : ascii v 1 (length v) = true := by
      rw [ha, hv]
      unfold byteListIsAscii
      rw [ite_eq_left (by omega)]
    rw [hv]
    change (if length v > 1536 then
        (match findNonasciiChunk ascii 1024 v 1 (length v) with
        | none => 1
        | some start => byteStringClassifyNonascii rd fi li ascii v start (length v))
      else if ascii v 1 (length v) then 1
      else byteStringClassifyNonascii rd fi li ascii v 1 (length v)) = 1
    rw [ite_eq_right (by omega), hascii]
    rfl

theorem u8mCanonicalSpecification (bs : List UInt8) :
    (byteStringClassifyVector byteListLength byteListGet byteListFirstindex byteListLastindex
      byteListIsAscii bs = 1 ↔ byteListIsAscii bs 1 bs.length = true) ∧
    (byteStringClassifyVector byteListLength byteListGet byteListFirstindex byteListLastindex
      byteListIsAscii bs = 2 ↔ byteListIsAscii bs 1 bs.length = false ∧ Utf8Language bs) ∧
    (byteStringClassifyVector byteListLength byteListGet byteListFirstindex byteListLastindex
      byteListIsAscii bs = 0 ↔ ¬ Utf8Language bs) := by
  rw [u8mBytesClassifyExact]
  cases ha : byteListIsAscii bs 1 bs.length with
  | true =>
      have hw := u8mAsciiWellFormed bs ha
      simp only [ite_true, ite_false, hw, Bool.true_eq_false, Bool.false_eq_true,
        true_and, false_and, and_true, and_false,
        not_true_eq_false, not_false_eq_true, iff_self, and_self]
      all_goals decide
  | false =>
      by_cases hd : bs.foldl utfDfaStep utf8DfaAccept = utf8DfaAccept
      · have hw := u8mDfaAccept_wellFormed bs hd
        simp only [ite_true, ite_false, hd, hw, Bool.true_eq_false, Bool.false_eq_true,
          true_and, false_and, and_true, and_false,
          not_true_eq_false, not_false_eq_true, iff_self, and_self]
        all_goals decide
      · have hw : ¬ Utf8Language bs := fun h => hd (u8mWellFormed_dfa_accept bs h)
        simp only [ite_true, ite_false, hd, hw, Bool.true_eq_false, Bool.false_eq_true,
          true_and, false_and, and_true, and_false,
          not_true_eq_false, not_false_eq_true, iff_self, and_self]
        all_goals decide

theorem u8mValidity_proven : Utf8LanguageValidity := by
  constructor
  · intro V length rd fi li ascii v hn ha
    have hc := u8mVectorClassifyEq length rd fi li ascii v ha
    have hs := u8mCanonicalSpecification (u8mVectorBytes length rd v)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hc]
      exact hs.1
    · rw [hc]
      exact hs.2.1
    · rw [hc]
      exact hs.2.2
    · change (byteStringClassifyVector length rd fi li ascii v != 0) = true ↔ _
      rw [hc]
      exact u8mByteValidity_iff (u8mVectorBytes length rd v)
  · intro S V codeunits length rd fi li ascii s ha
    have hc := u8mVectorClassifyEq length rd fi li ascii (codeunits s) (ha (codeunits s))
    have h : (byteStringClassifyVector length rd fi li ascii (codeunits s) != 0) = true ↔
        Utf8Language (u8mVectorBytes length rd (codeunits s)) := by
      rw [hc]
      exact u8mByteValidity_iff (u8mVectorBytes length rd (codeunits s))
    exact ⟨h, h⟩


end JuliaLean.ChatGPT.Batch4.Group11

namespace JuliaLean.ChatGPT.Batch4.Group11
open JuliaLean
open JuliaLean.base.strings.string

theorem utf8Language_to_frozen {bs : List UInt8} (h : Utf8Language bs) :
    JuliaLean.Proofs.base.strings.string.Utf8WellFormed bs := by
  induction h with
  | empty => exact .empty
  | ascii lead tail ih => exact .ascii lead ih
  | twoByte lead continuation tail ih => exact .twoByte lead continuation ih
  | threeE0 second third tail ih => exact .threeE0 second third ih
  | threeNormal lead second third tail ih => exact .threeNormal lead second third ih
  | threeEd second third tail ih => exact .threeEd second third ih
  | fourF0 second third fourth tail ih => exact .fourF0 second third fourth ih
  | fourNormal lead second third fourth tail ih => exact .fourNormal lead second third fourth ih
  | fourF4 second third fourth tail ih => exact .fourF4 second third fourth ih

theorem utf8Language_from_frozen {bs : List UInt8}
    (h : JuliaLean.Proofs.base.strings.string.Utf8WellFormed bs) : Utf8Language bs := by
  induction h with
  | empty => exact .empty
  | ascii lead tail ih => exact .ascii lead ih
  | twoByte lead continuation tail ih => exact .twoByte lead continuation ih
  | threeE0 second third tail ih => exact .threeE0 second third ih
  | threeNormal lead second third tail ih => exact .threeNormal lead second third ih
  | threeEd second third tail ih => exact .threeEd second third ih
  | fourF0 second third fourth tail ih => exact .fourF0 second third fourth ih
  | fourNormal lead second third fourth tail ih => exact .fourNormal lead second third fourth ih
  | fourF4 second third fourth tail ih => exact .fourF4 second third fourth ih

theorem utf8Language_iff_frozen (bs : List UInt8) :
    Utf8Language bs ↔ JuliaLean.Proofs.base.strings.string.Utf8WellFormed bs :=
  ⟨utf8Language_to_frozen, utf8Language_from_frozen⟩

theorem StringscovaStringIsvalidBytesRebuilt_proven : JuliaLean.Proofs.base.strings.string.Utf8Validity := by
  have H := u8mValidity_proven
  constructor
  · intro V length rd fi li ascii v hn ha
    have hs := H.1 length rd fi li ascii v hn ha
    refine ⟨hs.1, ?_, ?_, ?_⟩
    · constructor
      · intro h
        obtain ⟨hASCII, hLanguage⟩ := hs.2.1.mp h
        exact ⟨hASCII, utf8Language_to_frozen hLanguage⟩
      · rintro ⟨hASCII, hLanguage⟩
        exact hs.2.1.mpr ⟨hASCII, utf8Language_from_frozen hLanguage⟩
    · constructor
      · intro h hLanguage
        exact hs.2.2.1.mp h (utf8Language_from_frozen hLanguage)
      · intro h
        apply hs.2.2.1.mpr
        intro hLanguage
        exact h (utf8Language_to_frozen hLanguage)
    · exact hs.2.2.2.trans (utf8Language_iff_frozen _)
  · intro S V codeunits length rd fi li ascii s ha
    have hs := H.2 codeunits length rd fi li ascii s ha
    exact ⟨hs.1.trans (utf8Language_iff_frozen _), hs.2.trans (utf8Language_iff_frozen _)⟩

end JuliaLean.ChatGPT.Batch4.Group11
end

namespace JuliaLean.Proofs.base.strings.string

def entries : List JuliaLean.Registry.Entry := [
  { id := "strings-iterate-valid-indices", juliaFile := "base/strings/string.jl",
    juliaFns := ["iterate(::String,::Int)", "iterate(::StringView,::Int)"],
    statement := "Iteration visits every valid character-start byte index once, in order, for Strings and StringViews.",
    source := "base/strings/string.jl:508-514", status := .todo, prop := ``IterateVisitsValid,
    notes := "Statement defect: The constructible one-byte StringView over [0x80] is visited at index 1 but the frozen continuation-byte mask rejects that start; no Julia-bug refutation is claimed. The exact universal String conjunct, additional trace existence, ordered starts, and bounded actual-view iteration are preserved as partial results." },
  { id := "string-iteration-string-only", juliaFile := "base/strings/string.jl",
    juliaFns := ["isvalid(::String,::Int)", "iterate(::String,::Int)"],
    statement := "A String index is valid exactly when it occurs as an iteration start from index one, including for malformed byte sequences.",
    source := "base/strings/basic.jl:112-116,148-153; base/strings/string.jl:508-514,662",
    status := .proven, prop := ``Round1.StringIndexValidityMatchesIteration, thm := some ``JuliaLean.ChatGPT.Batch2.Group5.StringIterationStringOnly_proven },
  { id := "strings-length-iterate-steps", juliaFile := "base/strings/string.jl",
    juliaFns := ["length(::String)", "iterate(::String,::Int)"],
    statement := "String length equals the number of characters produced by a complete iteration.",
    source := "base/strings/basic.jl:367-376, base/strings/string.jl:508-514,598-600",
    status := .proven, prop := ``Round1.StringLengthIterationCount, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsLengthIterateSteps_proven },
  { id := "strings-thisind-idempotent", juliaFile := "base/strings/string.jl",
    juliaFns := ["thisind(::String,::Int)"],
    statement := "Applying thisind to a valid character index returns that index.",
    source := "base/strings/string.jl:252-271", status := .proven, prop := ``ThisindIdempotent,
    thm := some ``JuliaLean.ChatGPT.Batch2.Group2.StringsThisindIdempotent_proven },
  { id := "stringscova-string-thisind-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["thisind(::String,::Int)"],
    statement := "For every String and every native Int index, thisind returns the iteration-character start covering that byte, at most three bytes back, preserves 0 and ncodeunits+1 and throws BoundsError outside that domain. A complete actual iteration trace must exist; no hypothesis assumes a valid result.",
    source := "base/strings/string.jl:245,252-271; base/strings/basic.jl:416-443; doc/src/manual/strings.md:410-424,773",
    status := .proven, prop := ``Round3.ThisindLocatesCharacter, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringscovaStringThisindRebuilt_proven },
  { id := "strings-prevind-after-nextind", juliaFile := "base/strings/string.jl",
    juliaFns := ["nextind(::String,::Int)", "prevind(::AbstractString,::Int,::Int)"],
    statement := "For every valid String character start i, prevind(s,nextind(s,i)) returns i.",
    source := "base/strings/basic.jl:505-514,564-573; base/strings/string.jl:273-306",
    status := .proven, prop := ``Round1.PrevindAfterNextind,
    thm := some ``JuliaLean.ChatGPT.Batch2.Group2.StringsPrevindAfterNextind_proven },
  { id := "strings-nextind-after-prevind", juliaFile := "base/strings/string.jl",
    juliaFns := ["nextind(::String,::Int)", "prevind(::AbstractString,::Int,::Int)"],
    statement := "For every valid String character start i after the first code unit, nextind(s,prevind(s,i)) returns i.",
    source := "base/strings/basic.jl:505-514,564-573; base/strings/string.jl:273-306",
    status := .proven, prop := ``Round1.NextindAfterPrevind,
    thm := some ``JuliaLean.ChatGPT.Batch2.Group2.StringsNextindAfterPrevind_proven },
  { id := "stringscova-string-nextind-dispatch-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["nextind(::String,::Int)"],
    statement := "For every String/native Int, nextind returns the next iteration-character boundary for any in-bounds byte (including interior/malformed bytes), advances by at most four bytes, maps zero to one and gives BoundsError elsewhere. Complete trace existence is concluded.",
    source := "base/strings/string.jl:273-306; base/strings/basic.jl:516-527; doc/src/manual/strings.md:389-390,410-424,774",
    status := .proven, prop := ``Round3.NextindLocatesFollowingCharacter, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringscovaStringNextindDispatchRebuilt_proven },
  { id := "strings-cmp-malformed", juliaFile := "base/strings/string.jl",
    juliaFns := ["cmp(::String,::String)", "cmp(::AbstractString,::AbstractString)"],
    statement := "String byte comparison agrees with generic AbstractString character comparison, including malformed byte sequences.",
    source := "base/strings/string.jl:221-236, base/strings/basic.jl:275-282,308-317",
    status := .refuted, prop := ``Round1.CmpAgreesOnAllStrings,
    thm := some ``JuliaLean.ChatGPT.Batch2.Group2.StringsCmpMalformed_refuted,
    issue := "none found (queries: issues: cmp malformed string; issues: cmp invalid UTF-8 String AbstractString; issues: isless invalid string)",
    notes := "Confirmed by repro/strings-cmp-malformed.jl." },
  { id := "strings-cmp-valid-utf8", juliaFile := "base/strings/string.jl",
    juliaFns := ["cmp(::String,::String)", "cmp(::AbstractString,::AbstractString)"],
    statement := "On well-formed UTF-8 strings, byte-specialized String comparison agrees with generic AbstractString character comparison.",
    source := "base/strings/string.jl:221-236, base/strings/basic.jl:275-282,308-317",
    status := .proven, prop := ``Round1.CmpAgreesOnValidUtf8, thm := some ``JuliaLean.ChatGPT.Batch2.Group5.StringsCmpValidUtf8_proven },
  { id := "transcode-string-vector-alias", juliaFile := "base/strings/string.jl",
    juliaFns := ["String(::Vector{UInt8})", "jl_genericmemory_to_string (src/genericmemory.c)"],
    statement := "Once String(v) has returned a String, no later operation on arrays changes its bytes.",
    source := "base/strings/string.jl:85,114-127", status := .refuted, prop := ``StringVectorImmutable, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.TranscodeStringVectorAlias_refuted,
    issue := "Searched JuliaLang/julia issues and PRs; duplicate #64194; see bugs/transcode-string-vector-alias.yaml",
    notes := "A retained reshape can mutate the adopted String bytes; reproduced on release and pinned nightly." },
  { id := "memsafety-string-view-physical-index", juliaFile := "base/strings/string.jl",
    juliaFns := ["iterate(::StringView,::Int)", "getindex(::StringView,::Int)"],
    statement := "A successful StringView iteration index is one-based and lies inside its backing byte data.",
    source := "base/strings/string.jl:508-514,540-545", status := .todo,
    prop := ``StringViewAccessesInBounds,
    notes := "Statement defect: The unbounded view model admits length 2^63, which Julia cannot construct; the signed code-unit count then wraps. Require a representable storage bound. iterBoundedViewNonemptyIff proves the iteration clause under length < 2^62, and checkedScalarAccessBounds proves the checked-access clause." },
  { id := "memsafety-string-range-copy", juliaFile := "base/strings/string.jl",
    juliaFns := ["getindex(::String,::UnitRange{Int})"],
    statement := "After range and string-index checks, the copied byte count stays within the source String.",
    source := "base/strings/string.jl:580-595", status := .proven,
    prop := ``StringRangeAccessesInBounds, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.MemsafetyStringRangeCopy_proven,
    notes := "The statement is vacuous and needs restating: the universal callback law requires a bounded JString of every Nat length, contradicting JString.small at amount 2^62. This proof does not establish the intended runtime memory-safety claim; a separate repair review specifies feasible-copy and callback-law obligations." },
  { id := "stringscova-string-getindex-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["getindex(::String,::Int)"],
    statement := "Indexing a valid String character start returns the character yielded by iteration.",
    source := "base/strings/basic.jl:112-116; base/strings/string.jl:508-514,540-545",
    status := .proven, prop := ``Round1.ScalarGetindexMatchesIteration, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringscovaStringGetindexRebuilt_proven },
  { id := "stringscova-string-isvalid-bytes-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["isvalid(::Type{String},::AbstractVector{UInt8})"],
    statement := "String byte validity is exactly membership in the UTF-8 encoding language.",
    source := "base/strings/string.jl:433-502", status := .proven, prop := ``Utf8Validity, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringscovaStringIsvalidBytesRebuilt_proven },
  { id := "stringscova-string-length-view-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["length(::StringView)"],
    statement := "StringView length agrees with String character length over the same bytes.",
    source := "base/strings/string.jl:598-604", status := .proven, prop := ``LengthViewAgreement, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringscovaStringLengthViewRebuilt_proven },
  { id := "strings-stringview-construction", juliaFile := "base/strings/string.jl",
    juliaFns := ["StringView{T}(data::T)"],
    statement := "StringView construction preserves one-based checks and rejects abstract element types.",
    source := "base/strings/string.jl:35-47", status := .proven, prop := ``StringViewConstruction, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsStringviewConstruction_proven },
  { id := "strings-index-error-display", juliaFile := "base/strings/string.jl",
    juliaFns := ["showerror(::IO,::StringIndexError)"],
    statement := "The error display reports the requested index and nearby valid character indices.",
    source := "base/strings/string.jl:62-76", status := .proven, prop := ``StringIndexErrorDisplay, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsIndexErrorDisplay_proven },
  { id := "strings-abstractvector-construction", juliaFile := "base/strings/string.jl",
    juliaFns := ["String(::AbstractVector{UInt8})"],
    statement := "String construction from a byte vector preserves its bytes while transferring temporary memory.",
    source := "base/strings/string.jl:112", status := .proven, prop := ``AbstractVectorStringBytes, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsAbstractvectorConstruction_proven },
  { id := "strings-vector-transfer", juliaFile := "base/strings/string.jl",
    juliaFns := ["String(::Vector{UInt8})", "takestring!(::Vector{UInt8})"],
    statement := "String construction empties the vector and records shared memory only on the generic-memory path.",
    source := "base/strings/string.jl:114-127,159", status := .proven, prop := ``StringVectorTransfer, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsVectorTransfer_proven },
  { id := "strings-unsafe-string-null", juliaFile := "base/strings/string.jl",
    juliaFns := ["unsafe_string(::Union{Ptr{UInt8},Ptr{Int8}},::Integer)", "unsafe_string(::Union{Ptr{UInt8},Ptr{Int8}})"],
    statement := "Both unsafe_string overloads reject a null pointer with ArgumentError.",
    source := "base/strings/string.jl:172-179", status := .proven, prop := ``UnsafeStringRejectsNull, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsUnsafeStringNull_proven },
  { id := "strings-unsafe-string-length-copies-bytes", juliaFile := "base/strings/string.jl",
    juliaFns := ["unsafe_string(::Ptr{UInt8},::Integer)"],
    statement := "The length-taking unsafe_string copies exactly the requested byte count.",
    source := "base/strings/string.jl:172-175", status := .proven, prop := ``UnsafeStringLengthCopiesBytes, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsUnsafeStringLengthCopiesBytes_proven },
  { id := "strings-unsafe-string-nul-prefix", juliaFile := "base/strings/string.jl",
    juliaFns := ["unsafe_string(::Ptr{UInt8})"],
    statement := "The NUL-terminated unsafe_string copies only the byte prefix before the first zero.",
    source := "base/strings/string.jl:176-179", status := .proven, prop := ``UnsafeStringNulCopiesPrefix, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsUnsafeStringNulPrefix_proven },
  { id := "strings-string-from-abstract", juliaFile := "base/strings/string.jl",
    juliaFns := ["String(::AbstractString)"],
    statement := "String(::AbstractString) preserves the byte sequence produced by print_to_string.",
    source := "base/strings/string.jl:192", status := .proven, prop := ``StringFromAbstractStringBytes, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsStringFromAbstract_proven },
  { id := "strings-symbol-string", juliaFile := "base/strings/string.jl",
    juliaFns := ["String(::Symbol)"],
    statement := "Symbol conversion copies the symbol's NUL-terminated byte prefix.",
    source := "base/strings/string.jl:193", status := .proven, prop := ``StringSymbolConversion, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsSymbolString_proven },
  { id := "strings-storage-conversions", juliaFile := "base/strings/string.jl",
    juliaFns := ["unsafe_wrap(::Type{Memory{UInt8}},::String)", "unsafe_wrap(::Type{Vector{UInt8}},::String)",
      "Vector{UInt8}(::CodeUnits{UInt8,String})", "Vector{UInt8}(::String)", "Array{UInt8}(::String)",
      "String(::CodeUnits{UInt8,String})"],
    statement := "String and byte-storage conversions preserve the represented bytes or storage contents.",
    source := "base/strings/string.jl:195-202", status := .proven, prop := ``StringStorageConversions, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsStorageConversions_proven },
  { id := "strings-pointer-offsets", juliaFile := "base/strings/string.jl",
    juliaFns := ["pointer(::String,::Integer)"],
    statement := "The indexed String pointer is the base pointer plus the one-based byte offset minus one.",
    source := "base/strings/string.jl:207", status := .proven, prop := ``StringPointerOffsets, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsPointerOffsets_proven },
  { id := "strings-byte-length", juliaFile := "base/strings/string.jl",
    juliaFns := ["ncodeunits(::String)"],
    statement := "The String codeunit count equals the number of stored bytes.",
    source := "base/strings/string.jl:209", status := .proven, prop := ``ByteLengthMatchesStorage, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsByteLength_proven },
  { id := "strings-codeunit-type", juliaFile := "base/strings/string.jl",
    juliaFns := ["codeunit(::String)"],
    statement := "String's code-unit type is UInt8.",
    source := "base/strings/string.jl:210", status := .proven, prop := ``CodeunitTypeUInt8, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsCodeunitType_proven },
  { id := "strings-codeunit-bytes", juliaFile := "base/strings/string.jl",
    juliaFns := ["codeunit(::String,::Int)"],
    statement := "Each in-bounds String codeunit is the byte stored at that one-based index.",
    source := "base/strings/string.jl:213-217", status := .proven, prop := ``StringCodeunitBytes,
    thm := some ``JuliaLean.ChatGPT.Batch2.Group2.StringsCodeunitBytes_proven },
  { id := "strings-codeunit-bounds", juliaFile := "base/strings/string.jl",
    juliaFns := ["codeunit(::String,::Int)"],
    statement := "For every String and native Int, checked codeunit access equals partial one-based storage lookup: return the actual stored byte exactly on its storage domain, otherwise BoundsError.",
    source := "base/strings/string.jl:213-217; base/strings/basic.jl:45-105; doc/src/manual/strings.md:405-408",
    status := .proven, prop := ``Round3.CodeunitHasExactlyStorageDomain, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsCodeunitBounds_proven },
  { id := "strings-lastindex-character-start", juliaFile := "base/strings/string.jl",
    juliaFns := ["lastindex(::String)"],
    statement := "lastindex(String) is the start of the final character in complete actual iteration, or zero for an empty String.",
    source := "base/strings/string.jl:249; base/abstractarray.jl:410-418; doc/src/manual/strings.md:195-200,766-768",
    status := .proven, prop := ``Round3.LastindexIsFinalCharacterStart, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsLastindexCharacterStart_proven },
  { id := "strings-string-index-validity", juliaFile := "base/strings/string.jl",
    juliaFns := ["isvalid(::String,::Int)"],
    statement := "An in-bounds string index is valid exactly when its byte is not a continuation byte.",
    source := "base/strings/string.jl:662", status := .todo, prop := ``StringIndexValidity,
    notes := "Statement defect: For the constructible String(UInt8[0x80]), isvalid(s,1) is true while the continuation-byte mask is false. This is normal malformed-character behavior; use actual character boundaries or an appropriate valid-UTF-8 restriction." },
  { id := "strings-character-length-range", juliaFile := "base/strings/string.jl",
    juliaFns := ["_length_continued", "length_continued(::String)", "length_continued(::StringView)",
      "_length(::Union{String,StringView})", "length(::String,::Int,::Int)", "length(::StringView,::Int,::Int)"],
    statement := "Range length counts bytes that are not UTF-8 continuation bytes after aligning the first index to its character start.",
    source := "base/strings/string.jl:615-658", status := .todo, prop := ``CharacterLengthRange,
    notes := "Statement defect: For String(UInt8[0x80]) and endpoints 1,1, Julia and the model return length 1 but the frozen nonContinuationCount is 0. Count actual starts in the original requested interval; merely aligning the left endpoint is also insufficient." },
  { id := "string-character-length-range-string-only", juliaFile := "base/strings/string.jl",
    juliaFns := ["length(::String,::Int,::Int)"],
    statement := "String range length equals the number of valid character-start indices in the requested interval.",
    source := "base/strings/basic.jl:367-376; base/strings/string.jl:607-658",
    status := .proven, prop := ``Round1.StringCharacterLengthRangeCountsValidIndices, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringCharacterLengthRangeStringOnly_proven },
  { id := "strings-range-length-native-domain", juliaFile := "base/strings/string.jl",
    juliaFns := ["length(::String,::Int,::Int)"],
    statement := "For every String and every pair of native Ints, length(s,i,j) counts complete actual iteration starts in the inclusive interval on exactly 1<=i<=ncodeunits+1 and 0<=j<=ncodeunits, including empty spans, and otherwise gives BoundsError. Complete trace existence is concluded, and malformed byte patterns remain.",
    source := "base/strings/string.jl:607-609,615-658; base/strings/basic.jl:367-379; doc/src/manual/strings.md:769-770",
    status := .proven, prop := ``Round3.RangeLengthHasExactlyCharacterDomain, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsRangeLengthNativeDomain_proven },
  { id := "strings-length-view-agreement", juliaFile := "base/strings/string.jl",
    juliaFns := ["length(::StringView)", "length(::String)"],
    statement := "StringView and String have equal character lengths over the same bytes.",
    source := "base/strings/string.jl:598-604", status := .proven, prop := ``LengthViewAgreement, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsLengthViewAgreement_proven },
  { id := "strings-ascii-agreement", juliaFile := "base/strings/string.jl",
    juliaFns := ["isascii(::String)"],
    statement := "A String is ASCII exactly when every character yielded by iteration is ASCII.",
    source := "base/strings/basic.jl:590-592; base/strings/string.jl:508-514,665",
    status := .proven, prop := ``Round2.AsciiMatchesIteratedCharacters,
    thm := some ``JuliaLean.ChatGPT.Batch3.Group4.StringsAsciiAgreement_proven },
  { id := "strings-string-typemin", juliaFile := "base/strings/string.jl",
    juliaFns := ["typemin(::Type{String})", "typemin(::String)"],
    statement := "The minimum String value is the empty string.",
    source := "base/strings/string.jl:240-241", status := .proven, prop := ``StringTypeminEmpty, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsStringTypemin_proven },
  { id := "strings-string-equality-bytes", juliaFile := "base/strings/string.jl",
    juliaFns := ["==(String,String)"],
    statement := "String equality is byte-sequence equality.",
    source := "base/strings/string.jl:238", status := .proven, prop := ``StringEqualityByContents, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsStringEqualityBytes_proven },
  { id := "strings-repeat-character", juliaFile := "base/strings/string.jl",
    juliaFns := ["repeat(::AbstractChar,::Integer)"],
    statement := "Repeating a character rejects negative counts with ArgumentError.",
    source := "base/strings/string.jl:682-715", status := .proven, prop := ``RepeatCharRejectsNegative, thm := some ``JuliaLean.ChatGPT.Batch4.Group11.StringsRepeatCharacter_proven }
]

/-! Nothing to promise:
- `pointer(::String)`@206 forwards to the external pointer conversion without changing it.
- `codeunit(::String,::Integer)`@212 converts to `Int` and forwards to indexed codeunit.
- `getindex(::Union{String,StringView},::AbstractUnitRange)`@575 converts endpoints and dispatches to range indexing.
- `repeat(::Char,::BitInteger)`@668 forwards to generic character repetition.
-/

/-- Every Julia method maps to a property or the explicit no-promise entry. -/
def methodProperties : List (String × String) := [
  ("StringView{T}@35", "StringViewConstruction"),
  ("string_index_err@60", "IndexErrorAtRequestedIndex"),
  ("showerror@62", "StringIndexErrorDisplay"),
  ("between@78", "BetweenInclusive"),
  ("unsafe_takestring@136", "UnsafeTakeStringBytes"),
  ("String(::AbstractVector{UInt8})@112", "AbstractVectorStringBytes"),
  ("String(::Vector{UInt8})@114", "StringVectorTransfer"),
  ("takestring!@159", "StringVectorTransfer"),
  ("unsafe_string(::Union{Ptr{UInt8},Ptr{Int8}},::Integer)@172", "UnsafeStringRejectsNull + UnsafeStringLengthCopiesBytes"),
  ("unsafe_string(::Union{Ptr{UInt8},Ptr{Int8}})@176", "UnsafeStringRejectsNull + UnsafeStringNulCopiesPrefix"),
  ("_string_n(::Integer)@184", "StringAllocationSize"),
  ("String(::AbstractString)@192", "StringFromAbstractStringBytes"),
  ("String(::Symbol)@193", "StringSymbolConversion"),
  ("unsafe_wrap(::Type{Memory{UInt8}},::String)@195", "StringStorageConversions"),
  ("unsafe_wrap(::Type{Vector{UInt8}},::String)@196", "StringStorageConversions"),
  ("Vector{UInt8}(::CodeUnits{UInt8,String})@198", "StringStorageConversions"),
  ("Vector{UInt8}(::String)@199", "StringStorageConversions"),
  ("Array{UInt8}(::String)@200", "StringStorageConversions"),
  ("String(::CodeUnits{UInt8,String})@202", "StringStorageConversions"),
  ("pointer(::String)@206", "NothingToPromise"),
  ("pointer(::String,::Integer)@207", "StringPointerOffsets"),
  ("ncodeunits(::String)@209", "ByteLengthMatchesStorage"),
  ("codeunit(::String)@210", "CodeunitTypeUInt8"),
  ("codeunit(::String,::Int)@213", "StringCodeunitBytes + StringCodeunitBounds + Round3.CodeunitHasExactlyStorageDomain"),
  ("codeunit(::String,::Integer)@212", "NothingToPromise"),
  ("_memcmp(::Union{Ptr{UInt8},AbstractString},::Union{Ptr{UInt8},AbstractString},::Int)@224",
    "Round1.CmpAgreesOnAllStrings + Round1.CmpAgreesOnValidUtf8"),
  ("_memcmp(::Union{Ptr{UInt8},AbstractString},::Union{Ptr{UInt8},AbstractString})@223",
    "Round1.CmpAgreesOnAllStrings + Round1.CmpAgreesOnValidUtf8"),
  ("_memcmp(::String,::String)@221", "Round1.CmpAgreesOnAllStrings + Round1.CmpAgreesOnValidUtf8"),
  ("cmp(::String,::String)@232", "Round1.CmpAgreesOnAllStrings + Round1.CmpAgreesOnValidUtf8"),
  ("==(::String,::String)@238", "StringEqualityByContents"),
  ("typemin(::Type{String})@240", "StringTypeminEmpty"),
  ("typemin(::String)@241", "StringTypeminEmpty"),
  ("_thisind_str@252", "ThisindWithinThree"),
  ("thisind(::String,::Int)@245", "ThisindIdempotent + Round3.ThisindLocatesCharacter"),
  ("lastindex(::String)@249", "Round3.LastindexIsFinalCharacterStart"),
  ("_nextind_str@276", "NextindAdvance"),
  ("nextind(::String,::Int)@273", "NextindAdvance + Round1.PrevindAfterNextind + Round1.NextindAfterPrevind + Round3.NextindLocatesFollowingCharacter"),
  ("_utf_dfa_step@433", "Utf8Validity"),
  ("_isvalid_utf8_dfa@435", "Utf8Validity"),
  ("_find_nonascii_chunk@442", "FindNonasciiChunkFirst"),
  ("_byte_string_classify_nonascii@476", "Utf8Validity"),
  ("byte_string_classify(::AbstractVector{UInt8})@462", "Utf8Validity"),
  ("byte_string_classify(::AbstractString)@459", "Utf8Validity"),
  ("isvalid(::Type{String},::AbstractVector{UInt8})@499", "Utf8Validity"),
  ("isvalid(::Type{String},::AbstractString)@500", "Utf8Validity"),
  ("isvalid(::AbstractString)@502", "Utf8Validity"),
  ("is_valid_continuation@504", "ContinuationByte"),
  ("iterate_continued@517", "GetindexContinuedMatchesIteration"),
  ("iterate(::Union{String,StringView},::Int)@508",
    "IterateVisitsValid + StringViewAccessesInBounds + Round1.StringIndexValidityMatchesIteration"),
  ("getindex_continued@548", "GetindexContinuedMatchesIteration"),
  ("getindex(::Union{String,StringView},::Int)@540", "Round1.ScalarGetindexMatchesIteration + StringViewAccessesInBounds"),
  ("getindex(::Union{String,StringView},::AbstractUnitRange)@575", "NothingToPromise"),
  ("getindex(::String,::UnitRange{Int})@580", "StringRangeAccessesInBounds"),
  ("_length_continued@635", "CharacterLengthRange"),
  ("length_continued(::String,::Int,::Int,::Int)@626", "CharacterLengthRange"),
  ("length_continued(::StringView,::Int,::Int,::Int)@630", "CharacterLengthRange"),
  ("_length(::Union{String,StringView},::Int,::Int)@615", "CharacterLengthRange"),
  ("length(::String,::Int,::Int)@607",
    "CharacterLengthRange + Round1.StringCharacterLengthRangeCountsValidIndices + Round3.RangeLengthHasExactlyCharacterDomain"),
  ("length(::StringView,::Int,::Int)@611", "CharacterLengthRange"),
  ("length(::String)@598", "Round1.StringLengthIterationCount"),
  ("length(::StringView)@602", "LengthViewAgreement"),
  ("isvalid(::String,::Int)@662", "StringIndexValidity + Round1.StringIndexValidityMatchesIteration"),
  ("isascii(::String)@665", "Round2.AsciiMatchesIteratedCharacters"),
  ("repeat(::AbstractChar,::Integer)@682", "RepeatCharRejectsNegative"),
  ("repeat(::Char,::BitInteger)@668", "NothingToPromise")
]

end JuliaLean.Proofs.base.strings.string

namespace JuliaLean.ChatGPT.Batch8.Group1

open _root_.JuliaLean
open _root_.JuliaLean.base.strings.string
open _root_.JuliaLean.Proofs.base.strings.string

/-- The source's unsigned one-based check detects positive indices below any
nonnegative representable signed length. -/
theorem stringViewUnsignedGuard (i : Index) (n : Int)
    (hn0 : 0 ≤ n) (hnmax : n < 2 ^ 63) :
    (JInt.rem .u64 i - JInt.lit .u64 1).val < n ↔
      1 ≤ i.val ∧ i.val ≤ n := by
  have hi := i.property
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hi
  change ((i.val % (2 ^ 64) - 1) % (2 ^ 64) < n) ↔ _
  omega

/-- Signed wrapping of a natural value cannot increase it. The range proof
keeps the storage observation abstract. -/
theorem stringSignedLengthWrapLe (length : Nat) :
    wrapInt .i64 (Int.ofNat length) ≤ Int.ofNat length := by
  by_cases hsmall : length < 9223372036854775808
  · have hrange : IntTy.i64.min ≤ Int.ofNat length ∧
        Int.ofNat length ≤ IntTy.i64.max := by
      change -9223372036854775808 ≤ Int.ofNat length ∧
        Int.ofNat length ≤ 9223372036854775807
      simp only [Int.ofNat_eq_natCast] at *
      omega
    exact Int.le_of_eq (wrapInt_of_inRange .i64 (Int.ofNat length) hrange)
  · have hupper := (wrapInt_bounds .i64 (Int.ofNat length)).2
    change wrapInt .i64 (Int.ofNat length) ≤ 9223372036854775807 at hupper
    simp only [Int.ofNat_eq_natCast] at *
    omega

/-- Wrapping a nonnegative storage length into a signed word cannot increase it. -/
theorem stringViewWrappedLengthLe (view : StringView (List UInt8)) :
    (stringViewNcodeunits view).val ≤ (view.data.length : Int) := by
  exact stringSignedLengthWrapLe view.data.length

/-- A guarded choice between present values is present precisely when the
outer Boolean guard is true. -/
theorem stringOptionSomeGuard {A : Type} (guard branch : Bool) (left right : A) :
    (if !guard then none else if !branch then some left else some right) ≠ none ↔
      guard = true := by
  cases guard with
  | false =>
    constructor
    · intro h
      exact False.elim (h rfl)
    · intro h
      cases h
  | true =>
    constructor
    · intro _
      rfl
    · intro _
      cases branch <;> (intro h; cases h)

/-- The source entry condition with every storage operation kept abstract. -/
theorem stringIterateGuardGeneric {S : Type}
    (firstindex ncodeunits : S → Index) (codeunit : S → Index → UInt8)
    (betweenByte : UInt8 → UInt8 → UInt8 → Bool) (value : S) (i : Index) :
    iterateString firstindex ncodeunits codeunit betweenByte value i ≠ none ↔
      (JInt.rem .u64 i - JInt.lit .u64 1).val < (ncodeunits value).val := by
  unfold iterateString
  simpa only [decide_eq_true_eq] using
    stringOptionSomeGuard
      (decide ((JInt.rem .u64 i - JInt.lit .u64 1).val < (ncodeunits value).val))
      (betweenByte (codeunit value i) 0x80 0xf7)
      ((codeunit value i).toUInt32 <<< 24, i + JuliaLean.Strings.ix 1)
      (iterateContinued ncodeunits codeunit value i ((codeunit value i).toUInt32 <<< 24))

/-- The exact view iteration entry condition, without a storage-size assumption. -/
theorem stringViewIterationGuard (view : StringView (List UInt8)) (i : Index) :
    stringViewIterate view i ≠ none ↔
      (JInt.rem .u64 i - JInt.lit .u64 1).val < (stringViewNcodeunits view).val := by
  exact stringIterateGuardGeneric stringViewFirstindex stringViewNcodeunits
    stringViewByteAt stringBetweenByte view i

/-- The safety direction of the frozen view target holds for every modeled view.
The missing size restriction affects only its converse. -/
theorem stringViewSuccessfulIterationBounds (view : StringView (List UInt8))
    (i : Index) (h : stringViewIterate view i ≠ none) :
    1 ≤ i.val ∧ i.val ≤ Int.ofNat view.data.length := by
  have hg := (stringViewIterationGuard view i).mp h
  have hu : 0 ≤ (JInt.rem .u64 i - JInt.lit .u64 1).val :=
    (JInt.rem .u64 i - JInt.lit .u64 1 : JInt .u64).property.1
  have hn : (stringViewNcodeunits view).val ≤ 9223372036854775807 :=
    (stringViewNcodeunits view).property.2
  have bounds := (stringViewUnsignedGuard i (stringViewNcodeunits view).val
    (by omega) (by omega)).mp hg
  exact ⟨bounds.1, Int.le_trans bounds.2 (stringViewWrappedLengthLe view)⟩

/-- Every representable backing length satisfies the entire iteration iff.
This strengthens the earlier bound of fewer than 2^62 bytes. -/
theorem stringViewIterationBoundsRepresentable (view : StringView (List UInt8))
    (hsize : view.data.length < 2 ^ 63) (i : Index) :
    stringViewIterate view i ≠ none ↔
      1 ≤ i.val ∧ i.val ≤ Int.ofNat view.data.length := by
  have hlength : (stringViewNcodeunits view).val = (view.data.length : Int) := by
    change wrapInt .i64 (view.data.length : Int) = _
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  rw [stringViewIterationGuard, hlength]
  exact stringViewUnsignedGuard i (view.data.length : Int) (by omega) (by omega)


open _root_.JuliaLean.Proofs.base.strings.util.Round6

/-- The view's checked byte reader agrees with the same bytes represented as a
String whenever the read is in the source's byte domain. -/
theorem stringViewCheckedByteAsString (s : JString) (i : Index)
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ (s.bytes.length : Int)) :
    stringViewCodeunitAt false ⟨s.bytes⟩ i = .ok (parentByte s i.val) := by
  have hhi' : i.val ≤ Int.ofNat s.bytes.length := hhi
  simp only [stringViewCodeunitAt, hlo, hhi', decide_true, Bool.true_and, ite_true]
  change (.ok (s.bytes.getD (i.val.toNat - 1) 0) : StringResult UInt8) =
    .ok (s.bytes.getD (i.val - 1).toNat 0)
  rw [show i.val.toNat - 1 = (i.val - 1).toNat by omega]

/-- Character normalization agrees for a bounded StringView and its byte-identical
String at every in-bounds byte, including malformed encodings. -/
theorem stringViewThisindAsStringInBounds (s : JString) (i : Index)
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ (s.bytes.length : Int)) :
    stringViewThisind ⟨s.bytes⟩ i = stringThisind s i := by
  have hlen : (stringViewNcodeunits ⟨s.bytes⟩).val = (s.bytes.length : Int) :=
    stringNcodeunits_val s
  obtain ⟨r, hr, hrv⟩ := thisindStr_pure stringViewNcodeunits stringViewCodeunitAt
    (⟨s.bytes⟩ : StringView (List UInt8)) (parentByte s) i
    (fun k hk1 hkn => stringViewCheckedByteAsString s k hk1 (by rwa [hlen] at hkn))
    hlo (by rwa [hlen]) (by rw [hlen]; have := s.small; omega)
  obtain ⟨q, hq, hqv⟩ :=
    _root_.JuliaLean.ChatGPT.Batch4.Group11.iterThisindPure s i hlo hhi
  have heq : r = q := Subtype.ext (hrv.trans hqv.symm)
  change stringViewThisind ⟨s.bytes⟩ i = .ok r at hr
  rw [hr, hq, heq]

/-- Character normalization agrees also at sentinels and out-of-bounds indices. -/
theorem stringViewThisindAsString (s : JString) (i : Index) :
    stringViewThisind ⟨s.bytes⟩ i = stringThisind s i := by
  by_cases hin : 1 ≤ i.val ∧ i.val ≤ (s.bytes.length : Int)
  · exact stringViewThisindAsStringInBounds s i hin.1 hin.2
  · have hbetween : stringBetweenIndex i (JuliaLean.Strings.ix 1) (stringNcodeunits s) = false := by
      simp only [stringBetweenIndex, between, stringNcodeunits_val,
        show (JuliaLean.Strings.ix 1).val = 1 by rfl, Bool.and_eq_false_iff,
        decide_eq_false_iff_not]
      omega
    have hlen : stringViewNcodeunits ⟨s.bytes⟩ = stringNcodeunits s := rfl
    simp only [stringViewThisind, stringThisind, thisindString, thisindStr,
      hlen, hbetween, Bool.not_false, ite_true, throw_bind']

/-- Observational adapter for the source's StringView isvalid operation. -/
def stringViewIsvalidResult (view : StringView (List UInt8)) (i : Index) : StringResult Bool :=
  _root_.JuliaLean.base.strings.stringview.isvalidStringViewAt
    (fun value byte => .ok (1 ≤ byte.val && byte.val ≤ Int.ofNat value.data.length))
    stringViewThisind view i

/-- Character-start predicate extracted from the actual view isvalid model. -/
def stringViewActualBoundary (view : StringView (List UInt8)) (i : Index) : Bool :=
  match stringViewIsvalidResult view i with
  | .ok valid => valid
  | .error _ => false

/-- The actual view validity operation is total and agrees with the String
operation on the same bounded byte storage. -/
theorem stringViewIsvalidAsString (s : JString) (i : Index) :
    stringViewIsvalidResult ⟨s.bytes⟩ i = .ok (stringIsvalidIndex s i) := by
  unfold stringViewIsvalidResult _root_.JuliaLean.base.strings.stringview.isvalidStringViewAt
  simp only [bind, Except.bind, Int.ofNat_eq_natCast]
  by_cases hin : 1 ≤ i.val ∧ i.val ≤ (s.bytes.length : Int)
  · have hcheck : (1 ≤ i.val && i.val ≤ (s.bytes.length : Int)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact hin
    obtain ⟨q, hq, _⟩ := _root_.JuliaLean.ChatGPT.Batch4.Group11.iterThisindPure s i hin.1 hin.2
    simp only [hcheck, stringViewThisindAsString, hq]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, bind, Except.bind,
      pure, Except.pure, stringIsvalidIndex, isvalidStringIndex,
      stringCheckboundsBool, hcheck, Bool.true_and]
    change (.ok (q.val == i.val) : StringResult Bool) = .ok (match stringThisind s i with
      | .ok index => index.val == i.val | .error _ => false)
    rw [hq]
  · have hcheck : (1 ≤ i.val && i.val ≤ (s.bytes.length : Int)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    simp only [hcheck, Bool.not_false, ite_true, pure, Except.pure,
      stringIsvalidIndex, isvalidStringIndex, stringCheckboundsBool,
      Bool.false_and]

/-- The Boolean observation of actual StringView boundaries agrees exactly. -/
theorem stringViewActualBoundaryAsString (s : JString) (i : Index) :
    stringViewActualBoundary ⟨s.bytes⟩ i = stringIsvalidIndex s i := by
  unfold stringViewActualBoundary
  rw [stringViewIsvalidAsString]


/-- Correct enumeration for every small view, using the source's actual validity
operation and retaining malformed characters as legitimate starts. -/
theorem stringViewVisitsActualIndices (view : StringView (List UInt8))
    (hsize : view.data.length < 2 ^ 62) (rows : List (Index × UInt32 × Index))
    (trace : IterTrace stringViewIterate view (JuliaLean.Strings.ix 1) rows) :
    rows.map (fun row => row.1) =
      validByteIndices stringViewNcodeunits stringViewActualBoundary view := by
  let s : JString := ⟨view.data, hsize⟩
  change IterTrace stringViewIterate ⟨s.bytes⟩ (JuliaLean.Strings.ix 1) rows at trace
  change rows.map (fun row => row.1) =
    validByteIndices stringViewNcodeunits stringViewActualBoundary ⟨s.bytes⟩
  have h := _root_.JuliaLean.ChatGPT.Batch4.Group11.iterViewVisitsActualValid s rows trace
  have hboundary : stringViewActualBoundary ⟨s.bytes⟩ = stringIsvalidIndex s :=
    funext (stringViewActualBoundaryAsString s)
  unfold validByteIndices at h ⊢
  rw [hboundary]
  exact h

/-- Existence, uniqueness, exact enumeration, and ordered view starts all follow
from the same-byte String trace, with the storage premise exposed. -/
theorem stringViewActualTraceComplete (view : StringView (List UInt8))
    (hsize : view.data.length < 2 ^ 62) :
    ∃ rows, IterTrace stringViewIterate view (JuliaLean.Strings.ix 1) rows ∧
      rows.map (fun row => row.1) =
        validByteIndices stringViewNcodeunits stringViewActualBoundary view ∧
      (rows.map (fun row => row.1)).Pairwise (fun a b => a.val < b.val) ∧
      ∀ other, IterTrace stringViewIterate view (JuliaLean.Strings.ix 1) other → other = rows := by
  let s : JString := ⟨view.data, hsize⟩
  obtain ⟨rows, hrows, _⟩ :=
    _root_.JuliaLean.Proofs.base.strings.string.JuliaLean.ChatGPT.Batch2.Group5.iterationComplete s
  have hv : IterTrace stringViewIterate view (JuliaLean.Strings.ix 1) rows :=
    (_root_.JuliaLean.ChatGPT.Batch4.Group11.iterViewTraceAsString s
      (JuliaLean.Strings.ix 1) rows).mpr hrows
  refine ⟨rows, hv, stringViewVisitsActualIndices view hsize rows hv, ?_, ?_⟩
  · rw [_root_.JuliaLean.ChatGPT.Batch4.Group11.iterStringVisitsAllValid s rows hrows]
    exact _root_.JuliaLean.ChatGPT.Batch4.Group11.iterValidIndicesOrdered s
  · intro other hother
    exact _root_.JuliaLean.Proofs.base.strings.string.JuliaLean.ChatGPT.Batch2.Group5.iterationTraceUnique
      stringViewIterate view hother hv


/-- Continued byte counting agrees on identical storage for arbitrary counters. -/
theorem stringViewLengthContinuedAsString (s : JString) (i n c : Index) :
    stringViewLengthContinued ⟨s.bytes⟩ i n c = stringLengthContinued s i n c := by
  exact _root_.JuliaLean.ChatGPT.Batch4.Group11.lengthContinuedInternal_congr
    stringViewByteAt stringByteAt ⟨s.bytes⟩ s (fun _ => rfl) i n c

/-- The complete range operation agrees, including error and empty-interval
branches, for a bounded view and its byte-identical String. -/
theorem stringViewLengthRangeAsString (s : JString) (i j : Index) :
    stringViewLengthRange ⟨s.bytes⟩ i j = stringLengthRange s i j := by
  simp only [stringViewLengthRange, stringLengthRange, lengthViewRange,
    lengthStringRange, lengthRange, stringViewThisindAsString,
    stringViewLengthContinuedAsString]
  rfl

/-- An arbitrary complete view trace gives the exact range result on every pair
of indices. Character starts are filtered in the original requested interval. -/
theorem stringViewRangeCountsTrace (view : StringView (List UInt8))
    (hsize : view.data.length < 2 ^ 62) (rows : List (Index × UInt32 × Index))
    (trace : IterTrace stringViewIterate view (JuliaLean.Strings.ix 1) rows)
    (i j : Index) :
    stringViewLengthRange view i j =
      if 0 < i.val ∧ i.val ≤ (stringViewNcodeunits view).val + 1 ∧
          0 ≤ j.val ∧ j.val ≤ (stringViewNcodeunits view).val then
        .ok (JuliaLean.Strings.ix (Int.ofNat
          ((rows.map (fun row => row.1)).filter
            (fun start => decide (i.val ≤ start.val ∧ start.val ≤ j.val))).length))
      else .error (.jl .boundsError) := by
  let s : JString := ⟨view.data, hsize⟩
  have hs : (⟨s.bytes⟩ : StringView (List UInt8)) = view := rfl
  obtain ⟨reference, href, hcount⟩ :=
    _root_.JuliaLean.ChatGPT.Batch4.Group11.StringsRangeLengthNativeDomain_proven s
  have htrace : IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows :=
    (_root_.JuliaLean.ChatGPT.Batch4.Group11.iterViewTraceAsString s
      (JuliaLean.Strings.ix 1) rows).mp trace
  have heq := _root_.JuliaLean.Proofs.base.strings.string.JuliaLean.ChatGPT.Batch2.Group5.iterationTraceUnique
    stringIterate s htrace href
  rw [← hs, stringViewLengthRangeAsString, heq]
  exact hcount i j

/-- The range-length correction in predicate form, using source isvalid and
retaining the original left endpoint instead of moving it to thisind. -/
theorem stringViewRangeCountsActualIndices (view : StringView (List UInt8))
    (hsize : view.data.length < 2 ^ 62) (i j : Index)
    (hi : 0 < i.val) (hiMax : i.val ≤ (stringViewNcodeunits view).val + 1)
    (hj : 0 ≤ j.val) (hjMax : j.val < (stringViewNcodeunits view).val + 1) :
    stringViewLengthRange view i j = .ok (JuliaLean.Strings.ix (Int.ofNat
      (Round1.validIndexCount stringViewActualBoundary view i j))) := by
  let s : JString := ⟨view.data, hsize⟩
  have hs : (⟨s.bytes⟩ : StringView (List UInt8)) = view := rfl
  have hnv : (stringViewNcodeunits view).val = (s.bytes.length : Int) :=
    stringNcodeunits_val s
  have hcount := _root_.JuliaLean.ChatGPT.Batch4.Group11.StringCharacterLengthRangeStringOnly_proven
    s i j hi
    (by rw [_root_.JuliaLean.ChatGPT.Batch4.Group11.iterNcodeunitsSuccVal]
        simpa only [hnv] using hiMax)
    hj
    (by rw [_root_.JuliaLean.ChatGPT.Batch4.Group11.iterNcodeunitsSuccVal]
        simpa only [hnv] using hjMax)
  rw [← hs, stringViewLengthRangeAsString]
  simpa only [Round1.validIndexCount, stringViewActualBoundaryAsString] using hcount


/-- The sound direction of the frozen byte-mask criterion holds on arbitrary
String encodings: a byte without continuation bits is a character start. -/
theorem stringIndexValidOfNonContinuation (s : JString) (i : Index)
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ (stringNcodeunits s).val)
    (hmask : ((stringByteAt s i &&& 0xc0) != 0x80) = true) :
    stringIsvalidIndex s i = true := by
  have hhiBytes : i.val ≤ (s.bytes.length : Int) := by
    rwa [stringNcodeunits_val] at hhi
  have hbyte : parentByte s i.val = stringByteAt s i := by
    unfold parentByte stringByteAt
    congr 2
    omega
  have hcont : contB (parentByte s i.val) = false := by
    rw [hbyte]
    change (!contB (stringByteAt s i)) = true at hmask
    cases hb : contB (stringByteAt s i) with
    | false => rfl
    | true => rw [hb] at hmask; cases hmask
  apply (stringIsvalid_iff_pure s i hlo hhiBytes).mpr
  rcases thisindPure_cases (parentByte s) i.val with h | h | h | h
  · exact h
  all_goals
    have hc := h.2.2.1
    rw [hcont] at hc
    cases hc


/-- Bytes outside the continuation interval satisfy the mask criterion. -/
theorem stringByteNonContinuationOutsideRange (byte : UInt8)
    (hout : byte.toNat < 128 ∨ 192 ≤ byte.toNat) :
    ((byte &&& 0xc0) != 0x80) = true := by
  change (!contB byte) = true
  cases hc : contB byte with
  | false => rfl
  | true =>
    have hrange := (contB_iff byte).mp hc
    omega

open _root_.JuliaLean.Proofs.base.strings.string.JuliaLean.ChatGPT.Batch2.Group5

/-- A well-shaped glyph begins with a byte outside the continuation interval. -/
theorem stringGlyphHeadNonContinuation (s : JString) (pre rest : List UInt8)
    (glyph : CmpGlyph) (hbytes : s.bytes = pre ++ glyph.bytes ++ rest) :
    ((stringByteAt s (cmpIndex pre.length) &&& 0xc0) != 0x80) = true := by
  have hlength := congrArg List.length hbytes
  simp only [List.length_append] at hlength
  have hsmall := s.small
  have hread := cmpReadPrefix s pre (glyph.bytes ++ rest)
    (by simpa only [List.append_assoc] using hbytes) 0 (by omega)
  simp only [Nat.add_zero] at hread
  rw [hread]
  cases glyph with
  | ascii byte hbyte =>
    change ((byte &&& 0xc0) != 0x80) = true
    exact stringByteNonContinuationOutsideRange byte (Or.inl hbyte)
  | two byte following hbyte _ =>
    change ((byte &&& 0xc0) != 0x80) = true
    exact stringByteNonContinuationOutsideRange byte (Or.inr hbyte.1)
  | three byte second third hbyte _ _ =>
    change ((byte &&& 0xc0) != 0x80) = true
    exact stringByteNonContinuationOutsideRange byte (Or.inr (by omega))
  | four byte second third fourth hbyte _ _ _ =>
    change ((byte &&& 0xc0) != 0x80) = true
    exact stringByteNonContinuationOutsideRange byte (Or.inr (by omega))

/-- The actual iterator over a sequence of well-shaped glyphs visits only their
non-continuation leading bytes. -/
theorem stringGlyphTraceNonContinuation (s : JString) (glyphs : List CmpGlyph)
    (pre : List UInt8) (hbytes : s.bytes = pre ++ cmpGlyphBytes glyphs) :
    ∃ rows, IterTrace stringIterate s (cmpIndex pre.length) rows ∧
      ∀ row ∈ rows, ((stringByteAt s row.1 &&& 0xc0) != 0x80) = true := by
  induction glyphs generalizing pre with
  | nil =>
    have hempty : s.bytes = pre := by
      simpa only [cmpGlyphBytes, List.flatMap_nil, List.append_nil] using hbytes
    refine ⟨[], .stop ?_, ?_⟩
    · rw [← congrArg List.length hempty]
      exact cmpIterEnd s
    · intro row hrow
      cases hrow
  | cons glyph glyphs ih =>
    have hsplit : s.bytes = pre ++ glyph.bytes ++ cmpGlyphBytes glyphs := by
      simpa only [cmpGlyphBytes, List.flatMap_cons, List.append_assoc] using hbytes
    obtain ⟨rows, htrace, hmask⟩ := ih (pre ++ glyph.bytes) hsplit
    have htail : IterTrace stringIterate s
        (cmpIndex (pre.length + glyph.bytes.length)) rows := by
      simpa only [List.length_append] using htrace
    refine ⟨(cmpIndex pre.length, glyph.bits,
      cmpIndex (pre.length + glyph.bytes.length)) :: rows,
      .step (cmpIterGlyph s pre (cmpGlyphBytes glyphs) glyph hsplit) htail, ?_⟩
    intro row hrow
    rcases List.mem_cons.mp hrow with heq | hrow
    · subst row
      exact stringGlyphHeadNonContinuation s pre (cmpGlyphBytes glyphs) glyph hsplit
    · exact hmask row hrow

/-- A separately qualified correction of index validity for a String accepted
by the installed UTF-8 classifier. The unqualified frozen target is unchanged. -/
theorem stringIndexValidityOnValidatedUtf8 (s : JString)
    (hutf8 : stringBytesAreValidUtf8 s.bytes = true) (i : Index)
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ (stringNcodeunits s).val) :
    stringIsvalidIndex s i = true ↔
      ((stringByteAt s i &&& 0xc0) != 0x80) = true := by
  constructor
  · intro hvalid
    have hshape := cmpUtf8Shape_of_valid s.bytes hutf8
    obtain ⟨glyphs, hbytes⟩ := cmpShapeGlyphs hshape
    obtain ⟨rows, htrace, hmask⟩ := stringGlyphTraceNonContinuation s glyphs []
      (by simpa only [List.nil_append] using hbytes.symm)
    have hfirst : IterTrace stringIterate s (JuliaLean.Strings.ix 1) rows := htrace
    have hmem : i ∈ rows.map (fun row => row.1) := by
      rw [_root_.JuliaLean.ChatGPT.Batch4.Group11.iterStringVisitsAllValid s rows hfirst]
      exact (_root_.JuliaLean.ChatGPT.Batch4.Group11.iterValidIndicesMem s i).mpr hvalid
    obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hmem
    rw [← heq]
    exact hmask row hrow
  · exact stringIndexValidOfNonContinuation s i hlo hhi

/-- The same corrected mask equivalence with the frozen inductive UTF-8
well-formedness predicate as its explicit premise. -/
theorem stringIndexValidityOnWellFormedUtf8 (s : JString)
    (hutf8 : Utf8WellFormed s.bytes) (i : Index)
    (hlo : 1 ≤ i.val) (hhi : i.val ≤ (stringNcodeunits s).val) :
    stringIsvalidIndex s i = true ↔
      ((stringByteAt s i &&& 0xc0) != 0x80) = true := by
  apply stringIndexValidityOnValidatedUtf8 s ?_ i hlo hhi
  exact (_root_.JuliaLean.ChatGPT.Batch4.Group11.u8mByteValidity_iff s.bytes).mpr
    (_root_.JuliaLean.ChatGPT.Batch4.Group11.utf8Language_from_frozen hutf8)

end JuliaLean.ChatGPT.Batch8.Group1

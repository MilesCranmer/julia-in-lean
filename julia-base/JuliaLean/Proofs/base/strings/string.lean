import JuliaLean.base.strings.string
import JuliaLean.base.strings.basic
import JuliaLean.base.char
import JuliaLean.Registry.Types

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


def entries : List JuliaLean.Registry.Entry := [
  { id := "strings-iterate-valid-indices", juliaFile := "base/strings/string.jl",
    juliaFns := ["iterate(::String,::Int)", "iterate(::StringView,::Int)"],
    statement := "Iteration visits every valid character-start byte index once, in order, for Strings and StringViews.",
    source := "base/strings/string.jl:508-514", status := .todo, prop := ``IterateVisitsValid },
  { id := "strings-length-iterate-steps", juliaFile := "base/strings/string.jl",
    juliaFns := ["length(::String)", "iterate(::String,::Int)"],
    statement := "String length equals the number of characters produced by iteration.",
    source := "base/strings/string.jl:508-514,598-600", status := .todo, prop := ``LengthIterateSteps },
  { id := "strings-thisind-idempotent", juliaFile := "base/strings/string.jl",
    juliaFns := ["thisind(::String,::Int)"],
    statement := "Applying thisind to a valid character index returns that index.",
    source := "base/strings/string.jl:252-271", status := .todo, prop := ``ThisindIdempotent },
  { id := "strings-prevind-after-nextind", juliaFile := "base/strings/string.jl",
    juliaFns := ["nextind(::String,::Int)", "prevind(::AbstractString,::Int,::Int)"],
    statement := "For every valid String index i, prevind(s,nextind(s,i)) returns i.",
    source := "base/strings/basic.jl:477-500, base/strings/string.jl:273-306",
    status := .todo, prop := ``PrevindAfterNextind },
  { id := "strings-nextind-after-prevind", juliaFile := "base/strings/string.jl",
    juliaFns := ["nextind(::String,::Int)", "prevind(::AbstractString,::Int,::Int)"],
    statement := "For valid String indices at or after the second character, nextind(s,prevind(s,i)) returns i.",
    source := "base/strings/basic.jl:477-500, base/strings/string.jl:273-306",
    status := .todo, prop := ``NextindAfterPrevind },
  { id := "strings-cmp-malformed", juliaFile := "base/strings/string.jl",
    juliaFns := ["cmp(::String,::String)", "cmp(::AbstractString,::AbstractString)"],
    statement := "String byte comparison agrees with generic AbstractString character comparison, including malformed byte sequences.",
    source := "base/strings/string.jl:221-236, base/strings/basic.jl:308-317",
    status := .todo, prop := ``CmpAgreesGeneric,
    notes := "Previously refuted; repro/strings-cmp-malformed.jl prints REPRODUCED strings-cmp-malformed." },
  { id := "transcode-string-vector-alias", juliaFile := "base/strings/string.jl",
    juliaFns := ["String(::Vector{UInt8})", "jl_genericmemory_to_string (src/genericmemory.c)"],
    statement := "Once String(v) has returned a String, no later operation on arrays changes its bytes.",
    source := "base/strings/string.jl:85,114-127", status := .todo, prop := ``StringVectorImmutable,
    notes := "Previously refuted; repro/transcode-string-vector-alias.jl prints REPRODUCED transcode-string-vector-alias." },
  { id := "memsafety-string-view-physical-index", juliaFile := "base/strings/string.jl",
    juliaFns := ["iterate(::StringView,::Int)", "getindex(::StringView,::Int)"],
    statement := "A successful StringView iteration index is one-based and lies inside its backing byte data.",
    source := "base/strings/string.jl:508-514,540-545", status := .todo,
    prop := ``StringViewAccessesInBounds },
  { id := "memsafety-string-range-copy", juliaFile := "base/strings/string.jl",
    juliaFns := ["getindex(::String,::UnitRange{Int})"],
    statement := "After range and string-index checks, the copied byte count stays within the source String.",
    source := "base/strings/string.jl:580-595", status := .todo,
    prop := ``StringRangeAccessesInBounds },
  { id := "stringscova-string-thisind-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["_thisind_str(::String,::Int)"],
    statement := "thisind finds a character start no more than three bytes before a valid index.",
    source := "base/strings/string.jl:252-271", status := .todo, prop := ``ThisindWithinThree },
  { id := "stringscova-string-nextind-dispatch-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["_nextind_str(::String,::Int)"],
    statement := "nextind advances from a valid character start to the next character boundary or end index.",
    source := "base/strings/string.jl:276-306", status := .todo, prop := ``NextindAdvance },
  { id := "stringscova-string-thisind-continued-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["_thisind_continued(::String,::Int)"],
    statement := "thisind checks at most the previous three continuation bytes before returning a character start.",
    source := "base/strings/string.jl:467-485", status := .todo, prop := ``ThisindWithinThree },
  { id := "stringscova-string-find-nonascii-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["_find_nonascii_chunk"],
    statement := "The non-ASCII chunk scan finds the first non-ASCII chunk, or reports none exactly when all bytes are ASCII.",
    source := "base/strings/string.jl:442-451", status := .todo, prop := ``FindNonasciiChunkFirst },
  { id := "stringscova-string-getindex-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["getindex(::String,::Int)"],
    statement := "Indexing a valid character start returns the character yielded by iteration.",
    source := "base/strings/string.jl:508-514,540-545", status := .todo,
    prop := ``ScalarGetindexMatchesIteration },
  { id := "stringscova-string-iterate-continued-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["iterate_continued(::String,::Int,::UInt32)"],
    statement := "Continued iteration and continued indexing decode the same character bits.",
    source := "base/strings/string.jl:517-538,548-573", status := .todo,
    prop := ``GetindexContinuedMatchesIteration },
  { id := "stringscova-string-continuation-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["is_valid_continuation(::UInt8)"],
    statement := "UTF-8 continuation bytes are exactly 0x80 through 0xbf.",
    source := "base/strings/string.jl:504", status := .todo, prop := ``ContinuationByte },
  { id := "stringscova-string-isvalid-bytes-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["isvalid(::Type{String},::AbstractVector{UInt8})"],
    statement := "String byte validity is exactly membership in the UTF-8 encoding language.",
    source := "base/strings/string.jl:433-502", status := .todo, prop := ``Utf8Validity },
  { id := "stringscova-string-length-view-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["length(::StringView)"],
    statement := "StringView length agrees with String character length over the same bytes.",
    source := "base/strings/string.jl:598-604", status := .todo, prop := ``LengthViewAgreement },
  { id := "stringscova-string-getindex-continued-rebuilt", juliaFile := "base/strings/string.jl",
    juliaFns := ["getindex_continued(::String,::Int,::UInt32)"],
    statement := "Continued scalar indexing agrees with continued iteration.",
    source := "base/strings/string.jl:517-538,548-573", status := .todo,
    prop := ``GetindexContinuedMatchesIteration },
  { id := "strings-stringview-construction", juliaFile := "base/strings/string.jl",
    juliaFns := ["StringView{T}(data::T)"],
    statement := "StringView construction preserves one-based checks and rejects abstract element types.",
    source := "base/strings/string.jl:35-47", status := .todo, prop := ``StringViewConstruction },
  { id := "strings-string-index-errors", juliaFile := "base/strings/string.jl",
    juliaFns := ["string_index_err(::AbstractString,::Integer)"],
    statement := "string_index_err throws at the requested integer converted to Int.",
    source := "base/strings/string.jl:60-61", status := .todo,
    prop := ``IndexErrorAtRequestedIndex },
  { id := "strings-index-error-display", juliaFile := "base/strings/string.jl",
    juliaFns := ["showerror(::IO,::StringIndexError)"],
    statement := "The error display reports the requested index and nearby valid character indices.",
    source := "base/strings/string.jl:62-76", status := .todo, prop := ``StringIndexErrorDisplay },
  { id := "strings-between-inclusive", juliaFile := "base/strings/string.jl",
    juliaFns := ["between(::Integer,::Integer,::Integer)"],
    statement := "between is true exactly when the value lies between the inclusive endpoints.",
    source := "base/strings/string.jl:78", status := .todo, prop := ``BetweenInclusive },
  { id := "strings-abstractvector-construction", juliaFile := "base/strings/string.jl",
    juliaFns := ["String(::AbstractVector{UInt8})"],
    statement := "String construction from a byte vector preserves its bytes while transferring temporary memory.",
    source := "base/strings/string.jl:112", status := .todo, prop := ``AbstractVectorStringBytes },
  { id := "strings-takestring-bytes", juliaFile := "base/strings/string.jl",
    juliaFns := ["unsafe_takestring(::Memory{UInt8})"],
    statement := "Taking a string from memory preserves its byte sequence.",
    source := "base/strings/string.jl:136-138", status := .todo, prop := ``UnsafeTakeStringBytes },
  { id := "strings-vector-transfer", juliaFile := "base/strings/string.jl",
    juliaFns := ["String(::Vector{UInt8})", "takestring!(::Vector{UInt8})"],
    statement := "String construction empties the vector and records shared memory only on the generic-memory path.",
    source := "base/strings/string.jl:114-127,159", status := .todo, prop := ``StringVectorTransfer },
  { id := "strings-unsafe-string-null", juliaFile := "base/strings/string.jl",
    juliaFns := ["unsafe_string(::Union{Ptr{UInt8},Ptr{Int8}},::Integer)", "unsafe_string(::Union{Ptr{UInt8},Ptr{Int8}})"],
    statement := "Both unsafe_string overloads reject a null pointer with ArgumentError.",
    source := "base/strings/string.jl:172-179", status := .todo, prop := ``UnsafeStringRejectsNull },
  { id := "strings-unsafe-string-length-copies-bytes", juliaFile := "base/strings/string.jl",
    juliaFns := ["unsafe_string(::Ptr{UInt8},::Integer)"],
    statement := "The length-taking unsafe_string copies exactly the requested byte count.",
    source := "base/strings/string.jl:172-175", status := .todo, prop := ``UnsafeStringLengthCopiesBytes },
  { id := "strings-unsafe-string-nul-prefix", juliaFile := "base/strings/string.jl",
    juliaFns := ["unsafe_string(::Ptr{UInt8})"],
    statement := "The NUL-terminated unsafe_string copies only the byte prefix before the first zero.",
    source := "base/strings/string.jl:176-179", status := .todo, prop := ``UnsafeStringNulCopiesPrefix },
  { id := "strings-allocation-size", juliaFile := "base/strings/string.jl",
    juliaFns := ["_string_n(::Integer)"],
    statement := "Successful Csize_t conversion makes _string_n allocate a String with exactly that many bytes.",
    source := "base/strings/string.jl:184-185", status := .todo, prop := ``StringAllocationSize },
  { id := "strings-string-from-abstract", juliaFile := "base/strings/string.jl",
    juliaFns := ["String(::AbstractString)"],
    statement := "String(::AbstractString) preserves the byte sequence produced by print_to_string.",
    source := "base/strings/string.jl:192", status := .todo, prop := ``StringFromAbstractStringBytes },
  { id := "strings-symbol-string", juliaFile := "base/strings/string.jl",
    juliaFns := ["String(::Symbol)"],
    statement := "Symbol conversion copies the symbol's NUL-terminated byte prefix.",
    source := "base/strings/string.jl:193", status := .todo, prop := ``StringSymbolConversion },
  { id := "strings-storage-conversions", juliaFile := "base/strings/string.jl",
    juliaFns := ["unsafe_wrap(::Type{Memory{UInt8}},::String)", "unsafe_wrap(::Type{Vector{UInt8}},::String)",
      "Vector{UInt8}(::CodeUnits{UInt8,String})", "Vector{UInt8}(::String)", "Array{UInt8}(::String)",
      "String(::CodeUnits{UInt8,String})"],
    statement := "String and byte-storage conversions preserve the represented bytes or storage contents.",
    source := "base/strings/string.jl:195-202", status := .todo, prop := ``StringStorageConversions },
  { id := "strings-pointer-offsets", juliaFile := "base/strings/string.jl",
    juliaFns := ["pointer(::String,::Integer)"],
    statement := "The indexed String pointer is the base pointer plus the one-based byte offset minus one.",
    source := "base/strings/string.jl:207", status := .todo, prop := ``StringPointerOffsets },
  { id := "strings-byte-length", juliaFile := "base/strings/string.jl",
    juliaFns := ["ncodeunits(::String)"],
    statement := "The String codeunit count equals the number of stored bytes.",
    source := "base/strings/string.jl:209", status := .todo, prop := ``ByteLengthMatchesStorage },
  { id := "strings-codeunit-type", juliaFile := "base/strings/string.jl",
    juliaFns := ["codeunit(::String)"],
    statement := "String's code-unit type is UInt8.",
    source := "base/strings/string.jl:210", status := .todo, prop := ``CodeunitTypeUInt8 },
  { id := "strings-codeunit-bytes", juliaFile := "base/strings/string.jl",
    juliaFns := ["codeunit(::String,::Int)"],
    statement := "Each in-bounds String codeunit is the byte stored at that one-based index.",
    source := "base/strings/string.jl:213-217", status := .todo, prop := ``StringCodeunitBytes },
  { id := "strings-codeunit-bounds", juliaFile := "base/strings/string.jl",
    juliaFns := ["codeunit(::String,::Int)"],
    statement := "Bounds-checked codeunit access rejects indices outside the stored bytes.",
    source := "base/strings/string.jl:213-217", status := .todo, prop := ``StringCodeunitBounds },
  { id := "strings-string-index-validity", juliaFile := "base/strings/string.jl",
    juliaFns := ["isvalid(::String,::Int)"],
    statement := "An in-bounds string index is valid exactly when its byte is not a continuation byte.",
    source := "base/strings/string.jl:662", status := .todo, prop := ``StringIndexValidity },
  { id := "strings-character-length-range", juliaFile := "base/strings/string.jl",
    juliaFns := ["_length_continued", "length_continued(::String)", "length_continued(::StringView)",
      "_length(::Union{String,StringView})", "length(::String,::Int,::Int)", "length(::StringView,::Int,::Int)"],
    statement := "Range length counts bytes that are not UTF-8 continuation bytes after aligning the first index to its character start.",
    source := "base/strings/string.jl:615-658", status := .todo, prop := ``CharacterLengthRange },
  { id := "strings-length-view-agreement", juliaFile := "base/strings/string.jl",
    juliaFns := ["length(::StringView)", "length(::String)"],
    statement := "StringView and String have equal character lengths over the same bytes.",
    source := "base/strings/string.jl:598-604", status := .todo, prop := ``LengthViewAgreement },
  { id := "strings-ascii-agreement", juliaFile := "base/strings/string.jl",
    juliaFns := ["isascii(::String)"],
    statement := "A String is ASCII exactly when every stored byte is below 0x80.",
    source := "base/strings/string.jl:665", status := .todo, prop := ``AsciiStringAgreement },
  { id := "strings-string-typemin", juliaFile := "base/strings/string.jl",
    juliaFns := ["typemin(::Type{String})", "typemin(::String)"],
    statement := "The minimum String value is the empty string.",
    source := "base/strings/string.jl:240-241", status := .todo, prop := ``StringTypeminEmpty },
  { id := "strings-string-equality-bytes", juliaFile := "base/strings/string.jl",
    juliaFns := ["==(String,String)"],
    statement := "String equality is byte-sequence equality.",
    source := "base/strings/string.jl:238", status := .todo, prop := ``StringEqualityByContents },
  { id := "strings-repeat-character", juliaFile := "base/strings/string.jl",
    juliaFns := ["repeat(::AbstractChar,::Integer)"],
    statement := "Repeating a character rejects negative counts with ArgumentError.",
    source := "base/strings/string.jl:682-715", status := .todo, prop := ``RepeatCharRejectsNegative }
]

/-! Nothing to promise:
- `pointer(::String)`@206 forwards to the external pointer conversion without changing it.
- `lastindex(::String)`@249 calls `thisind` at `ncodeunits`; its index behavior is covered by `thisind`.
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
  ("codeunit(::String,::Int)@213", "StringCodeunitBytes + StringCodeunitBounds"),
  ("codeunit(::String,::Integer)@212", "NothingToPromise"),
  ("_memcmp(::Union{Ptr{UInt8},AbstractString},::Union{Ptr{UInt8},AbstractString},::Int)@224",
    "CmpAgreesGeneric"),
  ("_memcmp(::Union{Ptr{UInt8},AbstractString},::Union{Ptr{UInt8},AbstractString})@223",
    "CmpAgreesGeneric"),
  ("_memcmp(::String,::String)@221", "CmpAgreesGeneric"),
  ("cmp(::String,::String)@232", "CmpAgreesGeneric"),
  ("==(::String,::String)@238", "StringEqualityByContents"),
  ("typemin(::Type{String})@240", "StringTypeminEmpty"),
  ("typemin(::String)@241", "StringTypeminEmpty"),
  ("_thisind_str@252", "ThisindWithinThree"),
  ("thisind(::String,::Int)@245", "ThisindIdempotent"),
  ("lastindex(::String)@249", "NothingToPromise"),
  ("_nextind_str@276", "NextindAdvance"),
  ("nextind(::String,::Int)@273", "NextindAdvance"),
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
  ("iterate(::Union{String,StringView},::Int)@508", "IterateVisitsValid + StringViewAccessesInBounds"),
  ("getindex_continued@548", "GetindexContinuedMatchesIteration"),
  ("getindex(::Union{String,StringView},::Int)@540", "ScalarGetindexMatchesIteration + StringViewAccessesInBounds"),
  ("getindex(::Union{String,StringView},::AbstractUnitRange)@575", "NothingToPromise"),
  ("getindex(::String,::UnitRange{Int})@580", "StringRangeAccessesInBounds"),
  ("_length_continued@635", "CharacterLengthRange"),
  ("length_continued(::String,::Int,::Int,::Int)@626", "CharacterLengthRange"),
  ("length_continued(::StringView,::Int,::Int,::Int)@630", "CharacterLengthRange"),
  ("_length(::Union{String,StringView},::Int,::Int)@615", "CharacterLengthRange"),
  ("length(::String,::Int,::Int)@607", "CharacterLengthRange"),
  ("length(::StringView,::Int,::Int)@611", "CharacterLengthRange"),
  ("length(::String)@598", "LengthIterateSteps"),
  ("length(::StringView)@602", "LengthViewAgreement"),
  ("isvalid(::String,::Int)@662", "StringIndexValidity"),
  ("isascii(::String)@665", "AsciiStringAgreement"),
  ("repeat(::AbstractChar,::Integer)@682", "RepeatCharRejectsNegative"),
  ("repeat(::Char,::BitInteger)@668", "NothingToPromise")
]

end JuliaLean.Proofs.base.strings.string

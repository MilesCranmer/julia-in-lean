import JuliaLean.StringsCovA.Search

namespace JuliaLean.StringsCovA.SearchRebuilt
open JuliaLean JuliaLean.Strings

/-! Concrete scalar helpers, `base/strings/search.jl:34-42`. -/

def lastUtf8Byte (character : UInt32) : UInt8 :=
  let shift := ((4 - Strings.ncodeunitsChar character) * 8) % 32
  (character >>> shift.toUInt32).toUInt8

def LastUtf8ByteProperty : Prop := ∀ character,
  lastUtf8Byte character =
    let shift := ((4 - Strings.ncodeunitsChar character) * 8) % 32
    (character >>> shift.toUInt32).toUInt8

theorem lastUtf8Byte_proven : LastUtf8ByteProperty := by
  intro character
  rfl

def isStandaloneByte (byte : UInt8) : Bool := byte < 0x80 || byte > 0xf7

def IsStandaloneByteProperty : Prop := ∀ byte,
  isStandaloneByte byte = true ↔ byte < 0x80 ∨ byte > 0xf7

theorem isStandaloneByte_proven : IsStandaloneByteProperty := by
  intro byte
  simp [isStandaloneByte]

structure IntegerInput (I : Type) where
  value : I
  toInt : SJl JInt64

structure FwIter where
  string : JStr
  character : UInt32
  lastByte : UInt8

def fwCtor (string : JStr) (convertChar : SJl UInt32) : SJl FwIter := do
  let character ← convertChar
  return ⟨string, character, Strings.lastUtf8Byte character⟩
def FwCtorProperty : Prop := ∀ string convertChar character,
  convertChar = .ok character → fwCtor string convertChar =
    .ok ⟨string, character, Strings.lastUtf8Byte character⟩
theorem fwCtor_proven : FwCtorProperty := by
  unfold FwCtorProperty
  intros; simp_all [fwCtor, bind, Except.bind, pure, Except.pure]

def fwIterate (iterator : FwIter) (index : JInt64) :=
  Strings.fwIterate iterator.string iterator.character index
def FwIterateProperty : Prop := ∀ iterator index,
  fwIterate iterator index = Strings.fwIterate iterator.string iterator.character index
theorem fwIterate_proven : FwIterateProperty := by unfold FwIterateProperty; intros; rfl

structure RvIter where
  string : JStr
  character : UInt32
  lastByte : UInt8

def rvCtor (string : JStr) (convertChar : SJl UInt32) : SJl RvIter := do
  let character ← convertChar
  return ⟨string, character, Strings.lastUtf8Byte character⟩
def RvCtorProperty : Prop := ∀ string convertChar character,
  convertChar = .ok character → rvCtor string convertChar =
    .ok ⟨string, character, Strings.lastUtf8Byte character⟩
theorem rvCtor_proven : RvCtorProperty := by
  unfold RvCtorProperty
  intros; simp_all [rvCtor, bind, Except.bind, pure, Except.pure]

def rvIterate (iterator : RvIter) (index : JInt64) :=
  Strings.rvIterate iterator.string iterator.character index
def RvIterateProperty : Prop := ∀ iterator index,
  rvIterate iterator index = Strings.rvIterate iterator.string iterator.character index
theorem rvIterate_proven : RvIterateProperty := by unfold RvIterateProperty; intros; rfl

def tryNext (iteration : SJl (Option (A × State))) : SJl (Option A) := do
  let result ← iteration
  return result.map Prod.fst
def TryNextProperty : Prop := ∀ (A State : Type) result,
  tryNext (A := A) (State := State) (.ok result) = .ok (result.map Prod.fst)
theorem tryNext_proven : TryNextProperty := by unfold TryNextProperty; intros; rfl

def findnextChar (character : UInt32) (string : JStr) (index : IntegerInput I) : SJl (Option JInt64) := do
  let converted ← index.toInt
  Strings.findnextChar character string converted
def FindnextCharProperty : Prop := ∀ (I : Type) character string (index : IntegerInput I) converted,
  index.toInt = .ok converted →
  findnextChar character string index = Strings.findnextChar character string converted
theorem findnextChar_proven : FindnextCharProperty := by
  unfold FindnextCharProperty
  intros; simp_all [findnextChar, bind, Except.bind, pure, Except.pure]

structure DenseBytes where
  bytes : List UInt8
  firstindex : JInt64

def findnextByte (array : DenseBytes) (byte : UInt8) (index : IntegerInput I) : SJl (Option JInt64) := do
  let converted ← index.toInt
  if converted < array.firstindex then .error boundsErr
  else Strings.findnextByte array.bytes byte converted
def FindnextByteProperty : Prop := ∀ (I : Type) array byte (index : IntegerInput I) converted,
  index.toInt = .ok converted → array.firstindex ≤ converted →
  findnextByte array byte index = Strings.findnextByte array.bytes byte converted
theorem findnextByte_proven : FindnextByteProperty := by
  intro I array byte index converted hconvert hbound
  unfold findnextByte
  rw [hconvert]
  simp only [bind, Except.bind]
  rw [if_neg (by
    change array.firstindex.val ≤ converted.val at hbound
    change ¬ converted.val < array.firstindex.val
    omega)]

def memchr (array : DenseBytes) (byte : UInt8) (index : JInt64) : Option JInt64 :=
  (array.bytes.drop (index.val - array.firstindex.val).toNat).findIdx? (fun value => value == byte) |>
    Option.map (fun offset => index + ix (Int.ofNat offset))
def MemchrProperty : Prop := ∀ array byte index,
  memchr array byte index =
    Option.map (fun offset => index + ix (Int.ofNat offset))
      ((array.bytes.drop (index.val - array.firstindex.val).toNat).findIdx?
        (fun value => value == byte))
theorem memchr_proven : MemchrProperty := by
  unfold MemchrProperty
  intros
  rfl

def findnextZero (array : DenseBytes) (index : IntegerInput I) : SJl (Option JInt64) :=
  findnextByte array 0 index
def FindnextZeroProperty : Prop := ∀ (I : Type) array (index : IntegerInput I),
  findnextZero array index = findnextByte array 0 index
theorem findnextZero_proven : FindnextZeroProperty := by unfold FindnextZeroProperty; intros; rfl

def findprevChar (character : UInt32) (string : JStr) (index : IntegerInput I) : SJl (Option JInt64) := do
  let converted ← index.toInt
  Strings.findprevChar character string converted
def FindprevCharProperty : Prop := ∀ (I : Type) character string (index : IntegerInput I) converted,
  index.toInt = .ok converted →
  findprevChar character string index = Strings.findprevChar character string converted
theorem findprevChar_proven : FindprevCharProperty := by
  unfold FindprevCharProperty
  intros; simp_all [findprevChar, bind, Except.bind, pure, Except.pure]

def findprevByte (array : DenseBytes) (byte : UInt8) (index : IntegerInput I) : SJl (Option JInt64) := do
  let converted ← index.toInt
  Strings.findprevByte array.bytes byte converted
def FindprevByteProperty : Prop := ∀ (I : Type) array byte (index : IntegerInput I) converted,
  index.toInt = .ok converted →
  findprevByte array byte index = Strings.findprevByte array.bytes byte converted
theorem findprevByte_proven : FindprevByteProperty := by
  unfold FindprevByteProperty
  intros; simp_all [findprevByte, bind, Except.bind, pure, Except.pure]

def memrchr (array : DenseBytes) (byte : UInt8) (index : JInt64) : Option JInt64 :=
  Strings.findprevByte array.bytes byte index |>.toOption.join
def MemrchrProperty : Prop := ∀ array byte index,
  memrchr array byte index = (Strings.findprevByte array.bytes byte index).toOption.join
theorem memrchr_proven : MemrchrProperty := by
  unfold MemrchrProperty
  intros
  rfl

def findprevZero (array : DenseBytes) (index : IntegerInput I) : SJl (Option JInt64) :=
  findprevByte array 0 index
def FindprevZeroProperty : Prop := ∀ (I : Type) array (index : IntegerInput I),
  findprevZero array index = findprevByte array 0 index
theorem findprevZero_proven : FindprevZeroProperty := by unfold FindprevZeroProperty; intros; rfl

def findallChar (character : UInt32) (string : JStr) : List Int :=
  (Strings.collectPairs string).filterMap
    (fun pair => if pair.1 == character then some pair.2.val else none)
def FindallCharProperty : Prop := ∀ character string,
  findallChar character string =
    (Strings.collectPairs string).filterMap
      (fun pair => if pair.1 == character then some pair.2.val else none)
theorem findallChar_proven : FindallCharProperty := by
  unfold FindallCharProperty
  intros
  rfl

/-! Wrapper and generic-search methods, `base/strings/search.jl:301-916`. -/

structure IndexedBytes where
  bytes : List UInt8
  firstindex : JInt64

def lastindexBytes (array : IndexedBytes) : JInt64 :=
  array.firstindex + ix (Int.ofNat array.bytes.length) - ix 1

def findfirstString (pattern string : S) (firstindex : S → SJl JInt64)
    (findnext : S → S → JInt64 → SJl R) : SJl R := do
  let start ← firstindex string
  findnext pattern string start

def FindfirstStringProperty : Prop :=
  (∀ (S R : Type) pattern string firstindex findnext start,
    firstindex string = .ok start →
    findfirstString pattern string firstindex (findnext : S → S → JInt64 → SJl R) =
      findnext pattern string start) ∧
  (∀ (S R : Type) pattern string firstindex findnext error,
    firstindex string = .error error →
    findfirstString pattern string firstindex (findnext : S → S → JInt64 → SJl R) = .error error)

theorem findfirstString_proven : FindfirstStringProperty := by
  constructor <;> intros <;>
    simp_all [findfirstString, bind, Except.bind, pure, Except.pure]

def findfirstChar (character : C) (string : S)
    (findfirstPredicate : C → S → SJl R) : SJl R :=
  findfirstPredicate character string

def FindfirstCharProperty : Prop := ∀ (C S R : Type) character string dispatch,
  findfirstChar character string (dispatch : C → S → SJl R) = dispatch character string

theorem findfirstChar_proven : FindfirstCharProperty := by
  unfold FindfirstCharProperty
  intros
  rfl

def findfirstVector (pattern array : A) (firstindex : A → SJl JInt64)
    (search : A → A → JInt64 → SJl R) : SJl R := do
  let start ← firstindex array
  search array pattern start

def FindfirstVectorProperty : Prop :=
  (∀ (A R : Type) pattern array firstindex search start,
    firstindex array = .ok start →
    findfirstVector pattern array firstindex (search : A → A → JInt64 → SJl R) =
      search array pattern start) ∧
  (∀ (A R : Type) pattern array firstindex search error,
    firstindex array = .error error →
    findfirstVector pattern array firstindex (search : A → A → JInt64 → SJl R) = .error error)

theorem findfirstVector_proven : FindfirstVectorProperty := by
  constructor <;> intros <;>
    simp_all [findfirstVector, bind, Except.bind, pure, Except.pure]

structure PredicateStep (C : Type) where
  index : JInt64
  character : C

def firstAccepted (test : C → SJl Bool) : List (PredicateStep C) → SJl (Option JInt64)
  | [] => .ok none
  | step :: rest => do
      let accepted ← test step.character
      if accepted then return some step.index
      firstAccepted test rest

def findnextPredicate (steps : List (PredicateStep C)) (test : C → SJl Bool) : SJl (Option JInt64) :=
  firstAccepted test steps

def FirstAcceptedProperty : Prop :=
  (∀ (C : Type) test (step : PredicateStep C) rest,
    test step.character = .ok true →
    firstAccepted test (step :: rest) = .ok (some step.index)) ∧
  (∀ (C : Type) test (step : PredicateStep C) rest,
    test step.character = .ok false →
    firstAccepted test (step :: rest) = firstAccepted test rest) ∧
  (∀ (C : Type) test (step : PredicateStep C) rest error,
    test step.character = .error error →
    firstAccepted test (step :: rest) = .error error) ∧
  (∀ (C : Type) (test : C → SJl Bool), firstAccepted test [] = .ok none)

theorem firstAccepted_proven : FirstAcceptedProperty := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [firstAccepted, bind, Except.bind, pure, Except.pure]

def charInAbstract (character : C) (string : S)
    (findfirst : C → S → SJl (Option JInt64)) : SJl Bool := do
  let result ← findfirst character string
  return result.isSome

def CharInAbstractProperty : Prop :=
  (∀ (C S : Type) character string findfirst index,
    findfirst character string = .ok (some index) →
    charInAbstract character string (findfirst : C → S → SJl (Option JInt64)) = .ok true) ∧
  (∀ (C S : Type) character string findfirst,
    findfirst character string = .ok none →
    charInAbstract character string (findfirst : C → S → SJl (Option JInt64)) = .ok false) ∧
  (∀ (C S : Type) character string findfirst error,
    findfirst character string = .error error →
    charInAbstract character string (findfirst : C → S → SJl (Option JInt64)) = .error error)

theorem charInAbstract_proven : CharInAbstractProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [charInAbstract, bind, Except.bind, pure, Except.pure]

def charInDense (character : C) (string : S)
    (findnext : C → S → JInt64 → SJl (Option JInt64)) : SJl Bool := do
  let result ← findnext character string (ix 1)
  return result.isSome

def CharInDenseProperty : Prop :=
  (∀ (C S : Type) character string findnext index,
    findnext character string (ix 1) = .ok (some index) →
    charInDense character string (findnext : C → S → JInt64 → SJl (Option JInt64)) = .ok true) ∧
  (∀ (C S : Type) character string findnext,
    findnext character string (ix 1) = .ok none →
    charInDense character string (findnext : C → S → JInt64 → SJl (Option JInt64)) = .ok false)

theorem charInDense_proven : CharInDenseProperty := by
  constructor <;> intros <;>
    simp_all [charInDense, bind, Except.bind, pure, Except.pure]

def searchindexChar (findnext : SJl (Option JInt64)) : SJl JInt64 := do
  let result ← findnext
  return result.getD (ix 0)

def SearchindexCharProperty : Prop :=
  (∀ index, searchindexChar (.ok (some index)) = .ok index) ∧
  searchindexChar (.ok none) = .ok (ix 0) ∧
  (∀ error, searchindexChar (.error error) = .error error)

theorem searchindexChar_proven : SearchindexCharProperty := by
  refine ⟨?_, rfl, ?_⟩ <;> intros <;> rfl

def searchBloomMask (value : UInt64) : UInt64 := (1 : UInt64) <<< (value &&& 63)

def SearchBloomMaskProperty : Prop := ∀ (value bit : UInt64),
  bit = value &&& 63 → searchBloomMask value = (1 : UInt64) <<< bit

theorem searchBloomMask_proven : SearchBloomMaskProperty := by
  intro value bit hbit
  rw [hbit]
  rfl

def nthStringByte (codeunit : JInt64 → SJl UInt8) (index : JInt64) : SJl UInt8 :=
  codeunit index

def NthStringByteProperty : Prop := ∀ codeunit index,
  nthStringByte codeunit index = codeunit index

theorem nthStringByte_proven : NthStringByteProperty := by
  unfold NthStringByteProperty
  intros
  rfl

def nthVectorByte (array : IndexedBytes) (index : JInt64) : SJl UInt8 :=
  let physical := index + (array.firstindex - ix 1)
  let offset := physical - array.firstindex
  if offset.val < 0 || offset.val ≥ array.bytes.length then .error boundsErr
  else .ok (array.bytes.getD offset.val.toNat 0)

def NthVectorByteProperty : Prop :=
  (∀ array index,
    (index + (array.firstindex - ix 1) - array.firstindex).val < 0 →
    nthVectorByte array index = .error boundsErr) ∧
  (∀ array index,
    0 ≤ (index + (array.firstindex - ix 1) - array.firstindex).val →
    (index + (array.firstindex - ix 1) - array.firstindex).val < array.bytes.length →
    nthVectorByte array index = .ok (array.bytes.getD
      (index + (array.firstindex - ix 1) - array.firstindex).val.toNat 0))

theorem nthVectorByte_proven : NthVectorByteProperty := by
  constructor
  · intros array index hneg
    simp [nthVectorByte, hneg]
  · intros array index hlo hhi
    simp [nthVectorByte, show ¬ (index + (array.firstindex - ix 1) - array.firstindex).val < 0 by omega,
      show ¬ (index + (array.firstindex - ix 1) - array.firstindex).val ≥ array.bytes.length by omega]

def normalizeIndex (array : IndexedBytes) (index : JInt64) : JInt64 :=
  index - (array.firstindex - ix 1)

def restoreIndex (array : IndexedBytes) (index : Int) : JInt64 :=
  if index = 0 then array.firstindex - ix 1
  else ix index + (array.firstindex - ix 1)

def searchindexBytes (source pattern : IndexedBytes) (index : IntegerInput I) : SJl JInt64 := do
  let converted ← index.toInt
  let found ← Strings.searchindexBytes source.bytes pattern.bytes (normalizeIndex source converted)
  return restoreIndex source found

def SearchindexBytesProperty : Prop :=
  (∀ (I : Type) source pattern (index : IntegerInput I) converted found,
    index.toInt = .ok converted →
    Strings.searchindexBytes source.bytes pattern.bytes (normalizeIndex source converted) = .ok found →
    searchindexBytes source pattern index = .ok (restoreIndex source found)) ∧
  (∀ (I : Type) source pattern (index : IntegerInput I) error,
    index.toInt = .error error → searchindexBytes source pattern index = .error error)

theorem searchindexBytes_proven : SearchindexBytesProperty := by
  constructor <;> intros <;>
    simp_all [searchindexBytes, bind, Except.bind, pure, Except.pure]

def denseSearchindex (singleByte : Bool) (index : IntegerInput I)
    (singleByteSearch : JInt64 → SJl (Option JInt64))
    (byteVectorSearch : JInt64 → SJl Int) : SJl JInt64 := do
  let converted ← index.toInt
  if singleByte then
    let found ← singleByteSearch converted
    return found.getD (ix 0)
  let found ← byteVectorSearch converted
  return ix found

def DenseSearchindexProperty : Prop :=
  (∀ (I : Type) (index : IntegerInput I) singleByteSearch byteVectorSearch converted,
    index.toInt = .ok converted →
    denseSearchindex false index singleByteSearch byteVectorSearch =
      (byteVectorSearch converted).map ix) ∧
  (∀ (I : Type) (index : IntegerInput I) singleByteSearch byteVectorSearch converted found,
    index.toInt = .ok converted →
    singleByteSearch converted = .ok found →
    denseSearchindex true index singleByteSearch byteVectorSearch = .ok (found.getD (ix 0)))

theorem denseSearchindex_proven : DenseSearchindexProperty := by
  constructor
  · intros I index singleByteSearch byteVectorSearch converted hconvert
    unfold denseSearchindex
    rw [hconvert]
    simp only [bind, Except.bind]
    rfl
  · intros I index singleByteSearch byteVectorSearch converted found hconvert hfound
    unfold denseSearchindex
    rw [hconvert]
    simp only [bind, Except.bind]
    rw [hfound]
    rfl

def searchRange (source pattern : IndexedBytes) (index : JInt64) : Option (JInt64 × JInt64) :=
  if pattern.bytes.isEmpty then some (index, index - ix 1)
  else if source.firstindex ≤ index then
    some (index, index + lastindexBytes pattern - pattern.firstindex)
  else none

def SearchRangeProperty : Prop :=
  (∀ source pattern index,
    pattern.bytes = [] → searchRange source pattern index = some (index, index - ix 1)) ∧
  (∀ source pattern index,
    pattern.bytes ≠ [] → source.firstindex ≤ index →
    searchRange source pattern index =
      some (index, index + lastindexBytes pattern - pattern.firstindex)) ∧
  (∀ source pattern index,
    pattern.bytes ≠ [] → index < source.firstindex →
    searchRange source pattern index = none)

theorem searchRange_proven : SearchRangeProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intros source pattern index hempty
    simp [searchRange, List.isEmpty_iff, hempty]
  · intros source pattern index hnonempty hbound
    simp [searchRange, List.isEmpty_iff, hnonempty, hbound]
  · intros source pattern index hnonempty hbound
    simp [searchRange, List.isEmpty_iff, hnonempty,
      show ¬ source.firstindex ≤ index by
        change ¬ source.firstindex.val ≤ index.val
        change index.val < source.firstindex.val at hbound
        omega]

/-- Auxiliary property of the range constructor alone. The constructor accepts
intermediate indices which need not arise from byte search. -/
def SyntheticOffsetPatternRangeProperty : Prop := ∀ source pattern index start stop,
  pattern.bytes ≠ [] →
  searchRange source pattern index = some (start, stop) →
  stop.val - start.val + 1 = pattern.bytes.length

theorem syntheticOffsetPatternRange_refuted : ¬ SyntheticOffsetPatternRangeProperty := by
  intro property
  let source : IndexedBytes := ⟨[0x40], ix 1⟩
  let pattern : IndexedBytes := ⟨[0x52, 0x62], ix 1⟩
  have result := property source pattern (ix 9223372036854775807)
    (ix 9223372036854775807) (ix (-9223372036854775808)) (by decide) (by decide)
  change (-9223372036854775808 : Int) - 9223372036854775807 + 1 = 2 at result
  omega

/-- The documented range-length promise, over indices returned by the actual
forward search rather than arbitrary range-constructor intermediates. -/
def OffsetPatternRangeProperty : Prop := ∀ (I : Type) source pattern (input : IntegerInput I) index start stop,
  pattern.bytes ≠ [] →
  searchindexBytes source pattern input = .ok index →
  searchRange source pattern index = some (start, stop) →
  stop.val - start.val + 1 = pattern.bytes.length

/-- Prior master used the pattern's last index as if its first index were one. -/
def legacySearchRange (source pattern : IndexedBytes) (index : JInt64) :
    Option (JInt64 × JInt64) :=
  if pattern.bytes.isEmpty then some (index, index - ix 1)
  else if source.firstindex ≤ index then
    some (index, index + lastindexBytes pattern - ix 1)
  else none

def LegacyOffsetPatternRangeProperty : Prop := ∀ source pattern index start stop,
  pattern.bytes ≠ [] →
  legacySearchRange source pattern index = some (start, stop) →
  stop.val - start.val + 1 = pattern.bytes.length

theorem offsetPatternRange_refuted : ¬ LegacyOffsetPatternRangeProperty := by
  intro property
  let source : IndexedBytes := ⟨[0x40, 0x52, 0x62, 0x63], ix 10⟩
  let pattern : IndexedBytes := ⟨[0x52, 0x62], ix 5⟩
  have result := property source pattern (ix 11) (ix 11) (ix 16) (by decide) (by decide)
  change (16 : Int) - 11 + 1 = 2 at result
  omega

def findnextString (pattern string : S) (start : IntegerInput I)
    (search : S → S → JInt64 → SJl R) : SJl R := do
  let converted ← start.toInt
  search string pattern converted

def FindnextStringProperty : Prop := ∀ (S I R : Type) pattern string (start : IntegerInput I)
    search converted,
  start.toInt = .ok converted →
  findnextString pattern string start (search : S → S → JInt64 → SJl R) =
    search string pattern converted

theorem findnextString_proven : FindnextStringProperty := by
  unfold FindnextStringProperty
  intros
  simp_all [findnextString, bind, Except.bind, pure, Except.pure]

def findnextCharWrapper (character : C) (string : S) (start : I)
    (findnextPredicate : C → S → I → SJl R) : SJl R :=
  findnextPredicate character string start

def FindnextCharWrapperProperty : Prop := ∀ (C S I R : Type) character string start dispatch,
  findnextCharWrapper character string start (dispatch : C → S → I → SJl R) =
    dispatch character string start

theorem findnextCharWrapper_proven : FindnextCharWrapperProperty := by
  unfold FindnextCharWrapperProperty
  intros
  rfl

def findnextVector (pattern array : A) (start : I)
    (search : A → A → I → SJl R) : SJl R := search array pattern start

def FindnextVectorProperty : Prop := ∀ (A I R : Type) pattern array start dispatch,
  findnextVector pattern array start (dispatch : A → A → I → SJl R) =
    dispatch array pattern start

theorem findnextVector_proven : FindnextVectorProperty := by
  unfold FindnextVectorProperty
  intros
  rfl

def findlastString (pattern string : S) (lastindex : S → SJl I)
    (findprev : S → S → I → SJl R) : SJl R := do
  let start ← lastindex string
  findprev pattern string start

def FindlastStringProperty : Prop := ∀ (S I R : Type) pattern string lastindex findprev start,
  lastindex string = .ok start →
  findlastString pattern string lastindex (findprev : S → S → I → SJl R) =
    findprev pattern string start

theorem findlastString_proven : FindlastStringProperty := by
  unfold FindlastStringProperty
  intros
  simp_all [findlastString, bind, Except.bind, pure, Except.pure]

def findlastVector (pattern array : A) (lastindex : A → SJl I)
    (findprev : A → A → I → SJl R) : SJl R := do
  let start ← lastindex array
  findprev pattern array start

def FindlastVectorProperty : Prop := ∀ (A I R : Type) pattern array lastindex findprev start,
  lastindex array = .ok start →
  findlastVector pattern array lastindex (findprev : A → A → I → SJl R) =
    findprev pattern array start

theorem findlastVector_proven : FindlastVectorProperty := by
  unfold FindlastVectorProperty
  intros
  simp_all [findlastVector, bind, Except.bind, pure, Except.pure]

def findlastChar (character : C) (string : S)
    (findlastPredicate : C → S → SJl R) : SJl R :=
  findlastPredicate character string

def FindlastCharProperty : Prop := ∀ (C S R : Type) character string dispatch,
  findlastChar character string (dispatch : C → S → SJl R) = dispatch character string

theorem findlastChar_proven : FindlastCharProperty := by
  unfold FindlastCharProperty
  intros
  rfl

structure MatchRange where
  first : JInt64
  last : JInt64
deriving DecidableEq

def findallResponses (overlap : Bool) (endIndex : JInt64)
    (nextind : JInt64 → SJl JInt64) : List (Option MatchRange) → SJl (List MatchRange)
  | [] => .ok []
  | none :: _ => .ok []
  | some range :: rest =>
      let pivot := if overlap = true ∨ range.last < range.first then range.first else range.last
      if endIndex < pivot then .ok [range]
      else do
        let _ ← nextind pivot
        let following ← findallResponses overlap endIndex nextind rest
        return range :: following

def FindallResponsesProperty : Prop :=
  (∀ overlap endIndex nextind,
    findallResponses overlap endIndex nextind [] = .ok []) ∧
  (∀ overlap endIndex nextind rest,
    findallResponses overlap endIndex nextind (none :: rest) = .ok []) ∧
  (∀ overlap endIndex nextind range rest,
    endIndex < (if overlap = true ∨ range.last < range.first then range.first else range.last) →
    findallResponses overlap endIndex nextind (some range :: rest) = .ok [range])

theorem findallResponses_proven : FindallResponsesProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intros; rfl
  · intros; rfl
  · intros overlap endIndex nextind range rest h
    simp [findallResponses, h]

def findprevPredicate (steps : List (PredicateStep C)) (test : C → SJl Bool) : SJl (Option JInt64) :=
  firstAccepted test steps

def FindprevPredicateProperty : Prop := ∀ (C : Type) (steps : List (PredicateStep C)) test,
  findprevPredicate steps test = firstAccepted test steps

theorem findprevPredicate_proven : FindprevPredicateProperty := by
  unfold FindprevPredicateProperty
  intros
  rfl

structure GenericCandidate where
  index : JInt64
  suffixMatched : Bool

def firstMatchedCandidate : List GenericCandidate → Option JInt64
  | [] => none
  | candidate :: rest =>
      if candidate.suffixMatched then some candidate.index else firstMatchedCandidate rest

def lastMatchedCandidate : List GenericCandidate → Option JInt64
  | [] => none
  | candidate :: rest =>
      match lastMatchedCandidate rest with
      | some index => some index
      | none => if candidate.suffixMatched then some candidate.index else none

def searchindexGeneric (sourceFirst nextAfterLast start : JInt64)
    (patternEmpty : Bool) (candidates : List GenericCandidate) : SJl JInt64 :=
  let sentinel := sourceFirst - ix 1
  if patternEmpty then
    if sourceFirst ≤ start && start ≤ nextAfterLast then .ok start else .error boundsErr
  else .ok ((firstMatchedCandidate candidates).getD sentinel)

def SearchindexGenericProperty : Prop :=
  (∀ sourceFirst nextAfterLast start candidates,
    sourceFirst ≤ start → start ≤ nextAfterLast →
    searchindexGeneric sourceFirst nextAfterLast start true candidates = .ok start) ∧
  (∀ sourceFirst nextAfterLast start candidates,
    (start < sourceFirst ∨ nextAfterLast < start) →
    searchindexGeneric sourceFirst nextAfterLast start true candidates = .error boundsErr) ∧
  (∀ sourceFirst nextAfterLast start candidates,
    searchindexGeneric sourceFirst nextAfterLast start false candidates =
      .ok ((firstMatchedCandidate candidates).getD (sourceFirst - ix 1)))

theorem searchindexGeneric_proven : SearchindexGenericProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intros
    simp_all [searchindexGeneric]
  · intros sourceFirst nextAfterLast start candidates hout
    simp [searchindexGeneric]
    rcases hout with hlow | hhigh
    · have : ¬ sourceFirst ≤ start := by
        change ¬ sourceFirst.val ≤ start.val
        change start.val < sourceFirst.val at hlow
        omega
      simp [this]
    · by_cases hlo : sourceFirst ≤ start
      · have : ¬ start ≤ nextAfterLast := by
          change ¬ start.val ≤ nextAfterLast.val
          change nextAfterLast.val < start.val at hhigh
          omega
        simp [hlo, this]
      · simp [hlo]
  · intros
    rfl

def rsearchindexGeneric (sourceFirst nextAfterLast start : JInt64)
    (patternEmpty : Bool) (candidates : List GenericCandidate) : SJl JInt64 :=
  if patternEmpty then
    if sourceFirst ≤ start && start ≤ nextAfterLast then .ok start else .error boundsErr
  else .ok ((lastMatchedCandidate candidates).getD (ix 0))

def RsearchindexGenericProperty : Prop :=
  (∀ sourceFirst nextAfterLast start candidates,
    sourceFirst ≤ start → start ≤ nextAfterLast →
    rsearchindexGeneric sourceFirst nextAfterLast start true candidates = .ok start) ∧
  (∀ sourceFirst nextAfterLast start candidates,
    rsearchindexGeneric sourceFirst nextAfterLast start false candidates =
      .ok ((lastMatchedCandidate candidates).getD (ix 0)))

theorem rsearchindexGeneric_proven : RsearchindexGenericProperty := by
  constructor
  · intros; simp_all [rsearchindexGeneric]
  · intros; rfl

def rsearchindexBytes (source pattern : IndexedBytes) (index : IntegerInput I) : SJl JInt64 := do
  let converted ← index.toInt
  let normalized := normalizeIndex source converted
  let found ← Strings.rsearchindexBytes source.bytes pattern.bytes normalized.val
  return restoreIndex source found

def RsearchindexBytesProperty : Prop := ∀ (I : Type) source pattern (index : IntegerInput I)
    converted found,
  index.toInt = .ok converted →
  Strings.rsearchindexBytes source.bytes pattern.bytes (normalizeIndex source converted).val = .ok found →
  rsearchindexBytes source pattern index = .ok (restoreIndex source found)

theorem rsearchindexBytes_proven : RsearchindexBytesProperty := by
  unfold RsearchindexBytesProperty
  intros
  simp_all [rsearchindexBytes, bind, Except.bind, pure, Except.pure]

def denseRsearchindex (index : IntegerInput I) (search : JInt64 → SJl Int) : SJl JInt64 := do
  let converted ← index.toInt
  let found ← search converted
  return ix found

def DenseRsearchindexProperty : Prop := ∀ (I : Type) (index : IntegerInput I) search converted found,
  index.toInt = .ok converted →
  search converted = .ok found →
  denseRsearchindex index search = .ok (ix found)

theorem denseRsearchindex_proven : DenseRsearchindexProperty := by
  unfold DenseRsearchindexProperty
  intros
  simp_all [denseRsearchindex, bind, Except.bind, pure, Except.pure]

def rsearchRange (source pattern : IndexedBytes) (index : JInt64) : Option (JInt64 × JInt64) :=
  if pattern.bytes.isEmpty then some (index, index - ix 1)
  else if source.firstindex - ix 1 < index then
    some (index, index + lastindexBytes pattern - pattern.firstindex)
  else none

def RsearchRangeProperty : Prop :=
  (∀ source pattern index,
    pattern.bytes = [] → rsearchRange source pattern index = some (index, index - ix 1)) ∧
  (∀ source pattern index,
    pattern.bytes ≠ [] → source.firstindex - ix 1 < index →
    rsearchRange source pattern index =
      some (index, index + lastindexBytes pattern - pattern.firstindex))

theorem rsearchRange_proven : RsearchRangeProperty := by
  constructor
  · intros source pattern index hempty
    simp [rsearchRange, List.isEmpty_iff, hempty]
  · intros
    simp_all [rsearchRange, List.isEmpty_iff]

def findprevString (pattern string : S) (start : IntegerInput I)
    (search : S → S → JInt64 → SJl R) : SJl R := do
  let converted ← start.toInt
  search string pattern converted

def FindprevStringProperty : Prop := ∀ (S I R : Type) pattern string (start : IntegerInput I)
    search converted,
  start.toInt = .ok converted →
  findprevString pattern string start (search : S → S → JInt64 → SJl R) =
    search string pattern converted

theorem findprevString_proven : FindprevStringProperty := by
  unfold FindprevStringProperty
  intros
  simp_all [findprevString, bind, Except.bind, pure, Except.pure]

def findprevCharWrapper (character : C) (string : S) (start : I)
    (findprevPredicate : C → S → I → SJl R) : SJl R :=
  findprevPredicate character string start

def FindprevCharWrapperProperty : Prop := ∀ (C S I R : Type) character string start dispatch,
  findprevCharWrapper character string start (dispatch : C → S → I → SJl R) =
    dispatch character string start

theorem findprevCharWrapper_proven : FindprevCharWrapperProperty := by
  unfold FindprevCharWrapperProperty
  intros
  rfl

def findprevVector (pattern array : A) (start : I)
    (search : A → A → I → SJl R) : SJl R := search array pattern start

def FindprevVectorProperty : Prop := ∀ (A I R : Type) pattern array start dispatch,
  findprevVector pattern array start (dispatch : A → A → I → SJl R) =
    dispatch array pattern start

theorem findprevVector_proven : FindprevVectorProperty := by
  unfold FindprevVectorProperty
  intros
  rfl

def occursinSearch (needle haystack : S)
    (searchindex : S → S → JInt64 → SJl JInt64)
    (firstindex : S → SJl JInt64) : SJl Bool := do
  let start ← firstindex haystack
  let result ← searchindex haystack needle start
  return result.val ≠ 0

def OccursinSearchProperty : Prop := ∀ (S : Type) needle haystack searchindex firstindex
    start result,
  firstindex haystack = .ok start → searchindex haystack needle start = .ok result →
  occursinSearch needle haystack (searchindex : S → S → JInt64 → SJl JInt64) firstindex =
    .ok (result.val ≠ 0)

theorem occursinSearch_proven : OccursinSearchProperty := by
  unfold OccursinSearchProperty
  intros
  simp_all [occursinSearch, bind, Except.bind, pure, Except.pure]

structure OccursinFix (S : Type) where
  haystack : S
  apply : S → S → SJl Bool

def makeOccursinFix (haystack : S) (occursin : S → S → SJl Bool) : OccursinFix S :=
  ⟨haystack, occursin⟩

def OccursinFixProperty : Prop := ∀ (S : Type) haystack occursin needle,
  (makeOccursinFix haystack (occursin : S → S → SJl Bool)).apply needle haystack =
    occursin needle haystack

theorem occursinFix_proven : OccursinFixProperty := by
  unfold OccursinFixProperty
  intros
  rfl

inductive SearchError where
  | string (error : SErr)
  | errorException (message : String)
deriving Repr, DecidableEq

def stringIn : Except SearchError Unit :=
  .error (.errorException "use occursin(needle, haystack) for string containment")

def StringInProperty : Prop := ∀ _input : Unit,
  stringIn = .error (.errorException "use occursin(needle, haystack) for string containment")

theorem stringIn_proven : StringInProperty := by
  intro
  rfl

def byteIn (byte : B) (array : A)
    (findfirst : B → A → SJl (Option I)) : SJl Bool := do
  let result ← findfirst byte array
  return !result.isNone

def ByteInProperty : Prop :=
  (∀ (B A I : Type) byte array findfirst index,
    findfirst byte array = .ok (some index) →
    byteIn byte array (findfirst : B → A → SJl (Option I)) = .ok true) ∧
  (∀ (B A I : Type) byte array findfirst,
    findfirst byte array = .ok none →
    byteIn byte array (findfirst : B → A → SJl (Option I)) = .ok false)

theorem byteIn_proven : ByteInProperty := by
  constructor <;> intros <;>
    simp_all [byteIn, bind, Except.bind, pure, Except.pure]

end JuliaLean.StringsCovA.SearchRebuilt

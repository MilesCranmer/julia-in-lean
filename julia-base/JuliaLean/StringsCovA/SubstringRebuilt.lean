import JuliaLean.StringsCovA.Substring

namespace JuliaLean.StringsCovA.SubstringRebuilt

open JuliaLean JuliaLean.Strings

structure Sub (S : Type) where
  string : S
  offset : JInt64
  ncodeunits : JInt64

structure IntegerInput (I : Type) where
  value : I
  toInt : SJl JInt64

structure TypedCtorInput (S : Type) where
  string : S
  first : JInt64
  last : JInt64
  checkbounds : S → JInt64 → JInt64 → SJl Unit
  isvalid : S → JInt64 → SJl Bool
  stringIndexError : S → JInt64 → SJl Unit
  nextind : S → JInt64 → SJl JInt64

def typedCtor (input : TypedCtorInput S) : SJl (Sub S) :=
  if input.last < input.first then .ok ⟨input.string, ix 0, ix 0⟩
  else do
    let _ ← input.checkbounds input.string input.first input.last
    let firstValid ← input.isvalid input.string input.first
    if !firstValid then
      let _ ← input.stringIndexError input.string input.first
      .error .assertion
    else
      let lastValid ← input.isvalid input.string input.last
      if !lastValid then
        let _ ← input.stringIndexError input.string input.last
        .error .assertion
      else
        let after ← input.nextind input.string input.last
        return ⟨input.string, input.first - ix 1, after - input.first⟩

def TypedCtorProperty : Prop :=
  (∀ (S : Type) (input : TypedCtorInput S), input.last < input.first →
    typedCtor input = .ok ⟨input.string, ix 0, ix 0⟩) ∧
  (∀ (S : Type) (input : TypedCtorInput S) after,
    ¬(input.last < input.first) →
    input.checkbounds input.string input.first input.last = .ok () →
    input.isvalid input.string input.first = .ok true →
    input.isvalid input.string input.last = .ok true →
    input.nextind input.string input.last = .ok after →
    typedCtor input = .ok ⟨input.string, input.first - ix 1, after - input.first⟩)

theorem typedCtor_proven : TypedCtorProperty := by
  constructor <;> intros <;>
    simp_all [typedCtor, bind, Except.bind, pure, Except.pure]

def EmptyOffsetProperty : Prop := ∀ (S : Type) (input : TypedCtorInput S),
  input.last < input.first ->
  input.first = input.last + ix 1 ->
  input.checkbounds input.string input.first input.last = .ok () ->
    ∃ output, typedCtor input = .ok output ∧ output.offset = input.first - ix 1

def emptyOffsetInput : TypedCtorInput Unit where
  string := ()
  first := ix 4
  last := ix 3
  checkbounds := fun _ _ _ => .ok ()
  isvalid := fun _ _ => .error .assertion
  stringIndexError := fun _ _ => .error .assertion
  nextind := fun _ _ => .error .assertion

theorem emptyOffset_refuted : ¬ EmptyOffsetProperty := by
  intro property
  obtain ⟨output, hrun, hoffset⟩ :=
    property Unit emptyOffsetInput (by decide) (by decide) rfl
  simp [typedCtor, emptyOffsetInput] at hrun
  cases hrun
  have hval := congrArg Subtype.val hoffset
  change (ix 0).val = (ix 4 - ix 1).val at hval
  have hzero : (ix 0).val = 0 := by decide
  have hthree : (ix 4 - ix 1).val = 3 := by decide
  rw [hzero, hthree] at hval
  omega

structure RawCtorInput (S : Type) where
  string : S
  first : JInt64
  count : JInt64
  ncodeunits : S → SJl JInt64

def rawCtor (input : RawCtorInput S) : SJl (Sub S) := do
  let total ← input.ncodeunits input.string
  if input.count < ix 0 || input.first < ix 1 || total - input.first + ix 1 < input.count then
    .error (.jl .boundsError)
  else .ok ⟨input.string, input.first - ix 1, input.count⟩

def RawCtorProperty : Prop := ∀ (S : Type) (input : RawCtorInput S) total,
  input.ncodeunits input.string = .ok total →
  rawCtor input =
    if input.count < ix 0 || input.first < ix 1 || total - input.first + ix 1 < input.count then
      .error (.jl .boundsError)
    else .ok ⟨input.string, input.first - ix 1, input.count⟩

theorem rawCtor_proven : RawCtorProperty := by
  unfold RawCtorProperty
  intros
  simp_all [rawCtor, bind, Except.bind, pure, Except.pure]

structure RawNestedInput (S : Type) where
  substring : Sub S
  first : JInt64
  count : JInt64

def rawNested (input : RawNestedInput S) : SJl (Sub S) :=
  if input.count < ix 0 || input.first < ix 1 ||
      input.substring.ncodeunits - input.first + ix 1 < input.count then
    .error (.jl .boundsError)
  else .ok ⟨input.substring.string,
    input.first + input.substring.offset - ix 1, input.count⟩

def RawNestedProperty : Prop := ∀ (S : Type) (input : RawNestedInput S),
  rawNested input =
    if input.count < ix 0 || input.first < ix 1 ||
        input.substring.ncodeunits - input.first + ix 1 < input.count then
      .error (.jl .boundsError)
    else .ok ⟨input.substring.string,
      input.first + input.substring.offset - ix 1, input.count⟩

theorem rawNested_proven : RawNestedProperty := by unfold RawNestedProperty; intros; rfl

def typedWhole (s : S) (ncodeunits : S → SJl JInt64) : SJl (Sub S) := do
  let count ← ncodeunits s
  return ⟨s, ix 0, count⟩

def TypedWholeProperty : Prop := ∀ (S : Type) (s : S) ncodeunits count,
  ncodeunits s = .ok count → typedWhole s ncodeunits = .ok ⟨s, ix 0, count⟩
theorem typedWhole_proven : TypedWholeProperty := by
  unfold TypedWholeProperty
  intros
  simp_all [typedWhole, bind, Except.bind, pure, Except.pure]

def ctorInt (input : TypedCtorInput S) : SJl (Sub S) := typedCtor input
def CtorIntProperty : Prop := ∀ (S : Type) (input : TypedCtorInput S),
  ctorInt input = typedCtor input
theorem ctorInt_proven : CtorIntProperty := by unfold CtorIntProperty; intros; rfl

def ctorInteger (s : S) (first : IntegerInput I) (last : IntegerInput J)
    (ctor : S → JInt64 → JInt64 → SJl (Sub S)) : SJl (Sub S) := do
  let i ← first.toInt
  let j ← last.toInt
  ctor s i j

def CtorIntegerProperty : Prop := ∀ (S I J : Type) (s : S)
    (first : IntegerInput I) (last : IntegerInput J) ctor i j,
  first.toInt = .ok i → last.toInt = .ok j →
  ctorInteger s first last ctor = ctor s i j
theorem ctorInteger_proven : CtorIntegerProperty := by
  unfold CtorIntegerProperty
  intros
  simp_all [ctorInteger, bind, Except.bind, pure, Except.pure]

structure UnitRangeInput (I J : Type) where
  value : I
  first : I → SJl (IntegerInput J)
  last : I → SJl (IntegerInput J)

def ctorRange (s : S) (range : UnitRangeInput R I)
    (ctor : S → IntegerInput I → IntegerInput I → SJl (Sub S)) : SJl (Sub S) := do
  let first ← range.first range.value
  let last ← range.last range.value
  ctor s first last

def CtorRangeProperty : Prop := ∀ (S R I : Type) (s : S) (range : UnitRangeInput R I)
    ctor first last,
  range.first range.value = .ok first → range.last range.value = .ok last →
  ctorRange s range ctor = ctor s first last
theorem ctorRange_proven : CtorRangeProperty := by
  unfold CtorRangeProperty
  intros
  simp_all [ctorRange, bind, Except.bind, pure, Except.pure]

structure NestedCtorInput (S : Type) where
  substring : Sub S
  first : JInt64
  last : JInt64
  checkbounds : Sub S → JInt64 → JInt64 → SJl Unit
  parentCtor : S → JInt64 → JInt64 → SJl (Sub S)

def nestedCtor (input : NestedCtorInput S) : SJl (Sub S) := do
  if input.first ≤ input.last then
    let _ ← input.checkbounds input.substring input.first input.last
    pure ()
  else pure ()
  input.parentCtor input.substring.string
    (input.substring.offset + input.first) (input.substring.offset + input.last)

def NestedCtorProperty : Prop := ∀ (S : Type) (input : NestedCtorInput S),
  input.first ≤ input.last → input.checkbounds input.substring input.first input.last = .ok () →
  nestedCtor input = input.parentCtor input.substring.string
    (input.substring.offset + input.first) (input.substring.offset + input.last)
theorem nestedCtor_proven : NestedCtorProperty := by
  unfold NestedCtorProperty
  intros
  simp_all [nestedCtor, bind, Except.bind, pure, Except.pure]

def wholeAbstract (s : S) (ncodeunits : S → SJl JInt64)
    (rawUnchecked : S → JInt64 → JInt64 → SJl (Sub S)) : SJl (Sub S) := do
  let count ← ncodeunits s
  rawUnchecked s (ix 1) count

def WholeAbstractProperty : Prop := ∀ (S : Type) (s : S) ncodeunits rawUnchecked count,
  ncodeunits s = .ok count →
  wholeAbstract s ncodeunits rawUnchecked = rawUnchecked s (ix 1) count
theorem wholeAbstract_proven : WholeAbstractProperty := by
  unfold WholeAbstractProperty
  intros
  simp_all [wholeAbstract, bind, Except.bind, pure, Except.pure]

def wholeIdentity (s : Sub S) : Sub S := s
def WholeIdentityProperty : Prop := ∀ (S : Type) (s : Sub S), wholeIdentity s = s
theorem wholeIdentity_proven : WholeIdentityProperty := by unfold WholeIdentityProperty; intros; rfl

def viewRange (s : S) (range : R) (ctor : S → R → SJl V) : SJl V := ctor s range
def ViewRangeProperty : Prop := ∀ (S R V : Type) (s : S) range ctor,
  viewRange s range (ctor : S → R → SJl V) = ctor s range
theorem viewRange_proven : ViewRangeProperty := by unfold ViewRangeProperty; intros; rfl

def maybeviewRange (s : S) (range : R) (view : S → R → SJl V) : SJl V := view s range
def MaybeviewRangeProperty : Prop := ∀ (S R V : Type) (s : S) range view,
  maybeviewRange s range (view : S → R → SJl V) = view s range
theorem maybeviewRange_proven : MaybeviewRangeProperty := by unfold MaybeviewRangeProperty; intros; rfl

def maybeviewArgs (s : S) (args : Args) (getindex : S → Args → SJl V) : SJl V :=
  getindex s args
def MaybeviewArgsProperty : Prop := ∀ (S Args V : Type) (s : S) args getindex,
  maybeviewArgs s args (getindex : S → Args → SJl V) = getindex s args
theorem maybeviewArgs_proven : MaybeviewArgsProperty := by unfold MaybeviewArgsProperty; intros; rfl

structure ConvertInput (S T : Type) where
  source : S
  convertParent : S → SJl T
  substring : T → SJl (Sub T)
  typeAssert : Sub T → SJl (Sub T)

def convertSub (input : ConvertInput S T) : SJl (Sub T) := do
  let parent ← input.convertParent input.source
  let substring ← input.substring parent
  input.typeAssert substring

def ConvertSubProperty : Prop := ∀ (S T : Type) (input : ConvertInput S T) parent substring,
  input.convertParent input.source = .ok parent → input.substring parent = .ok substring →
  convertSub input = input.typeAssert substring
theorem convertSub_proven : ConvertSubProperty := by
  unfold ConvertSubProperty
  intros
  simp_all [convertSub, bind, Except.bind, pure, Except.pure]

def convertIdentity (s : Sub S) : Sub S := s
def ConvertIdentityProperty : Prop := ∀ (S : Type) (s : Sub S), convertIdentity s = s
theorem convertIdentity_proven : ConvertIdentityProperty := by unfold ConvertIdentityProperty; intros; rfl

structure CopyInput (P : Type) where
  parent : JStr
  offset : JInt64
  count : JInt64
  pointer : JStr → JInt64 → SJl P
  unsafeString : P → JInt64 → SJl JStr

def toString (input : CopyInput P) : SJl JStr := do
  let pointer ← input.pointer input.parent (input.offset + ix 1)
  input.unsafeString pointer input.count

def ToStringProperty : Prop := ∀ (P : Type) (input : CopyInput P) pointer,
  input.pointer input.parent (input.offset + ix 1) = .ok pointer →
  toString input = input.unsafeString pointer input.count
theorem toString_proven : ToStringProperty := by
  unfold ToStringProperty
  intros
  simp_all [toString, bind, Except.bind, pure, Except.pure]

/-! Generic accessors and pointer operations, lines 139-206. -/

def ncodeunits (s : Sub S) : JInt64 := s.ncodeunits
def NcodeunitsProperty : Prop := ∀ (S : Type) (s : Sub S), ncodeunits s = s.ncodeunits
theorem ncodeunits_proven : NcodeunitsProperty := by unfold NcodeunitsProperty; intros; rfl

def codeunitType (s : Sub S) (codeunit : S → SJl T) : SJl T := codeunit s.string
def CodeunitTypeProperty : Prop := ∀ (S T : Type) (s : Sub S) codeunit,
  codeunitType s (codeunit : S → SJl T) = codeunit s.string
theorem codeunitType_proven : CodeunitTypeProperty := by unfold CodeunitTypeProperty; intros; rfl

def lengthSub (s : Sub S) (length : S → JInt64 → JInt64 → SJl JInt64) : SJl JInt64 :=
  length s.string (s.offset + ix 1) (s.offset + s.ncodeunits)
def LengthSubProperty : Prop := ∀ (S : Type) (s : Sub S) length,
  lengthSub s length = length s.string (s.offset + ix 1) (s.offset + s.ncodeunits)
theorem lengthSub_proven : LengthSubProperty := by unfold LengthSubProperty; intros; rfl

def codeunitAt (s : Sub S) (index : I) (checkbounds : Sub S → I → SJl Unit)
    (add : JInt64 → I → SJl JInt64) (codeunit : S → JInt64 → SJl T) : SJl T := do
  let _ ← checkbounds s index
  let parentIndex ← add s.offset index
  codeunit s.string parentIndex

def CodeunitAtProperty : Prop := ∀ (S I T : Type) (s : Sub S) (index : I)
    (checkbounds : Sub S → I → SJl Unit) (add : JInt64 → I → SJl JInt64)
    (codeunit : S → JInt64 → SJl T) parentIndex,
  checkbounds s index = .ok () → add s.offset index = .ok parentIndex →
  codeunitAt s index checkbounds add codeunit = codeunit s.string parentIndex
theorem codeunitAt_proven : CodeunitAtProperty := by
  unfold CodeunitAtProperty
  intros
  simp_all [codeunitAt, bind, Except.bind, pure, Except.pure]

def getindexAt (s : Sub S) (index : I) (checkbounds : Sub S → I → SJl Unit)
    (add : JInt64 → I → SJl JInt64) (getindex : S → JInt64 → SJl T) : SJl T := do
  let _ ← checkbounds s index
  let parentIndex ← add s.offset index
  getindex s.string parentIndex

def GetindexAtProperty : Prop := ∀ (S I T : Type) (s : Sub S) (index : I)
    (checkbounds : Sub S → I → SJl Unit) (add : JInt64 → I → SJl JInt64)
    (getindex : S → JInt64 → SJl T) parentIndex,
  checkbounds s index = .ok () → add s.offset index = .ok parentIndex →
  getindexAt s index checkbounds add getindex = getindex s.string parentIndex
theorem getindexAt_proven : GetindexAtProperty := by
  unfold GetindexAtProperty
  intros
  simp_all [getindexAt, bind, Except.bind, pure, Except.pure]

def isvalidAt (s : Sub S) (index : I) (checkbounds : Sub S → I → SJl Bool)
    (add : JInt64 → I → SJl JInt64) (isvalid : S → JInt64 → SJl Bool) : SJl Bool := do
  let inbounds ← checkbounds s index
  if !inbounds then return false
  let parentIndex ← add s.offset index
  isvalid s.string parentIndex

def IsvalidAtProperty : Prop :=
  (∀ (S I : Type) (s : Sub S) (index : I)
      (checkbounds : Sub S → I → SJl Bool) (add : JInt64 → I → SJl JInt64)
      (isvalid : S → JInt64 → SJl Bool),
    checkbounds s index = .ok false → isvalidAt s index checkbounds add isvalid = .ok false) ∧
  (∀ (S I : Type) (s : Sub S) (index : I)
      (checkbounds : Sub S → I → SJl Bool) (add : JInt64 → I → SJl JInt64)
      (isvalid : S → JInt64 → SJl Bool) parentIndex,
    checkbounds s index = .ok true → add s.offset index = .ok parentIndex →
    isvalidAt s index checkbounds add isvalid = isvalid s.string parentIndex)
theorem isvalidAt_proven : IsvalidAtProperty := by
  constructor <;> intros <;>
    simp_all [isvalidAt, bind, Except.bind, pure, Except.pure]

def thisindString (s : JSub) (index : JInt64) : SJl JInt64 :=
  Strings.thisind s.view index
def ThisindStringProperty : Prop := ∀ s index,
  thisindString s index = Strings.thisind s.view index
theorem thisindString_proven : ThisindStringProperty := by unfold ThisindStringProperty; intros; rfl

def nextindString (s : JSub) (index : JInt64) : SJl JInt64 :=
  Strings.nextind s.view index
def NextindStringProperty : Prop := ∀ s index,
  nextindString s index = Strings.nextind s.view index
theorem nextindString_proven : NextindStringProperty := by unfold NextindStringProperty; intros; rfl

def lastindexString (s : JSub) : SJl JInt64 := thisindString s s.ncu
def LastindexStringProperty : Prop := ∀ s,
  lastindexString s = Strings.thisind s.view s.ncu
theorem lastindexString_proven : LastindexStringProperty := by
  unfold LastindexStringProperty lastindexString thisindString
  intros
  rfl

def parent (s : Sub S) : S := s.string
def ParentProperty : Prop := ∀ (S : Type) (s : Sub S), parent s = s.string
theorem parent_proven : ParentProperty := by unfold ParentProperty; intros; rfl

def parentindices (s : Sub S) (thisind : S → JInt64 → SJl JInt64) : SJl (JInt64 × JInt64) := do
  let last ← thisind s.string (s.offset + s.ncodeunits)
  return (s.offset + ix 1, last)
def ParentindicesProperty : Prop := ∀ (S : Type) (s : Sub S) thisind last,
  thisind s.string (s.offset + s.ncodeunits) = .ok last →
  parentindices s thisind = .ok (s.offset + ix 1, last)
theorem parentindices_proven : ParentindicesProperty := by
  unfold ParentindicesProperty
  intros
  simp_all [parentindices, bind, Except.bind, pure, Except.pure]

inductive StringOrSub where
  | string (value : JStr)
  | substring (value : JSub)

def stringSize : StringOrSub → JInt64
  | .string value => Strings.ncodeunits value
  | .substring value => value.ncu

def eqStringSub (a b : StringOrSub) (memcmp : StringOrSub → StringOrSub → Int) : Bool :=
  stringSize a == stringSize b && memcmp a b == 0
def EqStringSubProperty : Prop := ∀ a b memcmp,
  eqStringSub a b memcmp = (stringSize a == stringSize b && memcmp a b == 0)
theorem eqStringSub_proven : EqStringSubProperty := by unfold EqStringSubProperty; intros; rfl

def cmpSub (a b : JSub) (memcmp : JSub → JSub → Int) : Int :=
  let comparison := memcmp a b
  if comparison < 0 then -1 else if comparison > 0 then 1
  else if a.ncu < b.ncu then -1 else if b.ncu < a.ncu then 1 else 0
def CmpSubProperty : Prop := ∀ a b memcmp,
  cmpSub a b memcmp =
    let comparison := memcmp a b
    if comparison < 0 then -1 else if comparison > 0 then 1
    else if a.ncu < b.ncu then -1 else if b.ncu < a.ncu then 1 else 0
theorem cmpSub_proven : CmpSubProperty := by unfold CmpSubProperty; intros; rfl

def pointerAt (base : Nat) (s : JSub) (index : IntegerInput I)
    (subtractOne : I → SJl Int) : SJl Nat := do
  let delta ← subtractOne index.value
  return base + s.offset.val.toNat + delta.toNat
def PointerAtProperty : Prop := ∀ (I : Type) base s (index : IntegerInput I) subtractOne delta,
  subtractOne index.value = .ok delta →
  pointerAt base s index subtractOne = .ok (base + s.offset.val.toNat + delta.toNat)
theorem pointerAt_proven : PointerAtProperty := by
  unfold PointerAtProperty
  intros
  simp_all [pointerAt, bind, Except.bind, pure, Except.pure]

structure HashInput where
  substring : JSub
  seed : UInt64
  secret : UInt64
  pointer : JSub → SJl Nat
  sizeof : JSub → SJl Nat
  hashBytes : Nat → Nat → UInt64 → UInt64 → SJl UInt64
  toUInt : UInt64 → UInt64

def hashSub (input : HashInput) : SJl UInt64 := do
  let pointer ← input.pointer input.substring
  let size ← input.sizeof input.substring
  let hash ← input.hashBytes pointer size input.seed input.secret
  return input.toUInt hash

def HashSubProperty : Prop := ∀ input pointer size hash,
  input.pointer input.substring = .ok pointer → input.sizeof input.substring = .ok size →
  input.hashBytes pointer size input.seed input.secret = .ok hash →
  hashSub input = .ok (input.toUInt hash)
theorem hashSub_proven : HashSubProperty := by
  unfold HashSubProperty
  intros
  simp_all [hashSub, bind, Except.bind, pure, Except.pure]

inductive ParentTypeKind where | annotatedString | annotatedChar | other deriving DecidableEq
def isannotatedSub : ParentTypeKind → Bool
  | .annotatedString => true
  | .annotatedChar => true
  | .other => false
def IsannotatedSubProperty : Prop := ∀ kind,
  isannotatedSub kind = (kind = .annotatedString || kind = .annotatedChar)
theorem isannotatedSub_proven : IsannotatedSubProperty := by intro kind; cases kind <;> decide

/-! Unsafe writers, string construction, repeat, filter, and range indexing. -/

structure WriterInput (Out Source I : Type) where
  output : Out
  source : Source
  offset : I
  size : Source → SJl JInt64
  pointerOut : Out → I → SJl Nat
  pointerSource : Source → SJl Nat
  copy : Nat → Nat → JInt64 → SJl Out
  writable : Out → I → JInt64 → Prop

def writeBytes (input : WriterInput Out Source I) : SJl (Out × JInt64) := do
  let count ← input.size input.source
  let destination ← input.pointerOut input.output input.offset
  let source ← input.pointerSource input.source
  let output ← input.copy destination source count
  return (output, count)

def WriteBytesProperty : Prop := ∀ (Out Source I : Type) (input : WriterInput Out Source I)
    count destination source output,
  input.size input.source = .ok count → input.writable input.output input.offset count →
  input.pointerOut input.output input.offset = .ok destination →
  input.pointerSource input.source = .ok source →
  input.copy destination source count = .ok output →
  writeBytes input = .ok (output, count)
theorem writeBytes_proven : WriteBytesProperty := by
  unfold WriteBytesProperty
  intros
  simp_all [writeBytes, bind, Except.bind, pure, Except.pure]

structure CharWriterInput (Out I : Type) where
  output : Out
  character : UInt32
  offset : I
  pointer : Out → I → Nat → SJl Nat
  store : Out → Nat → UInt8 → SJl Out
  writable : Out → I → Nat → Prop

def writeCharStores (input : CharWriterInput Out I) : List UInt8 :=
  let bits := bswap32 input.character
  (List.range (ncodeunitsChar input.character)).map
    (fun offset => (bits >>> (UInt32.ofNat (8 * offset))).toUInt8)

def writeCharLoop (input : CharWriterInput Out I) : List UInt8 → Nat → Out → SJl Out
  | [], _, output => .ok output
  | byte :: rest, position, output => do
      let pointer ← input.pointer output input.offset position
      let output ← input.store output pointer byte
      writeCharLoop input rest (position + 1) output

def writeChar (input : CharWriterInput Out I) : SJl (Out × Nat) := do
  let output ← writeCharLoop input (writeCharStores input) 0 input.output
  return (output, ncodeunitsChar input.character)

def WriteCharProperty : Prop := ∀ (Out I : Type) (input : CharWriterInput Out I) output,
  input.writable input.output input.offset (ncodeunitsChar input.character) →
  writeCharLoop input (writeCharStores input) 0 input.output = .ok output →
  writeChar input = .ok (output, ncodeunitsChar input.character)
theorem writeChar_proven : WriteCharProperty := by
  unfold WriteCharProperty
  intros
  simp_all [writeChar, bind, Except.bind, pure, Except.pure]

inductive RestrictedValue where
  | char (value : UInt32)
  | string (value : JStr)
  | symbol (bytes : List UInt8)

inductive FullValue where
  | char (value : UInt32)
  | string (value : JStr)
  | substring (value : JSub)
  | symbol (bytes : List UInt8)

def stringRestricted (values : List RestrictedValue)
    (build : List RestrictedValue → SJl JStr) : SJl JStr := build values
def StringRestrictedProperty : Prop := ∀ values build,
  stringRestricted values build = build values
theorem stringRestricted_proven : StringRestrictedProperty := by unfold StringRestrictedProperty; intros; rfl

def fullValueSize : FullValue → JInt64
  | .char value => ix (ncodeunitsChar value)
  | .string value => Strings.ncodeunits value
  | .substring value => value.ncu
  | .symbol bytes => ix bytes.length

def sumSizes : List FullValue → JInt64
  | [] => ix 0
  | value :: rest => fullValueSize value + sumSizes rest

def writeValues (write : Out → FullValue → JInt64 → SJl (Out × JInt64)) :
    List FullValue → Out → JInt64 → SJl Out
  | [], output, _ => .ok output
  | value :: rest, output, offset => do
      let written ← write output value offset
      writeValues write rest written.1 (offset + written.2)

def buildString (values : List FullValue) (allocate : JInt64 → SJl Out)
    (write : Out → FullValue → JInt64 → SJl (Out × JInt64)) : SJl Out := do
  let output ← allocate (sumSizes values)
  writeValues write values output (ix 1)

def BuildStringProperty : Prop := ∀ (Out : Type) values allocate write output,
  allocate (sumSizes values) = .ok output →
  buildString values (allocate : JInt64 → SJl Out) write = writeValues write values output (ix 1)
theorem buildString_proven : BuildStringProperty := by
  unfold BuildStringProperty
  intros
  simp_all [buildString, bind, Except.bind, pure, Except.pure]

def repeatBitInteger (s : JStr) (count : I)
    (invokeInteger : JStr → I → SJl JStr) : SJl JStr := invokeInteger s count
def RepeatBitIntegerProperty : Prop := ∀ (I : Type) s count invokeInteger,
  repeatBitInteger s count (invokeInteger : JStr → I → SJl JStr) = invokeInteger s count
theorem repeatBitInteger_proven : RepeatBitIntegerProperty := by unfold RepeatBitIntegerProperty; intros; rfl

structure RepeatInput (I : Type) where
  bytes : List UInt8
  count : I
  negative : I → SJl Bool
  toUInt : I → SJl UInt64

def repeatInteger (input : RepeatInput I) : SJl (List UInt8) := do
  let negative ← input.negative input.count
  if negative then .error (.jl (.argumentError "negative repeat count"))
  else
    let count ← input.toUInt input.count
    if count = 0 then .ok []
    else if count = 1 then .ok input.bytes
    else if input.bytes.isEmpty then .ok []
    else if UInt64.ofNat input.bytes.length > UInt64.ofNat (2 ^ 64 - 1) / count then
      .error .outOfMemory
    else .ok (List.flatten (List.replicate count.toNat input.bytes))

def RepeatIntegerProperty : Prop :=
  (∀ (I : Type) (input : RepeatInput I),
    input.negative input.count = .ok true →
    repeatInteger input = .error (.jl (.argumentError "negative repeat count"))) ∧
  (∀ (I : Type) (input : RepeatInput I) count,
    input.negative input.count = .ok false → input.toUInt input.count = .ok count →
    count = 0 → repeatInteger input = .ok []) ∧
  (∀ (I : Type) (input : RepeatInput I) count,
    input.negative input.count = .ok false → input.toUInt input.count = .ok count →
    count = 1 → repeatInteger input = .ok input.bytes)
theorem repeatInteger_proven : RepeatIntegerProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [repeatInteger, bind, Except.bind, pure, Except.pure]

structure FilterInput (B : Type) where
  bytes : JStr
  characters : SJl (List UInt32)
  allocate : JInt64 → SJl B
  predicate : UInt32 → SJl Bool
  write : B → UInt32 → JInt64 → SJl (B × JInt64)
  resize : B → JInt64 → SJl B
  sizehint : B → JInt64 → SJl B
  makeString : B → SJl JStr

def filterLoop (input : FilterInput B) : List UInt32 → B → JInt64 → SJl (B × JInt64)
  | [], output, offset => .ok (output, offset)
  | character :: rest, output, offset => do
      let keep ← input.predicate character
      let result ← if keep then input.write output character offset else .ok (output, ix 0)
      filterLoop input rest result.1 (offset + result.2)

def filterString (input : FilterInput B) : SJl JStr := do
  let output ← input.allocate (Strings.ncodeunits input.bytes)
  let characters ← input.characters
  let result ← filterLoop input characters output (ix 1)
  let resized ← input.resize result.1 (result.2 - ix 1)
  let hinted ← input.sizehint resized (result.2 - ix 1)
  input.makeString hinted

def FilterStringProperty : Prop := ∀ (B : Type) (input : FilterInput B) output characters,
  input.allocate (Strings.ncodeunits input.bytes) = .ok output →
  input.characters = .ok characters →
  filterString input = do
    let result ← filterLoop input characters output (ix 1)
    let resized ← input.resize result.1 (result.2 - ix 1)
    let hinted ← input.sizehint resized (result.2 - ix 1)
    input.makeString hinted
theorem filterString_proven : FilterStringProperty := by
  unfold FilterStringProperty
  intros
  simp_all [filterString, bind, Except.bind, pure, Except.pure]

def rangeGetindex (s : S) (range : UnitRangeInput R I)
    (substring : S → UnitRangeInput R I → SJl V) : SJl V := substring s range
def RangeGetindexProperty : Prop := ∀ (S R I V : Type) s (range : UnitRangeInput R I) substring,
  rangeGetindex s range (substring : S → UnitRangeInput R I → SJl V) = substring s range
theorem rangeGetindex_proven : RangeGetindexProperty := by unfold RangeGetindexProperty; intros; rfl

end JuliaLean.StringsCovA.SubstringRebuilt

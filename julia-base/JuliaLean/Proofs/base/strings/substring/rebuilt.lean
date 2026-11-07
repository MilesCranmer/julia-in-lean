import JuliaLean.base.strings.substring
import JuliaLean.Proofs.base.strings.substring.coverage

namespace JuliaLean.StringsCovA.SubstringRebuilt

open JuliaLean JuliaLean.Strings

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

def RawNestedProperty : Prop := ∀ (S : Type) (input : RawNestedInput S),
  rawNested input =
    if input.count < ix 0 || input.first < ix 1 ||
        input.substring.ncodeunits - input.first + ix 1 < input.count then
      .error (.jl .boundsError)
    else .ok ⟨input.substring.string,
      input.first + input.substring.offset - ix 1, input.count⟩

theorem rawNested_proven : RawNestedProperty := by unfold RawNestedProperty; intros; rfl

def TypedWholeProperty : Prop := ∀ (S : Type) (s : S) ncodeunits count,
  ncodeunits s = .ok count → typedWhole s ncodeunits = .ok ⟨s, ix 0, count⟩
theorem typedWhole_proven : TypedWholeProperty := by
  unfold TypedWholeProperty
  intros
  simp_all [typedWhole, bind, Except.bind, pure, Except.pure]
def CtorIntProperty : Prop := ∀ (S : Type) (input : TypedCtorInput S),
  ctorInt input = typedCtor input
theorem ctorInt_proven : CtorIntProperty := by unfold CtorIntProperty; intros; rfl

def CtorIntegerProperty : Prop := ∀ (S I J : Type) (s : S)
    (first : IntegerInput I) (last : IntegerInput J) ctor i j,
  first.toInt = .ok i → last.toInt = .ok j →
  ctorInteger s first last ctor = ctor s i j
theorem ctorInteger_proven : CtorIntegerProperty := by
  unfold CtorIntegerProperty
  intros
  simp_all [ctorInteger, bind, Except.bind, pure, Except.pure]

def CtorRangeProperty : Prop := ∀ (S R I : Type) (s : S) (range : UnitRangeInput R I)
    ctor first last,
  range.first range.value = .ok first → range.last range.value = .ok last →
  ctorRange s range ctor = ctor s first last
theorem ctorRange_proven : CtorRangeProperty := by
  unfold CtorRangeProperty
  intros
  simp_all [ctorRange, bind, Except.bind, pure, Except.pure]

def NestedCtorProperty : Prop := ∀ (S : Type) (input : NestedCtorInput S),
  input.first ≤ input.last → input.checkbounds input.substring input.first input.last = .ok () →
  nestedCtor input = input.parentCtor input.substring.string
    (input.substring.offset + input.first) (input.substring.offset + input.last)
theorem nestedCtor_proven : NestedCtorProperty := by
  unfold NestedCtorProperty
  intros
  simp_all [nestedCtor, bind, Except.bind, pure, Except.pure]

def WholeAbstractProperty : Prop := ∀ (S : Type) (s : S) ncodeunits rawUnchecked count,
  ncodeunits s = .ok count →
  wholeAbstract s ncodeunits rawUnchecked = rawUnchecked s (ix 1) count
theorem wholeAbstract_proven : WholeAbstractProperty := by
  unfold WholeAbstractProperty
  intros
  simp_all [wholeAbstract, bind, Except.bind, pure, Except.pure]
def WholeIdentityProperty : Prop := ∀ (S : Type) (s : Sub S), wholeIdentity s = s
theorem wholeIdentity_proven : WholeIdentityProperty := by unfold WholeIdentityProperty; intros; rfl
def ViewRangeProperty : Prop := ∀ (S R V : Type) (s : S) range ctor,
  viewRange s range (ctor : S → R → SJl V) = ctor s range
theorem viewRange_proven : ViewRangeProperty := by unfold ViewRangeProperty; intros; rfl
def MaybeviewRangeProperty : Prop := ∀ (S R V : Type) (s : S) range view,
  maybeviewRange s range (view : S → R → SJl V) = view s range
theorem maybeviewRange_proven : MaybeviewRangeProperty := by unfold MaybeviewRangeProperty; intros; rfl
def MaybeviewArgsProperty : Prop := ∀ (S Args V : Type) (s : S) args getindex,
  maybeviewArgs s args (getindex : S → Args → SJl V) = getindex s args
theorem maybeviewArgs_proven : MaybeviewArgsProperty := by unfold MaybeviewArgsProperty; intros; rfl

def ConvertSubProperty : Prop := ∀ (S T : Type) (input : ConvertInput S T) parent substring,
  input.convertParent input.source = .ok parent → input.substring parent = .ok substring →
  convertSub input = input.typeAssert substring
theorem convertSub_proven : ConvertSubProperty := by
  unfold ConvertSubProperty
  intros
  simp_all [convertSub, bind, Except.bind, pure, Except.pure]
def ConvertIdentityProperty : Prop := ∀ (S : Type) (s : Sub S), convertIdentity s = s
theorem convertIdentity_proven : ConvertIdentityProperty := by unfold ConvertIdentityProperty; intros; rfl

def ToStringProperty : Prop := ∀ (P : Type) (input : CopyInput P) pointer,
  input.pointer input.parent (input.offset + ix 1) = .ok pointer →
  toString input = input.unsafeString pointer input.count
theorem toString_proven : ToStringProperty := by
  unfold ToStringProperty
  intros
  simp_all [toString, bind, Except.bind, pure, Except.pure]
def NcodeunitsProperty : Prop := ∀ (S : Type) (s : Sub S), ncodeunits s = s.ncodeunits
theorem ncodeunits_proven : NcodeunitsProperty := by unfold NcodeunitsProperty; intros; rfl
def CodeunitTypeProperty : Prop := ∀ (S T : Type) (s : Sub S) codeunit,
  codeunitType s (codeunit : S → SJl T) = codeunit s.string
theorem codeunitType_proven : CodeunitTypeProperty := by unfold CodeunitTypeProperty; intros; rfl
def LengthSubProperty : Prop := ∀ (S : Type) (s : Sub S) length,
  lengthSub s length = length s.string (s.offset + ix 1) (s.offset + s.ncodeunits)
theorem lengthSub_proven : LengthSubProperty := by unfold LengthSubProperty; intros; rfl

def CodeunitAtProperty : Prop := ∀ (S I T : Type) (s : Sub S) (index : I)
    (checkbounds : Sub S → I → SJl Unit) (add : JInt64 → I → SJl JInt64)
    (codeunit : S → JInt64 → SJl T) parentIndex,
  checkbounds s index = .ok () → add s.offset index = .ok parentIndex →
  codeunitAt s index checkbounds add codeunit = codeunit s.string parentIndex
theorem codeunitAt_proven : CodeunitAtProperty := by
  unfold CodeunitAtProperty
  intros
  simp_all [codeunitAt, bind, Except.bind, pure, Except.pure]

def GetindexAtProperty : Prop := ∀ (S I T : Type) (s : Sub S) (index : I)
    (checkbounds : Sub S → I → SJl Unit) (add : JInt64 → I → SJl JInt64)
    (getindex : S → JInt64 → SJl T) parentIndex,
  checkbounds s index = .ok () → add s.offset index = .ok parentIndex →
  getindexAt s index checkbounds add getindex = getindex s.string parentIndex
theorem getindexAt_proven : GetindexAtProperty := by
  unfold GetindexAtProperty
  intros
  simp_all [getindexAt, bind, Except.bind, pure, Except.pure]

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
def ThisindStringProperty : Prop := ∀ s index,
  thisindString s index = Strings.thisind s.view index
theorem thisindString_proven : ThisindStringProperty := by unfold ThisindStringProperty; intros; rfl
def NextindStringProperty : Prop := ∀ s index,
  nextindString s index = Strings.nextind s.view index
theorem nextindString_proven : NextindStringProperty := by unfold NextindStringProperty; intros; rfl
def LastindexStringProperty : Prop := ∀ s,
  lastindexString s = Strings.thisind s.view s.ncu
theorem lastindexString_proven : LastindexStringProperty := by
  unfold LastindexStringProperty lastindexString thisindString
  intros
  rfl
def ParentProperty : Prop := ∀ (S : Type) (s : Sub S), parent s = s.string
theorem parent_proven : ParentProperty := by unfold ParentProperty; intros; rfl
def ParentindicesProperty : Prop := ∀ (S : Type) (s : Sub S) thisind last,
  thisind s.string (s.offset + s.ncodeunits) = .ok last →
  parentindices s thisind = .ok (s.offset + ix 1, last)
theorem parentindices_proven : ParentindicesProperty := by
  unfold ParentindicesProperty
  intros
  simp_all [parentindices, bind, Except.bind, pure, Except.pure]
def EqStringSubProperty : Prop := ∀ a b memcmp,
  eqStringSub a b memcmp = (stringSize a == stringSize b && memcmp a b == 0)
theorem eqStringSub_proven : EqStringSubProperty := by unfold EqStringSubProperty; intros; rfl
def CmpSubProperty : Prop := ∀ a b memcmp,
  cmpSub a b memcmp =
    let comparison := memcmp a b
    if comparison < 0 then -1 else if comparison > 0 then 1
    else if a.ncu < b.ncu then -1 else if b.ncu < a.ncu then 1 else 0
theorem cmpSub_proven : CmpSubProperty := by unfold CmpSubProperty; intros; rfl
def PointerAtProperty : Prop := ∀ (I : Type) base s (index : IntegerInput I) subtractOne delta,
  subtractOne index.value = .ok delta →
  pointerAt base s index subtractOne = .ok (base + s.offset.val.toNat + delta.toNat)
theorem pointerAt_proven : PointerAtProperty := by
  unfold PointerAtProperty
  intros
  simp_all [pointerAt, bind, Except.bind, pure, Except.pure]

def HashSubProperty : Prop := ∀ input pointer size hash,
  input.pointer input.substring = .ok pointer → input.sizeof input.substring = .ok size →
  input.hashBytes pointer size input.seed input.secret = .ok hash →
  hashSub input = .ok (input.toUInt hash)
theorem hashSub_proven : HashSubProperty := by
  unfold HashSubProperty
  intros
  simp_all [hashSub, bind, Except.bind, pure, Except.pure]
def IsannotatedSubProperty : Prop := ∀ kind,
  isannotatedSub kind = (kind = .annotatedString || kind = .annotatedChar)
theorem isannotatedSub_proven : IsannotatedSubProperty := by intro kind; cases kind <;> decide

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

def WriteCharProperty : Prop := ∀ (Out I : Type) (input : CharWriterInput Out I) output,
  input.writable input.output input.offset (ncodeunitsChar input.character) →
  writeCharLoop input (writeCharStores input) 0 input.output = .ok output →
  writeChar input = .ok (output, ncodeunitsChar input.character)
theorem writeChar_proven : WriteCharProperty := by
  unfold WriteCharProperty
  intros
  simp_all [writeChar, bind, Except.bind, pure, Except.pure]
def StringRestrictedProperty : Prop := ∀ values build,
  stringRestricted values build = build values
theorem stringRestricted_proven : StringRestrictedProperty := by unfold StringRestrictedProperty; intros; rfl

def BuildStringProperty : Prop := ∀ (Out : Type) values allocate write output,
  allocate (sumSizes values) = .ok output →
  buildString values (allocate : JInt64 → SJl Out) write = writeValues write values output (ix 1)
theorem buildString_proven : BuildStringProperty := by
  unfold BuildStringProperty
  intros
  simp_all [buildString, bind, Except.bind, pure, Except.pure]
def RepeatBitIntegerProperty : Prop := ∀ (I : Type) s count invokeInteger,
  repeatBitInteger s count (invokeInteger : JStr → I → SJl JStr) = invokeInteger s count
theorem repeatBitInteger_proven : RepeatBitIntegerProperty := by unfold RepeatBitIntegerProperty; intros; rfl

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
def RangeGetindexProperty : Prop := ∀ (S R I V : Type) s (range : UnitRangeInput R I) substring,
  rangeGetindex s range (substring : S → UnitRangeInput R I → SJl V) = substring s range
theorem rangeGetindex_proven : RangeGetindexProperty := by unfold RangeGetindexProperty; intros; rfl

end JuliaLean.StringsCovA.SubstringRebuilt

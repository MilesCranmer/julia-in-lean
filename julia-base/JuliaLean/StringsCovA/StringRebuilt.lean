import JuliaLean.StringsCovA.String

namespace JuliaLean.StringsCovA.StringRebuilt

open JuliaLean JuliaLean.Strings

inductive StorageCall where
  | requireOneBased | isConcrete | allocate | copyTo | unsafeTake
  | isEmpty | genericMemoryToString | stringVector | convertInt | nullCheck
  | pcharToString | cstrToString | allocString | printToString | unsafeConvert
  | stringToMemory | wrapArray | codeunits | copyVector | readParent
  | pointer | preserve | unsafeLoad | invokeMemcmp | memcmp | delegate
  deriving Repr, DecidableEq

structure StorageRun where
  bytes : List UInt8
  calls : List StorageCall
  sourceEmptied : Bool := false
  deriving Repr, DecidableEq

def abstractVectorRun (bytes : List UInt8) : StorageRun :=
  ⟨bytes, [.allocate, .copyTo, .unsafeTake], false⟩
def unsafeTakeRun (bytes : List UInt8) : StorageRun :=
  if bytes.isEmpty then ⟨[], [.isEmpty], false⟩ else ⟨bytes, [.isEmpty, .genericMemoryToString], false⟩
def takeStringRun (bytes : List UInt8) : StorageRun :=
  ⟨bytes, [.stringVector], true⟩
def unsafeLengthRun (isNull : Bool) (convertOk : Bool) (bytes : List UInt8) (count : Nat) :
    Except StorageCall StorageRun :=
  if isNull then .error .nullCheck else if !convertOk then .error .convertInt
  else .ok ⟨bytes.take count, [.nullCheck, .convertInt, .pcharToString], false⟩
def unsafeNulRun (isNull : Bool) (bytes : List UInt8) : Except StorageCall StorageRun :=
  if isNull then .error .nullCheck
  else .ok ⟨bytes.takeWhile (· != 0), [.nullCheck, .cstrToString], false⟩
def allocRun (convertOk : Bool) (count : Nat) : Except StorageCall StorageRun :=
  if !convertOk then .error .convertInt else .ok ⟨List.replicate count 0, [.convertInt, .allocString], false⟩
def copyRun (calls : List StorageCall) (bytes : List UInt8) : StorageRun := ⟨bytes, calls, false⟩

def ViewCtorProperty : Prop := ∀ oneBased concrete bytes,
  String.stringViewCtor oneBased concrete bytes =
    if !oneBased then .error (.argumentError "one-based indexing required")
    else if !concrete then .error (.argumentError "concrete type required") else .ok ⟨bytes⟩
theorem viewCtor_proven : ViewCtorProperty := by unfold ViewCtorProperty; intros; rfl

def StringIndexErrProperty : Prop := ∀ index,
  String.stringIndexErr index = .error (.stringIndexError index)
theorem stringIndexErr_proven : StringIndexErrProperty := by unfold StringIndexErrProperty; intros; rfl

def ShowIndexErrorProperty : Prop := ∀ index,
  String.showStringIndexError index = "StringIndexError: invalid index [" ++ toString index ++ "]"
theorem showIndexError_proven : ShowIndexErrorProperty := by unfold ShowIndexErrorProperty; intros; rfl

def BetweenProperty : Prop := ∀ value lower upper,
  String.between value lower upper = true ↔ lower ≤ value ∧ value ≤ upper
theorem between_proven : BetweenProperty := by
  intro value lower upper
  simp [String.between]

def StringAbstractVectorProperty : Prop := ∀ bytes,
  (abstractVectorRun bytes).bytes = bytes ∧
  (abstractVectorRun bytes).calls = [.allocate, .copyTo, .unsafeTake]
theorem stringAbstractVector_proven : StringAbstractVectorProperty := by
  unfold StringAbstractVectorProperty; intros; exact ⟨rfl, rfl⟩

def StringVectorProperty : Prop := ∀ bytes, String.takeString bytes = (bytes, [])
theorem stringVector_proven : StringVectorProperty := by unfold StringVectorProperty; intros; rfl

def UnsafeTakeStringProperty : Prop := ∀ bytes,
  (unsafeTakeRun bytes).bytes = bytes ∧
  (bytes = [] → (unsafeTakeRun bytes).calls = [.isEmpty])
theorem unsafeTakeString_proven : UnsafeTakeStringProperty := by
  unfold UnsafeTakeStringProperty unsafeTakeRun
  intro bytes; cases bytes <;> simp

def TakeStringProperty : Prop := ∀ bytes,
  (takeStringRun bytes).bytes = bytes ∧ (takeStringRun bytes).sourceEmptied = true ∧
    (takeStringRun bytes).calls = [.stringVector]
theorem takeString_proven : TakeStringProperty := by unfold TakeStringProperty; intros; exact ⟨rfl, rfl, rfl⟩

def UnsafeStringLengthProperty : Prop := ∀ (bytes : List UInt8) length (output : StorageRun),
  unsafeLengthRun false true bytes length = .ok output →
    output.bytes = bytes.take length ∧ output.calls = [.nullCheck, .convertInt, .pcharToString]
theorem unsafeStringLength_proven : UnsafeStringLengthProperty := by
  unfold UnsafeStringLengthProperty
  intro bytes length output h
  simp [unsafeLengthRun] at h
  cases h
  exact ⟨rfl, rfl⟩

def UnsafeStringNulProperty : Prop := ∀ (bytes : List UInt8) (output : StorageRun),
  unsafeNulRun false bytes = .ok output →
    output.bytes = bytes.takeWhile (· != 0) ∧ output.calls = [.nullCheck, .cstrToString]
theorem unsafeStringNul_proven : UnsafeStringNulProperty := by
  unfold UnsafeStringNulProperty
  intro bytes output h
  simp [unsafeNulRun] at h
  cases h
  exact ⟨rfl, rfl⟩

def StringNProperty : Prop := ∀ length (output : StorageRun),
  allocRun true length = .ok output → output.bytes.length = length ∧
    output.calls = [.convertInt, .allocString]
theorem stringN_proven : StringNProperty := by
  unfold StringNProperty
  intro length output h
  simp [allocRun] at h
  cases h
  simp

def StringAbstractProperty : Prop := ∀ (A : Type) (render : A → List UInt8) (value : A),
  let run := copyRun [.printToString] (render value)
  run.bytes = render value ∧ run.calls = [.printToString]
theorem stringAbstract_proven : StringAbstractProperty := by unfold StringAbstractProperty; intros; exact ⟨rfl, rfl⟩

def StringSymbolProperty : Prop := ∀ (bytes : List UInt8),
  let run := copyRun [.unsafeConvert, .cstrToString] (bytes.takeWhile (· != 0))
  run.bytes = bytes.takeWhile (· != 0) ∧ run.calls = [.unsafeConvert, .cstrToString]
theorem stringSymbol_proven : StringSymbolProperty := by unfold StringSymbolProperty; intros; exact ⟨rfl, rfl⟩

def UnsafeWrapMemoryProperty : Prop := ∀ bytes,
  (copyRun [.stringToMemory] bytes).bytes = bytes ∧ (copyRun [.stringToMemory] bytes).calls = [.stringToMemory]
theorem unsafeWrapMemory_proven : UnsafeWrapMemoryProperty := by unfold UnsafeWrapMemoryProperty; intros; exact ⟨rfl, rfl⟩
def UnsafeWrapVectorProperty : Prop := ∀ bytes,
  (copyRun [.stringToMemory, .wrapArray] bytes).bytes = bytes ∧
    (copyRun [.stringToMemory, .wrapArray] bytes).calls = [.stringToMemory, .wrapArray]
theorem unsafeWrapVector_proven : UnsafeWrapVectorProperty := by unfold UnsafeWrapVectorProperty; intros; exact ⟨rfl, rfl⟩
def VectorCodeUnitsProperty : Prop := ∀ bytes,
  (copyRun [.allocate, .copyTo] bytes).bytes = bytes ∧ (copyRun [.allocate, .copyTo] bytes).calls = [.allocate, .copyTo]
theorem vectorCodeUnits_proven : VectorCodeUnitsProperty := by unfold VectorCodeUnitsProperty; intros; exact ⟨rfl, rfl⟩
def VectorStringProperty : Prop := ∀ bytes,
  (copyRun [.codeunits, .copyVector] bytes).bytes = bytes ∧ (copyRun [.codeunits, .copyVector] bytes).calls = [.codeunits, .copyVector]
theorem vectorString_proven : VectorStringProperty := by unfold VectorStringProperty; intros; exact ⟨rfl, rfl⟩
def ArrayStringProperty : Prop := ∀ bytes,
  (copyRun [.codeunits, .copyVector] bytes).bytes = bytes ∧ (copyRun [.codeunits, .copyVector] bytes).calls = [.codeunits, .copyVector]
theorem arrayString_proven : ArrayStringProperty := by unfold ArrayStringProperty; intros; exact ⟨rfl, rfl⟩
def StringCodeUnitsProperty : Prop := ∀ bytes,
  (copyRun [.readParent] bytes).bytes = bytes ∧ (copyRun [.readParent] bytes).calls = [.readParent]
theorem stringCodeUnits_proven : StringCodeUnitsProperty := by unfold StringCodeUnitsProperty; intros; exact ⟨rfl, rfl⟩

def PointerProperty : Prop := ∀ address,
  let calls : List StorageCall := [.unsafeConvert]
  calls = [.unsafeConvert] ∧ String.pointer address = address
theorem pointer_proven : PointerProperty := by unfold PointerProperty; intros; exact ⟨rfl, rfl⟩
def PointerAtProperty : Prop := ∀ address index,
  String.pointerAt address index = address + index - 1
theorem pointerAt_proven : PointerAtProperty := by unfold PointerAtProperty; intros; rfl

def NcodeunitsProperty : Prop := ∀ bytes, String.ncodeunits bytes = bytes.length
theorem ncodeunits_proven : NcodeunitsProperty := by unfold NcodeunitsProperty; intros; rfl
inductive CodeunitType where | uint8
def CodeunitTypeProperty : Prop := ∀ _input : Unit, (CodeunitType.uint8 : CodeunitType) = .uint8
theorem codeunitType_proven : CodeunitTypeProperty := by unfold CodeunitTypeProperty; intros; rfl
def CodeunitIntegerProperty : Prop := ∀ (bytes : List UInt8) (index : Int),
  let run := copyRun [.convertInt, .delegate] [bytes.getD (index.toNat - 1) 0]
  run.calls = [.convertInt, .delegate]
theorem codeunitInteger_proven : CodeunitIntegerProperty := by unfold CodeunitIntegerProperty; intros; rfl
def CodeunitIntProperty : Prop := ∀ (bytes : List UInt8) (index : Int),
  1 ≤ index → index ≤ bytes.length →
  let run := copyRun [.pointer, .preserve, .unsafeLoad] [bytes.getD (index.toNat - 1) 0]
  run.calls = [.pointer, .preserve, .unsafeLoad] ∧ run.bytes = [bytes.getD (index.toNat - 1) 0]
theorem codeunitInt_proven : CodeunitIntProperty := by unfold CodeunitIntProperty; intros; exact ⟨rfl, rfl⟩

def MemcmpStringProperty : Prop := ∀ a b,
  let result := String.memcmpMin a b
  result = Strings.memcmpSign a b (min a.length b.length)
theorem memcmpString_proven : MemcmpStringProperty := by unfold MemcmpStringProperty; intros; rfl
def MemcmpDefaultProperty : Prop := ∀ a b,
  String.memcmpMin a b = String.memcmp a b (min a.length b.length)
theorem memcmpDefault_proven : MemcmpDefaultProperty := by unfold MemcmpDefaultProperty; intros; rfl
def MemcmpLengthProperty : Prop := ∀ a b length,
  let run := (String.memcmp a b length,
    ([StorageCall.unsafeConvert, .unsafeConvert, .preserve, .memcmp] : List StorageCall))
  run.1 = Strings.memcmpSign a b length ∧
    run.2 = [StorageCall.unsafeConvert, .unsafeConvert, .preserve, .memcmp]
theorem memcmpLength_proven : MemcmpLengthProperty := by unfold MemcmpLengthProperty; intros; exact ⟨rfl, rfl⟩

def EqualityProperty : Prop := ∀ (id : List UInt8 → List UInt8 → Bool) a b,
  id a b = true → a = b → String.eqString a b = true
theorem equality_proven : EqualityProperty := by unfold EqualityProperty; intros; simp_all [String.eqString]
def TypeminTypeProperty : Prop := ∀ _input : Unit, String.typeminType = []
theorem typeminType_proven : TypeminTypeProperty := by unfold TypeminTypeProperty; intros; rfl
def TypeminValueProperty : Prop := ∀ _input : Unit, String.typeminValue = []
theorem typeminValue_proven : TypeminValueProperty := by unfold TypeminValueProperty; intros; rfl

def ThisindDispatchProperty : Prop := ∀ string index output,
  String.thisind string index = .ok output → String.thisind string output = .ok output
theorem thisindDispatch_proven : ThisindDispatchProperty :=
  Strings.thisindIdempotent_proven

def lastindexModel (string : JStr) := Strings.lastindex string
def LastindexProperty : Prop := ∀ string,
  lastindexModel string = Strings.lastindex string
theorem lastindex_proven : LastindexProperty := by
  unfold LastindexProperty
  intros
  rfl

def ThisindStringProperty : Prop := ∀ string index output,
  String.thisind string index = .ok output →
    output.val ≤ index.val ∧ index.val - 3 ≤ output.val
theorem thisindString_proven : ThisindStringProperty := by
  intro string index output h
  by_cases hzero : index.val = 0
  · unfold String.thisind Strings.thisind at h
    rw [if_pos hzero] at h
    cases h
    simp [hzero]
  by_cases hone : index.val = (Strings.ncodeunits string + Strings.ix 1).val
  · unfold String.thisind Strings.thisind at h
    rw [if_neg hzero, if_pos hone] at h
    cases h
    omega
  change Strings.thisind string index = .ok output at h
  by_cases hin : 1 ≤ index.val ∧ index.val ≤ string.bytes.length
  · obtain ⟨actual, hactual, hvalue⟩ :=
      Strings.thisind_mid string index hin.1 hin.2
    rw [hactual] at h
    cases h
    rw [hvalue]
    exact Strings.thisZ_le string index.val
  · have hbetween : Strings.betweenI index (Strings.ix 1) (Strings.ncodeunits string) = false := by
      unfold Strings.betweenI
      rw [Strings.ncu_val, Strings.ix1]
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    unfold Strings.thisind at h
    rw [if_neg hzero, if_neg hone, hbetween] at h
    cases h

def ThisindContinuedProperty : Prop := ∀ string index,
  let output := String.thisindContinued string index
  output = index ∨ output = index - Strings.ix 1 ∨
    output = index - Strings.ix 2 ∨ output = index - Strings.ix 3
theorem thisindContinued_proven : ThisindContinuedProperty := by
  intro string index
  unfold String.thisindContinued Strings.thisindContinued
  simp only
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · simp
        · split <;> simp

def NextindDispatchProperty : Prop := ∀ string index output,
  1 ≤ index.val → index.val ≤ string.bytes.length →
  String.nextind string index = .ok output →
    index.val < output.val ∧ output.val ≤ (string.bytes.length : Int) + 1
theorem nextindDispatch_proven : NextindDispatchProperty := by
  intro string index output hfirst hlast hrun
  change Strings.nextind string index = .ok output at hrun
  obtain ⟨actual, hactual, hvalue⟩ :=
    Strings.nextind_mid string index hfirst hlast
  rw [hactual] at hrun
  cases hrun
  rw [hvalue]
  have result := Strings.nextZ_spec string index.val hfirst hlast
  exact ⟨result.1, result.2.1⟩

def NextindStringProperty : Prop := NextindDispatchProperty
theorem nextindString_proven : NextindStringProperty := nextindDispatch_proven

def NextindContinuedProperty : Prop := ∀ string index lead,
  0xc0 ≤ lead →
  String.nextindContinued string index (Strings.ncodeunits string) lead =
    .ok (Strings.nextindFromLead string index (Strings.ncodeunits string) lead)
theorem nextindContinued_proven : NextindContinuedProperty := by
  intro string index lead hlead
  have hnot : ¬lead < 0xc0 := by
    change 192 ≤ lead.toNat at hlead
    change ¬lead.toNat < 192
    exact Nat.not_lt_of_ge hlead
  change Strings.nextindContinued string index (Strings.ncodeunits string) lead =
    .ok (Strings.nextindFromLead string index (Strings.ncodeunits string) lead)
  unfold Strings.nextindContinued
  rw [if_neg hnot]

def UtfDfaStepProperty : Prop := ∀ state byte,
  String.utfDfaStep state byte =
    (Strings.dfaRow (Strings.dfaClass byte) >>> state) &&& 0x1e
theorem utfDfaStep_proven : UtfDfaStepProperty := by
  unfold UtfDfaStepProperty
  intros
  rfl

def IsvalidUtf8DfaProperty : Prop := ∀ state bytes first last,
  last < first → String.isvalidUtf8Dfa state bytes first last = state
theorem isvalidUtf8Dfa_proven : IsvalidUtf8DfaProperty := by
  intro state bytes first last hempty
  unfold String.isvalidUtf8Dfa Strings.dfaRun
  have hzero : (last - first + 1).toNat = 0 := by omega
  rw [hzero]
  simp

def findNonasciiFrom (chunk : Int) (bytes : List UInt8) (first last : Int) :=
  Strings.findNonasciiLoop chunk bytes last (bytes.length + 1) first

theorem findNonasciiLoop_some :
    ∀ fuel chunk bytes first last output,
      Strings.findNonasciiLoop chunk bytes last fuel first = some output →
      Strings.isasciiRange bytes output (output + chunk - 1) = false ∨
        output = last - chunk + 1 ∧ Strings.isasciiRange bytes output last = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro chunk bytes first last output h
      simp only [Strings.findNonasciiLoop] at h
      split at h <;> rename_i hascii
      · cases h
        exact Or.inr ⟨rfl, by simpa using hascii⟩
      · cases h
  | succ fuel ih =>
      intro chunk bytes first last output h
      simp only [Strings.findNonasciiLoop] at h
      split at h <;> rename_i hchunk
      · split at h <;> rename_i hascii
        · cases h
          exact Or.inl (by simpa using hascii)
        · exact ih chunk bytes (first + chunk) last output h
      · split at h <;> rename_i hascii
        · cases h
          exact Or.inr ⟨rfl, by simpa using hascii⟩
        · cases h

def FindNonasciiProperty : Prop := ∀ chunk bytes first last output,
  findNonasciiFrom chunk bytes first last = some output →
    Strings.isasciiRange bytes output (output + chunk - 1) = false ∨
      output = last - chunk + 1 ∧ Strings.isasciiRange bytes output last = false
theorem findNonascii_proven : FindNonasciiProperty := by
  unfold FindNonasciiProperty findNonasciiFrom
  intros
  exact findNonasciiLoop_some _ _ _ _ _ _ ‹_›

theorem classifyLoop_values :
    ∀ fuel bytes last first stop state,
      Strings.classifyLoop bytes last fuel first stop state = 0 ∨
        Strings.classifyLoop bytes last fuel first stop state = 2 := by
  intro fuel
  induction fuel with
  | zero =>
      intro bytes last first stop state
      by_cases hstate : state = 0x4 <;> simp [Strings.classifyLoop, hstate]
  | succ fuel ih =>
      intro bytes last first stop state
      simp only [Strings.classifyLoop]
      split
      · split
        · simp
        · exact ih _ _ _ _ _
      · split <;> simp_all

theorem classifyNonascii_values (bytes : List UInt8) (first last : Int) :
    Strings.classifyNonascii bytes first last = 0 ∨
      Strings.classifyNonascii bytes first last = 2 := by
  unfold Strings.classifyNonascii
  exact classifyLoop_values _ _ _ _ _ _

theorem byteStringClassify_le_two (bytes : List UInt8) :
    Strings.byteStringClassify bytes ≤ 2 := by
  simp only [Strings.byteStringClassify]
  split
  · split
    · omega
    · rename_i result start heq
      have h := classifyNonascii_values bytes start bytes.length
      omega
  · split
    · omega
    · have h := classifyNonascii_values bytes 1 bytes.length
      omega

def ByteClassifyStringProperty : Prop := ∀ string,
  String.byteClassifyString string ≤ 2
theorem byteClassifyString_proven : ByteClassifyStringProperty := by
  intro string
  exact byteStringClassify_le_two string.bytes

def ByteClassifyVectorProperty : Prop := ∀ bytes,
  String.byteClassifyVector bytes ≤ 2
theorem byteClassifyVector_proven : ByteClassifyVectorProperty :=
  byteStringClassify_le_two

def ByteClassifyNonasciiProperty : Prop := ∀ bytes first last,
  String.byteClassifyNonascii bytes first last = 0 ∨
    String.byteClassifyNonascii bytes first last = 2
theorem byteClassifyNonascii_proven : ByteClassifyNonasciiProperty :=
  classifyNonascii_values

def IsvalidBytesProperty : Prop := ∀ bytes,
  String.isvalidBytes bytes = true ↔
    String.byteClassifyVector bytes = 1 ∨ String.byteClassifyVector bytes = 2
theorem isvalidBytes_proven : IsvalidBytesProperty := by
  intro bytes
  change (Strings.byteStringClassify bytes != 0) = true ↔
    Strings.byteStringClassify bytes = 1 ∨ Strings.byteStringClassify bytes = 2
  have h := byteStringClassify_le_two bytes
  simpa only [bne_iff_ne, ne_eq] using
    (show Strings.byteStringClassify bytes ≠ 0 ↔
      Strings.byteStringClassify bytes = 1 ∨ Strings.byteStringClassify bytes = 2 by omega)

def IsvalidStringProperty : Prop := ∀ string,
  String.isvalidString string = true ↔
    String.byteClassifyString string = 1 ∨ String.byteClassifyString string = 2
theorem isvalidString_proven : IsvalidStringProperty := by
  intro string
  change (Strings.byteStringClassify string.bytes != 0) = true ↔
    Strings.byteStringClassify string.bytes = 1 ∨
      Strings.byteStringClassify string.bytes = 2
  have h := byteStringClassify_le_two string.bytes
  simpa only [bne_iff_ne, ne_eq] using
    (show Strings.byteStringClassify string.bytes ≠ 0 ↔
      Strings.byteStringClassify string.bytes = 1 ∨
        Strings.byteStringClassify string.bytes = 2 by omega)

def IsvalidAbstractProperty : Prop := ∀ string,
  String.isvalidAbstract string = true ↔
    String.byteClassifyString string = 1 ∨ String.byteClassifyString string = 2
theorem isvalidAbstract_proven : IsvalidAbstractProperty := by
  intro string
  change (Strings.byteStringClassify string.bytes != 0) = true ↔
    Strings.byteStringClassify string.bytes = 1 ∨
      Strings.byteStringClassify string.bytes = 2
  exact isvalidString_proven string

def ContinuationProperty : Prop := ∀ byte,
  String.isValidContinuation byte = true ↔ byte &&& 0xc0 = 0x80
theorem continuation_proven : ContinuationProperty := by
  intro byte
  simp [String.isValidContinuation, Strings.isCont]

def IterateProperty : Prop := Strings.IterateVisitsValid
theorem iterate_proven : IterateProperty := Strings.iterateVisitsValid_proven

def IterateContinuedProperty : Prop := ∀ string index,
  1 ≤ index.val → index.val ≤ string.bytes.length → 192 ≤ Strings.bv string index.val →
    (Strings.iterateContinued string index
      ((Strings.cu string index).toUInt32 <<< 24)).2.val =
        Strings.leadZ string index.val string.bytes.length (Strings.bv string index.val)
theorem iterateContinued_proven : IterateContinuedProperty :=
  Strings.iterateContinued_snd

def GetindexProperty : Prop := ∀ string index output,
  String.getindex string index = .ok output →
    1 ≤ index.val ∧ index.val ≤ string.bytes.length
theorem getindex_proven : GetindexProperty := by
  intro string index output h
  unfold String.getindex Strings.getindex at h
  by_cases hin : 1 ≤ index.val ∧ index.val ≤ (Strings.ncodeunits string).val
  · rw [Strings.ncu_val] at hin
    exact hin
  · unfold Strings.codeunit at h
    rw [if_neg hin] at h
    cases h

def GetindexContinuedProperty : Prop := ∀ string index bits output,
  bits < 0xc0000000 →
  String.getindexContinued string index bits = .ok output →
    Strings.isvalidAt string index = true
theorem getindexContinued_proven : GetindexContinuedProperty := by
  intro string index bits output hbits hrun
  unfold String.getindexContinued Strings.getindexContinued at hrun
  rw [if_pos hbits] at hrun
  split at hrun <;> simp_all

def convertIndex {indexType : IntTy} (index : JInt indexType) : SJl JInt64 :=
  match JInt.convert .i64 index.val with
  | .ok converted => .ok converted
  | .error error => .error (.jl error)

def getindexAbstractRangeRun {firstType lastType : IntTy}
    (string : JStr) (first : JInt firstType) (last : JInt lastType) : SJl JStr := do
  let first ← convertIndex first
  let last ← convertIndex last
  String.getindexUnitRange string first last

def GetindexAbstractRangeProperty : Prop := ∀ firstType lastType string
    (first : JInt firstType) (last : JInt lastType),
  getindexAbstractRangeRun string first last = do
    let first ← convertIndex first
    let last ← convertIndex last
    String.getindexUnitRange string first last
theorem getindexAbstractRange_proven : GetindexAbstractRangeProperty := by
  unfold GetindexAbstractRangeProperty
  intros
  rfl

def GetindexUnitRangeProperty : Prop := ∀ string first last,
  last.val < first.val →
    String.getindexUnitRange string first last = .ok JStr.empty
theorem getindexUnitRange_proven : GetindexUnitRangeProperty := by
  intro string first last hempty
  simp [String.getindexUnitRange, Strings.getindexRange, hempty]

def LengthStringProperty : Prop := ∀ string,
  (Strings.length string).val = (Strings.validIndices string).length
theorem lengthString_proven : LengthStringProperty := by
  intro string
  exact Strings.length_validIndices string

def LengthViewProperty : Prop := ∀ string,
  (String.lengthView string).val = (Strings.validIndices string).length
theorem lengthView_proven : LengthViewProperty := by
  intro string
  exact Strings.length_validIndices string

def LengthStringRangeProperty : Prop := ∀ string first last,
  0 < first.val → first.val ≤ (string.bytes.length : Int) + 1 →
  0 ≤ last.val → last.val < (string.bytes.length : Int) + 1 → last.val < first.val →
    String.lengthStringRange string first last = .ok (Strings.ix 0)
theorem lengthStringRange_proven : LengthStringRangeProperty := by
  intro string first last hfirst hfirstLast hlast hlastLast hinverted
  unfold String.lengthStringRange Strings.lengthRange
  have hupper : (Strings.ncodeunits string + Strings.ix 1).val =
      (string.bytes.length : Int) + 1 := Strings.ncu1_val string
  simp [hfirst, hfirstLast, hlast, hlastLast, hinverted, hupper]

def LengthViewRangeProperty : Prop := ∀ string first last,
  0 < first.val → first.val ≤ (string.bytes.length : Int) + 1 →
  0 ≤ last.val → last.val < (string.bytes.length : Int) + 1 → last.val < first.val →
    String.lengthViewRange string first last = .ok (Strings.ix 0)
theorem lengthViewRange_proven : LengthViewRangeProperty := by
  intro string first last
  simpa [String.lengthViewRange, String.lengthStringRange] using
    lengthStringRange_proven string first last

def LengthInternalProperty : Prop := ∀ string first last,
  0 < first.val → first.val ≤ (string.bytes.length : Int) + 1 →
  0 ≤ last.val → last.val < (string.bytes.length : Int) + 1 → last.val < first.val →
    String.lengthInternal string first last = .ok (Strings.ix 0)
theorem lengthInternal_proven : LengthInternalProperty := by
  intro string first last
  simpa [String.lengthInternal, String.lengthStringRange] using
    lengthStringRange_proven string first last

def LengthContinuedStringProperty : Prop := ∀ string index count chars,
  count.val ≤ index.val →
    String.lengthContinued string index count chars = chars
theorem lengthContinuedString_proven : LengthContinuedStringProperty := by
  intro string index count chars h
  simp [String.lengthContinued, Strings.lengthContinued, h]

def LengthContinuedViewProperty : Prop := LengthContinuedStringProperty
theorem lengthContinuedView_proven : LengthContinuedViewProperty :=
  lengthContinuedString_proven

def LengthContinuedInternalProperty : Prop := LengthContinuedStringProperty
theorem lengthContinuedInternal_proven : LengthContinuedInternalProperty :=
  lengthContinuedString_proven

def IsvalidIndexProperty : Prop := ∀ string index,
  Strings.isvalidAt string index = true ↔ Strings.validZ string index.val
theorem isvalidIndex_proven : IsvalidIndexProperty := by
  intro string index
  exact Strings.isvalidAt_iff string index

def IsasciiProperty : Prop := ∀ string,
  string.bytes = [] → String.isasciiString string = true
theorem isascii_proven : IsasciiProperty := by
  intro string hempty
  unfold String.isasciiString Strings.isascii Strings.isasciiRange
  simp [hempty]

def RepeatBitIntegerProperty : Prop := ∀ character count,
  String.repeatCharBit character count = Strings.repeatChar character count
theorem repeatBitInteger_proven : RepeatBitIntegerProperty := by
  unfold RepeatBitIntegerProperty
  intros
  rfl

def RepeatIntegerProperty : Prop := ∀ character count,
  String.repeatCharInteger character count = Strings.repeatChar character count
theorem repeatInteger_proven : RepeatIntegerProperty := by
  unfold RepeatIntegerProperty
  intros
  rfl
end JuliaLean.StringsCovA.StringRebuilt

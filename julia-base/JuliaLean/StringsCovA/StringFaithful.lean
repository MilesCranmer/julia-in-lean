import JuliaLean.StringsCovA.String

namespace JuliaLean.StringsCovA.StringFaithful

open JuliaLean JuliaLean.Strings

def ViewCtorProperty : Prop := ∀ oneBased concrete bytes, String.stringViewCtor oneBased concrete bytes =
  if !oneBased then .error (.argumentError "one-based indexing required")
  else if !concrete then .error (.argumentError "concrete type required") else .ok ⟨bytes⟩
theorem viewCtor_proven : ViewCtorProperty := by unfold ViewCtorProperty; intros; rfl
def IndexErrorProperty : Prop :=
  (∀ i, String.stringIndexErr i = .error (.stringIndexError i)) ∧
  (∀ i, String.showStringIndexError i = "StringIndexError: invalid index [" ++ toString i ++ "]")
theorem indexError_proven : IndexErrorProperty := by constructor <;> intros <;> rfl
def BetweenProperty : Prop := ∀ b lo hi, String.between b lo hi = (decide (lo ≤ b) && decide (b ≤ hi))
theorem between_proven : BetweenProperty := by unfold BetweenProperty; intros; rfl

def ConstructorsProperty : Prop :=
  (∀ v, String.stringAbstractVector v = v) ∧
  (∀ m, String.unsafeTakeString m = m) ∧
  (∀ v, String.takeString v = (v, [])) ∧
  (∀ m n, String.unsafeStringLength m n = m.take n) ∧
  (∀ m, String.unsafeStringNul m = m.takeWhile (· != 0)) ∧
  (∀ n, String.stringN n = List.replicate n 0) ∧
  (∀ (α : Type) render (s : α), String.stringAbstract render s = render s) ∧
  (∀ m, String.stringSymbol m = String.unsafeStringNul m)
theorem constructors_proven : ConstructorsProperty := by
  unfold ConstructorsProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def StorageConversionProperty : Prop :=
  (∀ s, String.unsafeWrapMemory s = s) ∧ (∀ s, String.unsafeWrapVector s = s) ∧
  (∀ s, String.vectorCodeUnits s = s) ∧ (∀ s, String.vectorString s = s) ∧
  (∀ s, String.arrayString s = s) ∧ (∀ s, String.stringCodeUnits s = s)
theorem storageConversion_proven : StorageConversionProperty := by
  unfold StorageConversionProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def PointerProperty : Prop :=
  (∀ address, String.pointer address = address) ∧
  (∀ address i, String.pointerAt address i = address + i - 1)
theorem pointer_proven : PointerProperty := by constructor <;> intros <;> rfl
def CodeunitProperty : Prop :=
  (∀ s, String.ncodeunits s = s.length) ∧
  (∀ _u : Unit, String.codeunitType = 8) ∧
  (∀ s i, String.codeunit s i =
    if 1 ≤ i ∧ i ≤ s.length then .ok (s.getD (i.toNat - 1) 0) else .error .boundsError)
theorem codeunit_proven : CodeunitProperty := by
  unfold CodeunitProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def MemcmpProperty : Prop :=
  (∀ a b, String.memcmpMin a b = String.memcmp a b (min a.length b.length)) ∧
  (∀ a b n, String.memcmp a b n = Strings.memcmpSign a b n)
theorem memcmp_proven : MemcmpProperty := by constructor <;> intros <;> rfl
def EqProperty : Prop := ∀ a b, String.eqString a b = (a == b)
theorem eq_proven : EqProperty := by unfold EqProperty; intros; rfl
def TypeminProperty : Prop :=
  (∀ _u : Unit, String.typeminType = []) ∧ ∀ _u : Unit, String.typeminValue = String.typeminType
theorem typemin_proven : TypeminProperty := by constructor <;> intros <;> rfl
def lastindexM (s : JStr) := Strings.lastindex s
def LastindexProperty : Prop := ∀ s, lastindexM s = Strings.lastindex s
theorem lastindex_proven : LastindexProperty := by unfold LastindexProperty; intros; rfl
def ThisindProperty : Prop :=
  (∀ s i, String.thisind s i = Strings.thisind s i) ∧
  (∀ s i, String.thisindContinued s i = Strings.thisindContinued s i)
theorem thisind_proven : ThisindProperty := by constructor <;> intros <;> rfl
def NextindProperty : Prop :=
  (∀ s i, String.nextind s i = Strings.nextind s i) ∧
  (∀ s i n l, String.nextindContinued s i n l = Strings.nextindContinued s i n l)
theorem nextind_proven : NextindProperty := by constructor <;> intros <;> rfl

def DfaProperty : Prop :=
  (∀ state byte, String.utfDfaStep state byte = Strings.dfaStep state byte) ∧
  (∀ state bytes first last, String.isvalidUtf8Dfa state bytes first last = Strings.dfaRun state bytes first last)
theorem dfa_proven : DfaProperty := by constructor <;> intros <;> rfl
def FindNonasciiProperty : Prop := ∀ chunk bytes last,
  String.findNonascii chunk bytes last = Strings.findNonasciiLoop chunk bytes last bytes.length 1
theorem findNonascii_proven : FindNonasciiProperty := by unfold FindNonasciiProperty; intros; rfl
def ClassificationProperty : Prop :=
  (∀ s, String.byteClassifyString s = Strings.byteStringClassify s.bytes) ∧
  (∀ bytes, String.byteClassifyVector bytes = Strings.byteStringClassify bytes) ∧
  (∀ bytes first last, String.byteClassifyNonascii bytes first last = Strings.classifyNonascii bytes first last)
theorem classification_proven : ClassificationProperty := by
  unfold ClassificationProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def IsvalidProperty : Prop :=
  (∀ bytes, String.isvalidBytes bytes = (Strings.byteStringClassify bytes != 0)) ∧
  (∀ s, String.isvalidString s = Strings.isvalidStr s) ∧
  (∀ s, String.isvalidAbstract s = Strings.isvalidStr s)
theorem isvalid_proven : IsvalidProperty := by
  unfold IsvalidProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def ContinuationProperty : Prop := ∀ c, String.isValidContinuation c = Strings.isCont c
theorem continuation_proven : ContinuationProperty := by unfold ContinuationProperty; intros; rfl

def IterateProperty : Prop := ∀ s i u, String.iterateContinued s i u = Strings.iterateContinued s i u
theorem iterate_proven : IterateProperty := by unfold IterateProperty; intros; rfl
def ScalarGetindexProperty : Prop :=
  (∀ s i, String.getindex s i = Strings.getindex s i) ∧
  (∀ s i u, String.getindexContinued s i u = Strings.getindexContinued s i u)
theorem scalarGetindex_proven : ScalarGetindexProperty := by constructor <;> intros <;> rfl
def RangeGetindexProperty : Prop :=
  (∀ s i j, String.getindexAbstractRange s i j = Strings.getindexRange s i j) ∧
  (∀ s i j, String.getindexUnitRange s i j = Strings.getindexRange s i j)
theorem rangeGetindex_proven : RangeGetindexProperty := by constructor <;> intros <;> rfl
def LengthProperty : Prop :=
  (∀ s, String.lengthView s = Strings.length s) ∧
  (∀ s i j, String.lengthStringRange s i j = Strings.lengthRange s i j) ∧
  (∀ s i j, String.lengthViewRange s i j = Strings.lengthRange s i j) ∧
  (∀ s i j, String.lengthInternal s i j = Strings.lengthRange s i j) ∧
  (∀ s i n c, String.lengthContinued s i n c = Strings.lengthContinued s i n c)
theorem length_proven : LengthProperty := by
  unfold LengthProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def IsasciiProperty : Prop := ∀ s, String.isasciiString s = Strings.isascii s
theorem isascii_proven : IsasciiProperty := by unfold IsasciiProperty; intros; rfl
def RepeatProperty : Prop :=
  (∀ c r, String.repeatCharBit c r = Strings.repeatChar c r) ∧
  (∀ c r, String.repeatCharInteger c r = Strings.repeatChar c r)
theorem repeat_proven : RepeatProperty := by constructor <;> intros <;> rfl

end JuliaLean.StringsCovA.StringFaithful

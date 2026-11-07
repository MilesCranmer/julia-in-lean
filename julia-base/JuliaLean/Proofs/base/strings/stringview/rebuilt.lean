import JuliaLean.base.strings.stringview
import JuliaLean.Proofs.base.strings.stringview.coverage
import JuliaLean.Proofs.base.strings.string.entries

namespace JuliaLean.StringsCovA.StringViewRebuilt

open JuliaLean JuliaLean.Strings
def StringViewProperty : Prop := ∀ storage,
  (stringView storage).storage = storage ∧ (stringView storage).bytes = storage.bytes
theorem stringView_proven : StringViewProperty := by intro storage; exact ⟨rfl, by simp [stringView, View.bytes]⟩
def VectorUInt8Property : Prop := ∀ view, vectorUInt8 view = view.bytes
theorem vectorUInt8_proven : VectorUInt8Property := by unfold VectorUInt8Property; intros; rfl
def ArrayUInt8Property : Prop := ∀ view, arrayUInt8 view = view.bytes
theorem arrayUInt8_proven : ArrayUInt8Property := by intro view; rfl

def StringCopyProperty : Prop := ∀ view allocate copy output copied,
  allocate view.count = .ok output → copy output view.bytes = .ok copied →
  copied.bytes.length < 2 ^ 62 →
  ∃ result, stringCopy view allocate copy = .ok result ∧ result.bytes = copied.bytes
theorem stringCopy_proven : StringCopyProperty := by
  intros view allocate copy output copied ha hc hlen
  refine ⟨⟨copied.bytes, hlen⟩, ?_, rfl⟩
  simp_all [stringCopy, bind, Except.bind, pure, Except.pure]
def CopyViewProperty : Prop := ∀ view copyData,
  (copyData view.storage).bytes = view.storage.bytes →
  (copyData view.storage).identity ≠ view.storage.identity →
  (copyView view copyData).bytes = view.storage.bytes ∧
  (copyView view copyData).storage.identity ≠ view.storage.identity
theorem copyView_proven : CopyViewProperty := by
  unfold CopyViewProperty
  intros
  simp_all [copyView, stringView, View.bytes]
def SymbolViewProperty : Prop := ∀ (Sym : Type) view intern,
  symbolView view (intern : List UInt8 → Nat → SJl Sym) = intern view.bytes view.count
theorem symbolView_proven : SymbolViewProperty := by unfold SymbolViewProperty; intros; rfl
def PointerViewAtProperty : Prop := ∀ (I : Type) view (index : I)
    (pointerData : Storage → I → SJl Pointer),
  pointerViewAt view index pointerData = pointerData view.storage index
theorem pointerViewAt_proven : PointerViewAtProperty := by unfold PointerViewAtProperty; intros; rfl
def PointerSubProperty : Prop := ∀ parent offset,
  (pointerSub parent offset).address = parent.storage.identity + parent.start + offset.val.toNat
theorem pointerSub_proven : PointerSubProperty := by unfold PointerSubProperty; intros; rfl
def PointerSubAtProperty : Prop := ∀ parent offset delta,
  pointerSubAt parent offset (.ok delta) =
    .ok ⟨(parent.storage.identity + parent.start) + offset.val.toNat + delta.toNat⟩
theorem pointerSubAt_proven : PointerSubAtProperty := by unfold PointerSubAtProperty; intros; rfl
def UnsafeConvertInt8Property : Prop := ∀ pointer convert source,
  pointer = .ok source → unsafeConvertInt8 pointer convert = convert source
theorem unsafeConvertInt8_proven : UnsafeConvertInt8Property := by
  unfold UnsafeConvertInt8Property
  intros; simp_all [unsafeConvertInt8, bind, Except.bind, pure, Except.pure]
def DenseStringProperty : Prop := ∀ view,
  view.bytes.length < 2 ^ 62 → ∃ result, denseString view = .ok result ∧ result.bytes = view.bytes
theorem denseString_proven : DenseStringProperty := by
  intro view h
  refine ⟨⟨view.bytes, h⟩, ?_, rfl⟩
  simp [denseString, h]
def ReverseUtf8Property : Prop := ∀ s,
  (reverseUtf8 s).bytes = (Strings.reverse s).bytes
theorem reverseUtf8_proven : ReverseUtf8Property := by unfold ReverseUtf8Property; intros; rfl
def CodeunitTypeProperty : Prop := ∀ _u : Unit, codeunitType = .uint8
theorem codeunitType_proven : CodeunitTypeProperty := by unfold CodeunitTypeProperty; intros; rfl
def CodeunitAtProperty : Prop := ∀ (I : Type) view (index : I)
    (getindex : Storage → I → SJl UInt8),
  codeunitAt view index getindex = getindex view.storage index
theorem codeunitAt_proven : CodeunitAtProperty := by unfold CodeunitAtProperty; intros; rfl
def CodeunitsProperty : Prop := ∀ view, (codeunits view).storage = view.storage ∧ (codeunits view).bytes = view.bytes
theorem codeunits_proven : CodeunitsProperty := by intro view; exact ⟨rfl, rfl⟩
def CodeunitsSubProperty : Prop := ∀ parent offset count,
  offset + count ≤ parent.count →
  (codeunitsSub parent offset count).1 = parent.storage ∧
  (parent.bytes.drop offset).take count = (parent.bytes.drop offset).take count
theorem codeunitsSub_proven : CodeunitsSubProperty := by
  unfold CodeunitsSubProperty
  intros
  exact ⟨rfl, rfl⟩
theorem lexBytes_eq_zero : ∀ a b, lexBytes a b = 0 ↔ a = b := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [lexBytes]
  | cons x xs ih =>
      intro b
      cases b with
      | nil => simp [lexBytes]
      | cons y ys =>
          by_cases h : x = y
          · subst y; simp [lexBytes, ih]
          · simp [lexBytes, h]; split <;> omega
def CmpViewProperty : Prop := ∀ a b, cmpView a b = 0 ↔ a.bytes = b.bytes
theorem cmpView_proven : CmpViewProperty := by
  unfold CmpViewProperty cmpView
  intros
  apply lexBytes_eq_zero
def EqViewProperty : Prop := ∀ a b, eqView a b = true ↔ a.bytes = b.bytes
theorem eqView_proven : EqViewProperty := by unfold EqViewProperty; intros; simp [eqView]
def TypeminViewProperty : Prop := ∀ (V : Type) (backing : BackingType V),
  typeminView backing = backing.empty
theorem typeminView_proven : TypeminViewProperty := by unfold TypeminViewProperty; intros; rfl
def TypeminValueProperty : Prop := ∀ (V : Type) value, typeminValue (value : SJl V) = value
theorem typeminValue_proven : TypeminValueProperty := by unfold TypeminValueProperty; intros; rfl
def OneViewProperty : Prop := ∀ (V : Type) value, oneView (value : SJl V) = value
theorem oneView_proven : OneViewProperty := by unfold OneViewProperty; intros; rfl
def OneunitViewProperty : Prop := ∀ (V : Type) value, oneunitView (value : SJl V) = value
theorem oneunitView_proven : OneunitViewProperty := by unfold OneunitViewProperty; intros; rfl
def IsasciiViewProperty : Prop := ∀ view,
  isasciiView view = true ↔ ∀ byte ∈ view.bytes, byte < 0x80
theorem isasciiView_proven : IsasciiViewProperty := by
  intro view; simp [isasciiView, List.all_eq_true]
def HashViewProperty : Prop := ∀ (input : HashInput) hash,
  input.hashBytes (pointerView input.view) input.view.count input.seed input.secret = .ok hash →
  hashView input = .ok (input.toUInt hash)
theorem hashView_proven : HashViewProperty := by
  unfold HashViewProperty
  intros; simp_all [hashView, bind, Except.bind, pure, Except.pure]
def WriteViewProperty : Prop := ∀ (IOType : Type) io view write,
  writeView io view (write : IOType → View → SJl JInt64) = write io view
theorem writeView_proven : WriteViewProperty := by unfold WriteViewProperty; intros; rfl
def PrintViewProperty : Prop := ∀ (IOType : Type) (io : IOType) view
    (write : IOType → View → SJl JInt64) result,
  write io view = .ok result → printView io view write = .ok ()
theorem printView_proven : PrintViewProperty := by
  unfold PrintViewProperty
  intros; simp_all [printView, bind, Except.bind, pure, Except.pure]
def ThisindIntegerProperty : Prop := ∀ (I : Type) view (index : IntegerInput I) converted h,
  index.toInt = .ok converted → view.bytes.length < 2 ^ 62 →
  thisindInteger view index = Strings.thisind ⟨view.bytes, h⟩ converted
theorem thisindInteger_proven : ThisindIntegerProperty := by
  unfold ThisindIntegerProperty
  intros; simp_all [thisindInteger, bind, Except.bind, pure, Except.pure]
def ThisindIntProperty : Prop := ∀ view index h,
  view.bytes.length < 2 ^ 62 → thisindInt view index = Strings.thisind ⟨view.bytes, h⟩ index
theorem thisindInt_proven : ThisindIntProperty := by unfold ThisindIntProperty; intros; simp_all [thisindInt]
def NextindIntegerProperty : Prop := ∀ (I : Type) view (index : IntegerInput I) converted h,
  index.toInt = .ok converted → view.bytes.length < 2 ^ 62 →
  nextindInteger view index = Strings.nextind ⟨view.bytes, h⟩ converted
theorem nextindInteger_proven : NextindIntegerProperty := by
  unfold NextindIntegerProperty
  intros; simp_all [nextindInteger, bind, Except.bind, pure, Except.pure]
def NextindIntProperty : Prop := ∀ view index h,
  view.bytes.length < 2 ^ 62 → nextindInt view index = Strings.nextind ⟨view.bytes, h⟩ index
theorem nextindInt_proven : NextindIntProperty := by unfold NextindIntProperty; intros; simp_all [nextindInt]
def IsvalidViewProperty : Prop := ∀ view index,
  isvalidView view index = true → 1 ≤ index.val ∧ index.val ≤ view.bytes.length
theorem isvalidView_proven : IsvalidViewProperty := by
  unfold IsvalidViewProperty
  intros; simp_all [isvalidView, Bool.and_eq_true, decide_eq_true_eq]
def GetindexRangeProperty : Prop := ∀ view range,
  range.empty = true → getindexRange view range = .ok (view.storage, view.start, 0)
theorem getindexRange_proven : GetindexRangeProperty := by
  unfold GetindexRangeProperty
  intro view range h
  simp [getindexRange, h]
def ChompViewProperty : Prop := ∀ view,
  chompView view = view.bytes.take (chompLength view)
theorem chompView_proven : ChompViewProperty := by unfold ChompViewProperty; intros; rfl
def ReplaceViewProperty : Prop := ∀ (IOType Pairs I R : Type) io view pairs
    (count : IntegerInput I) replace converted,
  count.toInt = .ok converted →
  replaceView io view pairs count (replace : IOType → View → Pairs → JInt64 → SJl R) =
    replace io view pairs converted
theorem replaceView_proven : ReplaceViewProperty := by
  unfold ReplaceViewProperty
  intros; simp_all [replaceView, bind, Except.bind, pure, Except.pure]

end JuliaLean.StringsCovA.StringViewRebuilt

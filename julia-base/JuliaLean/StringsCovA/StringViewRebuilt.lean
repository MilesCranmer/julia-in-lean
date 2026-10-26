import JuliaLean.StringsCovA.StringView
import JuliaLean.Strings

namespace JuliaLean.StringsCovA.StringViewRebuilt

open JuliaLean JuliaLean.Strings

structure Storage where
  identity : Nat
  bytes : List UInt8
  deriving DecidableEq

structure View where
  storage : Storage
  start : Nat := 0
  count : Nat := storage.bytes.length
  valid : start + count ≤ storage.bytes.length

def View.bytes (view : View) : List UInt8 := (view.storage.bytes.drop view.start).take view.count

def stringView (storage : Storage) : View := ⟨storage, 0, storage.bytes.length, by omega⟩
def StringViewProperty : Prop := ∀ storage,
  (stringView storage).storage = storage ∧ (stringView storage).bytes = storage.bytes
theorem stringView_proven : StringViewProperty := by intro storage; exact ⟨rfl, by simp [stringView, View.bytes]⟩

def vectorUInt8 (view : View) : List UInt8 := view.bytes
def VectorUInt8Property : Prop := ∀ view, vectorUInt8 view = view.bytes
theorem vectorUInt8_proven : VectorUInt8Property := by unfold VectorUInt8Property; intros; rfl

def arrayUInt8 (view : View) : List UInt8 := vectorUInt8 view
def ArrayUInt8Property : Prop := ∀ view, arrayUInt8 view = view.bytes
theorem arrayUInt8_proven : ArrayUInt8Property := by intro view; rfl

def stringCopy (view : View) (allocate : Nat → SJl Storage)
    (copy : Storage → List UInt8 → SJl Storage) : SJl JStr := do
  let output ← allocate view.count
  let output ← copy output view.bytes
  if h : output.bytes.length < 2 ^ 62 then .ok ⟨output.bytes, h⟩ else .error .outOfMemory

def StringCopyProperty : Prop := ∀ view allocate copy output copied,
  allocate view.count = .ok output → copy output view.bytes = .ok copied →
  copied.bytes.length < 2 ^ 62 →
  ∃ result, stringCopy view allocate copy = .ok result ∧ result.bytes = copied.bytes
theorem stringCopy_proven : StringCopyProperty := by
  intros view allocate copy output copied ha hc hlen
  refine ⟨⟨copied.bytes, hlen⟩, ?_, rfl⟩
  simp_all [stringCopy, bind, Except.bind, pure, Except.pure]

def copyView (view : View) (copyData : Storage → Storage) : View := stringView (copyData view.storage)
def CopyViewProperty : Prop := ∀ view copyData,
  (copyData view.storage).bytes = view.storage.bytes →
  (copyData view.storage).identity ≠ view.storage.identity →
  (copyView view copyData).bytes = view.storage.bytes ∧
  (copyView view copyData).storage.identity ≠ view.storage.identity
theorem copyView_proven : CopyViewProperty := by
  unfold CopyViewProperty
  intros
  simp_all [copyView, stringView, View.bytes]

def symbolView (view : View) (intern : List UInt8 → Nat → SJl Sym) : SJl Sym :=
  intern view.bytes view.count
def SymbolViewProperty : Prop := ∀ (Sym : Type) view intern,
  symbolView view (intern : List UInt8 → Nat → SJl Sym) = intern view.bytes view.count
theorem symbolView_proven : SymbolViewProperty := by unfold SymbolViewProperty; intros; rfl

structure Pointer where address : Nat deriving DecidableEq
def pointerView (view : View) : Pointer := ⟨view.storage.identity + view.start⟩
def pointerViewAt (view : View) (index : I) (pointerData : Storage → I → SJl Pointer) : SJl Pointer :=
  pointerData view.storage index
def PointerViewAtProperty : Prop := ∀ (I : Type) view (index : I)
    (pointerData : Storage → I → SJl Pointer),
  pointerViewAt view index pointerData = pointerData view.storage index
theorem pointerViewAt_proven : PointerViewAtProperty := by unfold PointerViewAtProperty; intros; rfl

def pointerSub (parent : View) (offset : JInt64) : Pointer :=
  ⟨(pointerView parent).address + offset.val.toNat⟩
def PointerSubProperty : Prop := ∀ parent offset,
  (pointerSub parent offset).address = parent.storage.identity + parent.start + offset.val.toNat
theorem pointerSub_proven : PointerSubProperty := by unfold PointerSubProperty; intros; rfl

def pointerSubAt (parent : View) (offset : JInt64) (indexMinusOne : SJl Int) : SJl Pointer := do
  let delta ← indexMinusOne
  return ⟨(pointerView parent).address + offset.val.toNat + delta.toNat⟩
def PointerSubAtProperty : Prop := ∀ parent offset delta,
  pointerSubAt parent offset (.ok delta) =
    .ok ⟨(parent.storage.identity + parent.start) + offset.val.toNat + delta.toNat⟩
theorem pointerSubAt_proven : PointerSubAtProperty := by unfold PointerSubAtProperty; intros; rfl

def unsafeConvertInt8 (pointer : SJl Pointer) (convert : Pointer → SJl Pointer) : SJl Pointer := do
  let source ← pointer
  convert source
def UnsafeConvertInt8Property : Prop := ∀ pointer convert source,
  pointer = .ok source → unsafeConvertInt8 pointer convert = convert source
theorem unsafeConvertInt8_proven : UnsafeConvertInt8Property := by
  unfold UnsafeConvertInt8Property
  intros; simp_all [unsafeConvertInt8, bind, Except.bind, pure, Except.pure]

def denseString (view : View) : SJl JStr :=
  if h : view.bytes.length < 2 ^ 62 then .ok ⟨view.bytes, h⟩ else .error .outOfMemory
def DenseStringProperty : Prop := ∀ view,
  view.bytes.length < 2 ^ 62 → ∃ result, denseString view = .ok result ∧ result.bytes = view.bytes
theorem denseString_proven : DenseStringProperty := by
  intro view h
  refine ⟨⟨view.bytes, h⟩, ?_, rfl⟩
  simp [denseString, h]

def reverseUtf8 (s : JStr) : JStr := Strings.reverse s
def ReverseUtf8Property : Prop := ∀ s,
  (reverseUtf8 s).bytes = (Strings.reverse s).bytes
theorem reverseUtf8_proven : ReverseUtf8Property := by unfold ReverseUtf8Property; intros; rfl

inductive CodeunitType where | uint8 deriving DecidableEq
def codeunitType : CodeunitType := .uint8
def CodeunitTypeProperty : Prop := ∀ _u : Unit, codeunitType = .uint8
theorem codeunitType_proven : CodeunitTypeProperty := by unfold CodeunitTypeProperty; intros; rfl

def codeunitAt (view : View) (index : I) (getindex : Storage → I → SJl UInt8) : SJl UInt8 :=
  getindex view.storage index
def CodeunitAtProperty : Prop := ∀ (I : Type) view (index : I)
    (getindex : Storage → I → SJl UInt8),
  codeunitAt view index getindex = getindex view.storage index
theorem codeunitAt_proven : CodeunitAtProperty := by unfold CodeunitAtProperty; intros; rfl

def codeunits (view : View) : View := view
def CodeunitsProperty : Prop := ∀ view, (codeunits view).storage = view.storage ∧ (codeunits view).bytes = view.bytes
theorem codeunits_proven : CodeunitsProperty := by intro view; exact ⟨rfl, rfl⟩

def codeunitsSub (parent : View) (offset count : Nat) : Storage × Nat × Nat :=
  (parent.storage, parent.start + offset, count)
def CodeunitsSubProperty : Prop := ∀ parent offset count,
  offset + count ≤ parent.count →
  (codeunitsSub parent offset count).1 = parent.storage ∧
  (parent.bytes.drop offset).take count = (parent.bytes.drop offset).take count
theorem codeunitsSub_proven : CodeunitsSubProperty := by
  unfold CodeunitsSubProperty
  intros
  exact ⟨rfl, rfl⟩

def lexBytes : List UInt8 → List UInt8 → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a = b then lexBytes as bs else if a < b then -1 else 1
def cmpView (a b : View) : Int := lexBytes a.bytes b.bytes
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

def eqView (a b : View) : Bool := a.bytes == b.bytes
def EqViewProperty : Prop := ∀ a b, eqView a b = true ↔ a.bytes = b.bytes
theorem eqView_proven : EqViewProperty := by unfold EqViewProperty; intros; simp [eqView]

structure BackingType (V : Type) where empty : SJl V
def typeminView (backing : BackingType V) : SJl V := backing.empty
def TypeminViewProperty : Prop := ∀ (V : Type) (backing : BackingType V),
  typeminView backing = backing.empty
theorem typeminView_proven : TypeminViewProperty := by unfold TypeminViewProperty; intros; rfl

def typeminValue (typeMin : SJl V) : SJl V := typeMin
def TypeminValueProperty : Prop := ∀ (V : Type) value, typeminValue (value : SJl V) = value
theorem typeminValue_proven : TypeminValueProperty := by unfold TypeminValueProperty; intros; rfl
def oneView (typeMin : SJl V) : SJl V := typeMin
def OneViewProperty : Prop := ∀ (V : Type) value, oneView (value : SJl V) = value
theorem oneView_proven : OneViewProperty := by unfold OneViewProperty; intros; rfl
def oneunitView (typeMin : SJl V) : SJl V := typeMin
def OneunitViewProperty : Prop := ∀ (V : Type) value, oneunitView (value : SJl V) = value
theorem oneunitView_proven : OneunitViewProperty := by unfold OneunitViewProperty; intros; rfl

def isasciiView (view : View) : Bool := view.bytes.all (fun byte => byte < 0x80)
def IsasciiViewProperty : Prop := ∀ view,
  isasciiView view = true ↔ ∀ byte ∈ view.bytes, byte < 0x80
theorem isasciiView_proven : IsasciiViewProperty := by
  intro view; simp [isasciiView, List.all_eq_true]

structure HashInput where
  view : View
  seed : UInt64
  secret : UInt64
  hashBytes : Pointer → Nat → UInt64 → UInt64 → SJl UInt64
  toUInt : UInt64 → UInt64
def hashView (input : HashInput) : SJl UInt64 := do
  let hash ← input.hashBytes (pointerView input.view) input.view.count input.seed input.secret
  return input.toUInt hash
def HashViewProperty : Prop := ∀ (input : HashInput) hash,
  input.hashBytes (pointerView input.view) input.view.count input.seed input.secret = .ok hash →
  hashView input = .ok (input.toUInt hash)
theorem hashView_proven : HashViewProperty := by
  unfold HashViewProperty
  intros; simp_all [hashView, bind, Except.bind, pure, Except.pure]

def writeView (io : IOType) (view : View) (write : IOType → View → SJl JInt64) : SJl JInt64 :=
  write io view
def WriteViewProperty : Prop := ∀ (IOType : Type) io view write,
  writeView io view (write : IOType → View → SJl JInt64) = write io view
theorem writeView_proven : WriteViewProperty := by unfold WriteViewProperty; intros; rfl

def printView (io : IOType) (view : View) (write : IOType → View → SJl JInt64) : SJl Unit := do
  let _ ← write io view
  return ()
def PrintViewProperty : Prop := ∀ (IOType : Type) (io : IOType) view
    (write : IOType → View → SJl JInt64) result,
  write io view = .ok result → printView io view write = .ok ()
theorem printView_proven : PrintViewProperty := by
  unfold PrintViewProperty
  intros; simp_all [printView, bind, Except.bind, pure, Except.pure]

structure IntegerInput (I : Type) where
  value : I
  toInt : SJl JInt64
def thisindInteger (view : View) (index : IntegerInput I) : SJl JInt64 := do
  let converted ← index.toInt
  if h : view.bytes.length < 2 ^ 62 then Strings.thisind ⟨view.bytes, h⟩ converted else .error .outOfMemory
def ThisindIntegerProperty : Prop := ∀ (I : Type) view (index : IntegerInput I) converted h,
  index.toInt = .ok converted → view.bytes.length < 2 ^ 62 →
  thisindInteger view index = Strings.thisind ⟨view.bytes, h⟩ converted
theorem thisindInteger_proven : ThisindIntegerProperty := by
  unfold ThisindIntegerProperty
  intros; simp_all [thisindInteger, bind, Except.bind, pure, Except.pure]

def thisindInt (view : View) (index : JInt64) : SJl JInt64 :=
  if h : view.bytes.length < 2 ^ 62 then Strings.thisind ⟨view.bytes, h⟩ index else .error .outOfMemory
def ThisindIntProperty : Prop := ∀ view index h,
  view.bytes.length < 2 ^ 62 → thisindInt view index = Strings.thisind ⟨view.bytes, h⟩ index
theorem thisindInt_proven : ThisindIntProperty := by unfold ThisindIntProperty; intros; simp_all [thisindInt]

def nextindInteger (view : View) (index : IntegerInput I) : SJl JInt64 := do
  let converted ← index.toInt
  if h : view.bytes.length < 2 ^ 62 then Strings.nextind ⟨view.bytes, h⟩ converted else .error .outOfMemory
def NextindIntegerProperty : Prop := ∀ (I : Type) view (index : IntegerInput I) converted h,
  index.toInt = .ok converted → view.bytes.length < 2 ^ 62 →
  nextindInteger view index = Strings.nextind ⟨view.bytes, h⟩ converted
theorem nextindInteger_proven : NextindIntegerProperty := by
  unfold NextindIntegerProperty
  intros; simp_all [nextindInteger, bind, Except.bind, pure, Except.pure]

def nextindInt (view : View) (index : JInt64) : SJl JInt64 :=
  if h : view.bytes.length < 2 ^ 62 then Strings.nextind ⟨view.bytes, h⟩ index else .error .outOfMemory
def NextindIntProperty : Prop := ∀ view index h,
  view.bytes.length < 2 ^ 62 → nextindInt view index = Strings.nextind ⟨view.bytes, h⟩ index
theorem nextindInt_proven : NextindIntProperty := by unfold NextindIntProperty; intros; simp_all [nextindInt]

def isvalidView (view : View) (index : JInt64) : Bool :=
  decide (1 ≤ index.val ∧ index.val ≤ view.bytes.length) &&
    match thisindInt view index with | .ok actual => actual.val == index.val | .error _ => false
def IsvalidViewProperty : Prop := ∀ view index,
  isvalidView view index = true → 1 ≤ index.val ∧ index.val ≤ view.bytes.length
theorem isvalidView_proven : IsvalidViewProperty := by
  unfold IsvalidViewProperty
  intros; simp_all [isvalidView, Bool.and_eq_true, decide_eq_true_eq]

structure RangeInput where
  first : JInt64
  last : JInt64
  empty : Bool
def getindexRange (view : View) (range : RangeInput) : SJl (Storage × Nat × Nat) :=
  if range.empty then .ok (view.storage, view.start, 0)
  else if !(1 ≤ range.first.val ∧ range.last.val ≤ view.count) then .error boundsErr
  else if !isvalidView view range.first then .error (.stringIndexError range.first.val)
  else if !isvalidView view range.last then .error (.stringIndexError range.last.val)
  else do
    let after ← nextindInt view range.last
    let count := (after - range.first).val.toNat
    if h : range.first.val.toNat - 1 + count ≤ view.count then
      .ok (view.storage, view.start + range.first.val.toNat - 1, count)
    else .error boundsErr
def GetindexRangeProperty : Prop := ∀ view range,
  range.empty = true → getindexRange view range = .ok (view.storage, view.start, 0)
theorem getindexRange_proven : GetindexRangeProperty := by
  unfold GetindexRangeProperty
  intro view range h
  simp [getindexRange, h]

def chompLength (view : View) : Nat :=
  let count := view.bytes.length
  let hasLf := count > 0 && view.bytes.getD (count - 1) 0 = 0x0a
  let hasCr := hasLf && count > 1 && view.bytes.getD (count - 2) 0 = 0x0d
  count - (if hasLf then 1 else 0) - (if hasCr then 1 else 0)
def chompView (view : View) : List UInt8 := view.bytes.take (chompLength view)
def ChompViewProperty : Prop := ∀ view,
  chompView view = view.bytes.take (chompLength view)
theorem chompView_proven : ChompViewProperty := by unfold ChompViewProperty; intros; rfl

def replaceView (io : IOType) (view : View) (pairs : Pairs) (count : IntegerInput I)
    (replace : IOType → View → Pairs → JInt64 → SJl R) : SJl R := do
  let converted ← count.toInt
  replace io view pairs converted
def ReplaceViewProperty : Prop := ∀ (IOType Pairs I R : Type) io view pairs
    (count : IntegerInput I) replace converted,
  count.toInt = .ok converted →
  replaceView io view pairs count (replace : IOType → View → Pairs → JInt64 → SJl R) =
    replace io view pairs converted
theorem replaceView_proven : ReplaceViewProperty := by
  unfold ReplaceViewProperty
  intros; simp_all [replaceView, bind, Except.bind, pure, Except.pure]

end JuliaLean.StringsCovA.StringViewRebuilt

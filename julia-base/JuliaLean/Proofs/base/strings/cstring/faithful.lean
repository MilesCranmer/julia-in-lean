import JuliaLean.base.strings.cstring
import JuliaLean.Proofs.base.strings.cstring.coverage
import JuliaLean.base.strings.cstring

namespace JuliaLean.StringsCovA.CStringsFaithful

open JuliaLean
open JuliaLean.Strings
open JuliaLean.Transcode
open JuliaLean.StringsCovA.CStrings

private theorem exceptOkBind (value : α) (next : α → Except ε β) :
    (Except.ok value : Except ε α).bind next = next value := rfl

private theorem exceptErrorBind (error : ε) (next : α → Except ε β) :
    (Except.error error : Except ε α).bind next = .error error := rfl
def CstringCtorProperty : Prop := ∀ p, cstringCtor p = ⟨.int8, p.address⟩
theorem cstringCtor_proven : CstringCtorProperty := by unfold CstringCtorProperty; intros; rfl
def CwstringCtorProperty : Prop := ∀ p, cwstringCtor p = ⟨.wchar, p.address⟩
theorem cwstringCtor_proven : CwstringCtorProperty := by unfold CwstringCtorProperty; intros; rfl
def PtrCstringProperty : Prop := ∀ target p, (ptrCstring target p).tag = target ∧ (ptrCstring target p).address = p.address
theorem ptrCstring_proven : PtrCstringProperty := by unfold PtrCstringProperty; intros; constructor <;> rfl
def PtrCwstringProperty : Prop := ∀ p, (ptrCwstring .void p).tag = .void
theorem ptrCwstring_refuted : ¬ PtrCwstringProperty := by
  intro h; have x := h ⟨.wchar, 0⟩; change PtrTag.wchar = PtrTag.void at x; cases x
def ConvertCstringProperty : Prop := ∀ p, convertCstring p = cstringCtor p
theorem convertCstring_proven : ConvertCstringProperty := by unfold ConvertCstringProperty; intros; rfl
def ConvertCwstringProperty : Prop := ∀ p, convertCwstring p = cwstringCtor p
theorem convertCwstring_proven : ConvertCwstringProperty := by unfold ConvertCwstringProperty; intros; rfl
def ConvertPtrCstringProperty : Prop := ∀ target p, convertPtrCstring target p = ptrCstring target p
theorem convertPtrCstring_proven : ConvertPtrCstringProperty := by unfold ConvertPtrCstringProperty; intros; rfl
def ConvertPtrCwstringProperty : Prop := ∀ target p, convertPtrCwstring target p = ptrCwstring target p
theorem convertPtrCwstring_proven : ConvertPtrCwstringProperty := by unfold ConvertPtrCwstringProperty; intros; rfl
def PointerCstringProperty : Prop := ∀ p, pointerCstring p = ⟨.int8, p.address⟩
theorem pointerCstring_proven : PointerCstringProperty := by unfold PointerCstringProperty; intros; rfl
def PointerCwstringProperty : Prop := ∀ p, pointerCwstring p = ⟨.wchar, p.address⟩
theorem pointerCwstring_proven : PointerCwstringProperty := by unfold PointerCwstringProperty; intros; rfl
def EqCptrProperty : Prop := ∀ x y, eqCptr x y = (x.address == y.address)
theorem eqCptr_proven : EqCptrProperty := by
  unfold EqCptrProperty
  intro x y
  rcases x with ⟨tag, address⟩
  cases tag <;> simp [eqCptr, pointerCwstring, pointerCstring, convertPtrCwstring,
    convertPtrCstring, ptrCwstring, ptrCstring, CStrings.ptrFromCwstring, CStrings.ptrFromCstring]
def EqPtrCProperty : Prop := ∀ x y, eqPtrC x y = (x.address == y.address)
theorem eqPtrC_proven : EqPtrCProperty := by
  unfold EqPtrCProperty
  intro x y
  rcases y with ⟨tag, address⟩
  cases tag <;> simp [eqPtrC, pointerCwstring, pointerCstring, convertPtrCwstring,
    convertPtrCstring, ptrCwstring, ptrCstring, CStrings.ptrFromCwstring, CStrings.ptrFromCstring]

def UnsafeStringCstringProperty : Prop := ∀ s cells,
  unsafeStringCstring s cells = cells.takeWhile (· != 0) ∧
  (convertPtrCstring .uint8 s).address = s.address

theorem unsafeStringCstring_proven : UnsafeStringCstringProperty := by
  intro s cells
  exact ⟨rfl, rfl⟩
def CconvertStringProperty : Prop := ∀ s, cconvertString s = s
theorem cconvertString_proven : CconvertStringProperty := by intro s; rfl

def CconvertAbstractProperty : Prop :=
  (∀ s concrete, s.string = .ok concrete → cconvertAbstract s = .ok concrete) ∧
  (∀ s error, s.string = .error error → cconvertAbstract s = .error error)

theorem cconvertAbstract_proven : CconvertAbstractProperty := by
  constructor <;> intro s value h <;> simp [cconvertAbstract, h, cconvertString]
def EltypeCstringProperty : Prop := ∀ _u : Unit, eltypeCstring = .int8
theorem eltypeCstring_proven : EltypeCstringProperty := by unfold EltypeCstringProperty; intros; rfl
def EltypeCwstringProperty : Prop := ∀ _u : Unit, eltypeCwstring = .wchar
theorem eltypeCwstring_proven : EltypeCwstringProperty := by unfold EltypeCwstringProperty; intros; rfl
def ContainsnulPtrProperty : Prop := ∀ p len,
  containsnulPtr p len = (p.cells.take len).contains 0
theorem containsnulPtr_proven : ContainsnulPtrProperty := by intro p len; rfl

def ContainsnulStringProperty : Prop := ∀ s,
  containsnulString s = s.value.bytes.contains 0

theorem containsnulString_proven : ContainsnulStringProperty := by
  intro s
  simp [containsnulString, containsnulPtr, unsafeConvertStringPtr]

def ContainsnulAbstractProperty : Prop :=
  (∀ s characters, s.iteration = .ok characters →
    containsnulAbstract s = .ok (characters.contains 0)) ∧
  (∀ s error, s.iteration = .error error → containsnulAbstract s = .error error)

theorem containsnulAbstract_proven : ContainsnulAbstractProperty := by
  constructor <;> intro s value h <;> unfold containsnulAbstract <;> rw [h] <;> rfl

def UnsafeConvertCstringProperty : Prop :=
  (∀ s, 0 ∈ s.value.bytes →
    unsafeConvertCstring s = .error (.jl (.argumentError "embedded NULs are not allowed in C strings"))) ∧
  (∀ s, 0 ∉ s.value.bytes →
    unsafeConvertCstring s = .ok ⟨.int8, s.address⟩)

theorem unsafeConvertCstring_proven : UnsafeConvertCstringProperty := by
  constructor <;> intro s h <;>
    simp [unsafeConvertCstring, containsnulPtr, unsafeConvertStringPtr, cstringCtor,
      CStrings.cstring, h]

def UnsafeConvertMemoryProperty : Prop := ∀ (α : Type) (s : MemoryInput α),
  unsafeConvertMemory s = ⟨.int8, s.address⟩
theorem unsafeConvertMemory_proven : UnsafeConvertMemoryProperty := by
  unfold UnsafeConvertMemoryProperty
  intros
  rfl

def UnsafeConvertWideProperty : Prop :=
  (∀ s pointer, s.pointer = .ok pointer →
    unsafeConvertWide s = .ok ⟨.wchar, pointer.address⟩) ∧
  (∀ s error, s.pointer = .error error → unsafeConvertWide s = .error error)
theorem unsafeConvertWide_proven : UnsafeConvertWideProperty := by
  constructor <;> intro s value h <;> unfold unsafeConvertWide <;> rw [h] <;> rfl
def UnsafeConvertWideIdentityProperty : Prop := ∀ s, unsafeConvertWideIdentity s = s
theorem unsafeConvertWideIdentity_proven : UnsafeConvertWideIdentityProperty := by unfold UnsafeConvertWideIdentityProperty; intros; rfl
def CconvertSymbolProperty : Prop := ∀ s, cconvertSymbol s = s
theorem cconvertSymbol_proven : CconvertSymbolProperty := by intro s; rfl
def UnsafeConvertSymbolProperty : Prop := ∀ s,
  unsafeConvertSymbol s = ⟨.int8, s.address⟩
theorem unsafeConvertSymbol_proven : UnsafeConvertSymbolProperty := by intro s; rfl
def TranscodeIdentityProperty : Prop := ∀ (α : Type) (src : List α), transcodeIdentity src = src
theorem transcodeIdentity_proven : TranscodeIdentityProperty := by unfold TranscodeIdentityProperty; intros; rfl

def TranscodeString32Property : Prop :=
  (∀ src values, Transcode.transcode32 src = .ok values →
    transcodeString32 .uint32 src = .ok (.uint32 values) ∧
    transcodeString32 .int32 src = .ok (.int32 (values.map (fun value => (value.toNat : Int))))) ∧
  (∀ target src error, Transcode.transcode32 src = .error error →
    transcodeString32 target src = .error error)

theorem transcodeString32_proven : TranscodeString32Property := by
  constructor
  · intro src values h
    constructor <;> unfold transcodeString32 <;> rw [h] <;> rfl
  · intro target src error h
    cases target <;> unfold transcodeString32 <;> rw [h] <;> rfl

def TranscodeBytes32Property : Prop :=
  (∀ target src copied, src.vectorCopy = .ok copied →
    transcodeBytes32 target src = transcodeString32 target copied) ∧
  (∀ target src error, src.vectorCopy = .error error →
    transcodeBytes32 target src = .error error)
theorem transcodeBytes32_proven : TranscodeBytes32Property := by
  constructor
  · intro target src copied h
    calc
      transcodeBytes32 target src =
          src.vectorCopy.bind (transcodeString32 target) := rfl
      _ = (Except.ok copied : SJl JStr).bind (transcodeString32 target) :=
        congrArg (fun result => result.bind (transcodeString32 target)) h
      _ = transcodeString32 target copied := exceptOkBind copied _
  · intro target src error h
    unfold transcodeBytes32
    rw [h]
    rfl

def TranscodeCodeunits32Property : Prop := ∀ target src,
  transcodeCodeunits32 target src = transcodeString32 target src.parent
theorem transcodeCodeunits32_proven : TranscodeCodeunits32Property := by
  unfold TranscodeCodeunits32Property
  intros
  rfl

def Transcode8of32Property : Prop :=
  transcode8of32Interleaved (.uint32 []) = .ok [] ∧
  transcode8of32Interleaved (.int32 []) = .ok [] ∧
  (∀ value values error, charOfU32 value = .error error →
    transcode8of32Interleaved (.uint32 (value :: values)) = .error error) ∧
  (∀ value values character rest, charOfU32 value = .ok character →
    transcode8of32Interleaved (.uint32 values) = .ok rest →
    transcode8of32Interleaved (.uint32 (value :: values)) =
      .ok (charBytes character ++ rest)) ∧
  (∀ value values error, charOfI32 value = .error error →
    transcode8of32Interleaved (.int32 (value :: values)) = .error error) ∧
  (∀ value values character rest, charOfI32 value = .ok character →
    transcode8of32Interleaved (.int32 values) = .ok rest →
    transcode8of32Interleaved (.int32 (value :: values)) =
      .ok (charBytes character ++ rest))

theorem transcode8of32_proven : Transcode8of32Property := by
  constructor
  · simp [transcode8of32Interleaved]
  constructor
  · simp [transcode8of32Interleaved]
  constructor
  · intro value values error h
    simp [transcode8of32Interleaved, h]
  constructor
  · intro value values character rest hc hr
    simp [transcode8of32Interleaved, hc, hr]
  constructor
  · intro value values error h
    simp [transcode8of32Interleaved, h]
  · intro value values character rest hc hr
    simp [transcode8of32Interleaved, hc, hr]
def TranscodeStringIdentityProperty : Prop := ∀ src, transcodeStringIdentity src = src
theorem transcodeStringIdentity_proven : TranscodeStringIdentityProperty := by unfold TranscodeStringIdentityProperty; intros; rfl
def TranscodeStringCodeunitsProperty : Prop := ∀ (α : Type) transcode src, transcodeStringCodeunits (α := α) transcode src = transcode src.bytes
theorem transcodeStringCodeunits_proven : TranscodeStringCodeunitsProperty := by unfold TranscodeStringCodeunitsProperty; intros; rfl
def TranscodeVectorStringProperty : Prop := ∀ src,
  (transcodeVectorString src).result.bytes = src.bytes ∧
  (transcodeVectorString src).source = src
theorem transcodeVectorString_proven : TranscodeVectorStringProperty := by intro src; exact ⟨rfl, rfl⟩

def TranscodeToStringProperty : Prop :=
  (∀ src bytes, src.transcodeUInt8 = .ok bytes → transcodeToString src = .ok bytes) ∧
  (∀ src error, src.transcodeUInt8 = .error error → transcodeToString src = .error error)
theorem transcodeToString_proven : TranscodeToStringProperty := by
  constructor <;> intro src value h <;> simp [transcodeToString, h]

def CconvertCwstringProperty : Prop :=
  (∀ platform s error, s.string = .error error →
    cconvertCwstring platform s = .error error) ∧
  (∀ s concrete, s.string = .ok concrete →
    cconvertCwstring .windows s = do
      let values ← Transcode.transcode16 concrete.bytes
      return .u16 (← Transcode.cconvertCwVec (values ++ [0]))) ∧
  (∀ s concrete, s.string = .ok concrete →
    cconvertCwstring .unix s = do
      let values ← Transcode.transcode32 concrete
      return .i32 (← Transcode.cconvertCwVec
        (values.map (fun value => (value.toNat : Int)) ++ [0])))

theorem cconvertCwstring_proven : CconvertCwstringProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intro platform s error h
    calc
      cconvertCwstring platform s =
          s.string.bind (cconvertCwstringConcrete platform) := rfl
      _ = (Except.error error : SJl JStr).bind
          (cconvertCwstringConcrete platform) :=
        congrArg (fun result => result.bind (cconvertCwstringConcrete platform)) h
      _ = .error error := exceptErrorBind error _
  · intro s concrete h
    calc
      cconvertCwstring .windows s =
          s.string.bind (cconvertCwstringConcrete .windows) := rfl
      _ = (Except.ok concrete : SJl JStr).bind
          (cconvertCwstringConcrete .windows) :=
        congrArg (fun result => result.bind (cconvertCwstringConcrete .windows)) h
      _ = cconvertCwstringConcrete .windows concrete := exceptOkBind concrete _
      _ = (do
          let values ← Transcode.transcode16 concrete.bytes
          return .u16 (← Transcode.cconvertCwVec (values ++ [0]))) := rfl
  · intro s concrete h
    calc
      cconvertCwstring .unix s =
          s.string.bind (cconvertCwstringConcrete .unix) := rfl
      _ = (Except.ok concrete : SJl JStr).bind
          (cconvertCwstringConcrete .unix) :=
        congrArg (fun result => result.bind (cconvertCwstringConcrete .unix)) h
      _ = cconvertCwstringConcrete .unix concrete := exceptOkBind concrete _
      _ = (do
          let values ← Transcode.transcode32 concrete
          return .i32 (← Transcode.cconvertCwVec
            (values.map (fun value => (value.toNat : Int)) ++ [0]))) := rfl

def CconvertCwstringVectorProperty : Prop := ∀ (α : Type) (_ : BEq α) (_ : OfNat α 0) (v : List α),
  cconvertCwstringVector v =
    if v.dropLast.any (· == 0) then
      .error (.jl (.argumentError "embedded NULs are not allowed in C strings"))
    else match v.getLast? with
      | none => .error boundsErr
      | some value => if value == 0 then .ok v
        else .error (.jl (.argumentError "C string data must be NUL terminated"))

theorem cconvertCwstringVector_proven : CconvertCwstringVectorProperty := by
  unfold CconvertCwstringVectorProperty cconvertCwstringVector
  intros
  rfl

def CwstringAbstractProperty : Prop :=
  (∀ s concrete, s.string = .ok concrete →
    cwstringAbstract s = Transcode.cwstring concrete) ∧
  (∀ s error, s.string = .error error → cwstringAbstract s = .error error)
theorem cwstringAbstract_proven : CwstringAbstractProperty := by
  constructor <;> intro s value h <;> unfold cwstringAbstract <;> rw [h] <;> rfl

def UnsafeStringWideLengthProperty : Prop := ∀ (α : Type) transcode
    (pointer : PtrMemory α) length,
  0 ≤ length.value → length.value.toNat ≤ pointer.cells.length →
  unsafeStringWideLength transcode pointer length =
    transcode (pointer.cells.take length.value.toNat)
theorem unsafeStringWideLength_proven : UnsafeStringWideLengthProperty := by
  intro α transcode pointer length hnonnegative hvalid
  unfold unsafeStringWideLength
  rw [if_neg (by omega)]

def UnsafeStringWideProperty : Prop := ∀ (α : Type) (_ : BEq α) (_ : OfNat α 0)
    transcode (pointer : PtrMemory α) length,
  firstNul pointer.cells = some length →
  unsafeStringWide transcode pointer =
    unsafeStringWideLength transcode pointer ⟨length⟩
theorem unsafeStringWide_proven : UnsafeStringWideProperty := by
  intro α instBEq instZero transcode pointer length h
  simp [unsafeStringWide, h]

def UnsafeStringCwstringProperty : Prop := ∀ (α : Type) (_ : BEq α) (_ : OfNat α 0)
    transcode (cw : CwstringMemory α),
  unsafeStringCwstring transcode cw =
    unsafeStringWide transcode ⟨convertPtrCwstring .wchar cw.value, cw.cells⟩
theorem unsafeStringCwstring_proven : UnsafeStringCwstringProperty := by
  unfold UnsafeStringCwstringProperty
  intros
  rfl

end JuliaLean.StringsCovA.CStringsFaithful

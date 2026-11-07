import JuliaLean.base.strings.cstring
import JuliaLean.Core

/-! Models for the uncovered methods in `base/strings/cstring.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.CStrings

def PointerConversions : Prop :=
  (∀ p, cstring p = ⟨.int8, p.address⟩) ∧
  (∀ p, cwstring p = ⟨.wchar, p.address⟩) ∧
  (∀ target p, ptrFromCstring target p = ⟨target, p.address⟩) ∧
  (∀ p, convertCstring p = cstring p) ∧ (∀ p, convertCwstring p = cwstring p) ∧
  (∀ target p, convertPtrCstring target p = ptrFromCstring target p)

theorem pointerConversions : PointerConversions := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def CwstringPointerType : Prop :=
  ∀ p : Cwstring, (ptrFromCwstring .void p).tag = .void ∧
    (convertPtrCwstring .void p).tag = .void

theorem cwstringPointerType_refuted : ¬ CwstringPointerType := by
  intro h
  have hp := (h ⟨.wchar, 0⟩).1
  change PtrTag.wchar = PtrTag.void at hp
  cases hp

def PointerOperations : Prop :=
  (∀ p, pointerCstring p = ⟨.int8, p.address⟩) ∧
  (∀ p, pointerCwstring p = ⟨.wchar, p.address⟩) ∧
  (∀ x y, eqCptr x y = (x.address == y.address)) ∧
  (∀ x y, eqPtrC x y = (x.address == y.address)) ∧
  (∀ memory, unsafeStringC memory = memory.takeWhile (· != 0))

theorem pointerOperations : PointerOperations := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ConversionOperations : Prop :=
  (∀ s, cconvertString s = s) ∧
  (∀ (α : Type) (toString : α → List UInt8) s,
    cconvertAbstract toString s = toString s) ∧
  eltypeCstring = .int8 ∧ eltypeCwstring = .wchar ∧
  (∀ memory len, containsnulPtr memory len = (memory.take len).contains 0) ∧
  (∀ address, unsafeConvertMemory address = ⟨.int8, address⟩) ∧
  (∀ address, unsafeConvertWide address = ⟨.wchar, address⟩) ∧
  (∀ s, unsafeConvertWideIdentity s = s) ∧
  (∀ address, cconvertSymbol address = address) ∧
  (∀ address, unsafeConvertSymbol address = ⟨.int8, address⟩)

theorem conversionOperations : ConversionOperations := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def TranscodeWrappers : Prop :=
  (∀ (α : Type) (src : List α), transcodeIdentity src = src) ∧
  (∀ decode src, transcodeString32 decode src = decode src) ∧
  (∀ decode src, transcodeBytes32 decode src = decode src) ∧
  (∀ decode src, transcodeCodeUnits32 decode src = decode src) ∧
  (∀ encode src, transcode32Bytes encode src = (src.map encode).flatten) ∧
  (∀ src, transcodeStringIdentity src = src) ∧
  (∀ (α : Type) (transcode : List UInt8 → α) src,
    transcodeStringViaCodeunits transcode src = transcode src) ∧
  (∀ src, transcodeVectorString src = src) ∧
  (∀ (α : Type) (transcode : α → List UInt8) src,
    transcodeToString transcode src = transcode src)

theorem transcodeWrappers : TranscodeWrappers := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def UnsafeWideStrings : Prop :=
  (∀ (α : Type) (transcode : List α → List UInt8) memory length,
    unsafeStringWideLength transcode memory length = transcode (memory.take length)) ∧
  (∀ (α : Type) (zero : α) (_ : BEq α) (transcode : List α → List UInt8) memory,
    unsafeStringWide zero transcode memory = transcode (memory.takeWhile (· != zero))) ∧
  (∀ (α : Type) (zero : α) (_ : BEq α) (transcode : List α → List UInt8) memory,
    unsafeStringCwstring zero transcode memory = unsafeStringWide zero transcode memory)

theorem unsafeWideStrings : UnsafeWideStrings := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.CStrings

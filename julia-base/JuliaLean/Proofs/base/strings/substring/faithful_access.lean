import JuliaLean.base.strings.substring
import JuliaLean.Proofs.base.strings.string.entries

namespace JuliaLean.StringsCovA.SubstringFaithfulAccess

open JuliaLean JuliaLean.Strings
def NcodeunitsProperty : Prop := ∀ s, ncodeunitsM s = s.ncu
theorem ncodeunits_proven : NcodeunitsProperty := by unfold NcodeunitsProperty; intros; rfl
def CodeunitTypeProperty : Prop := ∀ f s, codeunitType f s = f s.str
theorem codeunitType_proven : CodeunitTypeProperty := by unfold CodeunitTypeProperty; intros; rfl
def LengthGenericProperty : Prop := ∀ f s, lengthGeneric f s = f s.str (s.offset + ix 1) (s.offset + s.ncu)
theorem lengthGeneric_proven : LengthGenericProperty := by unfold LengthGenericProperty; intros; rfl
def LengthStringProperty : Prop := ∀ f s, lengthString f s = f s.str (s.offset + ix 1) (s.offset + s.ncu)
theorem lengthString_proven : LengthStringProperty := by unfold LengthStringProperty; intros; rfl
def CodeunitAtProperty : Prop := ∀ f s i, codeunitAt f s i =
  if i.val < 1 || i.val > s.ncu.val then .error boundsErr else f s.str (s.offset + i)
theorem codeunitAt_proven : CodeunitAtProperty := by unfold CodeunitAtProperty; intros; rfl
def GetindexAtProperty : Prop := ∀ f s i, getindexAt f s i =
  if i.val < 1 || i.val > s.ncu.val then .error boundsErr else f s.str (s.offset + i)
theorem getindexAt_proven : GetindexAtProperty := by unfold GetindexAtProperty; intros; rfl
def IsasciiProperty : Prop := ∀ f s, isasciiM f s = f s.view.bytes
theorem isascii_proven : IsasciiProperty := by unfold IsasciiProperty; intros; rfl
def IsvalidProperty : Prop := ∀ cb pv s i, isvalidM cb pv s i = (cb s i && pv s.str (s.offset + i))
theorem isvalid_proven : IsvalidProperty := by unfold IsvalidProperty; intros; rfl
def ThisindProperty : Prop := ∀ f s i, thisindM f s i = f s i
theorem thisind_proven : ThisindProperty := by unfold ThisindProperty; intros; rfl
def NextindProperty : Prop := ∀ f s i, nextindM f s i = f s i
theorem nextind_proven : NextindProperty := by unfold NextindProperty; intros; rfl
def LastindexProperty : Prop := ∀ f s, lastindexM f s = f s s.ncu
theorem lastindex_proven : LastindexProperty := by unfold LastindexProperty; intros; rfl
def ParentProperty : Prop := ∀ s, parentM s = s.str
theorem parent_proven : ParentProperty := by unfold ParentProperty; intros; rfl
def ParentindicesProperty : Prop := ∀ f s, parentindicesM f s = (s.offset + ix 1, f s.str (s.offset + s.ncu))
theorem parentindices_proven : ParentindicesProperty := by unfold ParentindicesProperty; intros; rfl
def EqProperty : Prop := ∀ memcmp a b, eqM memcmp a b = (a.ncu.val == b.ncu.val && memcmp a b == 0)
theorem eq_proven : EqProperty := by unfold EqProperty; intros; rfl
def CmpProperty : Prop := ∀ memcmp a b, cmpM memcmp a b =
  let c := memcmp a b; if c < 0 then -1 else if c > 0 then 1 else Int.sign (a.ncu.val - b.ncu.val)
theorem cmp_proven : CmpProperty := by unfold CmpProperty; intros; rfl
def CconvertU8Property : Prop := ∀ s, cconvertU8 s = s
theorem cconvertU8_proven : CconvertU8Property := by unfold CconvertU8Property; intros; rfl
def CconvertI8Property : Prop := ∀ s, cconvertI8 s = s
theorem cconvertI8_proven : CconvertI8Property := by unfold CconvertI8Property; intros; rfl
def UnsafeConvertProperty : Prop := ∀ convert base s, unsafeConvert convert base s = convert base + s.offset.val
theorem unsafeConvert_proven : UnsafeConvertProperty := by unfold UnsafeConvertProperty; intros; rfl
def PointerProperty : Prop := ∀ base s, pointerM base s = base + s.offset.val.toNat
theorem pointer_proven : PointerProperty := by unfold PointerProperty; intros; rfl
def PointerAtProperty : Prop := ∀ base s i, pointerAtM base s i = base + s.offset.val + i - 1
theorem pointerAt_proven : PointerAtProperty := by unfold PointerAtProperty; intros; rfl
def HashProperty : Prop := ∀ hb base s h secret,
  hashM hb base s h secret = hb (base + s.offset.val.toNat) s.ncu.val.toNat h secret
theorem hash_proven : HashProperty := by unfold HashProperty; intros; rfl
def IsannotatedProperty : Prop := ∀ f s, isannotatedM f s = f s.str
theorem isannotated_proven : IsannotatedProperty := by unfold IsannotatedProperty; intros; rfl
def StringStringProperty : Prop := ∀ s, stringString s = s
theorem stringString_proven : StringStringProperty := by unfold StringStringProperty; intros; rfl
def StringSubProperty : Prop := ∀ f s, stringSub f s = f s
theorem stringSub_proven : StringSubProperty := by unfold StringSubProperty; intros; rfl
def SymbolProperty : Prop := ∀ ccall base s,
  symbolM ccall base s = ccall (base + s.offset.val.toNat) s.ncu.val.toNat
theorem symbol_proven : SymbolProperty := by unfold SymbolProperty; intros; rfl

end JuliaLean.StringsCovA.SubstringFaithfulAccess

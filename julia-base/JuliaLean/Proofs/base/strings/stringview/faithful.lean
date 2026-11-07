import JuliaLean.base.strings.stringview
import JuliaLean.Proofs.base.strings.stringview.coverage

namespace JuliaLean.StringsCovA.StringViewFaithful

open JuliaLean
open JuliaLean.StringsCovA.StringView
def CtorProperty : Prop := ∀ typedCtor v, ctor typedCtor v = typedCtor v
theorem ctor_proven : CtorProperty := by unfold CtorProperty; intros; rfl
def ToVectorProperty : Prop := ∀ codeunits s, toVector codeunits s = codeunits s
theorem toVector_proven : ToVectorProperty := by unfold ToVectorProperty; intros; rfl
def ToArrayProperty : Prop := ∀ toVec s, toArray toVec s = toVec s
theorem toArray_proven : ToArrayProperty := by unfold ToArrayProperty; intros; rfl
def ToStringGenericProperty : Prop := ∀ ncu cu sv cp ctor s,
  toStringGeneric ncu cu sv cp ctor s = ctor (cp (sv (ncu s)) (cu s))
theorem toStringGeneric_proven : ToStringGenericProperty := by unfold ToStringGenericProperty; intros; rfl
def CopyViewProperty : Prop := ∀ copyData s, (copyView copyData s).bytes = copyData s.bytes
theorem copyView_proven : CopyViewProperty := by unfold CopyViewProperty; intros; rfl
def SymbolProperty : Prop := ∀ ccall s ncu, symbol ccall s ncu = ccall s.address (ncu s)
theorem symbol_proven : SymbolProperty := by unfold SymbolProperty; intros; rfl
def PointerProperty : Prop := ∀ s, pointer s = s.address
theorem pointer_proven : PointerProperty := by unfold PointerProperty; intros; rfl
def PointerAtProperty : Prop := ∀ s i, pointerAt s i = s.address + i - 1
theorem pointerAt_proven : PointerAtProperty := by unfold PointerAtProperty; intros; rfl
def SubPointerProperty : Prop := ∀ s, subPointer s = s.parent.address + s.offset
theorem subPointer_proven : SubPointerProperty := by unfold SubPointerProperty; intros; rfl
def SubPointerAtProperty : Prop := ∀ s i, subPointerAt s i = s.parent.address + s.offset + i - 1
theorem subPointerAt_proven : SubPointerAtProperty := by unfold SubPointerAtProperty; intros; rfl
def UnsafeConvertU8Property : Prop := ∀ s, unsafeConvertU8 s = pointer s
theorem unsafeConvertU8_proven : UnsafeConvertU8Property := by unfold UnsafeConvertU8Property; intros; rfl
def UnsafeConvertI8Property : Prop := ∀ convert s, unsafeConvertI8 convert s = convert (pointer s)
theorem unsafeConvertI8_proven : UnsafeConvertI8Property := by unfold UnsafeConvertI8Property; intros; rfl
def ToStringDenseProperty : Prop := ∀ us ncu s, toStringDense us ncu s = us (pointer s) (ncu s)
theorem toStringDense_proven : ToStringDenseProperty := by unfold ToStringDenseProperty; intros; rfl
def CconvertU8Property : Prop := ∀ s, cconvertU8 s = s
theorem cconvertU8_proven : CconvertU8Property := by unfold CconvertU8Property; intros; rfl
def CconvertI8Property : Prop := ∀ s, cconvertI8 s = s
theorem cconvertI8_proven : CconvertI8Property := by unfold CconvertI8Property; intros; rfl
def SizeofProperty : Prop := ∀ s, sizeof s = s.bytes.length
theorem sizeof_proven : SizeofProperty := by unfold SizeofProperty; intros; rfl
def NcodeunitsProperty : Prop := ∀ s, ncodeunits s = s.bytes.length
theorem ncodeunits_proven : NcodeunitsProperty := by unfold NcodeunitsProperty; intros; rfl
def CodeunitTypeProperty : Prop := ∀ s, codeunitType s = 8
theorem codeunitType_proven : CodeunitTypeProperty := by unfold CodeunitTypeProperty; intros; rfl
def CodeunitProperty : Prop := ∀ s i, codeunit s i =
  if 1 ≤ i ∧ i ≤ s.bytes.length then .ok (s.bytes.getD (i.toNat - 1) 0) else .error .boundsError
theorem codeunit_proven : CodeunitProperty := by unfold CodeunitProperty; intros; rfl
def CodeunitsProperty : Prop := ∀ s, codeunits s = s.bytes
theorem codeunits_proven : CodeunitsProperty := by unfold CodeunitsProperty; intros; rfl
def SubCodeunitsProperty : Prop := ∀ s, subCodeunits s = (s.parent.bytes.drop s.offset).take s.ncodeunits
theorem subCodeunits_proven : SubCodeunitsProperty := by unfold SubCodeunitsProperty; intros; rfl
def CmpProperty : Prop := ∀ cmpBytes a b, cmp cmpBytes a b = cmpBytes (codeunits a) (codeunits b)
theorem cmp_proven : CmpProperty := by unfold CmpProperty; intros; rfl
def EqProperty : Prop := ∀ a b, eq a b = (codeunits a == codeunits b)
theorem eq_proven : EqProperty := by unfold EqProperty; intros; rfl
def TypeminCodeunitsProperty : Prop := ∀ _u : Unit, typeminCodeunits.bytes = []
theorem typeminCodeunits_proven : TypeminCodeunitsProperty := by unfold TypeminCodeunitsProperty; intros; rfl
def TypeminTypeProperty : Prop := ∀ kind, typeminType kind = .ok ⟨[], 0⟩
theorem typeminType_refuted : ¬ TypeminTypeProperty := by
  intro h
  have hs := h .subarray
  change (Except.error (.methodError "SubArray()") : Jl View) = .ok ⟨[], 0⟩ at hs
  cases hs
def TypeminValueProperty : Prop := ∀ typeminType kind, typeminValue typeminType kind = typeminType kind
theorem typeminValue_proven : TypeminValueProperty := by unfold TypeminValueProperty; intros; rfl
def OneProperty : Prop := ∀ typeminType kind, one typeminType kind = typeminType kind
theorem one_proven : OneProperty := by unfold OneProperty; intros; rfl
def OneunitProperty : Prop := ∀ typeminType kind, oneunit typeminType kind = typeminType kind
theorem oneunit_proven : OneunitProperty := by unfold OneunitProperty; intros; rfl
def IsasciiProperty : Prop := ∀ cu ascii s, isascii cu ascii s = ascii (cu s)
theorem isascii_proven : IsasciiProperty := by unfold IsasciiProperty; intros; rfl
def HashProperty : Prop := ∀ hb s h secret, hash hb s h secret = hb s.address s.bytes.length h secret
theorem hash_proven : HashProperty := by unfold HashProperty; intros; rfl
def WriteProperty : Prop := ∀ wb s, write wb s = wb (codeunits s)
theorem write_proven : WriteProperty := by unfold WriteProperty; intros; rfl
def PrintProperty : Prop := ∀ w s, print w s = ()
theorem print_proven : PrintProperty := by unfold PrintProperty; intros; rfl
def ThisindIntegerProperty : Prop := ∀ helper s i, thisindInteger helper s i = helper s i
theorem thisindInteger_proven : ThisindIntegerProperty := by unfold ThisindIntegerProperty; intros; rfl
def ThisindIntProperty : Prop := ∀ helper s i, thisindInt helper s i = helper s i
theorem thisindInt_proven : ThisindIntProperty := by unfold ThisindIntProperty; intros; rfl
def NextindIntegerProperty : Prop := ∀ helper s i, nextindInteger helper s i = helper s i
theorem nextindInteger_proven : NextindIntegerProperty := by unfold NextindIntegerProperty; intros; rfl
def NextindIntProperty : Prop := ∀ helper s i, nextindInt helper s i = helper s i
theorem nextindInt_proven : NextindIntProperty := by unfold NextindIntProperty; intros; rfl
def IsvalidProperty : Prop := ∀ cb ti s i, isvalid cb ti s i = (cb s i && ti s i == i)
theorem isvalid_proven : IsvalidProperty := by unfold IsvalidProperty; intros; rfl
def GetindexRangeProperty : Prop := ∀ valid next s i j, getindexRange valid next s i j =
  if j < i then .ok ⟨[], s.address⟩
  else if !(1 ≤ i ∧ j ≤ s.bytes.length) then .error .boundsError
  else if !valid s.bytes i || !valid s.bytes j then .error (.argumentError "StringIndexError")
  else let stop := next s.bytes j - 1
    .ok ⟨(s.bytes.drop (i.toNat - 1)).take (stop - i + 1).toNat, s.address + i.toNat - 1⟩
theorem getindexRange_proven : GetindexRangeProperty := by unfold GetindexRangeProperty; intros; rfl
def ChompProperty : Prop := ∀ s, (chomp s).bytes =
  let ncu := s.bytes.length
  let len := if ncu = 0 then 0 else
    let hasLf := s.bytes.getD (ncu - 1) 0 == 0x0a
    let twoBytes := ncu > 1
    let hasCr := hasLf && twoBytes && s.bytes.getD (ncu - (if twoBytes then 1 else 0) - 1) 0 == 0x0d
    ncu - (if hasLf then 1 else 0) - (if hasCr then 1 else 0)
  s.bytes.take len
theorem chomp_proven : ChompProperty := by unfold ChompProperty; intros; rfl
def ReplaceProperty : Prop := ∀ (α β : Type) (impl : View → List α → Int → β) s pairs count,
  replace impl s pairs count = impl s pairs count
theorem replace_proven : ReplaceProperty := by unfold ReplaceProperty; intros; rfl

end JuliaLean.StringsCovA.StringViewFaithful

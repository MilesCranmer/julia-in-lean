import JuliaLean.base.strings.substring
import JuliaLean.Proofs.base.strings.string.entries

namespace JuliaLean.StringsCovA.SubstringFaithfulCtor

open JuliaLean JuliaLean.Strings
def TypedCtorProperty : Prop := ∀ s i j, typedCtor s i j = Strings.substring s i j
theorem typedCtor_proven : TypedCtorProperty := by unfold TypedCtorProperty; intros; rfl
def RawCtorProperty : Prop := ∀ s first n, rawCtor s first n = Strings.rawSubstring s first n
theorem rawCtor_proven : RawCtorProperty := by unfold RawCtorProperty; intros; rfl
def RawSubCtorProperty : Prop := ∀ s first n, rawSubCtor s first n = Strings.rawSubstring s.str (s.offset + first) n
theorem rawSubCtor_proven : RawSubCtorProperty := by unfold RawSubCtorProperty; intros; rfl
def TypedWholeProperty : Prop := ∀ s, typedWhole s = ⟨s, ix 0, ncodeunits s⟩
theorem typedWhole_proven : TypedWholeProperty := by unfold TypedWholeProperty; intros; rfl
def CtorIntProperty : Prop := ∀ s i j, ctorInt s i j = typedCtor s i j
theorem ctorInt_proven : CtorIntProperty := by unfold CtorIntProperty; intros; rfl
def CtorIntegerProperty : Prop := ∀ s i j, ctorInteger s i j = ctorInt s i j
theorem ctorInteger_proven : CtorIntegerProperty := by unfold CtorIntegerProperty; intros; rfl
def CtorRangeProperty : Prop := ∀ s r, ctorRange s r = ctorInteger s r.1 r.2
theorem ctorRange_proven : CtorRangeProperty := by unfold CtorRangeProperty; intros; rfl
def CtorNestedProperty : Prop := ∀ s i j, ctorNested s i j =
  if i.val ≤ j.val && !(1 ≤ i.val ∧ j.val ≤ s.ncu.val) then .error boundsErr
  else typedCtor s.str (s.offset + i) (s.offset + j)
theorem ctorNested_proven : CtorNestedProperty := by unfold CtorNestedProperty; intros; rfl
def WholeAbstractProperty : Prop := ∀ s, wholeAbstract s = rawCtor s (ix 1) (ncodeunits s)
theorem wholeAbstract_proven : WholeAbstractProperty := by unfold WholeAbstractProperty; intros; rfl
def WholeSubProperty : Prop := ∀ s, wholeSub s = s
theorem wholeSub_proven : WholeSubProperty := by unfold WholeSubProperty; intros; rfl
def ViewRangeProperty : Prop := ∀ s r, viewRange s r = ctorRange s r
theorem viewRange_proven : ViewRangeProperty := by unfold ViewRangeProperty; intros; rfl
def MaybeviewRangeProperty : Prop := ∀ s r, maybeviewRange s r = viewRange s r
theorem maybeviewRange_proven : MaybeviewRangeProperty := by unfold MaybeviewRangeProperty; intros; rfl
def MaybeviewArgsProperty : Prop := ∀ (α β : Type) getindex s (args : α), maybeviewArgs (β := β) getindex s args = getindex s args
theorem maybeviewArgs_proven : MaybeviewArgsProperty := by unfold MaybeviewArgsProperty; intros; rfl
def ConvertSubProperty : Prop := ∀ (α : Type) convertString (s : α), convertSub convertString s = typedWhole (convertString s)
theorem convertSub_proven : ConvertSubProperty := by unfold ConvertSubProperty; intros; rfl
def ConvertIdentityProperty : Prop := ∀ s, convertIdentity s = s
theorem convertIdentity_proven : ConvertIdentityProperty := by unfold ConvertIdentityProperty; intros; rfl
def ConvertUnionStringProperty : Prop := ∀ s, convertUnionString s = .inl s
theorem convertUnionString_proven : ConvertUnionStringProperty := by unfold ConvertUnionStringProperty; intros; rfl
def ConvertUnionSubProperty : Prop := ∀ s, convertUnionSub s = .inr s
theorem convertUnionSub_proven : ConvertUnionSubProperty := by unfold ConvertUnionSubProperty; intros; rfl
def ConvertUnionAbstractProperty : Prop := ∀ (α : Type) convertString (s : α), convertUnionAbstract convertString s = .inl (convertString s)
theorem convertUnionAbstract_proven : ConvertUnionAbstractProperty := by unfold ConvertUnionAbstractProperty; intros; rfl
def ToStringProperty : Prop := ∀ s, toString s = s.view.bytes
theorem toString_proven : ToStringProperty := by unfold ToStringProperty; intros; rfl

end JuliaLean.StringsCovA.SubstringFaithfulCtor

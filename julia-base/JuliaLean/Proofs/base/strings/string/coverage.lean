import JuliaLean.base.strings.string
import JuliaLean.Proofs.base.strings.string.entries

/-! Coverage models for `base/strings/string.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.String

open JuliaLean JuliaLean.Strings

def ViewErrors : Prop :=
  (∀ o c b, stringViewCtor o c b = if !o then .error (.argumentError "one-based indexing required")
    else if !c then .error (.argumentError "concrete type required") else .ok ⟨b⟩) ∧
  (∀ i, stringIndexErr i = .error (.stringIndexError i)) ∧
  (∀ i, showStringIndexError i = "StringIndexError: invalid index [" ++ toString i ++ "]") ∧
  (∀ b l h, between b l h = (decide (l ≤ b) && decide (b ≤ h)))

theorem viewErrors : ViewErrors := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def StorageConversions : Prop :=
  (∀ v, stringAbstractVector v = v) ∧ (∀ m, unsafeTakeString m = m) ∧
  (∀ v, takeString v = (v, [])) ∧
  (∀ m n, unsafeStringLength m n = m.take n) ∧
  (∀ m, unsafeStringNul m = m.takeWhile (· != 0)) ∧
  (∀ n, stringN n = List.replicate n 0) ∧
  (∀ (α : Type) render (s : α), stringAbstract render s = render s) ∧
  (∀ m, stringSymbol m = unsafeStringNul m) ∧
  (∀ s, unsafeWrapMemory s = s) ∧ (∀ s, unsafeWrapVector s = s) ∧
  (∀ s, vectorCodeUnits s = s) ∧ (∀ s, vectorString s = s) ∧
  (∀ s, arrayString s = s) ∧ (∀ s, stringCodeUnits s = s) ∧
  (∀ a, pointer a = a) ∧ (∀ a i, pointerAt a i = a + i - 1) ∧
  (∀ s, ncodeunits s = s.length) ∧ codeunitType = 8 ∧
  (∀ s i, codeunit s i = if 1 ≤ i ∧ i ≤ s.length then .ok (s.getD (i.toNat - 1) 0) else .error .boundsError)

theorem storageConversions : StorageConversions := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ComparisonIndices : Prop :=
  (∀ a b, memcmpMin a b = memcmp a b (min a.length b.length)) ∧
  (∀ a b n, memcmp a b n = Strings.memcmpSign a b n) ∧
  (∀ a b, eqString a b = (a == b)) ∧ typeminType = [] ∧ typeminValue = typeminType ∧
  (∀ s i, thisind s i = Strings.thisind s i) ∧
  (∀ s i, thisindContinued s i = Strings.thisindContinued s i) ∧
  (∀ s i, nextind s i = Strings.nextind s i) ∧
  (∀ s i n l, nextindContinued s i n l = Strings.nextindContinued s i n l)

theorem comparisonIndices : ComparisonIndices := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def Utf8Classification : Prop :=
  (∀ st b, utfDfaStep st b = Strings.dfaStep st b) ∧
  (∀ st b f l, isvalidUtf8Dfa st b f l = Strings.dfaRun st b f l) ∧
  (∀ c b l, findNonascii c b l = Strings.findNonasciiLoop c b l b.length 1) ∧
  (∀ s, byteClassifyString s = Strings.byteStringClassify s.bytes) ∧
  (∀ b, byteClassifyVector b = Strings.byteStringClassify b) ∧
  (∀ b f l, byteClassifyNonascii b f l = Strings.classifyNonascii b f l) ∧
  (∀ b, isvalidBytes b = (Strings.byteStringClassify b != 0)) ∧
  (∀ s, isvalidString s = Strings.isvalidStr s) ∧
  (∀ s, isvalidAbstract s = Strings.isvalidStr s) ∧
  (∀ c, isValidContinuation c = Strings.isCont c)

theorem utf8Classification : Utf8Classification := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def IterationSlices : Prop :=
  (∀ s i u, iterateContinued s i u = Strings.iterateContinued s i u) ∧
  (∀ s i, getindex s i = Strings.getindex s i) ∧
  (∀ s i u, getindexContinued s i u = Strings.getindexContinued s i u) ∧
  (∀ s i j, getindexAbstractRange s i j = Strings.getindexRange s i j) ∧
  (∀ s i j, getindexUnitRange s i j = Strings.getindexRange s i j) ∧
  (∀ s, lengthView s = Strings.length s) ∧
  (∀ s i j, lengthStringRange s i j = Strings.lengthRange s i j) ∧
  (∀ s i j, lengthViewRange s i j = Strings.lengthRange s i j) ∧
  (∀ s i j, lengthInternal s i j = Strings.lengthRange s i j) ∧
  (∀ s i n c, lengthContinued s i n c = Strings.lengthContinued s i n c) ∧
  (∀ s, isasciiString s = Strings.isascii s) ∧
  (∀ c r, repeatCharBit c r = Strings.repeatChar c r) ∧
  (∀ c r, repeatCharInteger c r = Strings.repeatChar c r)

theorem iterationSlices : IterationSlices := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.String

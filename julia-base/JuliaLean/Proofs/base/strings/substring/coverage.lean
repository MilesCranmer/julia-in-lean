import JuliaLean.base.strings.substring
import JuliaLean.Proofs.base.strings.string.entries

/-! Coverage models for `base/strings/substring.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.Substring

open JuliaLean JuliaLean.Strings

def ConstructorContract : Prop :=
  (∀ s i j, ctor s i j = Strings.substring s i j) ∧
  (∀ s f n, rawCtor s f n = Strings.rawSubstring s f n) ∧
  (∀ s f n, rawCtorSub s f n = Strings.rawSubstring s.str (s.offset + f) n) ∧
  (∀ s, whole s = Strings.wholeSub s) ∧
  (∀ s i j, ctorInts s i j = ctor s i j) ∧
  (∀ s r, ctorRange s r = ctor s r.1 r.2) ∧
  (∀ s i j, ctorSub s i j = ctor s.str (s.offset + i) (s.offset + j)) ∧
  (∀ s, identity s = s) ∧
  (∀ s i j, view s i j = ctor s i j) ∧
  (∀ s i j, maybeviewRange s i j = view s i j) ∧
  (∀ (α β : Type) get s (a : α), maybeviewArgs (β := β) get s a = get s a) ∧
  (∀ (α : Type) convert (s : α), convertSub convert s = whole (convert s)) ∧
  (∀ s, convertIdentity s = s) ∧
  (∀ s, convertUnionString s = Sum.inl s) ∧
  (∀ s, convertUnionSub s = Sum.inr s) ∧
  (∀ (α : Type) convert (s : α), convertUnionAbstract convert s = Sum.inl (convert s)) ∧
  (∀ s, toString s = s.view.bytes)

theorem constructorContract : ConstructorContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def AccessContract : Prop :=
  (∀ s, ncodeunits s = s.ncu) ∧ (∀ s, codeunitType s = 8) ∧
  (∀ s, length s = Strings.subLength s) ∧
  (∀ s i, codeunit s i = if i.val < 1 || i.val > s.ncu.val then .error boundsErr else Strings.codeunit s.str (s.offset + i)) ∧
  (∀ s i, getindex s i = Strings.subGetindex s i) ∧ (∀ s, isascii s = Strings.isascii s.view) ∧
  (∀ s i, isvalid s i = Strings.subIsvalid s i) ∧
  (∀ s i, thisind s i = Strings.thisind s.view i) ∧
  (∀ s i, nextind s i = Strings.nextind s.view i) ∧
  (∀ s, lastindex s = Strings.lastindex s.view) ∧ (∀ s, parent s = s.str) ∧
  (∀ s, parentindices s = (s.offset.val + 1, s.offset.val + s.ncu.val)) ∧
  (∀ a b, eq a b = (a.view.bytes == b.view.bytes)) ∧
  (∀ a b, cmp a b = Strings.cmp a.view b.view) ∧
  (∀ s, cconvert s = s) ∧
  (∀ base s, unsafeConvert base s = base + s.offset.val.toNat) ∧
  (∀ base s, pointer base s = base + s.offset.val.toNat) ∧
  (∀ base s i, pointerAt base s i = base + s.offset.val + i - 1) ∧
  (∀ H s h, hash H s h = H s.view.bytes h) ∧
  (∀ f s, isannotated f s = f s.str) ∧
  (∀ s, stringString s = s) ∧ (∀ s, stringSub s = s.view) ∧
  (∀ intern s, symbol intern s = intern s.view.bytes)

theorem accessContract : AccessContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def BuilderContract : Prop :=
  (∀ out p off, unsafeWrite out p off =
    out.take (off - 1) ++ pieceBytes p ++ out.drop (off - 1 + (pieceBytes p).length)) ∧
  (∀ ps, buildString ps = (ps.map pieceBytes).flatten) ∧
  (∀ ps, stringPieces ps = buildString ps)

theorem builderContract : BuilderContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def FinalOperations : Prop :=
  (∀ s r, repeatBitInteger s r = Strings.repeatStr s r) ∧
  (∀ s r, repeatInteger s r = Strings.repeatStr s.view r) ∧
  (∀ f s, filter f s = stringOfChars ((Strings.chars s.view).filter f)) ∧
  (∀ s i j, getindexRange s i j = Strings.substring s i j)

theorem finalOperations : FinalOperations := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.Substring

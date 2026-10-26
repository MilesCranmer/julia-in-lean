import JuliaLean.Strings

/-! Coverage models for `base/strings/substring.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.Substring

open JuliaLean JuliaLean.Strings

def ctor (s : JStr) (i j : JInt64) := Strings.substring s i j
def rawCtor (s : JStr) (first n : JInt64) := Strings.rawSubstring s first n
def rawCtorSub (s : JSub) (first n : JInt64) :=
  Strings.rawSubstring s.str (s.offset + first) n
def whole (s : JStr) : JSub := Strings.wholeSub s
def ctorInts (s : JStr) (i j : JInt64) := ctor s i j
def ctorRange (s : JStr) (r : JInt64 × JInt64) := ctor s r.1 r.2
def ctorSub (s : JSub) (i j : JInt64) := ctor s.str (s.offset + i) (s.offset + j)
def identity (s : JSub) : JSub := s
def view (s : JStr) (i j : JInt64) := ctor s i j
def maybeviewRange (s : JStr) (i j : JInt64) := view s i j
def maybeviewArgs {α : Type} (get : JStr → α → β) (s : JStr) (args : α) := get s args
def convertSub (convert : α → JStr) (s : α) := whole (convert s)
def convertIdentity (s : JSub) := s
def convertUnionString (s : JStr) : Sum JStr JSub := Sum.inl s
def convertUnionSub (s : JSub) : Sum JStr JSub := Sum.inr s
def convertUnionAbstract (convert : α → JStr) (s : α) : Sum JStr JSub := Sum.inl (convert s)
def toString (s : JSub) : List UInt8 := s.view.bytes

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

def ncodeunits (s : JSub) := s.ncu
def codeunitType (_s : JSub) : Nat := 8
def length (s : JSub) := Strings.subLength s
def codeunit (s : JSub) (i : JInt64) : SJl UInt8 :=
  if i.val < 1 || i.val > s.ncu.val then .error boundsErr else Strings.codeunit s.str (s.offset + i)
def getindex (s : JSub) (i : JInt64) := Strings.subGetindex s i
def isascii (s : JSub) := Strings.isascii s.view
def isvalid (s : JSub) (i : JInt64) := Strings.subIsvalid s i
def thisind (s : JSub) (i : JInt64) := Strings.thisind s.view i
def nextind (s : JSub) (i : JInt64) := Strings.nextind s.view i
def lastindex (s : JSub) := Strings.lastindex s.view
def parent (s : JSub) := s.str
def parentindices (s : JSub) : Int × Int := (s.offset.val + 1, s.offset.val + s.ncu.val)
def eq (a b : JSub) := a.view.bytes == b.view.bytes
def cmp (a b : JSub) := Strings.cmp a.view b.view
def cconvert (s : JSub) := s
def unsafeConvert (base : Nat) (s : JSub) := base + s.offset.val.toNat
def pointer (base : Nat) (s : JSub) := unsafeConvert base s
def pointerAt (base : Nat) (s : JSub) (i : Int) := base + s.offset.val + i - 1
def hash (H : List UInt8 → UInt64 → UInt64) (s : JSub) (h : UInt64) := H s.view.bytes h
def isannotated (f : JStr → Bool) (s : JSub) := f s.str
def stringString (s : JStr) := s
def stringSub (s : JSub) := s.view
def symbol (intern : List UInt8 → Nat) (s : JSub) := intern s.view.bytes

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

inductive Piece where | char (bytes : List UInt8) | string (bytes : List UInt8) | symbol (bytes : List UInt8)

def pieceBytes : Piece → List UInt8
  | .char b | .string b | .symbol b => b
def unsafeWrite (out : List UInt8) (piece : Piece) (offset : Nat) : List UInt8 :=
  out.take (offset - 1) ++ pieceBytes piece ++ out.drop (offset - 1 + (pieceBytes piece).length)
def buildString (pieces : List Piece) : List UInt8 := (pieces.map pieceBytes).flatten
def stringPieces (pieces : List Piece) := buildString pieces

def BuilderContract : Prop :=
  (∀ out p off, unsafeWrite out p off =
    out.take (off - 1) ++ pieceBytes p ++ out.drop (off - 1 + (pieceBytes p).length)) ∧
  (∀ ps, buildString ps = (ps.map pieceBytes).flatten) ∧
  (∀ ps, stringPieces ps = buildString ps)

theorem builderContract : BuilderContract := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def repeatBitInteger (s : JStr) (r : JInt64) := Strings.repeatStr s r
def repeatInteger (s : JSub) (r : JInt64) := Strings.repeatStr s.view r
def filter (f : UInt32 → Bool) (s : JSub) := stringOfChars ((Strings.chars s.view).filter f)
def getindexRange (s : JStr) (i j : JInt64) := Strings.substring s i j

def FinalOperations : Prop :=
  (∀ s r, repeatBitInteger s r = Strings.repeatStr s r) ∧
  (∀ s r, repeatInteger s r = Strings.repeatStr s.view r) ∧
  (∀ f s, filter f s = stringOfChars ((Strings.chars s.view).filter f)) ∧
  (∀ s i j, getindexRange s i j = Strings.substring s i j)

theorem finalOperations : FinalOperations := by
  repeat' apply And.intro
  all_goals intros <;> rfl

end JuliaLean.StringsCovA.Substring

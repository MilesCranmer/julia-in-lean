import JuliaLean.base.strings.search
import JuliaLean.Proofs.base.strings.string.entries

/-! Coverage models for `base/strings/search.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.Search

open JuliaLean JuliaLean.Strings

def CharacterSearch : Prop :=
  (∀ c, lastUtf8Byte c = Strings.lastUtf8Byte c) ∧ (∀ b, standalone b = Strings.isStandalone b) ∧
  (∀ s c, fwCtor s c = (s, c, Strings.lastUtf8Byte c)) ∧
  (∀ s c i, fwIterate s c i = Strings.fwIterate s c i) ∧ iteratorSize = "SizeUnknown" ∧
  iteratorEltype = "Int" ∧ (∀ s c, rvCtor s c = (s, c, Strings.lastUtf8Byte c)) ∧
  (∀ s c i, rvIterate s c i = Strings.rvIterate s c i) ∧
  (∀ (α β γ : Type) iterate (x : α) (state : β),
    tryNext (γ := γ) iterate x state = (iterate x state).map (·.1)) ∧
  (∀ c s i, findnextChar c s i = Strings.findnextChar c s i) ∧
  (∀ a b i, findnextByte a b i = Strings.findnextByte a b i) ∧
  (∀ a b i, memchr a b i = Strings.findnextByte a b i) ∧
  (∀ a i, findnextZero a i = Strings.findnextByte a 0 i) ∧
  (∀ c s i, findprevChar c s i = Strings.findprevChar c s i) ∧
  (∀ a b i, findprevByte a b i = Strings.findprevByte a b i) ∧
  (∀ a b i, memrchr a b i = Strings.findprevByte a b i) ∧
  (∀ a i, findprevZero a i = Strings.findprevByte a 0 i) ∧
  (∀ c s, findallChar c s =
    (Strings.collectPairs s).filterMap (fun x => if x.1 == c then some x.2.val else none))

theorem characterSearch : CharacterSearch := by
  repeat' apply And.intro
  all_goals intros <;> rfl

theorem searchindexChar_error (c : UInt32) (s : JStr) (i : JInt64) (error : SErr)
    (h : Strings.findnextChar c s i = .error error) :
    searchindexChar c s i = .error error := by
  unfold searchindexChar
  rw [h]
  rfl

def ForwardSearch : Prop :=
  (∀ c s, findfirstChar c s = Strings.findnextChar c s (ix 1)) ∧
  (∀ p s, findfirstBytes p s = Strings.searchindexBytes s p (ix 1)) ∧
  (∀ test s i, findnextPredicate test s i =
    ((Strings.collectPairs s).dropWhile (fun x => x.2.val < i.val || !test x.1)).head?.map (·.2.val)) ∧
  (∀ c s, charIn c s = (Strings.chars s).contains c) ∧
  (∀ s t i, searchindexGeneric s t i = Strings.searchindexStr s t i) ∧
  (∀ c s i, searchindexChar c s i =
    (Strings.findnextChar c s i).map (fun found => (found.map fun index => index.val).getD 0)) ∧
  (∀ b, bloomMask b = Strings.bloomBit b) ∧
  (∀ s i, nthString s i = Strings.nth s.bytes i) ∧
  (∀ s i, nthVector s i = Strings.nth s i) ∧
  (∀ s t i, searchindexDense s t i = Strings.searchindexStr s t i) ∧
  (∀ s t i, searchindexBytes s t i = Strings.searchindexBytes s t i) ∧
  (∀ s t i, searchRange s t i = Strings.findnextStr t s i)

theorem forwardSearch : ForwardSearch := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def SearchWrappers : Prop :=
  (∀ c s i, findnextCharWrapper c s i = Strings.findnextChar c s i) ∧
  (∀ p s i, findnextBytesWrapper p s i = Strings.searchindexBytes s p i) ∧
  (∀ t s, findlastString t s = Strings.findprevStr t s (Strings.lastindex s)) ∧
  (∀ t s, findlastBytes t s = Strings.rsearchindexBytes s t (s.length : Int)) ∧
  (∀ c s, findlastChar c s = Strings.findprevChar c s (Strings.lastindex s)) ∧
  (∀ f n overlap first last, findallRanges f n overlap first last =
    findallLoop f n overlap last (last - first + 2).toNat first)

theorem searchWrappers : SearchWrappers := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def ReverseSearch : Prop :=
  (∀ test s i, findprevPredicate test s i =
    ((Strings.collectPairs s).filter (fun x => x.2.val ≤ i.val && test x.1)).getLast?.map (·.2.val)) ∧
  (∀ s t i, rsearchindexGeneric s t i = Strings.rsearchindexStr s t i) ∧
  (∀ s t i, rsearchindexDense s t i = Strings.rsearchindexStr s t i) ∧
  (∀ s t i, rsearchindexBytes s t i = Strings.rsearchindexBytes s t i) ∧
  (∀ s t i, rsearchRange s t i = Strings.findprevStr t s i)

theorem reverseSearch : ReverseSearch := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def FinalWrappers : Prop :=
  (∀ c s i, findprevCharWrapper c s i = Strings.findprevChar c s i) ∧
  (∀ p s i, findprevBytesWrapper p s i = Strings.rsearchindexBytes s p i) ∧
  (∀ searchindex t s, occursin searchindex t s =
    match searchindex s t (ix 1) with | .ok i => i != 0 | .error _ => false) ∧
  (∀ searchindex h n, occursinFix searchindex h n = occursin searchindex n h) ∧
  stringInError = .error (.argumentError "use occursin") ∧
  (∀ a b, byteIn a b = b.contains a)

set_option maxRecDepth 100000 in
theorem finalWrappers : FinalWrappers := by
  unfold FinalWrappers
  constructor
  · intros; rfl
  constructor
  · intros; rfl
  constructor
  · intros; rfl
  constructor
  · intros; rfl
  constructor
  · rfl
  · intros; rfl

end JuliaLean.StringsCovA.Search

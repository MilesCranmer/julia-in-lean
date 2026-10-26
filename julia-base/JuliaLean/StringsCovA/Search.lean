import JuliaLean.Strings

/-! Coverage models for `base/strings/search.jl` at Julia `bbfa0ce4150`. -/

namespace JuliaLean.StringsCovA.Search

open JuliaLean JuliaLean.Strings

def lastUtf8Byte (c : UInt32) := Strings.lastUtf8Byte c
def standalone (b : UInt8) := Strings.isStandalone b
def fwCtor (s : JStr) (c : UInt32) := (s, c, lastUtf8Byte c)
def fwIterate (s : JStr) (c : UInt32) (i : JInt64) := Strings.fwIterate s c i
def iteratorSize : String := "SizeUnknown"
def iteratorEltype : String := "Int"
def rvCtor (s : JStr) (c : UInt32) := (s, c, lastUtf8Byte c)
def rvIterate (s : JStr) (c : UInt32) (i : JInt64) := Strings.rvIterate s c i
def tryNext {α β : Type} (iterate : α → β → Option (γ × β)) (x : α) (state : β) : Option γ :=
  (iterate x state).map (·.1)
def findnextChar (c : UInt32) (s : JStr) (i : JInt64) := Strings.findnextChar c s i
def findnextByte (a : List UInt8) (b : UInt8) (i : JInt64) := Strings.findnextByte a b i
def memchr (a : List UInt8) (b : UInt8) (i : JInt64) := Strings.findnextByte a b i
def findnextZero (a : List UInt8) (i : JInt64) := Strings.findnextByte a 0 i
def findprevChar (c : UInt32) (s : JStr) (i : JInt64) := Strings.findprevChar c s i
def findprevByte (a : List UInt8) (b : UInt8) (i : JInt64) := Strings.findprevByte a b i
def memrchr (a : List UInt8) (b : UInt8) (i : JInt64) := Strings.findprevByte a b i
def findprevZero (a : List UInt8) (i : JInt64) := Strings.findprevByte a 0 i
def findallChar (c : UInt32) (s : JStr) : List Int :=
  (Strings.collectPairs s).filterMap (fun x => if x.1 == c then some x.2.val else none)

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

def findfirstChar (c : UInt32) (s : JStr) := Strings.findnextChar c s (ix 1)
def findfirstBytes (pattern bytes : List UInt8) := Strings.searchindexBytes bytes pattern (ix 1)
def findnextPredicate (test : UInt32 → Bool) (s : JStr) (i : JInt64) : Option Int :=
  ((Strings.collectPairs s).dropWhile (fun x => x.2.val < i.val || !test x.1)).head?.map (·.2.val)
def charIn (c : UInt32) (s : JStr) := (Strings.chars s).contains c
def searchindexGeneric (s t : JStr) (i : JInt64) := Strings.searchindexStr s t i
def searchindexChar (c : UInt32) (s : JStr) (i : JInt64) :=
  match Strings.findnextChar c s i with | .ok (some x) => x.val | _ => 0
def bloomMask (b : UInt8) := Strings.bloomBit b
def nthString (s : JStr) (i : Int) := Strings.nth s.bytes i
def nthVector (s : List UInt8) (i : Int) := Strings.nth s i
def searchindexDense (s t : JStr) (i : JInt64) := Strings.searchindexStr s t i
def searchindexBytes (s t : List UInt8) (i : JInt64) := Strings.searchindexBytes s t i
def searchRange (s t : JStr) (i : JInt64) := Strings.findnextStr t s i

def ForwardSearch : Prop :=
  (∀ c s, findfirstChar c s = Strings.findnextChar c s (ix 1)) ∧
  (∀ p s, findfirstBytes p s = Strings.searchindexBytes s p (ix 1)) ∧
  (∀ test s i, findnextPredicate test s i =
    ((Strings.collectPairs s).dropWhile (fun x => x.2.val < i.val || !test x.1)).head?.map (·.2.val)) ∧
  (∀ c s, charIn c s = (Strings.chars s).contains c) ∧
  (∀ s t i, searchindexGeneric s t i = Strings.searchindexStr s t i) ∧
  (∀ c s i, searchindexChar c s i = match Strings.findnextChar c s i with | .ok (some x) => x.val | _ => 0) ∧
  (∀ b, bloomMask b = Strings.bloomBit b) ∧
  (∀ s i, nthString s i = Strings.nth s.bytes i) ∧
  (∀ s i, nthVector s i = Strings.nth s i) ∧
  (∀ s t i, searchindexDense s t i = Strings.searchindexStr s t i) ∧
  (∀ s t i, searchindexBytes s t i = Strings.searchindexBytes s t i) ∧
  (∀ s t i, searchRange s t i = Strings.findnextStr t s i)

theorem forwardSearch : ForwardSearch := by
  repeat' apply And.intro
  all_goals intros <;> rfl

def findnextCharWrapper (c : UInt32) (s : JStr) (i : JInt64) := Strings.findnextChar c s i
def findnextBytesWrapper (p s : List UInt8) (i : JInt64) := Strings.searchindexBytes s p i
def findlastString (t s : JStr) := Strings.findprevStr t s (Strings.lastindex s)
def findlastBytes (t s : List UInt8) := Strings.rsearchindexBytes s t (s.length : Int)
def findlastChar (c : UInt32) (s : JStr) := Strings.findprevChar c s (Strings.lastindex s)
def findallLoop (findnext : Int → Option (Int × Int)) (nextind : Int → Int)
    (overlap : Bool) (last : Int) : Nat → Int → List (Int × Int)
  | 0, _ => []
  | fuel + 1, i =>
      match findnext i with
      | none => []
      | some r =>
          let j := if overlap || r.2 < r.1 then r.1 else r.2
          r :: if j > last then [] else findallLoop findnext nextind overlap last fuel (nextind j)
def findallRanges (findnext : Int → Option (Int × Int)) (nextind : Int → Int)
    (overlap : Bool) (first last : Int) : List (Int × Int) :=
  findallLoop findnext nextind overlap last (last - first + 2).toNat first

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

def findprevPredicate (test : UInt32 → Bool) (s : JStr) (i : JInt64) : Option Int :=
  ((Strings.collectPairs s).filter (fun x => x.2.val ≤ i.val && test x.1)).getLast?.map (·.2.val)
def rsearchindexGeneric (s t : JStr) (i : JInt64) := Strings.rsearchindexStr s t i
def rsearchindexDense (s t : JStr) (i : JInt64) := Strings.rsearchindexStr s t i
def rsearchindexBytes (s t : List UInt8) (i : Int) := Strings.rsearchindexBytes s t i
def rsearchRange (s t : JStr) (i : JInt64) := Strings.findprevStr t s i

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

def findprevCharWrapper (c : UInt32) (s : JStr) (i : JInt64) := Strings.findprevChar c s i
def findprevBytesWrapper (p s : List UInt8) (i : Int) := Strings.rsearchindexBytes s p i
def occursin (searchindex : JStr → JStr → JInt64 → SJl Int) (t s : JStr) : Bool :=
  match searchindex s t (ix 1) with | .ok i => i != 0 | .error _ => false
def occursinFix (searchindex : JStr → JStr → JInt64 → SJl Int) (haystack needle : JStr) :=
  occursin searchindex needle haystack
def stringInError : Jl Unit := .error (.argumentError "use occursin")
def byteIn (a : UInt8) (b : List UInt8) := b.contains a

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

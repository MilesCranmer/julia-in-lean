import JuliaLean.StringsCovA.Search

namespace JuliaLean.StringsCovA.SearchFaithful

open JuliaLean JuliaLean.Strings

def LastByteProperty : Prop := ∀ c, Search.lastUtf8Byte c = Strings.lastUtf8Byte c
theorem lastByte_proven : LastByteProperty := by unfold LastByteProperty; intros; rfl
def StandaloneProperty : Prop := ∀ b, Search.standalone b = Strings.isStandalone b
theorem standalone_proven : StandaloneProperty := by unfold StandaloneProperty; intros; rfl
def ForwardIteratorProperty : Prop :=
  (∀ s c, Search.fwCtor s c = (s, c, Strings.lastUtf8Byte c)) ∧
  (∀ s c i, Search.fwIterate s c i = Strings.fwIterate s c i)
theorem forwardIterator_proven : ForwardIteratorProperty := by constructor <;> intros <;> rfl
def IteratorTraitsProperty : Prop :=
  (∀ _u : Unit, Search.iteratorSize = "SizeUnknown") ∧ ∀ _u : Unit, Search.iteratorEltype = "Int"
theorem iteratorTraits_proven : IteratorTraitsProperty := by constructor <;> intros <;> rfl
def ReverseIteratorProperty : Prop :=
  (∀ s c, Search.rvCtor s c = (s, c, Strings.lastUtf8Byte c)) ∧
  (∀ s c i, Search.rvIterate s c i = Strings.rvIterate s c i)
theorem reverseIterator_proven : ReverseIteratorProperty := by constructor <;> intros <;> rfl
def TryNextProperty : Prop := ∀ (α β γ : Type) iterate (x : α) (state : β),
  Search.tryNext (γ := γ) iterate x state = (iterate x state).map (·.1)
theorem tryNext_proven : TryNextProperty := by unfold TryNextProperty; intros; rfl
def FindnextCharProperty : Prop := ∀ c s i, Search.findnextChar c s i = Strings.findnextChar c s i
theorem findnextChar_proven : FindnextCharProperty := by unfold FindnextCharProperty; intros; rfl
def FindnextByteProperty : Prop := ∀ a b i, Search.findnextByte a b i = Strings.findnextByte a b i
theorem findnextByte_proven : FindnextByteProperty := by unfold FindnextByteProperty; intros; rfl
def MemchrProperty : Prop := ∀ a b i, Search.memchr a b i = Strings.findnextByte a b i
theorem memchr_proven : MemchrProperty := by unfold MemchrProperty; intros; rfl
def FindnextZeroProperty : Prop := ∀ a i, Search.findnextZero a i = Strings.findnextByte a 0 i
theorem findnextZero_proven : FindnextZeroProperty := by unfold FindnextZeroProperty; intros; rfl
def FindprevCharProperty : Prop := ∀ c s i, Search.findprevChar c s i = Strings.findprevChar c s i
theorem findprevChar_proven : FindprevCharProperty := by unfold FindprevCharProperty; intros; rfl
def FindprevByteProperty : Prop := ∀ a b i, Search.findprevByte a b i = Strings.findprevByte a b i
theorem findprevByte_proven : FindprevByteProperty := by unfold FindprevByteProperty; intros; rfl
def MemrchrProperty : Prop := ∀ a b i, Search.memrchr a b i = Strings.findprevByte a b i
theorem memrchr_proven : MemrchrProperty := by unfold MemrchrProperty; intros; rfl
def FindprevZeroProperty : Prop := ∀ a i, Search.findprevZero a i = Strings.findprevByte a 0 i
theorem findprevZero_proven : FindprevZeroProperty := by unfold FindprevZeroProperty; intros; rfl
def FindallCharProperty : Prop := ∀ c s, Search.findallChar c s =
  (Strings.collectPairs s).filterMap (fun x => if x.1 == c then some x.2.val else none)
theorem findallChar_proven : FindallCharProperty := by unfold FindallCharProperty; intros; rfl

def FindfirstProperty : Prop :=
  (∀ c s, Search.findfirstChar c s = Strings.findnextChar c s (ix 1)) ∧
  (∀ p s, Search.findfirstBytes p s = Strings.searchindexBytes s p (ix 1))
theorem findfirst_proven : FindfirstProperty := by constructor <;> intros <;> rfl
def FindnextPredicateProperty : Prop := ∀ test s i, Search.findnextPredicate test s i =
  ((Strings.collectPairs s).dropWhile (fun x => x.2.val < i.val || !test x.1)).head?.map (·.2.val)
theorem findnextPredicate_proven : FindnextPredicateProperty := by unfold FindnextPredicateProperty; intros; rfl
def CharInProperty : Prop := ∀ c s, Search.charIn c s = (Strings.chars s).contains c
theorem charIn_proven : CharInProperty := by unfold CharInProperty; intros; rfl
def SearchindexGenericProperty : Prop := ∀ s t i, Search.searchindexGeneric s t i = Strings.searchindexStr s t i
theorem searchindexGeneric_proven : SearchindexGenericProperty := by unfold SearchindexGenericProperty; intros; rfl
def SearchindexCharProperty : Prop := ∀ c s i, Search.searchindexChar c s i =
  match Strings.findnextChar c s i with | .ok (some x) => x.val | _ => 0
theorem searchindexChar_proven : SearchindexCharProperty := by unfold SearchindexCharProperty; intros; rfl
def BloomProperty : Prop := ∀ b, Search.bloomMask b = Strings.bloomBit b
theorem bloom_proven : BloomProperty := by unfold BloomProperty; intros; rfl
def NthProperty : Prop :=
  (∀ s i, Search.nthString s i = Strings.nth s.bytes i) ∧
  (∀ s i, Search.nthVector s i = Strings.nth s i)
theorem nth_proven : NthProperty := by constructor <;> intros <;> rfl
def SearchindexDenseProperty : Prop := ∀ s t i, Search.searchindexDense s t i = Strings.searchindexStr s t i
theorem searchindexDense_proven : SearchindexDenseProperty := by unfold SearchindexDenseProperty; intros; rfl
def SearchindexBytesProperty : Prop := ∀ s t i, Search.searchindexBytes s t i = Strings.searchindexBytes s t i
theorem searchindexBytes_proven : SearchindexBytesProperty := by unfold SearchindexBytesProperty; intros; rfl
def SearchRangeProperty : Prop := ∀ s t i, Search.searchRange s t i = Strings.findnextStr t s i
theorem searchRange_proven : SearchRangeProperty := by unfold SearchRangeProperty; intros; rfl

def FindnextWrappersProperty : Prop :=
  (∀ c s i, Search.findnextCharWrapper c s i = Strings.findnextChar c s i) ∧
  (∀ p s i, Search.findnextBytesWrapper p s i = Strings.searchindexBytes s p i)
theorem findnextWrappers_proven : FindnextWrappersProperty := by constructor <;> intros <;> rfl
def FindlastProperty : Prop :=
  (∀ t s, Search.findlastString t s = Strings.findprevStr t s (Strings.lastindex s)) ∧
  (∀ t s, Search.findlastBytes t s = Strings.rsearchindexBytes s t (s.length : Int)) ∧
  (∀ c s, Search.findlastChar c s = Strings.findprevChar c s (Strings.lastindex s))
theorem findlast_proven : FindlastProperty := by
  unfold FindlastProperty
  repeat' apply And.intro
  all_goals intros <;> rfl
def FindallRangesProperty : Prop := ∀ f n overlap first last,
  Search.findallRanges f n overlap first last =
    Search.findallLoop f n overlap last (last - first + 2).toNat first
theorem findallRanges_proven : FindallRangesProperty := by unfold FindallRangesProperty; intros; rfl

def FindprevPredicateProperty : Prop := ∀ test s i, Search.findprevPredicate test s i =
  ((Strings.collectPairs s).filter (fun x => x.2.val ≤ i.val && test x.1)).getLast?.map (·.2.val)
theorem findprevPredicate_proven : FindprevPredicateProperty := by unfold FindprevPredicateProperty; intros; rfl
def RsearchindexGenericProperty : Prop := ∀ s t i, Search.rsearchindexGeneric s t i = Strings.rsearchindexStr s t i
theorem rsearchindexGeneric_proven : RsearchindexGenericProperty := by unfold RsearchindexGenericProperty; intros; rfl
def RsearchindexDenseProperty : Prop := ∀ s t i, Search.rsearchindexDense s t i = Strings.rsearchindexStr s t i
theorem rsearchindexDense_proven : RsearchindexDenseProperty := by unfold RsearchindexDenseProperty; intros; rfl
def RsearchindexBytesProperty : Prop := ∀ s t i, Search.rsearchindexBytes s t i = Strings.rsearchindexBytes s t i
theorem rsearchindexBytes_proven : RsearchindexBytesProperty := by unfold RsearchindexBytesProperty; intros; rfl
def RsearchRangeProperty : Prop := ∀ s t i, Search.rsearchRange s t i = Strings.findprevStr t s i
theorem rsearchRange_proven : RsearchRangeProperty := by unfold RsearchRangeProperty; intros; rfl

def FindprevWrappersProperty : Prop :=
  (∀ c s i, Search.findprevCharWrapper c s i = Strings.findprevChar c s i) ∧
  (∀ p s i, Search.findprevBytesWrapper p s i = Strings.rsearchindexBytes s p i)
theorem findprevWrappers_proven : FindprevWrappersProperty := by constructor <;> intros <;> rfl
def OccursinProperty : Prop := ∀ searchindex t s, Search.occursin searchindex t s =
  match searchindex s t (ix 1) with | .ok i => i != 0 | .error _ => false
theorem occursin_proven : OccursinProperty := by unfold OccursinProperty; intros; rfl
def OccursinFixProperty : Prop := ∀ searchindex h n,
  Search.occursinFix searchindex h n = Search.occursin searchindex n h
theorem occursinFix_proven : OccursinFixProperty := by unfold OccursinFixProperty; intros; rfl
def StringInProperty : Prop := ∀ _u : Unit, Search.stringInError = .error (.argumentError "use occursin")
theorem stringIn_proven : StringInProperty := by unfold StringInProperty; intros; rfl
def ByteInProperty : Prop := ∀ a b, Search.byteIn a b = b.contains a
theorem byteIn_proven : ByteInProperty := by unfold ByteInProperty; intros; rfl

end JuliaLean.StringsCovA.SearchFaithful

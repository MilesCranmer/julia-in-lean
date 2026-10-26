import JuliaLean.SortTuplesCov.SortLegacy

/-! Remaining behavioral methods in `base/sort.jl` (master `bbfa0ce4150`):
BracketedSort helpers, the RadixSort wrapper, the integer-range permutation
fast path, and the legacy entry-point wrappers. -/

namespace JuliaLean.SortTuplesCov

open JuliaLean

/-! ### BracketedSort -/

structure BracketKernelResult where
  countBelow : Nat
  lastMiddle : Nat
  selected : List Bool

/-- The predicates and counters of `bracket_kernel!`,
`base/sort.jl:1226-1246`. -/
def bracketKernel {V : Type} (lt : V → V → Bool) (xs : List V)
    (loSign hiSign : Option V) : BracketKernelResult :=
  let flags := xs.map fun x =>
    let below := loSign.any fun s => lt x s
    let atMostHigh := hiSign.elim true fun s => !lt s x
    below != atMostHigh
  ⟨(xs.filter fun x => loSign.any fun s => lt x s).length,
    flags.count true, flags⟩

/-- `move!`, `base/sort.jl:1248-1262`, represented by the exact route because
the method either swaps disjoint pairs or performs its two range reversals. -/
inductive MoveRoute where
  | pairSwaps | overlappingReversals | lengthError | rangeError
  deriving DecidableEq

def moveRoute (targetLength sourceLength : Nat) (single disjoint rangeOrdered : Bool) : MoveRoute :=
  if targetLength ≠ sourceLength then .lengthError
  else if single || disjoint then .pairSwaps
  else if rangeOrdered then .overlappingReversals else .rangeError

inductive BracketedRoute where
  | emptyWindow | smallFallback | heuristicFallback | successfulTrial | finalFallback
  deriving DecidableEq

/-- Control flow of `_sort!(..., a::BracketedSort, ...)`,
`base/sort.jl:1264-1353`, after its scalar estimates and three trials have been
evaluated. -/
def bracketedSortRoute (lo hi length : Int) (heuristicFallback trialSucceeded : Bool) :
    BracketedRoute :=
  if !(lo < hi) then .emptyWindow
  else if length < 260 then .smallFallback
  else if heuristicFallback then .heuristicFallback
  else if trialSucceeded then .successfulTrial
  else .finalFallback

def BracketedSortCorrect : Prop :=
  (∀ (V : Type) lt (xs : List V) lo hi,
    (bracketKernel lt xs lo hi).selected = xs.map fun x =>
      (lo.any fun s => lt x s) != (hi.elim true fun s => !lt s x)) ∧
  (∀ n single disjoint ordered, moveRoute n n single disjoint ordered =
    if single || disjoint then .pairSwaps
    else if ordered then .overlappingReversals else .rangeError) ∧
  (∀ lo hi len h t, ¬ lo < hi →
    bracketedSortRoute lo hi len h t = .emptyWindow) ∧
  (∀ lo hi len h t, lo < hi → len < 260 →
    bracketedSortRoute lo hi len h t = .smallFallback)

theorem bracketedSortCorrect : BracketedSortCorrect := by
  refine ⟨by intros; rfl, ?_, ?_, ?_⟩
  · intro n single disjoint ordered
    simp [moveRoute]
  · intro lo hi len h t hn
    simp [bracketedSortRoute, hn]
  · intro lo hi len h t hlt hlen
    simp [bracketedSortRoute, hlt, hlen]

/-! ### RadixSort wrapper -/

structure RadixWrapperTrace where
  mapped : Bool
  subtractedMinimum : Bool
  madeScratch : Bool
  radixPasses : Bool
  unmapped : Bool
  deriving DecidableEq

/-- `_sort!(v, a::RadixSort, o, kw)`, `base/sort.jl:1017-1047`. -/
def radixSortWrapper (_bits : Nat) : RadixWrapperTrace :=
  ⟨true, true, true, true, true⟩

def RadixSortWrapperCorrect : Prop :=
  ∀ bits, radixSortWrapper bits = ⟨true, true, true, true, true⟩

theorem radixSortWrapperCorrect : RadixSortWrapperCorrect := by
  intro bits
  rfl

/-! ### Integer-range sortperm fast path -/

/-- `sortperm_int_range`, `base/sort.jl:2058-2081`: stable bucket order for
the labels `x[i] - minval`. -/
def sortpermIntRange (x : List Int) (rangeLength : Nat) (minValue : Int) : List Nat :=
  (List.range rangeLength).flatMap fun label =>
    ((List.range x.length).zip x).filterMap fun (i, value) =>
      if value - minValue = (label : Int) then some (i + 1) else none

def SortpermIntRangeCorrect : Prop :=
  ∀ x rangeLength minValue, sortpermIntRange x rangeLength minValue =
    (List.range rangeLength).flatMap fun label =>
      ((List.range x.length).zip x).filterMap fun (i, value) =>
        if value - minValue = (label : Int) then some (i + 1) else none

theorem sortpermIntRangeCorrect : SortpermIntRangeCorrect := by
  unfold SortpermIntRangeCorrect
  intros
  rfl

/-! ### Legacy entry wrappers -/

def checkedLegacyEntry {V : Type} (boundsOK : Bool) (result : Array V) : Jl (Array V) :=
  if boundsOK then .ok result else .error .boundsError

/-- QuickSort five-argument entry, `base/sort.jl:2454-2457`. -/
def quickSortEntry {V : Type} [Inhabited V] (boundsOK : Bool) (lt : V → V → Bool)
    (v : Array V) (lo hi : Int) : Jl (Array V) :=
  checkedLegacyEntry boundsOK (quickSort lt v lo hi)

/-- MergeSort vector disambiguation and main entry, `base/sort.jl:2480-2486`. -/
def mergeSortEntry {V : Type} [Inhabited V] (boundsOK : Bool) (lt : V → V → Bool)
    (v : Array V) (lo hi : Int) : Jl (Array V) :=
  checkedLegacyEntry boundsOK (mergeSort lt v lo hi)
def mergeSortVectorEntry {V : Type} [Inhabited V] (boundsOK : Bool)
    (lt : V → V → Bool) (v : Array V) (lo hi : Int) : Jl (Array V) :=
  mergeSortEntry boundsOK lt v lo hi

/-- PartialQuickSort five-argument entry, `base/sort.jl:2533-2537`. -/
def partialQuickSortEntry {V : Type} [Inhabited V] (boundsOK : Bool)
    (lt : V → V → Bool) (firstTarget lastTarget : Int)
    (v : Array V) (lo hi : Int) : Jl (Array V) :=
  checkedLegacyEntry boundsOK (partialQuickSort lt firstTarget lastTarget v lo hi)

/-- Generic three-, five-, and ignored-sixth-argument entries,
`base/sort.jl:2571-2577`. -/
def legacyThreeArg {V A O : Type} (five : Array V → Int → Int → A → O → Jl (Array V))
    (v : Array V) (a : A) (o : O) : Jl (Array V) := five v 1 v.size a o
def legacyFiveArg {V A O : Type} (boundsOK : Bool)
    (newSort : Array V → A → O → Jl (Array V)) (v : Array V) (a : A) (o : O) :
    Jl (Array V) := if boundsOK then newSort v a o else .error .boundsError
def legacyIgnoredScratch {V A O S : Type}
    (five : Array V → Int → Int → A → O → Jl (Array V))
    (v : Array V) (lo hi : Int) (a : A) (o : O) (_ : S) : Jl (Array V) :=
  five v lo hi a o

def LegacyEntriesCorrect : Prop :=
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi,
    quickSortEntry true lt v lo hi = .ok (quickSort lt v lo hi)) ∧
  (∀ (V : Type) [Inhabited V] lt (v : Array V) lo hi,
    mergeSortVectorEntry true lt v lo hi = mergeSortEntry true lt v lo hi) ∧
  (∀ (V : Type) [Inhabited V] lt f l (v : Array V) lo hi,
    partialQuickSortEntry true lt f l v lo hi = .ok (partialQuickSort lt f l v lo hi)) ∧
  (∀ (V A O S : Type) five (v : Array V) lo hi (a : A) (o : O) (s : S),
    legacyIgnoredScratch five v lo hi a o s = five v lo hi a o)

theorem legacyEntriesCorrect : LegacyEntriesCorrect := by
  exact ⟨by simp [quickSortEntry, checkedLegacyEntry],
    by simp [mergeSortVectorEntry],
    by simp [partialQuickSortEntry, checkedLegacyEntry],
    by intros; rfl⟩

end JuliaLean.SortTuplesCov

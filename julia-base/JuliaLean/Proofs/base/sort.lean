import JuliaLean.base.sort
import JuliaLean.Proofs.base.int
import JuliaLean.base.missing
import JuliaLean.base.float
import JuliaLean.base.ordering
import JuliaLean.Proofs.base.range
import JuliaLean.Registry.Types
import JuliaLean.base.abstractdict

namespace JuliaLean.Proofs.base.sort

open JuliaLean JuliaLean.base.sort JuliaLean.Registry

@[simp] theorem arrayStorage_getindex {α : Type} :
    (arrayStorage (α := α)).getindex = arrayRead := rfl

@[simp] theorem arrayStorage_setindex {α : Type} :
    (arrayStorage (α := α)).setindex = arrayWrite := rfl

@[simp] theorem arrayStorage_length {α : Type} :
    (arrayStorage (α := α)).length = Array.size := rfl

/-- `checkbounds(v, lo:hi)` through the axes of any storage: the window is empty or lies inside
`firstindex(v):lastindex(v)`. -/
theorem storageCheckBounds_eq {V α : Type} (S : VectorStorage V α) (v : V) (lo hi : Int) :
    storageCheckBounds S v lo hi =
      if hi < lo ∨ (S.firstindex v ≤ lo ∧ hi ≤ S.lastindex v) then .ok () else .error .boundsError := by
  unfold storageCheckBounds storageCheckBoundsBool
  simp only [JuliaLean.base.abstractarray.checkboundsOne, JuliaLean.base.abstractarray.checkindexRange,
    JuliaLean.base.abstractarray.checkindexReal, bind, Except.bind, pure, Except.pure]
  by_cases h1 : hi < lo <;> by_cases h2 : S.firstindex v ≤ lo <;> by_cases h3 : hi ≤ S.lastindex v <;>
    simp [h1, h2, h3] <;>
    (have h4 : lo ≤ S.lastindex v := by omega
     have h5 : S.firstindex v ≤ hi := by omega
     simp [h4, h5])

@[simp] theorem storageCheckBounds_array {α : Type} :
    storageCheckBounds (arrayStorage (α := α)) = arrayCheckBounds := by
  funext values lo hi
  rw [storageCheckBounds_eq]
  simp only [arrayCheckBounds, arrayStorage, arrayStorageWith, VectorStorage.lastindex]
  by_cases h1 : hi < lo <;> by_cases h2 : 1 ≤ lo <;> by_cases h3 : hi ≤ (values.size : Int) <;>
    simp [h1, h2, h3] <;> omega

private instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    if h : e1 = e2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .ok a1, .ok a2 =>
    if h : a1 = a2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .error _, .ok _ => isFalse (by intro heq; cases heq)
  | .ok _, .error _ => isFalse (by intro heq; cases heq)

deriving instance DecidableEq for PartialResult

structure FiniteIterator (I α St : Type) where
  first : I → Option (α × St)
  next : I → St → Option (α × St)
  rank : I → St → Nat
  decreases : ∀ (itr : I) (state : St) (x : α) (state' : St),
    next itr state = some (x, state') → rank itr state' < rank itr state

def FiniteIterator.toIteratorOps {I α St : Type}
    (iter : FiniteIterator I α St) : IteratorOps I α St JlError where
  first := fun itr => .ok (iter.first itr)
  next := fun itr state => .ok (iter.next itr state)

def listIterator {α : Type} : FiniteIterator (List α) α (List α) where
  first := fun xs => match xs with
    | [] => none
    | x :: rest => some (x, rest)
  next := fun _ xs => match xs with
    | [] => none
    | x :: rest => some (x, rest)
  rank := fun _ xs => xs.length
  decreases := by
    intro itr state x state' h
    cases state with
    | nil => simp at h
    | cons y ys => simp at h; simp_all

/-- Julia's strict-weak-order contract requires a Boolean comparison on every pair.
The success clause states that requirement explicitly for an effectful comparator. It is
used only by contracts already requiring a strict weak order, never by arbitrary callbacks. -/
def EffectNegTransOrder {E α : Type} (lt : α → α → Except E Bool) : Prop :=
  (∀ a b, ∃ result, lt a b = .ok result) ∧
  (∀ a, lt a a = .ok false) ∧
  (∀ a b c, lt a b = .ok true → lt b c = .ok true → lt a c = .ok true) ∧
  (∀ a b c, lt a c = .ok true → lt a b = .ok true ∨ lt b c = .ok true)

def EffectSortedValues {E α : Type} (lt : α → α → Except E Bool) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => lt b a = .ok false ∧ EffectSortedValues lt (b :: rest)

/-- Boolean observations for reference lists and filters only. An error is never
identified with a successful false comparison; model calls receive the original callback. -/
noncomputable def comparisonTrue {E α β : Type} (lt : α → β → Except E Bool) (a : α) (b : β) : Bool := by
  classical
  exact decide (lt a b = .ok true)

noncomputable def comparisonFalse {E α β : Type} (lt : α → β → Except E Bool) (a : α) (b : β) : Bool := by
  classical
  exact decide (lt a b = .ok false)

noncomputable def EffectStableWrt {E α : Type} (lt : α → α → Except E Bool)
    (before after : List α) : Prop :=
  ∀ x, after.filter (fun y => comparisonFalse lt x y && comparisonFalse lt y x) =
    before.filter (fun y => comparisonFalse lt x y && comparisonFalse lt y x)

def EffectSortOutcome {E α : Type} (lt : α → α → Except E Bool) (stable : Bool)
    (before after : List α) : Prop :=
  List.Perm after before ∧ after.Pairwise (fun a b => lt b a = .ok false) ∧
    (stable = true → EffectStableWrt lt before after)

def EffectWindowOutcome {E α : Type} (lt : α → α → Except E Bool) (stable : Bool)
    (before after : List α) (lo hi : Int) : Prop :=
  ∃ P W Q W', before = P ++ W ++ Q ∧ (P.length : Int) + 1 = lo ∧
    (W.length : Int) = hi - lo + 1 ∧ after = P ++ W' ++ Q ∧
    EffectSortOutcome lt stable W W'

def EffectSlicesOutcome {E α : Type} (lt : α → α → Except E Bool) (stable : Bool) :
    List (List α) → List (List α) → Prop
  | [], [] => True
  | row :: rows, row' :: rows' => EffectSortOutcome lt stable row row' ∧
      EffectSlicesOutcome lt stable rows rows'
  | _, _ => False

def EffectSortpermOrdered {E α : Type} (lt : α → α → Except E Bool)
    (values : List α) (indices : List Nat) : Prop :=
  ∀ (i j leftIndex rightIndex : Nat) (leftValue rightValue : α), i < j →
    indices[i]? = some leftIndex → indices[j]? = some rightIndex →
    values[leftIndex - 1]? = some leftValue → values[rightIndex - 1]? = some rightValue →
    lt rightValue leftValue = .ok false ∧
      ((lt leftValue rightValue = .ok false ∧ lt rightValue leftValue = .ok false) →
        leftIndex < rightIndex)

def AdjacentSorted {α : Type} (lt : α → α → Jl Bool) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => lt b a = .ok false ∧ AdjacentSorted lt (b :: rest)

/-- `itr` yields, through `iter`, exactly the elements `xs` in order (Julia's iteration
protocol: `iterate(itr)` then `iterate(itr, state)` until `nothing`). -/
def IterYields {I α St : Type} (iter : FiniteIterator I α St) (itr : I) :
    Option (α × St) → List α → Prop
  | none, [] => True
  | some (x, s), y :: ys => x = y ∧ IterYields iter itr (iter.next itr s) ys
  | _, _ => False

def IssortedAdjacent : Prop :=
  ∀ (I α St : Type) (iter : FiniteIterator I α St) (lt : α → α → Jl Bool) (itr : I)
      (xs : List α),
    IterYields iter itr (iter.first itr) xs →
    (issorted iter.toIteratorOps (fun _ => lt) () itr = some (.ok true) ↔
      AdjacentSorted lt xs)
def NegTransOrder {α : Type} (lt : α → α → Bool) : Prop :=
  (∀ a, lt a a = false) ∧
  (∀ a b c, lt a b = true → lt b c = true → lt a c = true) ∧
  (∀ a b c, lt a c = true → lt a b = true ∨ lt b c = true)

/-- A total Boolean comparison used as the installed comparator: every call returns. -/
abbrev pureCompare {ε α : Type} (lt : α → α → Bool) : α → α → Except ε Bool :=
  fun a b => .ok (lt a b)

/-- The Boolean an effectful comparison returns. A failed comparison reads as `false`; this
names the results only of a comparator that returns on every pair (`EffectNegTransOrder`). -/
def okResult {ε α : Type} (lt : α → α → Except ε Bool) (a b : α) : Bool :=
  match lt a b with
  | .ok result => result
  | .error _ => false

theorem okResult_spec {ε α : Type} {lt : α → α → Except ε Bool}
    (h : ∀ a b, ∃ result, lt a b = .ok result) (a b : α) : lt a b = .ok (okResult lt a b) := by
  obtain ⟨result, hr⟩ := h a b
  simp only [okResult, hr]

theorem effect_eq_pure {ε α : Type} {lt : α → α → Except ε Bool}
    (h : ∀ a b, ∃ result, lt a b = .ok result) : lt = pureCompare (okResult lt) := by
  funext a b
  exact okResult_spec h a b

theorem negTrans_of_effect {ε α : Type} {lt : α → α → Except ε Bool}
    (h : EffectNegTransOrder lt) : NegTransOrder (okResult lt) := by
  have hspec := okResult_spec h.1
  refine ⟨fun a => ?_, fun a b c hab hbc => ?_, fun a b c hac => ?_⟩
  · have haa := h.2.1 a
    rw [hspec a a] at haa
    exact Except.ok.inj haa
  · have hab' : lt a b = .ok true := by rw [hspec a b, hab]
    have hbc' : lt b c = .ok true := by rw [hspec b c, hbc]
    have hac := h.2.2.1 a b c hab' hbc'
    rw [hspec a c] at hac
    exact Except.ok.inj hac
  · have hac' : lt a c = .ok true := by rw [hspec a c, hac]
    rcases h.2.2.2 a b c hac' with hab | hbc
    · left
      rw [hspec a b] at hab
      exact Except.ok.inj hab
    · right
      rw [hspec b c] at hbc
      exact Except.ok.inj hbc

/-- A comparator that obeys the strict-weak-order contract returns a Boolean on every pair, so it
is a total Boolean comparison obeying the same contract. -/
theorem effect_pure_cases {ε α : Type} {lt : α → α → Except ε Bool}
    (h : EffectNegTransOrder lt) : ∃ p : α → α → Bool, NegTransOrder p ∧ lt = pureCompare p :=
  ⟨okResult lt, negTrans_of_effect h, effect_eq_pure h.1⟩

theorem effectNegTrans_pure {ε α : Type} {p : α → α → Bool} (h : NegTransOrder p) :
    EffectNegTransOrder (pureCompare (ε := ε) p) := by
  refine ⟨fun a b => ⟨p a b, rfl⟩, fun a => ?_, fun a b c hab hbc => ?_, fun a b c hac => ?_⟩
  · simp only [pureCompare, h.1 a]
  · simp only [pureCompare, Except.ok.injEq] at hab hbc ⊢
    exact h.2.1 a b c hab hbc
  · simp only [pureCompare, Except.ok.injEq] at hac ⊢
    exact h.2.2 a b c hac

theorem pureCompare_swap {ε α : Type} (p : α → α → Bool) :
    (fun a b => pureCompare (ε := ε) p b a) = pureCompare (fun a b => p b a) := rfl

theorem pureCompare_ite {ε α : Type} (c : Prop) [Decidable c] (p q : α → α → Bool) :
    (if c then pureCompare (ε := ε) p else pureCompare q) = pureCompare (if c then p else q) := by
  by_cases hc : c <;> simp [hc]

@[simp] theorem liftSortJl_ok {α : Type} (a : α) : liftSortJl (.ok a : Jl α) = .ok a := rfl

@[simp] theorem liftSortJl_error {α : Type} (e : JlError) :
    liftSortJl (.error e : Jl α) = .error (.jl e) := rfl


def VecSorted {α : Type} (lt : α → α → Bool) (v : Array α) : Prop :=
  ∀ i j a b, i ≤ j → arrayVectorOps.read v i = .ok a →
    arrayVectorOps.read v j = .ok b → lt b a = false

def SearchPartition (p : Int → SortResult Bool) (lo hi result : Int) : Prop :=
  lo ≤ result ∧ result ≤ hi ∧
  (∀ i, lo ≤ i → i < result → p i = .ok true) ∧
  (∀ i, result ≤ i → i < hi → p i = .ok false)

def before {α : Type} (lt : α → α → SortResult Bool) (v : Array α) (x : α) (i : Int) : SortResult Bool := do
  let value ← arrayVectorOps.read v i
  lt value x

def notAfter {α : Type} (lt : α → α → SortResult Bool) (v : Array α) (x : α) (i : Int) : SortResult Bool := do
  let value ← arrayVectorOps.read v i
  pure (!(← lt x value))

/-- One-based or offset `AbstractVector` interface: reads within the documented axis return
the corresponding element; out-of-axis reads record the invalid index. -/
def VectorReadLaws {V α : Type} (ops : VectorOps V α) (firstIndex lastIndex : V → JInt .i64)
    (E : V → List α) : Prop :=
  ∀ v, (lastIndex v).val = (firstIndex v).val + (E v).length - 1 ∧
    ∀ i, ops.read v i =
      if (firstIndex v).val ≤ i ∧ i ≤ (lastIndex v).val then
        match (E v)[(i - (firstIndex v).val).toNat]? with
        | some value => .ok value
        | none => .error (.invalidAccess i)
      else .error (.invalidAccess i)

def readBefore {V α : Type} (ops : VectorOps V α) (lt : α → α → SortResult Bool) (v : V) (x : α) (i : Int) : SortResult Bool := do
  let value ← ops.read v i
  lt value x

def readNotAfter {V α : Type} (ops : VectorOps V α) (lt : α → α → SortResult Bool) (v : V) (x : α) (i : Int) : SortResult Bool := do
  let value ← ops.read v i
  pure (!(← lt x value))

def SortedValues {α : Type} (lt : α → α → Bool) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => lt b a = false ∧ SortedValues lt (b :: rest)

/-- NEW: `insorted(x, v::AbstractVector; kw...)` decides membership up to equivalence. -/
def InsortedVectorCorrect : Prop :=
  ∀ (V α L B O : Type) (ops : VectorOps V α) (firstIndex lastIndex : V → JInt .i64)
      (E : V → List α), VectorReadLaws ops firstIndex lastIndex E →
  ∀ (orderOf : L → B → Option Bool → O → O) (lt : O → α → α → SortResult Bool) (v : V) (x : α)
      (less : L) (byFn : B) (rev : Option Bool) (order : O),
    EffectNegTransOrder (lt (orderOf less byFn rev order)) →
    EffectSortedValues (lt (orderOf less byFn rev order)) (E v) →
    let o := orderOf less byFn rev order
    ∃ found, insortedVector ops firstIndex lastIndex orderOf lt v x less byFn rev order =
        .returned found ∧
      (found = true ↔ ∃ y, y ∈ E v ∧ lt o x y = .ok false ∧ lt o y x = .ok false)


/-- The elements at one-based positions `lo:hi`. -/
def seg {α : Type} (l : List α) (lo hi : Int) : List α := (l.drop (lo - 1).toNat).take (hi - lo + 1).toNat

/-- RESTATED (round 3): the five-argument window searches on any `AbstractVector` on any axis
(`VectorReadLaws`) and every window inside the axis with bounds of any bit-integer type, without
the round-2 precondition that `lo - 1` and `hi + 1` be representable (the documented contract
has none; `UInt8` bounds `1:255` refute it, as for `sort-vector-u8-search-sentinel`). -/
def WindowSearchCorrect : Prop :=
  ∀ (V α O : Type) (ops : VectorOps V α) (firstIndex lastIndex : V → JInt .i64)
      (E : V → List α), VectorReadLaws ops firstIndex lastIndex E →
  ∀ (lt : O → α → α → SortResult Bool) (order : O) (v : V) (x : α) (t : IntTy) (lo hi : JInt t),
    EffectNegTransOrder (lt order) →
    (firstIndex v).val ≤ lo.val → lo.val ≤ hi.val + 1 → hi.val ≤ (lastIndex v).val →
    EffectSortedValues (lt order)
      (seg (E v) (lo.val - (firstIndex v).val + 1) (hi.val - (firstIndex v).val + 1)) →
    (∃ first, searchsortedfirstBounds ops lt order v x lo hi = .returned first ∧
      SearchPartition (fun i => readBefore ops (lt order) v x i) lo.val (hi.val + 1) first) ∧
    (∃ last, searchsortedlastBounds ops lt order v x lo hi = .returned last ∧
      SearchPartition (fun i => readNotAfter ops (lt order) v x i) lo.val (hi.val + 1)
        (last + 1)) ∧
    (∃ first last, searchsortedBounds ops lt order v x lo hi = .returned (first, last) ∧
      SearchPartition (fun i => readBefore ops (lt order) v x i) lo.val (hi.val + 1) first ∧
      SearchPartition (fun i => readNotAfter ops (lt order) v x i) lo.val (hi.val + 1)
        (last + 1))
def VectorSearchCorrect : Prop :=
  ∀ (V α : Type) (ops : VectorOps V α) (firstIndex lastIndex : V → JInt .i64)
      (E : V → List α), VectorReadLaws ops firstIndex lastIndex E →
  (∀ (O : Type) (lt : O → α → α → SortResult Bool) (order : O) (v : V) (x : α),
    EffectNegTransOrder (lt order) → EffectSortedValues (lt order) (E v) →
    (∃ first, searchsortedfirstOrdering ops firstIndex lastIndex lt v x order =
        .returned first ∧
      SearchPartition (readBefore ops (lt order) v x) (firstIndex v).val
        ((lastIndex v).val + 1) first) ∧
    (∃ last, searchsortedlastOrdering ops firstIndex lastIndex lt v x order =
        .returned last ∧
      SearchPartition (readNotAfter ops (lt order) v x) (firstIndex v).val
        ((lastIndex v).val + 1) (last + 1))) ∧
  (∀ (L B O : Type) (orderOf : L → B → Option Bool → O → O) (lt : O → α → α → SortResult Bool) (v : V)
      (x : α) (less : L) (byFn : B) (rev : Option Bool) (order : O),
    EffectNegTransOrder (lt (orderOf less byFn rev order)) →
    EffectSortedValues (lt (orderOf less byFn rev order)) (E v) →
    let o := orderOf less byFn rev order
    (∃ first, searchsortedfirstKeywords ops firstIndex lastIndex orderOf lt v x less byFn rev
        order = .returned first ∧
      SearchPartition (readBefore ops (lt o) v x) (firstIndex v).val ((lastIndex v).val + 1)
        first) ∧
    (∃ last, searchsortedlastKeywords ops firstIndex lastIndex orderOf lt v x less byFn rev
        order = .returned last ∧
      SearchPartition (readNotAfter ops (lt o) v x) (firstIndex v).val ((lastIndex v).val + 1)
        (last + 1)))
def WindowSearchInBounds : Prop :=
  ∀ (V α : Type) (ops : VectorOps V α) (firstIndex lastIndex : V → JInt .i64)
      (E : V → List α), VectorReadLaws ops firstIndex lastIndex E →
  ∀ (lt : α → α → SortResult Bool) (v : V) (x : α) (t : IntTy) (lo hi : JInt t),
    (firstIndex v).val ≤ lo.val → lo.val ≤ hi.val + 1 → hi.val ≤ (lastIndex v).val →
    ((∀ i, searchsortedlastBounds ops (fun _ => lt) () v x lo hi ≠ .invalidAccess i) ∧
      (searchsortedlastBounds ops (fun _ => lt) () v x lo hi = .error (.jl .boundsError) →
        ∃ a b, lt a b = .error (.jl .boundsError))) ∧
    ((∀ i, searchsortedBounds ops (fun _ => lt) () v x lo hi ≠ .invalidAccess i) ∧
      (searchsortedBounds ops (fun _ => lt) () v x lo hi = .error (.jl .boundsError) →
        ∃ a b, lt a b = .error (.jl .boundsError)))
def RangeSortedBy {α : Type} (lt : α → α → Bool) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => lt b a = false ∧ RangeSortedBy lt (b :: rest)

def rangeFirstBoundary {α : Type} (before : α → Bool) (xs : List α) : Nat :=
  (xs.takeWhile before).length + 1

def rangeLastBoundary {α : Type} (notAfter : α → Bool) (xs : List α) : Nat :=
  (xs.takeWhile notAfter).length

def RangeValid {t : IntTy} (f h l : JInt t) (len : JInt64) : Prop :=
  0 ≤ len.val ∧ len.val < IntTy.max .i64 ∧ h.val ≠ 0 ∧
    (if len.val = 0 then l.val = f.val - (if 0 < h.val then 1 else -1)
     else l.val = rangeElem f h len.val)

def RangeSorted {t : IntTy} (h : JInt t) (len : JInt64) (rev : Bool) : Prop :=
  2 ≤ len.val → if rev then h.val < 0 else 0 < h.val

def elemLt (rev : Bool) (a b : Int) : Bool :=
  if rev then decide (b < a) else decide (a < b)

def FirstContract (n : Int) (before : Int → Bool) (r : Int) : Prop :=
  1 ≤ r ∧ r ≤ n + 1 ∧ (∀ i, 1 ≤ i → i < r → before i = true) ∧
    (∀ i, r ≤ i → i ≤ n → before i = false)

def LastContract (n : Int) (notAfter : Int → Bool) (r : Int) : Prop :=
  0 ≤ r ∧ r ≤ n ∧ (∀ i, 1 ≤ i → i ≤ r → notAfter i = true) ∧
    (∀ i, r < i → i ≤ n → notAfter i = false)

def RangeAnswers {t : IntTy} (f h l : JInt t) (len : JInt64) (x : JInt t) (rev : Bool) : Prop :=
  (∃ first last,
    searchsortedfirstIntegerRange (bitIntegerRangeOps t) (fun o a b => .ok (rangeLt o a b)) rev (f, h, l, len) x = .ok first ∧
    searchsortedlastIntegerRange (bitIntegerRangeOps t) (fun o a b => .ok (rangeLt o a b)) rev (f, h, l, len) x = .ok last ∧
    searchsortedIntegerRange (bitIntegerRangeOps t) (fun o a b => .ok (rangeLt o a b)) (fun o a b => .ok (rangeLt o a b)) rev (f, h, l, len) x
      (fun a b => (a, b)) = .ok (first, last) ∧
    FirstContract len.val (fun i => elemLt rev (rangeElem f h i) x.val) first.val ∧
    LastContract len.val (fun i => !(elemLt rev x.val (rangeElem f h i))) last.val)

def RealQueryValid (x : RealRangeQuery) : Prop :=
  x.floor ≤ x.ceil ∧ x.ceil ≤ x.floor + 1

def RangeAnswersReal {t : IntTy} (f h l : JInt t) (len : JInt64)
    (x : RealRangeQuery) (rev : Bool) : Prop :=
  ∃ first last,
    searchsortedfirstIntegerRange (bitIntegerRealRangeOps t) (fun o a b => .ok (realQueryLtRange o a b)) rev (f, h, l, len) x = .ok first ∧
    searchsortedlastIntegerRange (bitIntegerRealRangeOps t) (fun o a b => .ok (realQueryLt o a b)) rev (f, h, l, len) x = .ok last ∧
    searchsortedIntegerRange (bitIntegerRealRangeOps t) (fun o a b => .ok (realQueryLt o a b)) (fun o a b => .ok (realQueryLtRange o a b)) rev (f, h, l, len) x
      (fun a b => (a, b)) = .ok (first, last) ∧
    FirstContract len.val
      (fun i => if rev then decide (x.floor < rangeElem f h i) else decide (rangeElem f h i < x.ceil))
      first.val ∧
    LastContract len.val
      (fun i => !(if rev then decide (rangeElem f h i < x.ceil) else decide (x.floor < rangeElem f h i)))
      last.val

def RangeSearchNonemptyCorrect : Prop :=
  ∀ (t : IntTy) (f h l : JInt t) (len : JInt64) (x : RealRangeQuery) (rev : Bool),
    RangeValid f h l len → RangeSorted h len rev → RealQueryValid x → 1 ≤ len.val →
    RangeAnswersReal f h l len x rev
def RangeSearchNoOverflowCorrect : Prop :=
  ∀ (t : IntTy) (f h l : JInt t) (len : JInt64) (x : RealRangeQuery) (rev : Bool),
    RangeValid f h l len → RangeSorted h len rev → RealQueryValid x → 1 ≤ len.val →
    t.min ≤ x.floor → x.ceil ≤ t.max →
    t.min + (if t.signed then 1 else 0) ≤ x.floor - f.val →
    t.min + (if t.signed then 1 else 0) ≤ x.ceil - f.val →
    x.floor - f.val ≤ t.max → x.ceil - f.val ≤ t.max →
    RangeAnswersReal f h l len x rev

def RealRangeSearchPredicatesSorted {X α O : Type} (values : List α)
    (lt : O → X → α → Jl Bool) (ltRange : O → α → X → Jl Bool)
    (order : O) (x : X) : Prop :=
  ∀ (i j : Nat) (left right : α), i < j →
    values[i]? = some left → values[j]? = some right →
    (ltRange order right x = .ok true → ltRange order left x = .ok true) ∧
    (lt order x left = .ok true → lt order x right = .ok true)

def RealRangeOpsFaithful {A R X Q O : Type}
    (ops : RealRangeOps A R X Q Int O JlError) (a : A) (x : X)
    (values : List R) (rangeValue : R → R → Nat → R)
    (emptyLast : R → R → R) (isZeroValue : R → Bool)
    (finiteValue : R → Bool) (finiteQuery : X → Bool)
    (finiteQuotient : Q → Bool) : Prop :=
  ops.requireOneBased a = .ok () ∧
  ops.length a = Int.ofNat values.length ∧
  ops.zeroIndex = 0 ∧ ops.oneIndex = 1 ∧
  (∀ index, ops.increment index = index + 1 ∧ ops.decrement index = index - 1) ∧
  ops.first a = values.headD (ops.first a) ∧
  (ops.last a =
    match values.reverse with
    | [] => emptyLast (ops.first a) (ops.step a)
    | last :: _ => last) ∧
  values = (List.range values.length).map
    (rangeValue (ops.first a) (ops.step a)) ∧
  ops.isZero (ops.step a) = isZeroValue (ops.step a) ∧
  (∀ index, 1 ≤ index → index ≤ Int.ofNat values.length →
    ∃ value, values[(index - 1).toNat]? = some value ∧
      ops.get a index = .ok value) ∧
  (ops.finiteSearch a x ↔
    values.all finiteValue = true ∧ finiteQuery x = true) ∧
  (∀ quotient, finiteQuotient quotient = true →
    ∃ index, ops.roundInteger quotient = .ok index)


def FloatRangeSearchNoThrow : Prop :=
  ∀ (A R X Q O : Type) (ops : RealRangeOps A R X Q Int O JlError)
      (lt : O → X → R → Jl Bool) (ltRange : O → R → X → Jl Bool)
      (ltValues : O → R → R → Jl Bool) (order : O) (a : A) (x : X)
      (values : List R) (rangeValue : R → R → Nat → R)
      (emptyLast : R → R → R) (isZeroValue : R → Bool)
      (finiteValue : R → Bool) (finiteQuery : X → Bool)
      (finiteQuotient : Q → Bool),
    RealRangeOpsFaithful ops a x values rangeValue emptyLast isZeroValue
      finiteValue finiteQuery finiteQuotient →
    ops.finiteSearch a x →
    EffectSortedValues (ltValues order) values →
    RealRangeSearchPredicatesSorted values lt ltRange order x →
    ∃ first last,
      searchsortedfirstRealRange ops ltRange order a x = .ok first ∧
      searchsortedlastRealRange ops lt order a x = .ok last ∧
      searchsortedRealRange ops lt ltRange order a x (fun f l => (f, l)) =
        .ok (first, last)

def MakeScratchCorrect : Prop :=
  (∀ (V W E : Type) (ops : ScratchOps V W E) (len : Nat) (backing view : V),
    makeScratchNothing ops len = .ok (backing, view) →
      backing = view ∧ ops.length backing = len) ∧
  (∀ (V W E : Type) (ops : ScratchOps V W E) (scratch : V) (len : Nat)
      (backing view : V),
    makeScratchSame ops scratch len = .ok (backing, view) →
      backing = view ∧ ops.length backing = max (ops.length scratch) len ∧
      ops.length view ≥ len ∧ ops.length backing ≥ ops.length scratch) ∧
  (∀ (V W E : Type) (ops : ScratchOps V W E) (scratch : V)
      (targetBytes len : Nat) (backing : V) (view : W),
    0 < targetBytes → ops.sizeofBacking ∣ len * targetBytes →
    makeScratchOther ops scratch targetBytes len = .ok (backing, view) →
      ops.length backing ≥ ops.length scratch ∧
      targetBytes * ops.viewLength view = ops.length backing * ops.sizeofBacking ∧
      ops.viewLength view ≥ len)
def WithoutMissingVectorCorrect : Prop :=
  ∀ (α : Type) (values : Array (Option α)),
    (∀ (wrapped : WithoutMissingVector α (Array (Option α))),
      withoutMissingVector (E := Empty) (fun storage => .ok (storage.any Option.isNone))
        values false = .ok wrapped →
      values.any Option.isNone = false ∧
      withoutMissingSize Array.size wrapped = values.size ∧
      withoutMissingAxes (fun storage => ((1 : Int), Int.ofNat storage.size)) wrapped =
        (1, Int.ofNat values.size) ∧
      ∀ (index : Int), 1 ≤ index → index ≤ values.size →
        ∃ value, withoutMissingGet arrayRead JlError.argumentError wrapped index = .ok value ∧
          arrayRead values index = .ok (some value)) ∧
    (∀ (wrapped : WithoutMissingVector α (Array (Option α))) (index : Int)
        (value : Option α),
      1 ≤ index → index ≤ wrapped.data.size →
      ∃ result, withoutMissingSet
          (fun storage value index => arrayWrite storage index value)
          wrapped value index = .ok result ∧
        result.data.size = wrapped.data.size ∧
        arrayRead result.data index = .ok value ∧
        ∀ other, other ≠ index → arrayRead result.data other = arrayRead wrapped.data other)


def WindowReadsSucceed {V α K E : Type} (indices : IntegerIndexOps K)
    (get : V → K → Except E α) (v : V) (lo hi : K) : Prop :=
  ∀ i, i ∈ indices.range (indices.addOne lo) hi →
    ∃ current previous, get v i = .ok current ∧
      get v (indices.previous i) = .ok previous

def WindowSorted {V α K O E : Type} (indices : IntegerIndexOps K)
    (get : V → K → Except E α) (lt : O → α → α → Bool)
    (v : V) (lo hi : K) (order : O) : Prop :=
  ∀ i, i ∈ indices.range (indices.addOne lo) hi →
    ∃ current previous, get v i = .ok current ∧
      get v (indices.previous i) = .ok previous ∧
      lt order current previous = false

def indexWindowOps {V α K E : Type} (indices : IntegerIndexOps K)
    (checkBounds : V → K → K → Except E Unit) (get : V → K → Except E α) :
    WindowOps V K K K (K × K) (List K) K (List K) K α E where
  bounds := fun lo hi => JuliaLean.base.sort.liftExcept (.ok (lo, hi))
  checkBounds := fun v (lo, hi) => JuliaLean.base.sort.liftExcept (checkBounds v lo hi)
  addOne := indices.addOne
  window := fun start hi => JuliaLean.base.sort.liftExcept (.ok (indices.range start hi))
  first := fun xs => JuliaLean.base.sort.liftExcept (.ok (match xs with | [] => none | x :: rest => some (x, rest)))
  next := fun _ xs => JuliaLean.base.sort.liftExcept (.ok (match xs with | [] => none | x :: rest => some (x, rest)))
  getCurrent := fun v i => JuliaLean.base.sort.liftExcept (get v i)
  previous := indices.previous
  getPrevious := fun v i => JuliaLean.base.sort.liftExcept (get v i)

def WindowIssortedCorrect : Prop :=
  ∀ (V α K O E : Type) (indices : IntegerIndexOps K)
      (checkBounds : V → K → K → Except E Unit) (get : V → K → Except E α)
      (lt : O → α → α → JuliaLean.base.ordering.OrderingResult Bool)
      (v : V) (lo hi : K) (order : O),
    checkBounds v lo hi = .ok () →
    WindowReadsSucceed indices get v lo hi →
    (issortedWindow (indexWindowOps indices checkBounds get) v lo hi
      (JuliaLean.base.ordering.OrdResult.plain (K := α) inferInstance
        JuliaLean.base.ordering.Forward (fun _ => lt order)) = some (.ok true) ↔
      ∀ i, i ∈ indices.range (indices.addOne lo) hi →
        ∃ current previous, get v i = .ok current ∧
          get v (indices.previous i) = .ok previous ∧ lt order current previous = .ok false)

/-- sorttuplescov-uint-mapping: native matched-width integer component, including both
inverse directions and both direct orders. Char and arbitrary Signed/Unsigned extensions
remain blocked rather than represented by their bit fields. -/
def UIntMappingIntegerCorrect : Prop :=
  (∀ (t : IntTy) (x : JInt t) (reverse : Bool),
    integerDecode t reverse (integerCode t reverse x) = x) ∧
  (∀ (t : IntTy) (code : JInt t.toUnsigned) (reverse : Bool),
    integerCode t reverse (integerDecode t reverse code) = code) ∧
  (∀ (t : IntTy) (x y : JInt t) (reverse : Bool),
    (if reverse then y.val < x.val else x.val < y.val) ↔
      (integerCode t reverse x).val < (integerCode t reverse y).val)

section UIntMappingIntegerProof

open JuliaLean.base.int JuliaLean.Proofs.base.int

theorem patternBxor {t : IntTy} (x y : JInt t) :
    pattern (JuliaLean.base.int.bxor x y) = pattern x ^^^ pattern y := by
  simp only [JuliaLean.base.int.bxor, JuliaLean.base.int.xor_int,
    JuliaLean.C.jlXorInt, pattern_toJInt, BitVec.toNat_xor, ← pattern_fromJInt]

theorem natXorTopBit (p n : Nat) (hn : 0 < n) (hp : p < 2 ^ n) :
    p ^^^ 2 ^ (n - 1) =
      if p < 2 ^ (n - 1) then p + 2 ^ (n - 1) else p - 2 ^ (n - 1) := by
  let q := 2 ^ (n - 1)
  have hqpos : 0 < q := by dsimp [q]; exact Nat.two_pow_pos _
  have hq2 : 2 * q = 2 ^ n := by
    dsimp [q]
    rw [show n = (n - 1) + 1 by omega, Nat.pow_succ]
    exact Nat.mul_comm _ _
  have hp2 : p < 2 * q := by omega
  have hdiv : p / q = 0 ∨ p / q = 1 := by
    by_cases hpq : p < q
    · left
      exact (Nat.div_eq_zero_iff_lt hqpos).2 hpq
    · right
      have hle : q ≤ p := Nat.le_of_not_gt hpq
      have hlt : p / q < 2 := (Nat.div_lt_iff_lt_mul hqpos).2 (by omega)
      have hpositive : 0 < p / q := Nat.div_pos hle hqpos
      omega
  have hdivXor : (p ^^^ q) / q = (p / q) ^^^ 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self (Nat.two_pow_pos (n - 1))]
  have hmodXor : (p ^^^ q) % q = p % q := by
    rw [Nat.xor_mod_two_pow]
    simp [q, Nat.mod_self]
  have hdecomp := Nat.mod_add_div (p ^^^ q) q
  rw [hmodXor, hdivXor] at hdecomp
  rcases hdiv with hzero | hone
  · have hpq : p < q := (Nat.div_eq_zero_iff_lt hqpos).1 hzero
    have hmod : p % q = p := Nat.mod_eq_of_lt hpq
    rw [hzero, hmod] at hdecomp
    simp at hdecomp
    rw [if_pos hpq]
    simpa [q] using hdecomp.symm
  · have hqle : q ≤ p := by
      have hmul := Nat.div_mul_le_self p q
      rw [hone] at hmul
      simpa using hmul
    have hmod : p % q = p - q := by
      have h := Nat.mod_add_div p q
      rw [hone] at h
      omega
    rw [hone, hmod] at hdecomp
    simp at hdecomp
    rw [if_neg (by omega)]
    simpa [q] using hdecomp.symm

theorem patternTypeminSigned {t : IntTy} (ht : t.signed = true) :
    pattern (JuliaLean.base.int.typemin t) = 2 ^ (t.bits - 1) := by
  cases t <;> simp_all [IntTy.signed, IntTy.bits, JuliaLean.base.int.typemin,
    typemin_Int8, typemin_Int16, typemin_Int32, typemin_Int64, typemin_Int128,
    JInt.lit, JInt.wrap, wrapInt, pattern] <;> decide +kernel

theorem patternSignedValue {t : IntTy} (ht : t.signed = true) (x : JInt t) :
    (pattern x : Int) = if x.val < 0 then x.val + 2 ^ t.bits else x.val := by
  have hu : (JuliaLean.base.int.unsigned x).val =
      if x.val < 0 then x.val + 2 ^ t.bits else x.val := by
    simpa [JuliaLean.base.int.unsigned, ht] using
      JuliaLean.Proofs.base.int.unsignedReinterprets_proven t ht x
  have htu : t.toUnsigned.signed = false := by
    cases t <;> simp_all [IntTy.toUnsigned, IntTy.signed]
  rw [← pattern_unsigned x, val_of_unsigned_pattern htu]
  exact hu

theorem mapSignedVal {t : IntTy} (ht : t.signed = true) (x : JInt t) :
    (JuliaLean.base.sort.mapSigned x).val = x.val + 2 ^ (t.bits - 1) := by
  have htu : t.toUnsigned.signed = false := by
    cases t <;> simp_all [IntTy.toUnsigned, IntTy.signed]
  have hmap : pattern (JuliaLean.base.sort.mapSigned x) =
      pattern x ^^^ 2 ^ (t.bits - 1) := by
    simp only [JuliaLean.base.sort.mapSigned, JuliaLean.base.sort.uintMapSigned,
      pattern_unsigned, patternBxor, patternTypeminSigned ht]
  have hval := (val_of_unsigned_pattern htu (JuliaLean.base.sort.mapSigned x)).symm
  rw [hmap, natXorTopBit (pattern x) t.bits
    (by cases t <;> simp_all [IntTy.signed, IntTy.bits]) (pattern_lt x)] at hval
  have hpowNat : 2 ^ t.bits = 2 * 2 ^ (t.bits - 1) := by
    have hn : (t.bits - 1) + 1 = t.bits := by cases t <;> decide
    calc
      2 ^ t.bits = 2 ^ ((t.bits - 1) + 1) := by rw [hn]
      _ = 2 ^ (t.bits - 1) * 2 := by rw [Nat.pow_succ]
      _ = 2 * 2 ^ (t.bits - 1) := by omega
  have hpow : (2 ^ t.bits : Int) = 2 * (2 ^ (t.bits - 1) : Int) := by
    exact_mod_cast hpowNat
  have hpattern := patternSignedValue ht x
  by_cases hneg : x.val < 0
  · have hpattern' : (pattern x : Int) = x.val + 2 ^ t.bits := by
      simpa [hneg] using hpattern
    have hmin : -(2 ^ (t.bits - 1) : Int) ≤ x.val := by
      simpa [IntTy.min, ht] using x.property.1
    have htop : (2 ^ (t.bits - 1) : Int) ≤ (pattern x : Int) := by
      rw [hpattern']
      omega
    have hnot : ¬ pattern x < 2 ^ (t.bits - 1) := by
      intro hlt
      have hlt' : (pattern x : Int) < 2 ^ (t.bits - 1) := by exact_mod_cast hlt
      omega
    rw [if_neg hnot] at hval
    push_cast at hval
    have htopNat : 2 ^ (t.bits - 1) ≤ pattern x := by exact_mod_cast htop
    rw [Int.natCast_sub htopNat] at hval
    rw [hpattern'] at hval
    rw [hpow] at hval
    have hpowCast : (↑(2 ^ (t.bits - 1) : Nat) : Int) =
        (2 ^ (t.bits - 1) : Int) := by norm_cast
    rw [hpowCast] at hval
    omega
  · have hpattern' : (pattern x : Int) = x.val := by
      simpa [hneg] using hpattern
    have hmax : x.val ≤ (2 ^ (t.bits - 1) : Int) - 1 := by
      simpa [IntTy.max, ht] using x.property.2
    have hlt : x.val < 2 ^ (t.bits - 1) := by omega
    have hbelow : pattern x < 2 ^ (t.bits - 1) := by
      have hpInt : (pattern x : Int) < 2 ^ (t.bits - 1) := by
        rw [hpattern']
        exact hlt
      exact_mod_cast hpInt
    rw [if_pos hbelow] at hval
    push_cast at hval
    rw [hpattern'] at hval
    omega

theorem unmapSignedVal {u : IntTy} (hu : u.signed = false) (x : JInt u) :
    (JuliaLean.base.sort.unmapSigned x).val = x.val - 2 ^ (u.bits - 1) := by
  have ht : u.toSigned.signed = true := by
    cases u <;> simp_all [IntTy.toSigned, IntTy.signed]
  have hbits : u.toSigned.bits = u.bits := by
    cases u <;> rfl
  have hmap : pattern (JuliaLean.base.sort.unmapSigned x) =
      pattern x ^^^ 2 ^ (u.bits - 1) := by
    simp only [JuliaLean.base.sort.unmapSigned, JuliaLean.base.sort.uintUnmapSigned,
      patternBxor, pattern_signed, patternTypeminSigned ht, hbits]
  have hvalue := patternSignedValue ht (JuliaLean.base.sort.unmapSigned x)
  rw [hmap, natXorTopBit (pattern x) u.bits (by cases u <;> decide)
    (pattern_lt x)] at hvalue
  have hpattern : (pattern x : Int) = x.val := by
    exact_mod_cast val_of_unsigned_pattern hu x
  have hpowNat : 2 ^ u.bits = 2 * 2 ^ (u.bits - 1) := by
    have hn : (u.bits - 1) + 1 = u.bits := by cases u <;> decide
    calc
      2 ^ u.bits = 2 ^ ((u.bits - 1) + 1) := by rw [hn]
      _ = 2 ^ (u.bits - 1) * 2 := by rw [Nat.pow_succ]
      _ = 2 * 2 ^ (u.bits - 1) := by omega
  have hpow : (2 ^ u.bits : Int) = 2 * (2 ^ (u.bits - 1) : Int) := by
    exact_mod_cast hpowNat
  have hxnonneg : 0 ≤ x.val := by
    rw [← hpattern]
    exact Int.natCast_nonneg _
  have hpatternNat : pattern x = x.val.toNat := pattern_of_unsigned hu x
  rw [hpatternNat, hbits, hpow] at hvalue
  have hminSigned :
      -(2 ^ (u.bits - 1) : Int) ≤ (JuliaLean.base.sort.unmapSigned x).val := by
    have h := (JuliaLean.base.sort.unmapSigned x).property.1
    simpa [IntTy.min, ht, hbits] using h
  have hmaxSigned :
      (JuliaLean.base.sort.unmapSigned x).val ≤ 2 ^ (u.bits - 1 : Nat) - 1 := by
    have h := (JuliaLean.base.sort.unmapSigned x).property.2
    simpa [IntTy.max, ht, hbits] using h
  have hxlt : x.val < (2 ^ u.bits : Int) := by
    rw [← hpattern]
    exact_mod_cast pattern_lt x
  by_cases hsmall : x.val.toNat < 2 ^ (u.bits - 1)
  · rw [if_pos hsmall] at hvalue
    have hxsmall : x.val < (2 ^ (u.bits - 1) : Int) := by
      have hcast := Int.toNat_of_nonneg hxnonneg
      rw [← hcast]
      exact_mod_cast hsmall
    push_cast at hvalue
    rw [Int.toNat_of_nonneg hxnonneg] at hvalue
    by_cases hneg : (JuliaLean.base.sort.unmapSigned x).val < 0
    · rw [if_pos hneg] at hvalue
      omega
    · rw [if_neg hneg] at hvalue
      omega
  · have hlarge : 2 ^ (u.bits - 1) ≤ x.val.toNat := by omega
    rw [if_neg hsmall] at hvalue
    push_cast at hvalue
    have hsubCast :
        ((x.val.toNat - 2 ^ (u.bits - 1) : Nat) : Int) =
          x.val - (2 ^ (u.bits - 1) : Int) := by
      have hsubAdd := Nat.sub_add_cancel hlarge
      have hcastAdd :
          ((x.val.toNat - 2 ^ (u.bits - 1) : Nat) : Int) +
              (2 ^ (u.bits - 1) : Int) = x.val := by
        calc
          _ = (x.val.toNat : Int) := by exact_mod_cast hsubAdd
          _ = x.val := Int.toNat_of_nonneg hxnonneg
      omega
    rw [hsubCast] at hvalue
    by_cases hneg : (JuliaLean.base.sort.unmapSigned x).val < 0
    · rw [if_pos hneg] at hvalue
      omega
    · rw [if_neg hneg] at hvalue
      omega

theorem mapUnmapSignedRoundTripVal {t : IntTy} (ht : t.signed = true)
    (hu : t.toUnsigned.signed = false) (x : JInt t) :
    (JuliaLean.base.sort.unmapSigned (JuliaLean.base.sort.mapSigned x)).val = x.val := by
  have hbits : t.toUnsigned.bits = t.bits := by cases t <;> rfl
  rw [unmapSignedVal hu (JuliaLean.base.sort.mapSigned x),
    mapSignedVal ht x, hbits]
  omega

theorem forwardIntegerRoundTrip :
    ∀ (t : IntTy) (x : JInt t),
      JuliaLean.base.sort.forwardIntegerDecode t
        (JuliaLean.base.sort.forwardIntegerCode t x) = x := by
  intro t x
  cases t with
  | i8 =>
      apply JuliaLean.Proofs.base.int.jint_eq
      simpa [JuliaLean.base.sort.forwardIntegerDecode,
        JuliaLean.base.sort.forwardIntegerCode] using
          mapUnmapSignedRoundTripVal (t := .i8) (by decide) (by decide) x
  | i16 =>
      apply JuliaLean.Proofs.base.int.jint_eq
      simpa [JuliaLean.base.sort.forwardIntegerDecode,
        JuliaLean.base.sort.forwardIntegerCode] using
          mapUnmapSignedRoundTripVal (t := .i16) (by decide) (by decide) x
  | i32 =>
      apply JuliaLean.Proofs.base.int.jint_eq
      simpa [JuliaLean.base.sort.forwardIntegerDecode,
        JuliaLean.base.sort.forwardIntegerCode] using
          mapUnmapSignedRoundTripVal (t := .i32) (by decide) (by decide) x
  | i64 =>
      apply JuliaLean.Proofs.base.int.jint_eq
      simpa [JuliaLean.base.sort.forwardIntegerDecode,
        JuliaLean.base.sort.forwardIntegerCode] using
          mapUnmapSignedRoundTripVal (t := .i64) (by decide) (by decide) x
  | i128 =>
      apply JuliaLean.Proofs.base.int.jint_eq
      simpa [JuliaLean.base.sort.forwardIntegerDecode,
        JuliaLean.base.sort.forwardIntegerCode] using
          mapUnmapSignedRoundTripVal (t := .i128) (by decide) (by decide) x
  | u8 => simp [JuliaLean.base.sort.forwardIntegerDecode,
      JuliaLean.base.sort.forwardIntegerCode, JuliaLean.base.sort.mapUnsigned,
      JuliaLean.base.sort.uintMapUnsigned, JuliaLean.base.sort.uintUnmapUnsigned]
  | u16 => simp [JuliaLean.base.sort.forwardIntegerDecode,
      JuliaLean.base.sort.forwardIntegerCode, JuliaLean.base.sort.mapUnsigned,
      JuliaLean.base.sort.uintMapUnsigned, JuliaLean.base.sort.uintUnmapUnsigned]
  | u32 => simp [JuliaLean.base.sort.forwardIntegerDecode,
      JuliaLean.base.sort.forwardIntegerCode, JuliaLean.base.sort.mapUnsigned,
      JuliaLean.base.sort.uintMapUnsigned, JuliaLean.base.sort.uintUnmapUnsigned]
  | u64 => simp [JuliaLean.base.sort.forwardIntegerDecode,
      JuliaLean.base.sort.forwardIntegerCode, JuliaLean.base.sort.mapUnsigned,
      JuliaLean.base.sort.uintMapUnsigned, JuliaLean.base.sort.uintUnmapUnsigned]
  | u128 => simp [JuliaLean.base.sort.forwardIntegerDecode,
      JuliaLean.base.sort.forwardIntegerCode, JuliaLean.base.sort.mapUnsigned,
      JuliaLean.base.sort.uintMapUnsigned, JuliaLean.base.sort.uintUnmapUnsigned]

theorem mapSignedUnmapSignedRoundTripVal {u : IntTy} (hu : u.signed = false)
    (x : JInt u) :
    (JuliaLean.base.sort.mapSigned (JuliaLean.base.sort.unmapSigned x)).val = x.val := by
  have ht : u.toSigned.signed = true := by
    cases u <;> simp [IntTy.toSigned, IntTy.signed]
  have hbits : u.toSigned.bits = u.bits := by cases u <;> rfl
  rw [mapSignedVal ht (JuliaLean.base.sort.unmapSigned x),
    unmapSignedVal hu x, hbits]
  omega

theorem forwardIntegerCodeDecodeRoundTrip :
    ∀ (t : IntTy) (code : JInt t.toUnsigned),
      JuliaLean.base.sort.forwardIntegerCode t
        (JuliaLean.base.sort.forwardIntegerDecode t code) = code := by
  intro t code
  cases t with
  | i8 =>
      apply JuliaLean.Proofs.base.int.jint_eq
      change (JuliaLean.base.sort.mapSigned (JuliaLean.base.sort.unmapSigned code)).val =
        code.val
      exact mapSignedUnmapSignedRoundTripVal (by decide) code
  | i16 =>
      apply JuliaLean.Proofs.base.int.jint_eq
      change (JuliaLean.base.sort.mapSigned (JuliaLean.base.sort.unmapSigned code)).val =
        code.val
      exact mapSignedUnmapSignedRoundTripVal (by decide) code
  | i32 =>
      apply JuliaLean.Proofs.base.int.jint_eq
      change (JuliaLean.base.sort.mapSigned (JuliaLean.base.sort.unmapSigned code)).val =
        code.val
      exact mapSignedUnmapSignedRoundTripVal (by decide) code
  | i64 =>
      apply JuliaLean.Proofs.base.int.jint_eq
      change (JuliaLean.base.sort.mapSigned (JuliaLean.base.sort.unmapSigned code)).val =
        code.val
      exact mapSignedUnmapSignedRoundTripVal (by decide) code
  | i128 =>
      apply JuliaLean.Proofs.base.int.jint_eq
      change (JuliaLean.base.sort.mapSigned (JuliaLean.base.sort.unmapSigned code)).val =
        code.val
      exact mapSignedUnmapSignedRoundTripVal (by decide) code
  | u8 => simp [JuliaLean.base.sort.forwardIntegerCode,
      JuliaLean.base.sort.forwardIntegerDecode, JuliaLean.base.sort.mapUnsigned,
      JuliaLean.base.sort.uintMapUnsigned, JuliaLean.base.sort.uintUnmapUnsigned]
  | u16 => simp [JuliaLean.base.sort.forwardIntegerCode,
      JuliaLean.base.sort.forwardIntegerDecode, JuliaLean.base.sort.mapUnsigned,
      JuliaLean.base.sort.uintMapUnsigned, JuliaLean.base.sort.uintUnmapUnsigned]
  | u32 => simp [JuliaLean.base.sort.forwardIntegerCode,
      JuliaLean.base.sort.forwardIntegerDecode, JuliaLean.base.sort.mapUnsigned,
      JuliaLean.base.sort.uintMapUnsigned, JuliaLean.base.sort.uintUnmapUnsigned]
  | u64 => simp [JuliaLean.base.sort.forwardIntegerCode,
      JuliaLean.base.sort.forwardIntegerDecode, JuliaLean.base.sort.mapUnsigned,
      JuliaLean.base.sort.uintMapUnsigned, JuliaLean.base.sort.uintUnmapUnsigned]
  | u128 => simp [JuliaLean.base.sort.forwardIntegerCode,
      JuliaLean.base.sort.forwardIntegerDecode, JuliaLean.base.sort.mapUnsigned,
      JuliaLean.base.sort.uintMapUnsigned, JuliaLean.base.sort.uintUnmapUnsigned]

theorem signedCodeOrder {t : IntTy} (ht : t.signed = true)
    (x y : JInt t) :
    x.val < y.val ↔
      (JuliaLean.base.sort.mapSigned x).val < (JuliaLean.base.sort.mapSigned y).val := by
  rw [mapSignedVal ht x, mapSignedVal ht y]
  omega

theorem unsignedCodeOrder {t : IntTy} (x y : JInt t) :
    x.val < y.val ↔
      (JuliaLean.base.sort.mapUnsigned x).val < (JuliaLean.base.sort.mapUnsigned y).val := by
  simp [JuliaLean.base.sort.mapUnsigned, JuliaLean.base.sort.uintMapUnsigned]

theorem forwardIntegerCodeOrder :
    ∀ (t : IntTy) (x y : JInt t),
      x.val < y.val ↔
        (JuliaLean.base.sort.forwardIntegerCode t x).val <
          (JuliaLean.base.sort.forwardIntegerCode t y).val := by
  intro t x y
  cases t with
  | i8 => simpa [JuliaLean.base.sort.forwardIntegerCode] using
      signedCodeOrder (by decide) x y
  | i16 => simpa [JuliaLean.base.sort.forwardIntegerCode] using
      signedCodeOrder (by decide) x y
  | i32 => simpa [JuliaLean.base.sort.forwardIntegerCode] using
      signedCodeOrder (by decide) x y
  | i64 => simpa [JuliaLean.base.sort.forwardIntegerCode] using
      signedCodeOrder (by decide) x y
  | i128 => simpa [JuliaLean.base.sort.forwardIntegerCode] using
      signedCodeOrder (by decide) x y
  | u8 =>
      change x.val < y.val ↔
        (JuliaLean.base.sort.mapUnsigned x).val <
          (JuliaLean.base.sort.mapUnsigned y).val
      exact unsignedCodeOrder x y
  | u16 =>
      change x.val < y.val ↔
        (JuliaLean.base.sort.mapUnsigned x).val <
          (JuliaLean.base.sort.mapUnsigned y).val
      exact unsignedCodeOrder x y
  | u32 =>
      change x.val < y.val ↔
        (JuliaLean.base.sort.mapUnsigned x).val <
          (JuliaLean.base.sort.mapUnsigned y).val
      exact unsignedCodeOrder x y
  | u64 =>
      change x.val < y.val ↔
        (JuliaLean.base.sort.mapUnsigned x).val <
          (JuliaLean.base.sort.mapUnsigned y).val
      exact unsignedCodeOrder x y
  | u128 =>
      change x.val < y.val ↔
        (JuliaLean.base.sort.mapUnsigned x).val <
          (JuliaLean.base.sort.mapUnsigned y).val
      exact unsignedCodeOrder x y

theorem bnotInvolutive {t : IntTy} (x : JInt t) :
    JuliaLean.base.int.bnot (JuliaLean.base.int.bnot x) = x := by
  apply JuliaLean.Proofs.base.int.jint_eq_of_pattern
  rw [pattern_bnot, pattern_bnot]
  have hp := pattern_lt x
  omega

theorem bnotUnsignedOrder {u : IntTy} (hu : u.signed = false)
    (x y : JInt u) :
    x.val < y.val ↔
      (JuliaLean.base.int.bnot y).val < (JuliaLean.base.int.bnot x).val := by
  have hxy : x.val < y.val ↔ pattern x < pattern y := by
    rw [← val_of_unsigned_pattern hu x, ← val_of_unsigned_pattern hu y]
    omega
  have hnot : (JuliaLean.base.int.bnot y).val < (JuliaLean.base.int.bnot x).val ↔
      pattern (JuliaLean.base.int.bnot y) < pattern (JuliaLean.base.int.bnot x) := by
    rw [← val_of_unsigned_pattern hu (JuliaLean.base.int.bnot y),
      ← val_of_unsigned_pattern hu (JuliaLean.base.int.bnot x)]
    omega
  rw [hxy, hnot, pattern_bnot, pattern_bnot]
  have hx := pattern_lt x
  have hy := pattern_lt y
  omega

theorem integerCodeReverse (t : IntTy) (x : JInt t) :
    integerCode t true x =
      JuliaLean.base.int.bnot (forwardIntegerCode t x) := by
  simp [integerCode, uintMapReverse, integerReverseMappingOps]

theorem integerDecodeReverse (t : IntTy) (code : JInt t.toUnsigned) :
    integerDecode t true code =
      forwardIntegerDecode t (JuliaLean.base.int.bnot code) := by
  simp [integerDecode, uintUnmapReverse, integerReverseMappingOps]

theorem uintMappingIntegerCorrect_proven : UIntMappingIntegerCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro t x reverse
    cases reverse with
    | false =>
        simpa [integerDecode, integerCode] using forwardIntegerRoundTrip t x
    | true =>
        rw [integerCodeReverse, integerDecodeReverse,
          bnotInvolutive, forwardIntegerRoundTrip]
  · intro t code reverse
    cases reverse with
    | false =>
        simpa [integerCode, integerDecode] using
          forwardIntegerCodeDecodeRoundTrip t code
    | true =>
        rw [integerDecodeReverse, integerCodeReverse,
          forwardIntegerCodeDecodeRoundTrip, bnotInvolutive]
  · intro t x y reverse
    cases reverse with
    | false =>
        simpa [integerCode] using forwardIntegerCodeOrder t x y
    | true =>
        have hu : t.toUnsigned.signed = false := by
          cases t <;> decide
        rw [integerCodeReverse, integerCodeReverse]
        exact (forwardIntegerCodeOrder t y x).trans
          (bnotUnsignedOrder hu (forwardIntegerCode t y) (forwardIntegerCode t x))

end UIntMappingIntegerProof
def UIntMappableDispatchCorrect : Prop :=
  (∀ (T O : Type) (order : O), uintMappableFallback T order = none) ∧
  (∀ (t : IntTy),
    uintMappableBitInteger (fun _ => JInt (unsignedIntegerType t)) (JInt t) =
      some (JInt (unsignedIntegerType t)) ∧
    (unsignedIntegerType t).bits = t.bits ∧
    (unsignedIntegerType t).signed = false) ∧
  (∀ (t : IntTy) (reverse : Unit),
    uintMappableReverse (integerReverseMappingOps t) (JInt t) reverse =
      some (JInt (unsignedIntegerType t)) ∧
    ∀ (x y : JInt t),
      integerDecode t true (integerCode t true x) = x ∧
      (y.val < x.val ↔ integerCode t true x < integerCode t true y)) ∧
  (uintMappableChar CharacterCode = some CharacterCode ∧
    ∀ (c : CharacterCode),
      uintUnmapChar CharacterCode.mk (uintMapChar CharacterCode.bits c) = c) ∧
  (∀ (α : Type) [Inhabited α] (lt : α → α → SortResult Bool)
      (mappableType : Option Type) (values : Array α),
    EffectNegTransOrder lt →
    let ops : UIntMappableSortOps (Array α) (Algorithm (BracketSortTarget Int) Int)
        (α → α → SortResult Bool) (ArraySortKeywords α) (Array α) JuliaLean.base.sort.SortException := {
      elementType := fun _ => α
      uintMappable := fun _ _ => mappableType
      yesAlgorithm := fun _ => .insertion
      noAlgorithm := fun _ => .insertion
      sort := fun v _ o kw => storageInsertion arrayStorage o v kw.lo kw.hi
    }
    ∃ result,
      sortIsUIntMappable ops values (.isUIntMappable .insertion .insertion) lt
        { lo := 1, hi := values.size } = .ok result ∧
      List.Perm values.toList result.toList ∧
      EffectSortedValues lt result.toList)

def AlgorithmPolicyDispatchCorrect : Prop :=
  (∀ (α : Type) [Inhabited α] (lt : α → α → SortResult Bool) (threshold : Nat) (values : Array α),
    EffectNegTransOrder lt →
    let ops : SmallSortOps (Array α) (Algorithm (BracketSortTarget Int) Int)
        (α → α → SortResult Bool) Int (ArraySortKeywords α) (Array α) JuliaLean.base.sort.SortException := {
      range := fun kw => .ok (kw.lo, kw.hi)
      spanLessThan := fun lo hi n => decide (hi - lo < Int.ofNat n)
      smallAlgorithm := fun _ => .insertion
      bigAlgorithm := fun _ => .insertion
      sort := fun v _ o kw => storageInsertion arrayStorage o v kw.lo kw.hi
    }
    ∃ res1 res2,
      sortSmall ops values (smallExplicit threshold .insertion .insertion) threshold lt
        { lo := 1, hi := values.size } = .ok res1 ∧
      sortSmall ops values (smallDefault threshold .insertion) threshold lt
        { lo := 1, hi := values.size } = .ok res2 ∧
      List.Perm values.toList res1.toList ∧ EffectSortedValues lt res1.toList ∧
      List.Perm values.toList res2.toList ∧ EffectSortedValues lt res2.toList) ∧
  (∀ (α : Type) [Inhabited α] (lt : α → α → SortResult Bool) (t : IntTy)
      (minimum maximum : JInt t) (reverse : Bool) (elemSz : Nat) (values : Array α),
    EffectNegTransOrder lt →
    let ops : ConsiderCountingOps (Array α) (JInt t) Nat Int
        (Algorithm (BracketSortTarget Int) Int) Bool (ArraySortKeywords α) (Array α) JuliaLean.base.sort.SortException := {
      rangeAndExtrema := fun kw => .ok (kw.lo, kw.hi, minimum, maximum)
      isReverse := id
      wrapSubtract := fun a b => a - b
      maybeUnsigned := fun x =>
        if t.signed then maybeUnsignedBitSigned (fun v : JInt t => v.val.toNat) x
        else maybeUnsignedInteger x.val.toNat
      span := fun hi lo => hi - lo
      elementSize := fun _ => elemSz
      rangeLessThan := fun u thresh => decide (Int.ofNat u < thresh)
      countingAlgorithm := fun _ => .insertion
      nextAlgorithm := fun _ => .insertion
      sort := fun v _ _ kw => storageInsertion arrayStorage lt v kw.lo kw.hi
    }
    maybeReverseForward minimum = minimum ∧
    maybeReverseReverse (fun x : JInt t => -x) minimum = -minimum ∧
    ∃ res1 res2,
      sortConsiderCountingInteger ops values (considerCountingSort .insertion) reverse
        { lo := 1, hi := values.size } = .ok res1 ∧
      sortConsiderCountingOther ops.sort id
        values (considerCountingSort .insertion) reverse
        { lo := 1, hi := values.size } = .ok res2 ∧
      List.Perm values.toList res1.toList ∧ EffectSortedValues lt res1.toList ∧
      List.Perm values.toList res2.toList ∧ EffectSortedValues lt res2.toList) ∧
  (∀ (α : Type) [Inhabited α] (lt : α → α → SortResult Bool) (t : IntTy)
      (minimum maximum : JInt t) (reverse : Bool) (elemSz : Nat) (logSpan : Float) (values : Array α),
    EffectNegTransOrder lt →
    let ops : ConsiderRadixSortOps (Array α) (JInt t) Int Nat
        (Algorithm (BracketSortTarget Int) Int) Bool (ArraySortKeywords α) (Array α) JuliaLean.base.sort.SortException := {
      rangeAndExtrema := fun kw => .ok (kw.lo, kw.hi, minimum, maximum)
      uintMap := fun x rev => (integerCode t rev x).val.toNat
      subtractUnsigned := Nat.sub
      topSetBit := fun u => if u = 0 then 0 else Nat.log2 u + 1
      unsignedToNat := id
      elementSize := fun _ => elemSz
      logarithmOfSpan := fun _ _ => logSpan
      floatOfNat := Float.ofNat
      multiplyFloat := (· * ·)
      addFloat := (· + ·)
      lessFloat := (· < ·)
      radixAlgorithm := fun _ => .insertion
      nextAlgorithm := fun _ => .insertion
      sort := fun v _ _ kw => storageInsertion arrayStorage lt v kw.lo kw.hi
    }
    ∃ result,
      sortConsiderRadix ops values (considerRadixSort .insertion) reverse
        { lo := 1, hi := values.size } = .ok result ∧
      List.Perm values.toList result.toList ∧ EffectSortedValues lt result.toList) ∧
  (∀ (α : Type) [Inhabited α] (lt : α → α → SortResult Bool) (values : Array α)
      (target : BracketSortTarget Int) (lo hi : Option Int),
    EffectNegTransOrder lt →
    let sortLeaf := fun (v : Array α) (_ : Algorithm (BracketSortTarget Int) Int)
      (o : α → α → SortResult Bool) (kw : ArraySortKeywords α) => storageInsertion arrayStorage o v kw.lo kw.hi
    isFullSortAlgorithm (initialOptimizations (Target := BracketSortTarget Int) (Index := Int) .insertion) = true ∧
    isFullSortAlgorithm (defalgArray (Target := BracketSortTarget Int) (Index := Int) values) = true ∧
    isFullSortAlgorithm (defalgNumberOrMissing (Target := BracketSortTarget Int) (Index := Int) values) = true ∧
    isFullSortAlgorithm (defalgMissing (Target := BracketSortTarget Int) (Index := Int) values) = true ∧
    isFullSortAlgorithm (defalgBottom (Target := BracketSortTarget Int) (Index := Int) values) = true ∧
    isFullSortAlgorithm (defalgOther (Target := BracketSortTarget Int) (Index := Int) values) = true ∧
    isFullSortAlgorithm (maybeApplyInitialGeneric (Target := BracketSortTarget Int) (Index := Int) .insertion) = true ∧
    isFullSortAlgorithm (maybeApplyInitialQuick (Target := BracketSortTarget Int) (Index := Int)) = true ∧
    isFullSortAlgorithm (maybeApplyInitialMerge (Target := BracketSortTarget Int) (Index := Int)) = true ∧
    isFullSortAlgorithm (maybeApplyInitialInsertion (Target := BracketSortTarget Int) (Index := Int)) = true ∧
    isFullSortAlgorithm (scratchQuickDefault (Target := BracketSortTarget Int) (Index := Int)) = true ∧
    scratchQuickBounds (Target := BracketSortTarget Int) lo hi = .scratchQuickSort lo hi smallAlgorithm ∧
    scratchQuickSingle (Target := BracketSortTarget Int) lo = .scratchQuickSort lo lo smallAlgorithm ∧
    scratchQuickRange bracketTargetEndpoints target =
      .scratchQuickSort (some (bracketTargetEndpoints.first target)) (some (bracketTargetEndpoints.last target)) smallAlgorithm ∧
    (match bracketedSort bracketTargetEndpoints target with
      | .bracketedSort k f =>
        k = target ∧ f target = initialOptimizations (scratchQuickRange bracketTargetEndpoints target)
      | _ => False) ∧
    ∃ r1 r2 r3,
      sortSubArrayFallback sortLeaf id values .insertion lt { lo := 1, hi := values.size } = .ok r1 ∧
      sortBoolOther sortLeaf id values .insertion lt { lo := 1, hi := values.size } = .ok r2 ∧
      sortDefaultAlgorithm sortLeaf values lt { lo := 1, hi := values.size } = .ok r3 ∧
      List.Perm values.toList r1.toList ∧ EffectSortedValues lt r1.toList ∧
      List.Perm values.toList r2.toList ∧ EffectSortedValues lt r2.toList ∧
      List.Perm values.toList r3.toList ∧ EffectSortedValues lt r3.toList)
/-- `in(x, r)` on a `LinRange{Float64}`, preserving the range model's exact error. -/
def linRangeContains (x : JuliaLean.base.float.FV .f64)
    (r : JuliaLean.base.range.LinRange (JuliaLean.base.float.FV .f64) JInt64) : SortResult Bool :=
  (JuliaLean.base.range.in_Real_AbstractRange x r).mapError
    (fun error => .native (.range error))

def InsortedRangeAgrees : Prop :=
  ∀ (r : JuliaLean.base.range.LinRange (JuliaLean.base.float.FV .f64) JInt64)
      (xs : List (JuliaLean.base.float.FV .f64)) (x : JuliaLean.base.float.FV .f64),
    JuliaLean.base.range.JLength.length r = .ok (JuliaLean.base.range.jint xs.length) →
    (∀ (i : Nat) (h : i < xs.length),
      JuliaLean.base.range.JGetindex.getindex r (JuliaLean.base.range.jint (i + 1)) =
        .ok xs[i]) →
    SortedValues JuliaLean.base.float.isless_IEEEFloat xs →
    ∃ found, insortedVector arrayVectorOps arrayFirstIndex arrayLastIndex
        (fun (_ : Unit) (_ : Unit) (_ : Option Bool) (_ : Unit) => ())
        (fun (_ : Unit) a b => .ok (JuliaLean.base.float.isless_IEEEFloat a b)) xs.toArray x () () none () =
        .returned found ∧
      (∃ b, JuliaLean.base.range.in_Real_AbstractRange x r = .ok b) ∧
      insortedRange linRangeContains x r = .ok found
def binary64Floor (value : Float) : Int :=
  let bits := value.toBits.toNat
  let exponent := bits / 2 ^ 52 % 2048
  let fraction := bits % 2 ^ 52
  let mantissa := if exponent = 0 then fraction else fraction + 2 ^ 52
  let signed : Int := if bits / 2 ^ 63 = 0 then Int.ofNat mantissa else -Int.ofNat mantissa
  let shift := if exponent = 0 then (-1074 : Int) else Int.ofNat exponent - 1075
  if 0 ≤ shift then signed * 2 ^ shift.toNat else signed / 2 ^ (-shift).toNat

def BracketNumericsLaws (numeric : BracketNumerics) : Prop :=
  (∀ (n : Nat), 260 ≤ n → Int.ofNat n ≤ IntTy.max .i64 →
    let root := numeric.cbrt n
    ∃ count : Int, numeric.roundInt (root * root) = .ok count ∧ 1 ≤ count ∧ count ≤ Int.ofNat n) ∧
  (∀ (value : Float), value.toBits.toNat / 2 ^ 52 % 2048 < 2047 →
    IntTy.min .i64 ≤ binary64Floor value → binary64Floor value ≤ IntTy.max .i64 →
    numeric.floorInt value = .ok (binary64Floor value)) ∧
  (∀ n, numeric.topSetBit n = if n = 0 then 0 else Nat.log2 n + 1) ∧
  (∀ (seed : Nat) (lo hi : Int), lo ≤ hi →
    ∃ index, numeric.sampleIndex seed lo hi = .ok index ∧ lo ≤ index ∧ index ≤ hi)

def insertStable {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if lt x y then x :: y :: ys else y :: insertStable lt x ys

def sortRef {α : Type} (lt : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertStable lt x acc) []

def oneBasedIndices (length : Nat) : List Nat :=
  (List.range length).map fun index => index + 1

def SortpermOrdered {α : Type} (lt : α → α → Bool)
    (values : List α) (indices : List Nat) : Prop :=
  ∀ (i j leftIndex rightIndex : Nat) (leftValue rightValue : α),
    i < j →
    indices[i]? = some leftIndex →
    indices[j]? = some rightIndex →
    values[leftIndex - 1]? = some leftValue →
    values[rightIndex - 1]? = some rightValue →
    lt rightValue leftValue = false ∧
      ((lt leftValue rightValue = false ∧ lt rightValue leftValue = false) →
        leftIndex < rightIndex)

/-- A finite prefix of Julia's iteration protocol and the next iterator result. This
relation describes input observations only; it does not mention issorted or comparisons. -/
inductive IterPrefix {I A St E : Type} (iter : IteratorOps I A St E) (itr : I) :
    Except E (Option (A × St)) → List A → Except E (Option (A × St)) → Prop where
  | empty (current : Except E (Option (A × St))) : IterPrefix iter itr current [] current
  | step (x : A) (state : St) (xs : List A) (next : Except E (Option (A × St))) :
      IterPrefix iter itr (iter.next itr state) xs next →
      IterPrefix iter itr (.ok (some (x, state))) (x :: xs) next

/-- Adjacent sequence pairs, independent of the sortedness loop's indices or state. -/
def AdjacentPairs {A : Type} (xs : List A) : List (A × A) := xs.zip xs.tail

def OrderedPrefix {A K : Type} (order : JuliaLean.base.ordering.OrdResult A K)
    (xs : List A) : Prop :=
  ∀ pair ∈ AdjacentPairs xs,
    JuliaLean.base.ordering.ordCompare order pair.2 pair.1 = .ok false

/-- All finite and infinite outcomes under a successfully constructed ordering. A finite
witness may precede an infinite tail. Divergence requires an ascending nonempty next
result at every finite prefix length; finite termination and exceptions are excluded by
that independent protocol condition, rather than by assuming the function returns. -/
def IteratorOutcome {I A K St E : Type} (iter : IteratorOps I A St E) (itr : I)
    (order : JuliaLean.base.ordering.OrdResult A K)
    (run : Option (Except (Sum E JuliaLean.base.ordering.OrderingError) Bool)) : Prop :=
  (run = some (.ok true) ↔ ∃ xs,
    IterPrefix iter itr (iter.first itr) xs (.ok none) ∧ OrderedPrefix order xs) ∧
  (run = some (.ok false) ↔ ∃ xs a b next,
    IterPrefix iter itr (iter.first itr) (xs ++ [a, b]) next ∧
    OrderedPrefix order (xs ++ [a]) ∧
      JuliaLean.base.ordering.ordCompare order b a = .ok true) ∧
  (∀ error, run = some (.error (.inr error)) ↔ ∃ xs a b next,
    IterPrefix iter itr (iter.first itr) (xs ++ [a, b]) next ∧
    OrderedPrefix order (xs ++ [a]) ∧
      JuliaLean.base.ordering.ordCompare order b a = .error error) ∧
  (∀ error, run = some (.error (.inl error)) ↔ ∃ xs,
    IterPrefix iter itr (iter.first itr) xs (.error error) ∧ OrderedPrefix order xs) ∧
  (run = none ↔ ∀ n : Nat, ∃ xs x state,
    xs.length = n ∧
    IterPrefix iter itr (iter.first itr) xs (.ok (some (x, state))) ∧
    OrderedPrefix order (xs ++ [x]))

def IssortedKeywordsCorrect : Prop :=
  ∀ (I A K St E : Type) (iter : IteratorOps I A St E) (itr : I)
      (less : Sum (K → K → JuliaLean.base.ordering.OrderingResult Bool)
        (K → K → JuliaLean.base.ordering.OrderingResult Bool))
      (byArg : JuliaLean.base.ordering.KeyArg A K)
      (rev : Option Bool) (order : JuliaLean.base.ordering.OrderArg K),
    match (if rev = some true then
      JuliaLean.base.ordering.ordBool less byArg true order
    else
      JuliaLean.base.ordering.ordNothing less byArg () order) with
    | .error error => issortedKeywords iter itr less byArg rev order = some (.error (.inr error))
    | .ok resolved =>
        IteratorOutcome iter itr resolved (issortedKeywords iter itr less byArg rev order)

def SearchsortedEquivalentRange : Prop :=
  ∀ (V α L B O : Type) (ops : VectorOps V α) (firstIndex lastIndex : V → JInt .i64)
      (E : V → List α), VectorReadLaws ops firstIndex lastIndex E →
  ∀ (orderOf : L → B → Option Bool → O → O) (lt : O → α → α → SortResult Bool) (v : V) (x : α)
      (less : L) (byFn : B) (rev : Option Bool) (order : O),
    EffectNegTransOrder (lt (orderOf less byFn rev order)) →
    EffectSortedValues (lt (orderOf less byFn rev order)) (E v) →
    let o := orderOf less byFn rev order
    ∃ first last,
      searchsortedKeywords ops firstIndex lastIndex orderOf lt v x less byFn rev order =
        .returned (first, last) ∧
      SearchPartition (readBefore ops (lt o) v x) (firstIndex v).val ((lastIndex v).val + 1)
        first ∧
      SearchPartition (readNotAfter ops (lt o) v x) (firstIndex v).val ((lastIndex v).val + 1)
        (last + 1) ∧
      first ≤ last + 1 ∧
      ∀ index value, ops.read v index = .ok value →
        ((first ≤ index ∧ index ≤ last) ↔ (lt o value x = .ok false ∧ lt o x value = .ok false))
def arraySlice {α : Type} (values : Array α) (lo hi : Int) : List α :=
  (values.toList.drop (lo - 1).toNat).take (hi - lo + 1).toNat

def SendToEndStablePartition : Prop :=
  ∀ (α : Type) (predicate : α → Bool) (values : Array α) (lo hi : Int),
    1 ≤ lo → lo ≤ hi + 1 → hi ≤ values.size →
    (∃ last result,
      (sendToEndBang (storageSendToEndOps arrayStorage)
        (fun value => fun state => .ok (predicate value, state))
        ⟨1, 1, values.size⟩ (some lo) (some hi)).run values = .ok (last, result) ∧
      List.Perm values.toList result.toList ∧
      (arraySlice result lo last).all (fun value => !predicate value) = true ∧
      (arraySlice result (last + 1) hi).all predicate = true ∧
      (arraySlice result lo hi).filter (fun value => !predicate value) =
        (arraySlice values lo hi).filter (fun value => !predicate value) ∧
      result.toList.take (lo - 1).toNat = values.toList.take (lo - 1).toNat ∧
      result.toList.drop hi.toNat = values.toList.drop hi.toNat) ∧
    (∀ endStable : Bool,
      ∃ first last result,
        (sendToEndForwardOrdering (storageSendToEndOps arrayStorage)
          (fun value => fun state => .ok (predicate value, state))
          ⟨1, 1, values.size⟩ endStable lo hi).run values = .ok ((first, last), result) ∧
        first = lo ∧ lo - 1 ≤ last ∧ last ≤ hi ∧
        List.Perm values.toList result.toList ∧
        (arraySlice result lo last).all (fun value => !predicate value) = true ∧
        (arraySlice result (last + 1) hi).all predicate = true ∧
        result.toList.take (lo - 1).toNat = values.toList.take (lo - 1).toNat ∧
        result.toList.drop hi.toNat = values.toList.drop hi.toNat) ∧
    (∀ endStable : Bool,
      ∃ first last result,
        (sendToEndReverseOrdering (storageSendToEndOps arrayStorage)
          (fun value => fun state => .ok (predicate value, state))
          ⟨1, 1, values.size⟩ endStable lo hi).run values = .ok ((first, last), result) ∧
        last = hi ∧ lo ≤ first ∧ first ≤ hi + 1 ∧
        List.Perm values.toList result.toList ∧
        (arraySlice result lo (first - 1)).all predicate = true ∧
        (arraySlice result first hi).all (fun value => !predicate value) = true ∧
        result.toList.take (lo - 1).toNat = values.toList.take (lo - 1).toNat ∧
        result.toList.drop hi.toNat = values.toList.drop hi.toNat)

def BoolSortCorrect : Prop :=
  ∀ (values : Array Bool) (lt : Bool → Bool → SortResult Bool),
    EffectNegTransOrder lt →
    ∃ result, sortBoolVector (storageBoolSortOps arrayStorage) values lt (1, values.size) = .ok result ∧
      List.Perm values.toList result.toList ∧ EffectSortedValues lt result.toList

def RadixSortCorrect : Prop :=
  ∀ (heuristic : Int → Int → JInt .u64 → Jl UInt8)
      (values : Array Nat) (bits : Nat) (chunk : UInt8),
    0 < bits → bits ≤ 128 → 0 < chunk.toNat → chunk.toNat ≤ 10 →
    (∀ value, value ∈ values.toList → value < 2 ^ bits) →
    ∃ vector temporary inVector,
      runArrayRadixSort (arrayRadixOps heuristic) values 1 values.size (JInt.wrap .u64 bits)
        (Array.replicate values.size 0) 0 (some chunk) = some (.ok (vector, temporary, inVector)) ∧
      let result := if inVector then vector else temporary
      List.Perm values.toList result.toList ∧
      SortedValues (fun a b : Nat => decide (a < b)) result.toList


def TupleSortExplicitAlgCorrect : Prop :=
  ∀ (n : Nat) (α : Type) [Inhabited α] (lt : α → α → SortResult Bool)
      (pivot : Int → Int → Int) (tuple : NTuple n α)
      (algorithm : Algorithm (BracketSortTarget Int) Int)
      (reverse : Option Bool),
    EffectNegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    let effective := if reverse = some true then fun a b => lt b a else lt
    ∃ result,
      sortTupleTop (nTuplePublicOps n pivot) tuple algorithm
        lt () reverse lt none = .ok result ∧
      List.Perm tuple.val result.val ∧
      EffectSortedValues effective result.val

def TupleMergeCorrect : Prop :=
  ∀ (m n : Nat) (α : Type) [Inhabited α] (lt : α → α → SortResult Bool)
      (left : NTuple m α) (right : NTuple n α),
    EffectNegTransOrder lt → EffectSortedValues lt left.val → EffectSortedValues lt right.val →
    ∃ result, mergeNTuple lt left right = .ok result ∧
      List.Perm (left.val ++ right.val) result.val ∧ EffectSortedValues lt result.val
def MissingDirectCorrect : Prop :=
  ∀ (Alg : Type) (nextAlgorithm : Alg → Alg)
      (sortWrapped : WithoutMissingVector Int (Array (Option Int)) → Alg → Bool →
        (Int × Int) → SortResult (Array (Option Int)))
      (sortVector : Array (Option Int) → Alg → Bool →
        (Int × Int) → SortResult (Array (Option Int)))
      (values : Array (Option Int)) (algorithm : Alg) (reverse : Bool),
    (∀ (wrapped : WithoutMissingVector Int (Array (Option Int))) (lo hi : Int),
      1 ≤ lo → lo ≤ hi + 1 → hi ≤ wrapped.data.size →
      (arraySlice wrapped.data lo hi).all Option.isSome = true →
      ∃ sorted, sortWrapped wrapped (nextAlgorithm algorithm) reverse (lo, hi) = .ok sorted ∧
        sorted.size = wrapped.data.size ∧
        List.Perm (arraySlice wrapped.data lo hi) (arraySlice sorted lo hi) ∧
        SortedValues (optionIntegerLess reverse) (arraySlice sorted lo hi) ∧
        sorted.toList.take (lo - 1).toNat = wrapped.data.toList.take (lo - 1).toNat ∧
        sorted.toList.drop hi.toNat = wrapped.data.toList.drop hi.toNat) →
    ∃ result,
      sortMissingOptimization
        (arrayMissingDirectOpsWithNext nextAlgorithm sortWrapped sortVector)
        values algorithm reverse (1, values.size) = .ok result ∧
      List.Perm values.toList result.toList ∧
      SortedValues (optionIntegerLess reverse) result.toList

def MissingPermutationCorrect : Prop :=
  ∀ (Alg : Type) (nextAlgorithm : Alg → Alg)
      (sortWrapped : WithoutMissingVector Int (Array (Option Int)) → Alg → Bool →
        (Int × Int) → SortResult (Array Int))
      (sortVector : Array Int → Alg → Bool → (Int × Int) → SortResult (Array Int))
      (values : Array (Option Int)) (algorithm : Alg) (reverse : Bool),
    let initial := (arrayIndexRange 1 values.size).toArray
    (∀ (current : Array Int) (lo hi : Int),
      1 ≤ lo → lo ≤ hi + 1 → hi ≤ current.size →
      current.size = values.size →
      (arraySlice current lo hi).Nodup →
      (∀ idx ∈ arraySlice current lo hi,
        1 ≤ idx ∧ idx ≤ Int.ofNat values.size ∧
        ∃ v, values[(idx - 1).toNat]? = some (some v)) →
      ∃ sorted, sortVector current (nextAlgorithm algorithm) reverse (lo, hi) = .ok sorted ∧
        sorted.size = current.size ∧
        List.Perm (arraySlice current lo hi) (arraySlice sorted lo hi) ∧
        SortpermOrdered (optionIntegerLess reverse) values.toList
          ((arraySlice sorted lo hi).map Int.toNat) ∧
        sorted.toList.take (lo - 1).toNat = current.toList.take (lo - 1).toNat ∧
        sorted.toList.drop hi.toNat = current.toList.drop hi.toNat) →
    ∃ result,
      sortMissingOptimization
        (arrayMissingPermutationOpsWithNext values nextAlgorithm sortWrapped sortVector)
        initial algorithm reverse (1, values.size) = .ok result ∧
      List.Perm initial.toList result.toList ∧
      SortpermOrdered (optionIntegerLess reverse) values.toList (result.toList.map Int.toNat)


/-- `sort!(v; scratch)` on a `Vector{Union{Missing, Int32}}` accepts a same-typed scratch vector
(sort.jl:511-516, 651-655, 1732-1741), through the installed public `sort!` model. -/
def SortMissingScratchAccepted : Prop :=
  ∀ (values scratch : Array (Option (JInt .i32))),
    ∃ sorted, sortMissingInt32Default juliaPivot values false (some scratch) = some (.ok sorted)

namespace MissingScratch


/-- The 98-element prefix case in repro/sorttuplescov-sort-missing-scratch.jl. -/
def values : Int32Values :=
  ((List.range 98).map fun index : Nat =>
    if index = 16 then none else
      some (JInt.lit .i32 (Int.ofNat (((137 * (index + 1)) % 1000) * 1000000)))).toArray

def scratch : Int32Values := Array.replicate 98 none

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fails : sortMissingInt32Default juliaPivot values false (some scratch) =
    some (.error (.jl (.argumentError "cannot reinterpret a non-bits scratch element type"))) := by
  decide +kernel


end MissingScratch

theorem sortMissingScratchAccepted_refuted : ¬ SortMissingScratchAccepted := by
  intro h
  obtain ⟨sorted, run⟩ := h MissingScratch.values MissingScratch.scratch
  rw [MissingScratch.fails] at run
  cases run

def IEEECodecLaws {α : Type} (codec : IEEECodec α) : Prop :=
  (∀ value, codec.decode (codec.encode value) = .ok value) ∧
  (∀ value, codec.encode value < 2 ^ 64) ∧
  (∀ a b, codec.less a b = .ok (
    if codec.isNaN b then !codec.isNaN a
    else if codec.isNaN a then false
    else if codec.signbit a != codec.signbit b then codec.signbit a
    else if codec.signbit a then decide (codec.encode b < codec.encode a)
    else decide (codec.encode a < codec.encode b)))

def IEEEFloatOptimizationCorrect : Prop :=
  (∀ (α : Type) (signbit : α → Bool) (x : α),
    afterZeroForward signbit x = !signbit x ∧
    afterZeroReverse signbit x = signbit x) ∧
  (∀ (isIEEE isConcrete : Type → Bool) (T : Type),
    isConcreteIEEEFloat isIEEE isConcrete T = (isIEEE T && isConcrete T)) ∧
  (∀ (α Alg : Type) (codec : IEEECodec α) (nextAlgorithm : Alg → Alg)
      (sortUnsigned : Array Nat → Alg → Bool → ArraySortKeywords Nat →
        SortResult (Array Nat × Option (Array Nat)))
      (sortFallback : Array α → Alg → Bool → ArraySortKeywords Nat →
        SortResult (Array α × Option (Array Nat)))
      (values : Array α) (algorithm : Alg) (reverse : Bool),
    IEEECodecLaws codec →
    codec.isIEEEFloat α = true → codec.isConcrete α = true →
    (∀ (bits : Array Nat) (rev : Bool) (kw : ArraySortKeywords Nat),
      1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 → kw.hi ≤ bits.size →
      ∃ sorted scratch,
        sortUnsigned bits (nextAlgorithm algorithm) rev kw = .ok (sorted, scratch) ∧
        sorted.size = bits.size ∧
        List.Perm (arraySlice bits kw.lo kw.hi) (arraySlice sorted kw.lo kw.hi) ∧
        SortedValues (fun a b : Nat => if rev then decide (b < a) else decide (a < b))
          (arraySlice sorted kw.lo kw.hi) ∧
        sorted.toList.take (kw.lo - 1).toNat = bits.toList.take (kw.lo - 1).toNat ∧
        sorted.toList.drop kw.hi.toNat = bits.toList.drop kw.hi.toNat) →
    ∃ result scratch,
      sortIEEEFloatOptimization
        (arrayIEEEDirectOpsWithNext codec nextAlgorithm sortUnsigned sortFallback)
        values algorithm reverse { lo := 1, hi := values.size } = .ok (result, scratch) ∧
      List.Perm values.toList result.toList ∧
      EffectSortedValues (if reverse then fun a b => codec.less b a else codec.less) result.toList ∧
      result.toList.filter codec.isNaN = values.toList.filter codec.isNaN)

def UIntVectorRoundTrip : Prop :=
  ∀ (t : IntTy) (values : Array (JInt t)) (lo hi : Int) (reverse : Bool),
    1 ≤ lo → lo ≤ hi + 1 → hi ≤ values.size →
    ∃ mapped,
      uintMapVectorBang (arrayIntegerMapOps t) values lo hi reverse = .ok mapped ∧
      mapped.size = values.size ∧
      uintUnmapVectorBang (arrayIntegerUnmapOps t) values mapped lo hi reverse = .ok values ∧
      (∀ index value, lo ≤ index → index ≤ hi → arrayRead values index = .ok value →
        arrayRead mapped index = .ok (integerCode t reverse value).val.toNat)

def RadixWrapperCorrect : Prop :=
  ∀ (t : IntTy) (heuristic : Int → Int → JInt .u64 → Jl UInt8)
      (values : Array (JInt t)) (minimum maximum : JInt t) (reverse : Bool),
    let low := if reverse then maximum.val else minimum.val
    let high := if reverse then minimum.val else maximum.val
    low ≤ high →
    (∀ value, value ∈ values.toList → low ≤ value.val ∧ value.val ≤ high) →
    ∃ result scratch,
      sortRadixAlgorithm (arrayRadixWrapperOps t heuristic) values reverse
        { lo := 1, hi := values.size, minimum, maximum } = some (.ok (result, scratch)) ∧
      List.Perm values.toList result.toList ∧
      SortedValues (fun a b : JInt t =>
        if reverse then decide (b.val < a.val) else decide (a.val < b.val)) result.toList

def sliceRows {α : Type} (width count : Nat) (values : List α) : List (List α) :=
  (List.range count).map fun index => (values.drop (index * width)).take width

def DimensionLayoutLaws {A α Axes : Type} (layout : DimensionArrayLayout A α Axes) : Prop :=
  ∀ array dimension, 1 ≤ dimension → dimension ≤ layout.ndims array →
    let before := layout.slices array dimension
    let width := layout.axisLength array dimension
    (∀ row, row ∈ before → row.length = width) ∧
    if dimension = 1 then
      layout.copyLinear array = .ok before.flatten.toArray ∧
      ∀ (updated : Array α), updated.size = before.flatten.length →
        ∃ result, layout.reshapeOriginalAxes array updated = .ok result ∧
          layout.axes result = layout.axes array ∧
          layout.slices result dimension = sliceRows width before.length updated.toList
    else
      let permutation := dimension ::
        ((List.range (layout.ndims array)).map Nat.succ).filter (· != dimension)
      ∃ permuted, layout.permute array permutation = .ok permuted ∧
        layout.vectorize permuted = .ok before.flatten.toArray ∧
        ∀ (updated : Array α), updated.size = before.flatten.length →
          ∃ result, layout.restorePermuted permuted updated
              (layout.inversePermutation permutation) = .ok result ∧
            layout.axes result = layout.axes array ∧
            layout.slices result dimension = sliceRows width before.length updated.toList

def SliceLayoutLaws {A α Axes Index K : Type}
    (layout : SliceArrayLayout A α Axes Index K) : Prop :=
  ∀ array dimension, 1 ≤ dimension → dimension ≤ layout.ndims array →
    let width := layout.axisLength array dimension
    ∃ indices, layout.cartesianIndices array dimension = .ok indices ∧
      indices.length = (layout.slices array dimension).length ∧
      (∀ row, row ∈ layout.slices array dimension → row.length = width) ∧
      ∀ current, layout.axes current = layout.axes array →
        layout.ndims current = layout.ndims array ∧
        layout.axisLength current dimension = width ∧
        (layout.slices current dimension).length = indices.length ∧
        (∀ (i : Nat) index row, indices[i]? = some index →
          (layout.slices current dimension)[i]? = some row →
          layout.view current (sliceSelectors layout current dimension index) =
            .ok row.toArray) ∧
        (∀ (i : Nat) index (updated : Array α), indices[i]? = some index →
          updated.size = width →
          ∃ result, layout.writeView current
              (sliceSelectors layout current dimension index) updated = .ok result ∧
            layout.axes result = layout.axes current ∧
            layout.slices result dimension =
              (layout.slices current dimension).set i updated.toList)


def BalancedParentheses (text : String) : Prop :=
  text.toList.count '(' = text.toList.count ')' ∧
  ∀ initial rest : List Char, text.toList = initial ++ rest →
    initial.count ')' ≤ initial.count '('

def displayTypeText {Alg Name : Type} (typeName : Alg → Name) (nameText : Name → String)
    (smallThreshold? : Alg → Option Nat) (algorithm : Alg) : String :=
  match smallThreshold? algorithm with
  | some n => "Base.Sort.Small{" ++ toString n ++ "}"
  | none => nameText (typeName algorithm)

def DisplayPrimitiveLaws {IO Alg Name Arg E : Type}
    (ops : AlgorithmDisplayOps IO Alg Name Arg E) (text : IO → String)
    (nameText : Name → String) (smallThreshold? : Alg → Option Nat)
    (argumentText : Arg → String) : Prop :=
  (∀ io printed result, ops.print io printed = .ok result →
    text result = text io ++ printed) ∧
  (∀ io printed result, ops.println io printed = .ok result →
    text result = text io ++ printed ++ "\n") ∧
  (∀ io algorithm,
    ops.showType io algorithm =
      match smallThreshold? algorithm with
      | some n => showSmallAlgorithmType ops io n
      | none => showAlgorithmType ops io algorithm) ∧
  (∀ io name result, ops.showTypeName io name = .ok result →
    text result = text io ++ nameText name) ∧
  (∀ io argument result, ops.printArgument io argument = .ok result →
    text result = text io ++ argumentText argument) ∧
  (∀ algorithm, BalancedParentheses (displayTypeText ops.algorithmTypeName nameText smallThreshold? algorithm)) ∧
  (∀ argument, BalancedParentheses (argumentText argument))

def AlgorithmDisplayWellFormed : Prop :=
  ∀ (IO Alg Name Arg E : Type) (ops : AlgorithmDisplayOps IO Alg Name Arg E)
      (text : IO → String) (nameText : Name → String)
      (smallThreshold? : Alg → Option Nat) (argumentText : Arg → String),
    DisplayPrimitiveLaws ops text nameText smallThreshold? argumentText →
    ∀ (io : IO), text io = "" →
      (∀ algorithm columns result,
        printAlgorithmTree ops io algorithm columns = .ok result →
        BalancedParentheses (text result)) ∧
      (∀ algorithm result,
        showAlgorithm (printAlgorithmTree ops) io algorithm = .ok result →
        BalancedParentheses (text result))
def SubArraySortCorrect : Prop :=
  ∀ (α Alg : Type) [Inhabited α] (lt : α → α → SortResult Bool)
      (nextAlgorithm : Alg → Alg)
      (view : FlatSortView α) (algorithm : Alg),
    EffectNegTransOrder lt →
    0 ≤ view.offset → view.offset + Int.ofNat view.length ≤ view.parent.storage.size →
    let sortSlice := fun (v : Array α) (_ : Alg) (o : α → α → SortResult Bool) (kw : ArraySortKeywords α) => do
      let sorted ← storageInsertion arrayStorage o v kw.lo kw.hi
      pure (sorted, kw.scratch)
    ∃ result, sortSubArrayUnwrappable
        (flatSubArraySortOpsWithNext view nextAlgorithm sortSlice)
        view algorithm lt { lo := 1, hi := view.length } = .ok result ∧
      result.offset = view.offset ∧ result.length = view.length ∧
      result.parent.dimensions = view.parent.dimensions ∧
      List.Perm view.parent.storage.toList result.parent.storage.toList ∧
      EffectSortedValues lt (arraySlice result.parent.storage
        (view.offset + 1) (view.offset + Int.ofNat view.length)) ∧
      result.parent.storage.toList.take view.offset.toNat =
        view.parent.storage.toList.take view.offset.toNat ∧
      result.parent.storage.toList.drop (view.offset + Int.ofNat view.length).toNat =
        view.parent.storage.toList.drop (view.offset + Int.ofNat view.length).toNat

/-- The only assumed law concerns unary log: log(0)=-Inf and positive inputs return
finite, nonnegative results. No heuristic or modeled floating-operation law is assumed. -/
def UnsignedLogLaws {u : IntTy} (log : JInt u → Jl F64) : Prop :=
  (∀ x, x.val = 0 →
    log x = .ok (JuliaLean.base.float.neg_IEEEFloat
      (JuliaLean.base.float.inf_float .f64))) ∧
  (∀ x, 0 < x.val → ∃ y, log x = .ok y ∧
    JuliaLean.base.float.isfinite_IEEEFloat y = true ∧
    JuliaLean.base.float.le_IEEEFloat (JuliaLean.base.float.zero_float .f64) y = true)

/-- sort-radix-chunk-covers-bits: native integer component after R7.1. Every native
bound-type pair and unsigned bit-count width is included, even when mixed-width
subtraction wraps. -/
def RadixChunkCoversBits : Prop :=
  ∀ (s t u : IntTy) (ieee : JuliaLean.base.math.IEEEOps .f64)
      (log : JInt (t.promote s).toUnsigned → Jl F64),
    UnsignedLogLaws log →
    ∀ (lo : JInt s) (hi : JInt t) (bits : JInt u.toUnsigned),
      lo.val < hi.val → 0 < bits.val → bits.val ≤ 128 →
      ∃ chunk,
        (radixChunkSizeHeuristic ieee log lo hi bits).run = some (.ok chunk) ∧
        1 ≤ chunk.val ∧ chunk.val ≤ 10 ∧ chunk.val ≤ bits.val ∧
        bits.val.toNat ≤
          ((bits.val.toNat + chunk.val.toNat - 1) / chunk.val.toNat) * chunk.val.toNat

def IEEEFloatPermutationCorrect : Prop :=
  ∀ (α Alg : Type) [Inhabited α] (codec : IEEECodec α)
      (nextAlgorithm : Alg → Alg)
      (sortPermutation : Array Int → Alg → (Bool × Array Nat) → ArraySortKeywords Nat →
        SortResult (Array Int × Option (Array Nat)))
      (sortFallback : Array Int → Alg → (Bool × Array α) → ArraySortKeywords Nat →
        SortResult (Array Int × Option (Array Nat)))
      (data : Array α) (initial : Array Int) (algorithm : Alg) (reverse : Bool),
    IEEECodecLaws codec →
    codec.isIEEEFloat α = true → codec.isConcrete α = true →
    initial.toList = arrayIndexRange 1 data.size →
    (∀ (indices : Array Int) (rev : Bool) (unsignedData : Array Nat) (kw : ArraySortKeywords Nat),
      1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 → kw.hi ≤ indices.size →
      unsignedData = data.map codec.encode →
      (arraySlice indices kw.lo kw.hi).Nodup →
      (∀ idx ∈ arraySlice indices kw.lo kw.hi, 1 ≤ idx ∧ idx ≤ Int.ofNat data.size) →
      ∃ sorted scratch,
        sortPermutation indices (nextAlgorithm algorithm) (rev, unsignedData) kw =
          .ok (sorted, scratch) ∧
        sorted.size = indices.size ∧
        List.Perm (arraySlice indices kw.lo kw.hi) (arraySlice sorted kw.lo kw.hi) ∧
        SortpermOrdered (fun a b : Nat => if rev then decide (b < a) else decide (a < b))
          unsignedData.toList ((arraySlice sorted kw.lo kw.hi).map Int.toNat) ∧
        sorted.toList.take (kw.lo - 1).toNat = indices.toList.take (kw.lo - 1).toNat ∧
        sorted.toList.drop kw.hi.toNat = indices.toList.drop kw.hi.toNat) →
    ∃ result scratch,
      sortIEEEFloatOptimization
        (arrayIEEEPermutationOpsWithNext codec nextAlgorithm sortPermutation sortFallback)
        initial algorithm (reverse, data)
        { lo := 1, hi := initial.size } = .ok (result, scratch) ∧
      List.Perm initial.toList result.toList ∧
      EffectSortpermOrdered (if reverse then fun a b => codec.less b a else codec.less)
        data.toList (result.toList.map Int.toNat)

/-! ## Proofs and Refutations (Batch 1) -/


theorem u8WindowReadsZero :
    searchsortedlastBounds arrayVectorOps (fun _ a b => .ok (decide (a < b))) ()
      (Array.replicate 255 (0 : Int)) 0 (JInt.lit .u8 1) (JInt.lit .u8 255) =
      .invalidAccess 0 := by
  decide +kernel


theorem rangeSearchNonemptyCorrect_refuted : ¬ RangeSearchNonemptyCorrect := by
  intro h
  have hv : RangeValid (t := .i8) (JInt.lit .i8 (-100)) (JInt.lit .i8 1)
      (JInt.lit .i8 100) (JInt.lit .i64 201) := by
    unfold RangeValid rangeElem; decide
  have hs : RangeSorted (t := .i8) (JInt.lit .i8 1) (JInt.lit .i64 201) false := by
    unfold RangeSorted; decide
  have hq : RealQueryValid ⟨50, 50⟩ := by unfold RealQueryValid; decide
  obtain ⟨first, last, _, hr, _, _, hc⟩ :=
    h .i8 _ _ _ _ ⟨50, 50⟩ false hv hs hq (by decide)
  have e : searchsortedlastIntegerRange (bitIntegerRealRangeOps .i8) (fun o a b => .ok (realQueryLt o a b)) false
      (JInt.lit .i8 (-100), JInt.lit .i8 1, JInt.lit .i8 100, JInt.lit .i64 201)
      ⟨50, 50⟩ = .ok (JInt.lit .i64 (-105)) := rfl
  rw [e] at hr
  cases hr
  exact absurd hc.1 (by decide)


theorem juliaPivot_bounds : ∀ lo hi : Int, lo ≤ hi →
    lo ≤ juliaPivot lo hi ∧ juliaPivot lo hi ≤ hi := by
  intro lo hi hle
  have hpos : 0 < (hi - lo + 1).toNat := by omega
  have key : ∀ d : Nat, lo ≤ lo + ((d % (hi - lo + 1).toNat : Nat) : Int) ∧
      lo + ((d % (hi - lo + 1).toNat : Nat) : Int) ≤ hi := by
    intro d
    have hmod := Nat.mod_lt d hpos
    omega
  exact key _

def intLt (a b : Int) : Bool := decide (a < b)

/-- The concrete integer primitive used by the counterexamples cannot throw. -/
def intCompare (a b : Int) : SortResult Bool := .ok (intLt a b)

theorem intCompare_order : EffectNegTransOrder intCompare := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    exact ⟨intLt a b, rfl⟩
  · intro a
    simp [intCompare, intLt]
  · intro a b c
    simp [intCompare, intLt]
    omega
  · intro a b c
    simp [intCompare, intLt]
    omega


theorem intLt_negTransOrder : NegTransOrder intLt := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; simp [intLt]
  · intro a b c; simp [intLt]; omega
  · intro a b c; simp [intLt]; omega

def reversedRangeInput : Array Int :=
  #[4, 5, 2, 1, 1, 4, 4, 4, 2, 4, 5, 5, 3, 3, 2, 2, 4, 5, 2, 2, 5, 5]
theorem reversedRangePartialSortOutcome :
    partialSortBang (storagePartialSortOps arrayStorage defaultBracketNumerics juliaPivot)
      reversedRangeInput (.ordinal 5 (-1) 3 3) (pureCompare intLt) none = .ok (.elements [2, 2, 1]) := by
  decide +kernel

def legacyPartialInput : Array Int :=
  #[1, 3, 4, 5, 3, 5, 5, 2, 1, 4, 5, 1, 4, 3, 5, 5, 5, 4, 3, 5, 5, 2]

theorem legacyPartialRangeOutcome :
    (match legacyPartialQuickSortBang (storagePartialQuickOps arrayStorage intCompare)
        legacyPartialInput 1 (Int.ofNat legacyPartialInput.size) (5, 3) () with
      | .ok out =>
        some (((List.range 3).map (fun i => (5 : Int) + Int.ofNat i * (-1))).filterMap
          (fun index => out[(index - 1).toNat]?))
      | .error _ => none) = some [2, 1, 1] := by
  decide +kernel

theorem legacyPartialRangeExpected :
    ((List.range 3).map (fun i => (5 : Int) + Int.ofNat i * (-1))).filterMap
      (fun index => (sortRef intLt legacyPartialInput.toList)[(index - 1).toNat]?) =
      [2, 2, 1] := by
  decide +kernel

def dummySliceLayout : SliceArrayLayout Unit Int Unit Nat Int where
  ndims := fun _ => 2
  axisLength := fun _ _ => 2
  cartesianIndices := fun _ _ => .ok [1, 2]
  coordinate := fun i _ => Int.ofNat i
  view := fun _ _ => .ok #[1, 2]
  writeView := fun _ _ _ => .ok ()
  axes := fun _ => ()
  slices := fun _ _ => [[1, 2], [1, 2]]


theorem forIn_window_check {V α K O E : Type}
    (indices : IntegerIndexOps K) (get : V → K → Except E α)
    (lt : O → α → α → Bool) (v : V) (order : O) :
    ∀ (xs : List K),
      (∀ i ∈ xs, ∃ current previous, get v i = .ok current ∧ get v (indices.previous i) = .ok previous) →
      ((do
        for i in xs do
          if lt order (← get v i) (← get v (indices.previous i)) then
            return false
        pure true : Except E Bool) = .ok true ↔
        ∀ i ∈ xs, ∃ current previous, get v i = .ok current ∧
          get v (indices.previous i) = .ok previous ∧ lt order current previous = false)
  | [], _ => by
    change (Except.ok true : Except E Bool) = .ok true ↔ _
    simp
  | i :: rest, hreads => by
    obtain ⟨curr, prev, hcurr, hprev⟩ := hreads i (by simp)
    have hrest : ∀ j ∈ rest, ∃ current previous, get v j = .ok current ∧
        get v (indices.previous j) = .ok previous :=
      fun j hj => hreads j (by simp [hj])
    simp only [List.forIn_cons, hcurr, hprev, bind, Except.bind, pure, Except.pure]
    cases hlt : lt order curr prev
    · simp only [Bool.false_eq_true, ↓reduceIte]
      change ((do
        for j in rest do
          if lt order (← get v j) (← get v (indices.previous j)) then
            return false
        pure true : Except E Bool) = .ok true ↔ _)
      rw [forIn_window_check indices get lt v order rest hrest]
      constructor
      · intro h j hj
        rcases List.mem_cons.1 hj with rfl | hj
        · exact ⟨curr, prev, hcurr, hprev, hlt⟩
        · exact h j hj
      · intro h j hj
        exact h j (by simp [hj])
    · simp only [↓reduceIte, Except.ok.injEq, Bool.false_eq_true, false_iff]
      intro hall
      obtain ⟨c, p, hc, hp, hf⟩ := hall i List.mem_cons_self
      rw [hcurr] at hc; cases hc
      rw [hprev] at hp; cases hp
      rw [hlt] at hf; cases hf


/-! ## Proofs and Refutations (Batch 2: Search and Range Search) -/

abbrev I64Idx (x : Int) : SearchIndex := searchIndex .i64 x

theorem I64Idx_val {x : Int} (h0 : IntTy.min .i64 ≤ x) (h1 : x ≤ IntTy.max .i64) :
    (I64Idx x).val = x :=
  wrapInt_of_inRange .i64 x ⟨h0, h1⟩

theorem add_I64Idx {a b : Int}
    (ha0 : IntTy.min .i64 ≤ a) (ha1 : a ≤ IntTy.max .i64)
    (hb0 : IntTy.min .i64 ≤ b) (hb1 : b ≤ IntTy.max .i64) :
    indexAdd (I64Idx a) (I64Idx b) = I64Idx (a + b) := by
  unfold indexAdd
  rw [I64Idx_val ha0 ha1, I64Idx_val hb0 hb1]
  rfl

theorem sub_I64Idx {a b : Int}
    (ha0 : IntTy.min .i64 ≤ a) (ha1 : a ≤ IntTy.max .i64)
    (hb0 : IntTy.min .i64 ≤ b) (hb1 : b ≤ IntTy.max .i64) :
    indexSub (I64Idx a) (I64Idx b) = I64Idx (a - b) := by
  unfold indexSub
  rw [I64Idx_val ha0 ha1, I64Idx_val hb0 hb1]
  rfl

theorem half_I64Idx {a : Int} (ha0 : 0 ≤ a) (ha1 : a ≤ IntTy.max .i64) :
    indexHalf (I64Idx a) = I64Idx (a / 2) := by
  unfold indexHalf
  have hmin : IntTy.min .i64 ≤ 0 := by decide
  have hmax : IntTy.max .i64 < 2 ^ 64 := by decide
  rw [I64Idx_val (by omega) ha1]
  show searchIndex .i64 ((a % 2 ^ 64) / 2) = _
  rw [Int.emod_eq_of_lt ha0 (by omega)]

theorem mid_I64Idx {a b : Int} (h0 : 0 ≤ a) (h1 : a ≤ b) (h2 : b ≤ IntTy.max .i64) :
    indexMidpoint (I64Idx a) (I64Idx b) = I64Idx (a + (b - a) / 2) := by
  have hmin : IntTy.min .i64 ≤ 0 := by decide
  unfold indexMidpoint
  rw [sub_I64Idx (by omega) (by omega) (by omega) (by omega),
    half_I64Idx (by omega) (by omega),
    add_I64Idx (by omega) (by omega) (by omega) (by omega)]

theorem arrayVectorOps_read_some {α : Type} {v : Array α} {i : Int}
    (h1 : 1 ≤ i) (h2 : i ≤ v.size) :
    ∃ a, arrayVectorOps.read v i = .ok a := by
  unfold arrayVectorOps
  dsimp only
  have hb : 1 ≤ i ∧ i ≤ (v.size : Int) := ⟨h1, h2⟩
  rw [if_pos hb]
  refine ⟨v[i.toNat - 1]'(by omega), ?_⟩
  rw [Array.getElem?_eq_getElem (by omega)]

theorem before_of_read {α : Type} {lt : α → α → Bool} {v : Array α} {x a : α} {i : Int}
    (h : arrayVectorOps.read v i = .ok a) :
    before (pureCompare lt) v x i = .ok (lt a x) := by
  simp [before, h, pureCompare, bind, Except.bind]

theorem notAfter_of_read {α : Type} {lt : α → α → Bool} {v : Array α} {x a : α} {i : Int}
    (h : arrayVectorOps.read v i = .ok a) :
    notAfter (pureCompare lt) v x i = .ok (!(lt x a)) := by
  simp [notAfter, h, pureCompare, bind, Except.bind, Except.map]
  rfl

theorem firstLoop_correct {α : Type} (lt : α → α → Bool) (v : Array α) (x : α)
    (hsz : v.size < IntTy.max .i64)
    (mono : ∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size →
      before (pureCompare lt) v x j = .ok true → before (pureCompare lt) v x i = .ok true) :
    ∀ (fuel len : Nat) (lo : Int) (hiIdx : SearchIndex),
      len < fuel → 1 ≤ lo → lo + len ≤ v.size + 1 →
      ∃ r, firstSearchLoop arrayVectorOps (fun _ a b => pureCompare lt a b) () v x fuel (I64Idx lo) hiIdx (I64Idx len) = .returned r ∧
        SearchPartition (before (pureCompare lt) v x) lo (lo + len) r := by
  have hmin : IntTy.min .i64 ≤ 0 := by decide
  intro fuel
  induction fuel with
  | zero => intro len lo hiIdx h; omega
  | succ fuel ih =>
    intro len lo hiIdx hfuel hlo hhi
    unfold firstSearchLoop
    rw [I64Idx_val (by omega) (by omega)]
    by_cases hz : (len : Int) = 0
    · rw [if_pos hz]
      refine ⟨_, rfl, ?_⟩
      rw [I64Idx_val (by omega) (by omega)]
      refine ⟨by omega, by omega, fun i h1 h2 => by omega, fun i h1 h2 => by omega⟩
    · rw [if_neg hz]
      have hhalf : indexHalf (I64Idx len) = I64Idx ((len : Int) / 2) := half_I64Idx (by omega) (by omega)
      have hm : indexAdd (I64Idx lo) (I64Idx ((len : Int) / 2)) = I64Idx (lo + (len : Int) / 2) :=
        add_I64Idx (by omega) (by omega) (by omega) (by omega)
      have hmv : (I64Idx (lo + (len : Int) / 2)).val = lo + (len : Int) / 2 := I64Idx_val (by omega) (by omega)
      simp only [hhalf, hm, hmv]
      obtain ⟨a, ha⟩ := arrayVectorOps_read_some (v := v) (i := lo + (len : Int) / 2) (by omega) (by omega)
      rw [ha]
      simp only [pureCompare]
      cases hc : lt a x
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hl2 : ((len : Int) / 2) = (((len / 2 : Nat)) : Int) := by omega
        rw [hl2]
        obtain ⟨r, hr, hp⟩ := ih (len / 2) lo (I64Idx (lo + ↑(len / 2))) (by omega) hlo (by omega)
        refine ⟨r, hr, ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hp
        have hmb : before (pureCompare lt) v x (lo + (len : Int) / 2) = .ok false := by
          rw [before_of_read ha, hc]
        refine ⟨h1, by omega, h3, ?_⟩
        intro i hi1 hi2
        by_cases hi : i < lo + ((len / 2 : Nat) : Int)
        · exact h4 i hi1 hi
        · obtain ⟨b, hb⟩ := arrayVectorOps_read_some (v := v) (i := i) (by omega) (by omega)
          rw [before_of_read hb]
          cases hbi : lt b x with
          | false => rfl
          | true =>
            have hb' : before (pureCompare lt) v x i = .ok true := by rw [before_of_read hb, hbi]
            have := mono (lo + (len : Int) / 2) i (by omega) (by omega) (by omega) hb'
            rw [hmb] at this; cases this
      · simp only [↓reduceIte]
        have e1 : indexAdd (I64Idx (lo + (len : Int) / 2)) (I64Idx 1) = I64Idx (lo + (len : Int) / 2 + 1) :=
          add_I64Idx (by omega) (by omega) (by omega) (by omega)
        have e2 : indexAdd (I64Idx ((len : Int) / 2)) (I64Idx 1) = I64Idx ((len : Int) / 2 + 1) :=
          add_I64Idx (by omega) (by omega) (by omega) (by omega)
        have e3 : indexSub (I64Idx len) (I64Idx ((len : Int) / 2 + 1)) = I64Idx ((len : Int) - ((len : Int) / 2 + 1)) :=
          sub_I64Idx (by omega) (by omega) (by omega) (by omega)
        rw [e1, e2, e3]
        have hl2 : (len : Int) - ((len : Int) / 2 + 1) = (((len - len / 2 - 1 : Nat)) : Int) := by omega
        rw [hl2]
        obtain ⟨r, hr, hp⟩ := ih (len - len / 2 - 1) (lo + (len : Int) / 2 + 1) hiIdx
          (by omega) (by omega) (by omega)
        refine ⟨r, hr, ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hp
        have hmb : before (pureCompare lt) v x (lo + (len : Int) / 2) = .ok true := by
          rw [before_of_read ha, hc]
        refine ⟨by omega, by omega, ?_, fun i hi1 hi2 => h4 i hi1 (by omega)⟩
        intro i hi1 hi2
        by_cases hi : lo + (len : Int) / 2 + 1 ≤ i
        · exact h3 i hi hi2
        · exact mono i (lo + (len : Int) / 2) (by omega) (by omega) (by omega) hmb

theorem lastLoop_correct {α : Type} (lt : α → α → Bool) (v : Array α) (x : α)
    (hsz : v.size < IntTy.max .i64)
    (mono : ∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size →
      notAfter (pureCompare lt) v x j = .ok true → notAfter (pureCompare lt) v x i = .ok true) :
    ∀ (fuel gap : Nat) (lo : Int), gap < fuel → 0 ≤ lo → lo + gap + 1 ≤ v.size + 1 →
      ∃ r, lastSearchLoop arrayVectorOps (fun _ a b => pureCompare lt a b) () v x (I64Idx 1) fuel (I64Idx lo) (I64Idx (lo + gap + 1)) = .returned r ∧
        SearchPartition (notAfter (pureCompare lt) v x) (lo + 1) (lo + gap + 1) (r + 1) := by
  have hmin : IntTy.min .i64 ≤ 0 := by decide
  intro fuel
  induction fuel with
  | zero => intro gap lo h; omega
  | succ fuel ih =>
    intro gap lo hfuel hlo hhi
    unfold lastSearchLoop
    have e0 : indexSub (I64Idx (lo + gap + 1)) (I64Idx 1) = I64Idx (lo + gap + 1 - 1) :=
      sub_I64Idx (by omega) (by omega) (by omega) (by omega)
    rw [e0, I64Idx_val (by omega) (by omega), I64Idx_val (by omega) (by omega)]
    by_cases hz : (gap : Int) = 0
    · rw [if_pos (by omega)]
      refine ⟨lo, rfl, ?_⟩
      refine ⟨by omega, by omega, fun i h1 h2 => by omega, fun i h1 h2 => by omega⟩
    · rw [if_neg (by omega)]
      have em : indexMidpoint (I64Idx lo) (I64Idx (lo + gap + 1)) = I64Idx (lo + (lo + gap + 1 - lo) / 2) :=
        mid_I64Idx (by omega) (by omega) (by omega)
      have emv : (I64Idx (lo + (lo + gap + 1 - lo) / 2)).val = lo + (lo + gap + 1 - lo) / 2 :=
        I64Idx_val (by omega) (by omega)
      simp only [em, emv]
      obtain ⟨a, ha⟩ := arrayVectorOps_read_some (v := v) (i := lo + (lo + gap + 1 - lo) / 2) (by omega) (by omega)
      rw [ha]
      simp only [pureCompare]
      have hmr : lo < lo + (lo + gap + 1 - lo) / 2 ∧ lo + (lo + gap + 1 - lo) / 2 < lo + gap + 1 := by
        omega
      generalize hmd : lo + (lo + gap + 1 - lo) / 2 = m at *
      cases hc : lt x a
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have he : lo + ↑gap + 1 = m + (((lo + gap - m : Int).toNat : Nat) : Int) + 1 := by omega
        rw [he]
        obtain ⟨r, hr, hp⟩ := ih (lo + gap - m).toNat m (by omega) (by omega) (by omega)
        refine ⟨r, hr, ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hp
        have hmv : notAfter (pureCompare lt) v x m = .ok true := by
          simp [notAfter_of_read ha, hc]
        refine ⟨by omega, by omega, ?_, fun i hi1 hi2 => h4 i hi1 (by omega)⟩
        intro i hi1 hi2
        by_cases hi : m + 1 ≤ i
        · exact h3 i hi hi2
        · exact mono i m (by omega) (by omega) (by omega) hmv
      · simp only [↓reduceIte]
        have he : m = lo + (((m - lo - 1 : Int).toNat : Nat) : Int) + 1 := by omega
        obtain ⟨r, hr, hp⟩ := ih (m - lo - 1).toNat lo (by omega) hlo (by omega)
        rw [← he] at hr hp
        refine ⟨r, hr, ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hp
        have hmv : notAfter (pureCompare lt) v x m = .ok false := by
          simp [notAfter_of_read ha, hc]
        refine ⟨h1, by omega, h3, ?_⟩
        intro i hi1 hi2
        by_cases hi : i < m
        · exact h4 i hi1 hi
        · obtain ⟨b, hb⟩ := arrayVectorOps_read_some (v := v) (i := i) (by omega) (by omega)
          rw [notAfter_of_read hb]
          cases hbi : lt x b with
          | false =>
            have hb' : notAfter (pureCompare lt) v x i = .ok true := by
              simp [notAfter_of_read hb, hbi]
            have := mono m i (by omega) (by omega) (by omega) hb'
            rw [hmv] at this; cases this
          | true => rfl


theorem search_monotone {α : Type} {lt : α → α → Bool} {v : Array α} {x : α}
    (hnt : NegTransOrder lt) (hs : VecSorted lt v) :
    (∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size →
      before (pureCompare lt) v x j = .ok true → before (pureCompare lt) v x i = .ok true) ∧
    (∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size →
      notAfter (pureCompare lt) v x j = .ok true → notAfter (pureCompare lt) v x i = .ok true) ∧
    (∀ i : Int, 1 ≤ i → i ≤ v.size →
      before (pureCompare lt) v x i = .ok true → notAfter (pureCompare lt) v x i = .ok true) := by
  obtain ⟨hirr, htrans, hneg⟩ := hnt
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hij hj hb
    obtain ⟨a, ha⟩ := arrayVectorOps_read_some (v := v) (i := i) hi (by omega)
    obtain ⟨b, hb'⟩ := arrayVectorOps_read_some (v := v) (i := j) (by omega) hj
    rw [before_of_read hb'] at hb
    rw [before_of_read ha]
    simp only [Except.ok.injEq] at hb ⊢
    rcases hneg b a x hb with h | h
    · rw [hs i j a b hij ha hb'] at h; exact absurd h (by decide)
    · exact h
  · intro i j hi hij hj hb
    obtain ⟨a, ha⟩ := arrayVectorOps_read_some (v := v) (i := i) hi (by omega)
    obtain ⟨b, hb'⟩ := arrayVectorOps_read_some (v := v) (i := j) (by omega) hj
    rw [notAfter_of_read hb'] at hb
    rw [notAfter_of_read ha]
    simp only [Except.ok.injEq] at hb ⊢
    cases hxa : lt x a with
    | false => rfl
    | true =>
      rcases hneg x b a hxa with h | h
      · rw [h] at hb; exact absurd hb (by decide)
      · rw [hs i j a b hij ha hb'] at h; exact absurd h (by decide)
  · intro i hi1 hi2 hb
    obtain ⟨a, ha⟩ := arrayVectorOps_read_some (v := v) (i := i) hi1 hi2
    rw [before_of_read ha] at hb
    rw [notAfter_of_read ha]
    simp only [Except.ok.injEq] at hb ⊢
    cases hxa : lt x a with
    | false => rfl
    | true =>
      have hxx := htrans a x a hb hxa
      rw [hirr a] at hxx
      cases hxx





theorem tmin_nonpos (t : IntTy) : t.min ≤ 0 := by
  cases t <;> decide

theorem tmax_pos (t : IntTy) : 1 ≤ t.max := by
  cases t <;> decide

theorem unsigned_min (t : IntTy) (h : t.signed = false) : t.min = 0 := by
  cases t <;> simp_all [IntTy.signed, IntTy.min]

theorem signed_max (t : IntTy) (h : t.signed = true) : t.max = -t.min - 1 := by
  cases t <;> simp_all [IntTy.signed, IntTy.min, IntTy.max]

theorem wrap_val {t : IntTy} (z : Int) (h : t.min ≤ z ∧ z ≤ t.max) :
    (JInt.wrap t z).val = z := wrapInt_of_inRange t z h

theorem sub_val {t : IntTy} (a b : JInt t)
    (h : t.min ≤ a.val - b.val ∧ a.val - b.val ≤ t.max) :
    (a - b).val = a.val - b.val := wrapInt_of_inRange t _ h

theorem qfacts (D H : Int) (hD : 0 ≤ D) (hH : 0 < H) :
    0 ≤ D / H ∧ D / H * H ≤ D ∧ D < (D / H + 1) * H ∧ D / H ≤ D := by
  have e := Int.mul_ediv_add_emod D H
  have m0 := Int.emod_nonneg D (show H ≠ 0 by omega)
  have m1 := Int.emod_lt_of_pos D hH
  have q0 : 0 ≤ D / H := Int.ediv_nonneg hD (by omega)
  have hc : H * (D / H) = D / H * H := Int.mul_comm _ _
  have hs : (D / H + 1) * H = D / H * H + H := by rw [Int.add_mul, Int.one_mul]
  have hq : D / H * 1 ≤ D / H * H := Int.mul_le_mul_of_nonneg_left (show 1 ≤ H by omega) q0
  rw [Int.mul_one] at hq
  refine ⟨q0, ?_, ?_, ?_⟩ <;> omega

theorem floor_char {D H : Int} (hH : 0 < H) (k : Int) : k ≤ D / H ↔ k * H ≤ D :=
  Int.le_ediv_iff_mul_le hH

theorem ceil_char {D H : Int} (hD : 0 ≤ D) (hH : 0 < H) (k : Int) :
    k < D / H + (if D / H * H ≠ D then 1 else 0) ↔ k * H < D := by
  obtain ⟨q0, qle, qlt, -⟩ := qfacts D H hD hH
  have hs : (D / H + 1) * H = D / H * H + H := by rw [Int.add_mul, Int.one_mul]
  by_cases hne : D / H * H ≠ D
  · rw [if_pos hne]
    constructor
    · intro hk
      have : k * H ≤ D / H * H := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      omega
    · intro hk
      have := Int.lt_of_mul_lt_mul_right (show k * H < (D / H + 1) * H by omega) (by omega)
      omega
  · rw [if_neg hne]
    have heq : D / H * H = D := by omega
    constructor
    · intro hk
      have := Int.mul_lt_mul_of_pos_right (show k < D / H by omega) hH
      omega
    · intro hk
      have := Int.lt_of_mul_lt_mul_right (show k * H < D / H * H by omega) (by omega)
      omega

theorem div_ok {t : IntTy} (a b : JInt t) (hb : b.val ≠ 0)
    (hn : ¬ (t.signed = true ∧ a.val = t.min ∧ b.val = -1)) :
    JInt.div a b = .ok (JInt.wrap t (a.val.tdiv b.val)) := by
  unfold JInt.div
  rw [if_neg hb, if_neg hn]

theorem add_lit {t : IntTy} (d : JInt t) (c : Int) (hc : c = 0 ∨ c = 1)
    (h : d.val + c ≤ t.max) : (d + JInt.lit t c).val = d.val + c := by
  have hm := tmin_nonpos t
  have h1 := tmax_pos t
  show wrapInt t (d.val + wrapInt t c) = _
  rw [wrapInt_of_inRange t c ⟨by omega, by omega⟩]
  exact wrapInt_of_inRange t _ ⟨by have := d.property.1; omega, h⟩

theorem sub_lit0 {t : IntTy} (d : JInt t) : (d - JInt.lit t 0).val = d.val := by
  have hm := tmin_nonpos t
  have h1 := tmax_pos t
  show wrapInt t (d.val - wrapInt t 0) = _
  rw [wrapInt_of_inRange t 0 ⟨by omega, by omega⟩, Int.sub_zero]
  exact wrapInt_of_inRange t _ d.property

theorem fldcld_pos {t : IntTy} (a b : JInt t) (ha : 0 ≤ a.val) (hb : 0 < b.val) :
    (∃ r, JInt.fld a b = .ok r ∧ r.val = a.val / b.val) ∧
    (∃ r, JInt.cld a b = .ok r ∧
      r.val = a.val / b.val + (if a.val / b.val * b.val ≠ a.val then 1 else 0)) := by
  obtain ⟨q0, qle, qlt, qa⟩ := qfacts a.val b.val ha hb
  have hmin := tmin_nonpos t
  have hamax := a.property.2
  have ht : a.val.tdiv b.val = a.val / b.val := Int.tdiv_eq_ediv_of_nonneg ha
  have hd := div_ok a b (by omega) (fun ⟨_, _, h⟩ => by omega)
  rw [ht] at hd
  generalize hq : a.val / b.val = q at *
  have wq : (JInt.wrap t q).val = q := wrap_val _ ⟨by omega, by omega⟩
  have hqb := Int.mul_nonneg q0 (show 0 ≤ b.val by omega)
  have wprod : (JInt.wrap t q * b).val = q * b.val := by
    show wrapInt t ((JInt.wrap t q).val * b.val) = _
    rw [wq]
    exact wrapInt_of_inRange t _ ⟨by omega, by omega⟩
  constructor
  · unfold JInt.fld
    rw [hd]
    simp only [bind, Except.bind]
    cases hs : t.signed
    · exact ⟨JInt.wrap t q, rfl, wq⟩
    · have hc : ¬ (((a.val < 0 ∧ 0 ≤ b.val) ∨ (0 ≤ a.val ∧ b.val < 0)) ∧
          (JInt.wrap t q * b).val ≠ a.val) := fun ⟨h1, _⟩ => by omega
      refine ⟨JInt.wrap t q - JInt.lit t 0, ?_, by rw [sub_lit0, wq]⟩
      rw [if_pos rfl, if_neg hc]
      rfl
  · unfold JInt.cld
    rw [hd]
    simp only [bind, Except.bind]
    by_cases hc : q * b.val ≠ a.val
    · have hpos : 0 < a.val := by
        rcases Int.lt_or_le 0 a.val with h' | h'
        · exact h'
        · exfalso
          have ha0 : a.val = 0 := by omega
          rw [ha0, Int.zero_ediv] at hq
          subst hq
          rw [Int.zero_mul] at hc
          exact hc ha0.symm
      have hcond : (¬ t.signed = true ∨ (a.val > 0 ↔ b.val > 0)) ∧
          (JInt.wrap t q * b).val ≠ a.val :=
        ⟨Or.inr ⟨fun _ => hb, fun _ => hpos⟩, by rw [wprod]; exact hc⟩
      refine ⟨JInt.wrap t q + JInt.lit t 1, ?_, ?_⟩
      · rw [if_pos hcond]
        rfl
      · have hqqb : q * 1 ≤ q * b.val := Int.mul_le_mul_of_nonneg_left (by omega) q0
        rw [Int.mul_one] at hqqb
        rw [if_pos hc, add_lit _ 1 (Or.inr rfl) (by rw [wq]; omega), wq]
    · have hcond : ¬ ((¬ t.signed = true ∨ (a.val > 0 ↔ b.val > 0)) ∧
          (JInt.wrap t q * b).val ≠ a.val) := by rw [wprod]; exact fun h => hc h.2
      refine ⟨JInt.wrap t q + JInt.lit t 0, ?_, ?_⟩
      · rw [if_neg hcond]
        rfl
      · rw [if_neg hc, add_lit _ 0 (Or.inl rfl) (by rw [wq]; omega), wq]

theorem fldcld_neg {t : IntTy} (a b : JInt t) (ha : a.val ≤ 0) (hb : b.val < 0)
    (hmin' : t.min < a.val) :
    (∃ r, JInt.fld a b = .ok r ∧ r.val = (-a.val) / (-b.val)) ∧
    (∃ r, JInt.cld a b = .ok r ∧
      r.val = (-a.val) / (-b.val) +
        (if (-a.val) / (-b.val) * (-b.val) ≠ -a.val then 1 else 0)) := by
  have hsg : t.signed = true := by
    cases hs : t.signed
    · have := unsigned_min t hs; have := b.property.1; omega
    · rfl
  obtain ⟨q0, qle, qlt, qa⟩ := qfacts (-a.val) (-b.val) (by omega) (by omega)
  have hmin := tmin_nonpos t
  have hbmin := b.property.1
  have hmx := signed_max t hsg
  have ht : a.val.tdiv b.val = (-a.val) / (-b.val) := by
    rw [← Int.neg_tdiv_neg, Int.tdiv_eq_ediv_of_nonneg (by omega)]
  have hd := div_ok a b (by omega) (fun ⟨_, h, _⟩ => by omega)
  rw [ht] at hd
  generalize hq : (-a.val) / (-b.val) = q at *
  have wq : (JInt.wrap t q).val = q := wrap_val _ ⟨by omega, by omega⟩
  have hprod : q * b.val = -(q * (-b.val)) := by rw [Int.mul_neg, Int.neg_neg]
  have hqb0 : 0 ≤ q * (-b.val) := Int.mul_nonneg q0 (by omega)
  have wprod : (JInt.wrap t q * b).val = q * b.val := by
    show wrapInt t ((JInt.wrap t q).val * b.val) = _
    rw [wq]
    exact wrapInt_of_inRange t _ ⟨by omega, by omega⟩
  constructor
  · unfold JInt.fld
    rw [hd]
    simp only [bind, Except.bind]
    have hc : ¬ (((a.val < 0 ∧ 0 ≤ b.val) ∨ (0 ≤ a.val ∧ b.val < 0)) ∧
        (JInt.wrap t q * b).val ≠ a.val) := by
      rw [wprod]
      intro ⟨h1, h2⟩
      rcases h1 with h1 | h1
      · omega
      · have ha0 : a.val = 0 := by omega
        rw [ha0, Int.neg_zero, Int.zero_ediv] at hq
        subst hq
        rw [Int.zero_mul] at h2
        exact h2 ha0.symm
    refine ⟨JInt.wrap t q - JInt.lit t 0, ?_, by rw [sub_lit0, wq]⟩
    rw [if_pos hsg, if_neg hc]
    rfl
  · unfold JInt.cld
    rw [hd]
    simp only [bind, Except.bind]
    by_cases hc : q * (-b.val) ≠ -a.val
    · have hcond : (¬ t.signed = true ∨ (a.val > 0 ↔ b.val > 0)) ∧
          (JInt.wrap t q * b).val ≠ a.val :=
        ⟨Or.inr ⟨fun _ => by omega, fun _ => by omega⟩, by rw [wprod]; omega⟩
      refine ⟨JInt.wrap t q + JInt.lit t 1, ?_, ?_⟩
      · rw [if_pos hcond]
        rfl
      · have hqqb : q * 1 ≤ q * (-b.val) := Int.mul_le_mul_of_nonneg_left (by omega) q0
        rw [Int.mul_one] at hqqb
        rw [if_pos hc, add_lit _ 1 (Or.inr rfl) (by rw [wq]; omega), wq]
    · have hcond : ¬ ((¬ t.signed = true ∨ (a.val > 0 ↔ b.val > 0)) ∧
          (JInt.wrap t q * b).val ≠ a.val) := by rw [wprod]; intro h; omega
      refine ⟨JInt.wrap t q + JInt.lit t 0, ?_, ?_⟩
      · rw [if_neg hcond]
        rfl
      · rw [if_neg hc, add_lit _ 0 (Or.inl rfl) (by rw [wq]; omega), wq]

theorem elemLt_false (a b : Int) : elemLt false a b = decide (a < b) := rfl
theorem elemLt_true (a b : Int) : elemLt true a b = decide (b < a) := rfl

theorem iff_not' {A B : Prop} (h : A ↔ B) : ¬A ↔ ¬B :=
  ⟨fun na b => na (h.mpr b), fun nb a => nb (h.mp a)⟩

macro "elem_tac" : tactic => `(tactic| (
  simp only [elemLt_false, elemLt_true, rangeElem, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not, Int.not_lt]
  omega))

theorem addOne_key {t : IntTy} (q : JInt t) (h0 : 0 ≤ q.val)
    (h1 : q.val + 1 < IntTy.max .i64) :
    ∃ r, toKeytype (addOneInt q) = .ok r ∧ r.val = q.val + 1 := by
  have hw : addOneInt q = q.val + 1 := by
    unfold addOneInt
    apply wrapInt_of_inRange
    cases t <;> simp [IntTy.promote, IntTy.bits, IntTy.signed, IntTy.min, IntTy.max] at h1 ⊢ <;> omega
  unfold toKeytype JInt.convert
  rw [hw, dif_pos ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega, by omega⟩]
  exact ⟨_, rfl, rfl⟩

theorem lit_one : (JInt.lit .i64 1).val = 1 := by decide
theorem lit_zero : (JInt.lit .i64 0).val = 0 := by decide

theorem len_add_one (len : JInt64) (h0 : 0 ≤ len.val) (h : len.val < IntTy.max .i64) :
    (len + JInt.lit .i64 1).val = len.val + 1 := by
  show wrapInt .i64 (len.val + wrapInt .i64 1) = _
  rw [wrapInt_of_inRange .i64 1 (by decide)]
  exact wrapInt_of_inRange .i64 _ ⟨by simp [IntTy.min, IntTy.signed, IntTy.bits]; omega, by omega⟩
theorem rangeSearchNoOverflowCorrect_int :
    ∀ (t : IntTy) (f h l : JInt t) (len : JInt64) (x : JInt t) (rev : Bool),
      RangeValid f h l len → RangeSorted h len rev → 1 ≤ len.val →
      t.min + (if t.signed then 1 else 0) ≤ x.val - f.val → x.val - f.val ≤ t.max →
      RangeAnswers f h l len x rev := by
  intro t f h l len x rev hv hs hne hdlo hdhi
  obtain ⟨hn0, hnmax, hh0, hl⟩ := hv
  rw [if_neg (by omega)] at hl
  unfold rangeElem at hl
  have hmin := tmin_nonpos t
  have hsmin : t.min ≤ x.val - f.val := by split at hdlo <;> omega
  have hd : (x - f).val = x.val - f.val := sub_val x f ⟨hsmin, hdhi⟩
  have hv1 := len_add_one len hn0 hnmax
  unfold RangeSorted at hs
  unfold RangeAnswers FirstContract LastContract
  generalize hN : len.val = n at *
  have hboth :
      (∃ first,
        searchsortedfirstIntegerRange (bitIntegerRangeOps t) (fun o a b => .ok (rangeLt o a b)) rev (f, h, l, len) x = .ok first ∧
        1 ≤ first.val ∧ first.val ≤ n + 1 ∧
        (∀ i, 1 ≤ i → i < first.val → elemLt rev (rangeElem f h i) x.val = true) ∧
        (∀ i, first.val ≤ i → i ≤ n → elemLt rev (rangeElem f h i) x.val = false)) ∧
      (∃ last,
        searchsortedlastIntegerRange (bitIntegerRangeOps t) (fun o a b => .ok (rangeLt o a b)) rev (f, h, l, len) x = .ok last ∧
        0 ≤ last.val ∧ last.val ≤ n ∧
        (∀ i, 1 ≤ i → i ≤ last.val → (!elemLt rev x.val (rangeElem f h i)) = true) ∧
        (∀ i, last.val < i → i ≤ n → (!elemLt rev x.val (rangeElem f h i)) = false)) := by
    cases rev
    · simp only [Bool.false_eq_true, ↓reduceIte] at hs
      have hmono : ∀ i, 1 ≤ i → i ≤ n →
          0 ≤ (i - 1) * h.val ∧ (i - 1) * h.val ≤ (n - 1) * h.val := by
        intro i hi1 hin
        by_cases h2 : 2 ≤ n
        · have hp := hs h2
          exact ⟨Int.mul_nonneg (by omega) (by omega),
            Int.mul_le_mul_of_nonneg_right (by omega) (by omega)⟩
        · have e1 : i - 1 = 0 := by omega
          have e2 : n - 1 = 0 := by omega
          rw [e1, e2, Int.zero_mul]
          exact ⟨Int.le_refl 0, Int.le_refl 0⟩
      constructor
      · unfold searchsortedfirstIntegerRange bitIntegerRangeOps rangeLt
        dsimp only [bind, Except.bind, pure, Except.pure, id_eq]
        simp only [hh0, decide_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
        by_cases b1 : f.val < x.val
        · rw [if_neg (by simpa using b1)]
          by_cases b2 : l.val < x.val
          · rw [if_pos (by simp [b2])]
            refine ⟨_, rfl, by omega, by omega, ?_, ?_⟩
            · intro i hi1 hir; have := hmono i hi1 (by omega); elem_tac
            · intro i hir hin; omega
          · have hn2 : 2 ≤ n := by
              refine Classical.byContradiction fun hc => ?_
              have e2 : n - 1 = 0 := by omega
              rw [e2, Int.zero_mul] at hl; omega
            have hp := hs hn2
            rw [if_neg (by simp [b2])]
            obtain ⟨-, r, hr, hrv⟩ := fldcld_pos (x - f) h (by omega) hp
            rw [hr]
            simp only [bind, Except.bind]
            rw [hd] at hrv
            have hceil := ceil_char (D := x.val - f.val) (by omega) hp
            have hq0 := (qfacts (x.val - f.val) h.val (by omega) hp).1
            have hc0 : 0 ≤ r.val := by rw [hrv]; split <;> omega
            have hcn : r.val ≤ n - 1 := by
              have := (iff_not' (hceil (n - 1))).mpr (by omega)
              rw [← hrv] at this; omega
            obtain ⟨k, hk, hkv⟩ := addOne_key r hc0 (by omega)
            rw [hk]
            refine ⟨k, rfl, ?_⟩
            rw [hkv]
            refine ⟨by omega, by omega, ?_, ?_⟩
            · intro i hi1 hir
              have := (hceil (i - 1)).mp (by rw [← hrv]; omega)
              elem_tac
            · intro i hir hin
              have := (iff_not' (hceil (i - 1))).mp (by rw [← hrv]; omega)
              elem_tac
        · rw [if_pos (by simpa using b1)]
          refine ⟨_, rfl, ?_⟩
          rw [lit_one]
          refine ⟨by omega, by omega, fun i hi1 hir => by omega, ?_⟩
          intro i hir hin; have := hmono i hir hin; elem_tac
      · unfold searchsortedlastIntegerRange bitIntegerRangeOps rangeLt
        dsimp only [bind, Except.bind, pure, Except.pure, id_eq]
        simp only [hh0, decide_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
        by_cases b1 : x.val < f.val
        · rw [if_pos (by simpa using b1)]
          refine ⟨_, rfl, ?_⟩
          rw [lit_zero]
          refine ⟨by omega, by omega, fun i hi1 hir => by omega, ?_⟩
          intro i hir hin; have := hmono i (by omega) hin; elem_tac
        · rw [if_neg (by simpa using b1)]
          by_cases b2 : x.val < l.val
          · have hn2 : 2 ≤ n := by
              refine Classical.byContradiction fun hc => ?_
              have e2 : n - 1 = 0 := by omega
              rw [e2, Int.zero_mul] at hl; omega
            have hp := hs hn2
            rw [if_neg (by simp [b2])]
            obtain ⟨⟨r, hr, hrv⟩, -⟩ := fldcld_pos (x - f) h (by omega) hp
            rw [hr]
            simp only [bind, Except.bind]
            rw [hd] at hrv
            have hq0 := (qfacts (x.val - f.val) h.val (by omega) hp).1
            have hlt : (x.val - f.val) / h.val < n - 1 :=
              (Int.ediv_lt_iff_lt_mul hp).mpr (by omega)
            obtain ⟨k, hk, hkv⟩ := addOne_key r (by omega) (by omega)
            rw [hk]
            refine ⟨k, rfl, ?_⟩
            rw [hkv]
            refine ⟨by omega, by omega, ?_, ?_⟩
            · intro i hi1 hir
              have := (floor_char (D := x.val - f.val) hp (i - 1)).mp (by omega)
              elem_tac
            · intro i hir hin
              have := (iff_not' (floor_char (D := x.val - f.val) hp (i - 1))).mp (by omega)
              elem_tac
          · rw [if_pos (by simp [b2])]
            refine ⟨_, rfl, by omega, by omega, ?_, ?_⟩
            · intro i hi1 hir; have := hmono i hi1 (by omega); elem_tac
            · intro i hir hin; omega
    · simp only [↓reduceIte] at hs
      have hmono : ∀ i, 1 ≤ i → i ≤ n →
          0 ≤ (i - 1) * (-h.val) ∧ (i - 1) * (-h.val) ≤ (n - 1) * (-h.val) := by
        intro i hi1 hin
        by_cases h2 : 2 ≤ n
        · have hp := hs h2
          exact ⟨Int.mul_nonneg (by omega) (by omega),
            Int.mul_le_mul_of_nonneg_right (by omega) (by omega)⟩
        · have e1 : i - 1 = 0 := by omega
          have e2 : n - 1 = 0 := by omega
          rw [e1, e2, Int.zero_mul]
          exact ⟨Int.le_refl 0, Int.le_refl 0⟩
      have neg_mul : ∀ k : Int, k * h.val = -(k * (-h.val)) := fun k => by
        rw [Int.mul_neg, Int.neg_neg]
      have hl' : l.val = f.val - (n - 1) * (-h.val) := by rw [hl, neg_mul]; omega
      have hsg : ∀ _ : h.val < 0, t.min < (x - f).val := by
        intro hp
        have hs' : t.signed = true := by
          cases hs' : t.signed
          · have := unsigned_min t hs'; have := h.property.1; omega
          · rfl
        rw [hs'] at hdlo; simp at hdlo; omega
      constructor
      · unfold searchsortedfirstIntegerRange bitIntegerRangeOps rangeLt
        dsimp only [bind, Except.bind, pure, Except.pure, id_eq]
        simp only [hh0, decide_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
        by_cases b1 : x.val < f.val
        · rw [if_neg (by simpa using b1)]
          by_cases b2 : x.val < l.val
          · rw [if_pos (by simp [b2])]
            refine ⟨_, rfl, by omega, by omega, ?_, ?_⟩
            · intro i hi1 hir
              have := hmono i hi1 (by omega); have := neg_mul (i - 1); elem_tac
            · intro i hir hin; omega
          · have hn2 : 2 ≤ n := by
              refine Classical.byContradiction fun hc => ?_
              have e2 : n - 1 = 0 := by omega
              rw [e2, Int.zero_mul] at hl'; omega
            have hp := hs hn2
            rw [if_neg (by simp [b2])]
            obtain ⟨-, r, hr, hrv⟩ := fldcld_neg (x - f) h (by omega) hp (hsg hp)
            rw [hr]
            simp only [bind, Except.bind]
            rw [hd] at hrv
            have hceil := ceil_char (D := -(x.val - f.val)) (H := -h.val) (by omega) (by omega)
            have hq0 := (qfacts (-(x.val - f.val)) (-h.val) (by omega) (by omega)).1
            have hc0 : 0 ≤ r.val := by rw [hrv]; split <;> omega
            have hcn : r.val ≤ n - 1 := by
              have := (iff_not' (hceil (n - 1))).mpr (by omega)
              rw [← hrv] at this; omega
            obtain ⟨k, hk, hkv⟩ := addOne_key r hc0 (by omega)
            rw [hk]
            refine ⟨k, rfl, ?_⟩
            rw [hkv]
            refine ⟨by omega, by omega, ?_, ?_⟩
            · intro i hi1 hir
              have := (hceil (i - 1)).mp (by rw [← hrv]; omega)
              have := neg_mul (i - 1); elem_tac
            · intro i hir hin
              have := (iff_not' (hceil (i - 1))).mp (by rw [← hrv]; omega)
              have := neg_mul (i - 1); elem_tac
        · rw [if_pos (by simpa using b1)]
          refine ⟨_, rfl, ?_⟩
          rw [lit_one]
          refine ⟨by omega, by omega, fun i hi1 hir => by omega, ?_⟩
          intro i hir hin; have := hmono i hir hin; have := neg_mul (i - 1); elem_tac
      · unfold searchsortedlastIntegerRange bitIntegerRangeOps rangeLt
        dsimp only [bind, Except.bind, pure, Except.pure, id_eq]
        simp only [hh0, decide_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
        by_cases b1 : f.val < x.val
        · rw [if_pos (by simpa using b1)]
          refine ⟨_, rfl, ?_⟩
          rw [lit_zero]
          refine ⟨by omega, by omega, fun i hi1 hir => by omega, ?_⟩
          intro i hir hin; have := hmono i (by omega) hin; have := neg_mul (i - 1); elem_tac
        · rw [if_neg (by simpa using b1)]
          by_cases b2 : l.val < x.val
          · have hn2 : 2 ≤ n := by
              refine Classical.byContradiction fun hc => ?_
              have e2 : n - 1 = 0 := by omega
              rw [e2, Int.zero_mul] at hl'; omega
            have hp := hs hn2
            rw [if_neg (by simp [b2])]
            obtain ⟨⟨r, hr, hrv⟩, -⟩ := fldcld_neg (x - f) h (by omega) hp (hsg hp)
            rw [hr]
            simp only [bind, Except.bind]
            rw [hd] at hrv
            have hq0 := (qfacts (-(x.val - f.val)) (-h.val) (by omega) (by omega)).1
            have hlt : (-(x.val - f.val)) / (-h.val) < n - 1 :=
              (Int.ediv_lt_iff_lt_mul (by omega)).mpr (by omega)
            obtain ⟨k, hk, hkv⟩ := addOne_key r (by omega) (by omega)
            rw [hk]
            refine ⟨k, rfl, ?_⟩
            rw [hkv]
            refine ⟨by omega, by omega, ?_, ?_⟩
            · intro i hi1 hir
              have := (floor_char (D := -(x.val - f.val)) (H := -h.val) (by omega) (i - 1)).mp (by omega)
              have := neg_mul (i - 1); elem_tac
            · intro i hir hin
              have := (iff_not' (floor_char (D := -(x.val - f.val)) (H := -h.val) (by omega) (i - 1))).mp (by omega)
              have := neg_mul (i - 1); elem_tac
          · rw [if_pos (by simp [b2])]
            refine ⟨_, rfl, by omega, by omega, ?_, ?_⟩
            · intro i hi1 hir; have := hmono i hi1 (by omega); have := neg_mul (i - 1); elem_tac
            · intro i hir hin; omega
  obtain ⟨⟨first, hfirst, hf1, hf2, hf3, hf4⟩, ⟨last, hlast, hl1, hl2, hl3, hl4⟩⟩ := hboth
  refine ⟨first, last, hfirst, hlast, ?_, ⟨hf1, hf2, hf3, hf4⟩, ⟨hl1, hl2, hl3, hl4⟩⟩
  unfold searchsortedIntegerRange
  rw [hfirst, hlast]
  rfl



/-! ## Proofs and Refutations (Batch 3) -/

theorem negTransOrder_asymm {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) {a b : α} (hab : lt a b = true) : lt b a = false := by
  obtain ⟨hirr, htrans, _⟩ := hnt
  cases hba : lt b a
  · rfl
  · have := htrans a b a hab hba
    rw [hirr a] at this
    cases this

theorem negTransOrder_not_trans {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) {a b c : α} (hab : lt a b = false) (hbc : lt b c = false) :
    lt a c = false := by
  obtain ⟨_, _, hneg⟩ := hnt
  cases hac : lt a c
  · rfl
  · rcases hneg a b c hac with h | h
    · rw [hab] at h; cases h
    · rw [hbc] at h; cases h

theorem sortedValues_iff_pairwise {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) :
    ∀ (xs : List α), SortedValues lt xs ↔ xs.Pairwise (fun a b => lt b a = false)
  | [] => by simp [SortedValues]
  | [a] => by simp [SortedValues]
  | a :: b :: rest => by
    unfold SortedValues
    rw [sortedValues_iff_pairwise hnt (b :: rest)]
    constructor
    · rintro ⟨hba, hpw⟩
      refine List.Pairwise.cons ?_ hpw
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hba
      · have hzb := (List.pairwise_cons.1 hpw).1 z hz
        exact negTransOrder_not_trans hnt hzb hba
    · intro hpw
      have ⟨hall, hpw'⟩ := List.pairwise_cons.1 hpw
      exact ⟨hall b (by simp), hpw'⟩

theorem mergeAnyNTupleLoop_correct {α : Type} [Inhabited α] {lt : α → α → Bool}
    (hnt : NegTransOrder lt) :
    ∀ (fuel : Nat) (left right : AnyNTuple α),
      left.2.val.length + right.2.val.length < fuel →
      SortedValues lt left.2.val →
      SortedValues lt right.2.val →
      ∃ merged,
        mergeAnyNTupleLoop (pureCompare lt) fuel left right = .ok merged ∧
        List.Perm (left.2.val ++ right.2.val) merged.2.val ∧
        SortedValues lt merged.2.val
  | 0, left, right, hfuel, _, _ => by omega
  | fuel + 1, ⟨m, ⟨xs, hxs⟩⟩, ⟨n, ⟨ys, hys⟩⟩, hfuel, hleft, hright => by
    unfold mergeAnyNTupleLoop
    cases xs with
    | nil =>
      cases ys with
      | nil =>
        exact ⟨⟨m, ⟨[], hxs⟩⟩, rfl, List.Perm.refl _, trivial⟩
      | cons y ys' =>
        exact ⟨⟨n, ⟨y :: ys', hys⟩⟩, rfl, by simp, hright⟩
    | cons x xs' =>
      cases ys with
      | nil =>
        exact ⟨⟨m, ⟨x :: xs', hxs⟩⟩, rfl, by simp, hleft⟩
      | cons y ys' =>
        dsimp only [mergeTupleNonempty, List.headD_cons, List.tail_cons]
        simp only [pureCompare, bind, Except.bind]
        have hpwL := (sortedValues_iff_pairwise hnt (x :: xs')).1 hleft
        have hpwR := (sortedValues_iff_pairwise hnt (y :: ys')).1 hright
        have hleft' : SortedValues lt xs' :=
          (sortedValues_iff_pairwise hnt xs').2 (List.pairwise_cons.1 hpwL).2
        have hright' : SortedValues lt ys' :=
          (sortedValues_iff_pairwise hnt ys').2 (List.pairwise_cons.1 hpwR).2
        by_cases hlt : lt y x = true
        · simp only [hlt, ↓reduceIte]
          obtain ⟨rest, hrec, hperm, hsort⟩ :=
            mergeAnyNTupleLoop_correct hnt fuel
              ⟨m, ⟨x :: xs', hxs⟩⟩ ⟨n - 1, ⟨ys', by simp at hys; omega⟩⟩
              (by simp at hfuel ⊢; omega) hleft hright'
          rw [hrec]
          simp only [bind, Except.bind, pure, Except.pure]
          refine ⟨_, rfl, ?_, ?_⟩
          · exact List.Perm.trans List.perm_middle (List.Perm.cons y hperm)
          · rw [sortedValues_iff_pairwise hnt]
            have hpwRest := (sortedValues_iff_pairwise hnt rest.2.val).1 hsort
            refine List.Pairwise.cons ?_ hpwRest
            intro z hz
            have hz' : z ∈ (x :: xs') ++ ys' := hperm.symm.subset hz
            have hxy : lt x y = false := negTransOrder_asymm hnt hlt
            rcases List.mem_append.1 hz' with hzx | hzy
            · rcases List.mem_cons.1 hzx with rfl | hzx'
              · exact hxy
              · have hzx0 := (List.pairwise_cons.1 hpwL).1 z hzx'
                exact negTransOrder_not_trans hnt hzx0 hxy
            · exact (List.pairwise_cons.1 hpwR).1 z hzy
        · have hltF : lt y x = false := Bool.eq_false_iff.2 hlt
          simp only [hltF, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨rest, hrec, hperm, hsort⟩ :=
            mergeAnyNTupleLoop_correct hnt fuel
              ⟨m - 1, ⟨xs', by simp at hxs; omega⟩⟩ ⟨n, ⟨y :: ys', hys⟩⟩
              (by simp at hfuel ⊢; omega) hleft' hright
          rw [hrec]
          simp only [bind, Except.bind, pure, Except.pure]
          refine ⟨_, rfl, List.Perm.cons x hperm, ?_⟩
          rw [sortedValues_iff_pairwise hnt]
          have hpwRest := (sortedValues_iff_pairwise hnt rest.2.val).1 hsort
          refine List.Pairwise.cons ?_ hpwRest
          intro z hz
          have hz' : z ∈ xs' ++ (y :: ys') := hperm.symm.subset hz
          rcases List.mem_append.1 hz' with hzx | hzy
          · exact (List.pairwise_cons.1 hpwL).1 z hzx
          · rcases List.mem_cons.1 hzy with rfl | hzy'
            · exact hltF
            · have hzy0 := (List.pairwise_cons.1 hpwR).1 z hzy'
              exact negTransOrder_not_trans hnt hzy0 hltF

theorem tupleMergeCorrect_proven : TupleMergeCorrect := by
  intro m n α _ lt left right hnt hleft hright
  obtain ⟨p, hp, rfl⟩ := effect_pure_cases hnt
  have hsorted : ∀ xs : List α,
      EffectSortedValues (pureCompare (ε := SortException) p) xs ↔ SortedValues p xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      cases xs with
      | nil => rfl
      | cons b rest =>
        change (pureCompare (ε := SortException) p b a = .ok false ∧
          EffectSortedValues (pureCompare p) (b :: rest)) ↔
          (p b a = false ∧ SortedValues p (b :: rest))
        rw [ih]
        simp only [pureCompare, Except.ok.injEq]
  obtain ⟨merged, hloop, hperm, hsort⟩ :=
    mergeAnyNTupleLoop_correct hp (m + n + 1) ⟨m, left⟩ ⟨n, right⟩
      (by simp [left.property, right.property]) ((hsorted left.val).1 hleft) ((hsorted right.val).1 hright)
  have hlen : merged.2.val.length = m + n := by
    rw [← hperm.length_eq, List.length_append, left.property, right.property]
  unfold mergeNTuple
  rw [hloop]
  simp only [bind, Except.bind, pure, Except.pure, hlen, ↓reduceDIte]
  exact ⟨⟨merged.2.val, hlen⟩, rfl, hperm, (hsorted _).2 hsort⟩

theorem integerCode_lt_two_pow (t : IntTy) (x : JInt t) (reverse : Bool) :
    (integerCode t reverse x).val.toNat < 2 ^ t.bits := by
  have hx := (integerCode t reverse x).property
  cases t <;>
    simp [IntTy.toUnsigned, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at hx ⊢ <;> omega

theorem arrayWrite_self {α : Type} (values : Array α) (index : Int) (value : α)
    (hread : arrayRead values index = .ok value) :
    arrayWrite values index value = .ok values := by
  unfold arrayRead at hread
  split at hread
  · rename_i h1
    cases hget : values[(index - 1).toNat]? with
    | none => rw [hget] at hread; cases hread
    | some v =>
      rw [hget] at hread
      injection hread with hveq
      subst hveq
      have hi : (index - 1).toNat < values.size := (Array.getElem?_eq_some_iff.1 hget).1
      have h2 : index ≤ (values.size : Int) := by omega
      unfold arrayWrite
      simp only [h1, h2, and_self, ↓reduceIte]
      congr 1
      apply Array.ext'
      have hgetList : values.toList[(index - 1).toNat]? = some v := by
        simpa using hget
      have hiList : (index - 1).toNat < values.toList.length := by simpa using hi
      have hgetEq : values.toList[(index - 1).toNat] = v := (List.getElem_eq_iff hiList).2 hgetList
      simp only [Array.toList_set!, ← hgetEq]
      exact List.set_getElem_self hiList
  · cases hread

theorem forIn_uintMap_loop (t : IntTy) (values : Array (JInt t)) (reverse : Bool) :
    ∀ (xs : List Int) (u : Array Nat),
      u.size = values.size →
      (∀ i ∈ xs, 1 ≤ i ∧ i ≤ (values.size : Int)) →
      ∃ mapped,
        (do
          let mut unsignedVector := u
          for index in xs do
            let value ← arrayRead values index
            let mapped ← (Except.ok (integerCode t reverse value).val.toNat : Jl Nat)
            unsignedVector ← arrayWrite unsignedVector index mapped
          pure unsignedVector : Jl (Array Nat)) = .ok mapped ∧
        mapped.size = values.size ∧
        ∀ j, 1 ≤ j → j ≤ (values.size : Int) →
          (j ∈ xs → ∀ v, arrayRead values j = .ok v →
            arrayRead mapped j = .ok (integerCode t reverse v).val.toNat) ∧
          (j ∉ xs → arrayRead mapped j = arrayRead u j)
  | [], u, hsize, _ => by
    refine ⟨u, rfl, hsize, ?_⟩
    intro j _ _
    exact ⟨(fun hj => by cases hj), fun _ => rfl⟩
  | i :: rest, u, hsize, hbounds => by
    have hi : 1 ≤ i ∧ i ≤ (values.size : Int) := hbounds i List.mem_cons_self
    have hiNat : (i - 1).toNat < values.size := by omega
    have hread : arrayRead values i = .ok (values[(i - 1).toNat]'hiNat) := by
      unfold arrayRead
      simp only [hi.1, ↓reduceIte, Array.getElem?_eq_getElem hiNat]
    let u' := u.set! (i - 1).toNat (integerCode t reverse (values[(i - 1).toNat]'hiNat)).val.toNat
    have hwrite : arrayWrite u i (integerCode t reverse (values[(i - 1).toNat]'hiNat)).val.toNat = .ok u' := by
      unfold arrayWrite
      simp only [hsize, hi.1, hi.2, and_self, ↓reduceIte]; rfl
    have hsize' : u'.size = values.size := by simp [u', hsize]
    have hrest : ∀ k ∈ rest, 1 ≤ k ∧ k ≤ (values.size : Int) :=
      fun k hk => hbounds k (List.mem_cons_of_mem i hk)
    obtain ⟨mapped, hloop, hmsize, hmprop⟩ :=
      forIn_uintMap_loop t values reverse rest u' hsize' hrest
    refine ⟨mapped, ?_, hmsize, ?_⟩
    · simp only [List.forIn_cons, hread, hwrite, bind, Except.bind, pure, Except.pure]
      exact hloop
    · intro j hj1 hj2
      obtain ⟨hmem, hnotmem⟩ := hmprop j hj1 hj2
      constructor
      · intro hjcons v hv
        by_cases hjrest : j ∈ rest
        · exact hmem hjrest v hv
        · rcases List.mem_cons.1 hjcons with rfl | hjr
          · rw [hnotmem hjrest]
            rw [hread] at hv
            injection hv with hveq
            subst hveq
            unfold arrayRead
            have hiNatU : (j - 1).toNat < u.size := by omega
            simp only [hj1, ↓reduceIte, u', Array.set!, Array.setIfInBounds, hiNatU,
              ↓reduceDIte, Array.getElem?_set]
          · exact absurd hjr hjrest
      · intro hjnot
        have hjnotRest : j ∉ rest := fun h => hjnot (List.mem_cons_of_mem i h)
        have hjne : j ≠ i := fun h => hjnot (h ▸ List.mem_cons_self)
        rw [hnotmem hjnotRest]
        unfold arrayRead
        have hiNatU : (i - 1).toNat < u.size := by omega
        have hneNat : (i - 1).toNat ≠ (j - 1).toNat := by omega
        simp only [hj1, ↓reduceIte, u', Array.set!, Array.setIfInBounds, hiNatU,
          ↓reduceDIte, Array.getElem?_set, hneNat]


theorem mem_arrayIndexRange {lo hi i : Int} :
    i ∈ arrayIndexRange lo hi ↔ lo ≤ i ∧ i ≤ hi := by
  unfold arrayIndexRange
  simp only [List.mem_map, List.mem_range, Int.ofNat_eq_natCast]
  constructor
  · rintro ⟨k, hk, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨(i - lo).toNat, by omega, by omega⟩


theorem balanced_empty : BalancedParentheses "" := by
  refine ⟨rfl, ?_⟩
  intro initial rest h
  have : initial = [] := by
    cases initial with
    | nil => rfl
    | cons c cs => cases h
  subst this
  decide

theorem balanced_append {s t : String}
    (hs : BalancedParentheses s) (ht : BalancedParentheses t) :
    BalancedParentheses (s ++ t) := by
  obtain ⟨hsc, hsp⟩ := hs
  obtain ⟨htc, htp⟩ := ht
  refine ⟨?_, ?_⟩
  · simp only [String.toList_append, List.count_append]
    omega
  · intro initial rest h
    rw [String.toList_append] at h
    rcases List.append_eq_append_iff.1 h with ⟨as, h1, h2⟩ | ⟨cs, h1, h2⟩
    · subst h1
      have := htp as rest h2
      simp only [List.count_append]
      omega
    · exact hsp initial cs h1

theorem balanced_of_no_parens {s : String}
    (hopen : s.toList.count '(' = 0) (hclose : s.toList.count ')' = 0) :
    BalancedParentheses s := by
  refine ⟨by omega, ?_⟩
  intro initial rest h
  have hc : s.toList.count ')' = initial.count ')' + rest.count ')' := by
    rw [h, List.count_append]
  omega

theorem count_replicate_spaces (n : Nat) :
    (String.ofList (List.replicate (4 * n) ' ')).toList.count '(' = 0 ∧
      (String.ofList (List.replicate (4 * n) ' ')).toList.count ')' = 0 := by
  simp [List.count_replicate]

theorem balanced_parens_wrap {body : String} (hb : BalancedParentheses body) :
    BalancedParentheses ("(" ++ body ++ ")") := by
  obtain ⟨hbc, hbp⟩ := hb
  refine ⟨?_, ?_⟩
  · simp only [String.toList_append, List.count_append]
    change (['('].count '(' + body.toList.count '(') + [')'].count '(' =
      (['('].count ')' + body.toList.count ')') + [')'].count ')'
    have c1 : ['('].count '(' = 1 := rfl
    have c2 : ['('].count ')' = 0 := rfl
    have c3 : [')'].count '(' = 0 := rfl
    have c4 : [')'].count ')' = 1 := rfl
    omega
  · intro initial rest h
    simp only [String.toList_append] at h
    change '(' :: (body.toList ++ [')']) = initial ++ rest at h
    cases initial with
    | nil => decide
    | cons c init' =>
      simp only [List.cons_append, List.cons.injEq] at h
      rcases h with ⟨rfl, htail⟩
      rcases List.append_eq_append_iff.1 htail with ⟨as, h1, h2⟩ | ⟨cs, h1, h2⟩
      · cases as with
        | nil =>
          simp only [List.append_nil] at h1
          subst h1
          have c1 : ('(' :: body.toList).count ')' = body.toList.count ')' := rfl
          have c2 : ('(' :: body.toList).count '(' = body.toList.count '(' + 1 := by simp
          omega
        | cons d ds =>
          have hlen : (d :: ds ++ rest).length = 1 := by rw [← h2]; rfl
          have hds : ds = [] ∧ rest = [] := by
            cases ds with
            | nil =>
              cases rest with
              | nil => exact ⟨rfl, rfl⟩
              | cons _ _ => simp at hlen
            | cons _ _ => simp at hlen
          rcases hds with ⟨rfl, rfl⟩
          simp only [List.append_nil, List.cons.injEq, and_true] at h2
          subst h2 h1
          have c1 : ('(' :: (body.toList ++ [')'])).count ')' = body.toList.count ')' + 1 := by
            simp [List.count_append]
          have c2 : ('(' :: (body.toList ++ [')'])).count '(' = body.toList.count '(' + 1 := by
            simp [List.count_append]
          omega
      · have := hbp init' cs h1
        have c1 : ('(' :: init').count ')' = init'.count ')' := rfl
        have c2 : ('(' :: init').count '(' = init'.count '(' + 1 := by simp
        omega

theorem showType_text {IO Alg Name Arg E : Type}
    (ops : AlgorithmDisplayOps IO Alg Name Arg E)
    (text : IO → String) (nameText : Name → String)
    (smallThreshold? : Alg → Option Nat) (argumentText : Arg → String)
    (hlaws : DisplayPrimitiveLaws ops text nameText smallThreshold? argumentText)
    (io : IO) (algorithm : Alg) (result : IO)
    (h : ops.showType io algorithm = .ok result) :
    text result = text io ++ displayTypeText ops.algorithmTypeName nameText smallThreshold? algorithm := by
  have ⟨hprint, _, hshow, hshowName, _, _, _⟩ := hlaws
  rw [hshow io algorithm] at h
  unfold displayTypeText
  cases hsm : smallThreshold? algorithm with
  | some n =>
    rw [hsm] at h
    exact hprint io ("Base.Sort.Small{" ++ toString n ++ "}") result h
  | none =>
    rw [hsm] at h
    exact hshowName io (ops.algorithmTypeName algorithm) result h

theorem forIn_display_args {IO Alg Name Arg E : Type}
    (ops : AlgorithmDisplayOps IO Alg Name Arg E)
    (text : IO → String) (nameText : Name → String)
    (smallThreshold? : Alg → Option Nat) (argumentText : Arg → String)
    (hlaws : DisplayPrimitiveLaws ops text nameText smallThreshold? argumentText)
    (algorithm : Alg) (columns : Nat)
    (hchild : ∀ name ∈ ops.fieldNames algorithm,
      ops.isAlgorithm (ops.getField algorithm name) = true →
      ∀ (io : IO) (result : IO),
        printAlgorithmTree ops io (ops.toAlgorithm (ops.getField algorithm name)) (columns + 1) = .ok result →
        ∃ suffix, text result = text io ++ suffix ∧ BalancedParentheses suffix) :
    ∀ (names : List Name),
      (∀ name ∈ names, name ∈ ops.fieldNames algorithm) →
      ∀ (io : IO) (index : Nat) (out : IO × Nat),
        (forIn names (io, index) fun name state => do
          let mut io := state.1
          let mut index := state.2
          let argument := ops.getField algorithm name
          if index > 0 then
            io ← ops.print io ","
          if ops.isAlgorithm argument then
            io ← ops.println io ""
            io ← printAlgorithmTree ops io (ops.toAlgorithm argument) (columns + 1)
          else
            if index > 0 then
              io ← ops.print io " "
            io ← ops.printArgument io argument
          index := index + 1
          pure (ForInStep.yield (io, index))) = .ok out →
        ∃ suffix, text out.1 = text io ++ suffix ∧ BalancedParentheses suffix
  | [], _, io, index, out, h => by
    injection h with heq
    subst heq
    exact ⟨"", by simp, balanced_empty⟩
  | name :: rest, hsub, io, index, out, h => by
    have ⟨hprint, hprintln, _, _, harg, _, hbalArg⟩ := hlaws
    have hmem : name ∈ ops.fieldNames algorithm := hsub name List.mem_cons_self
    have hsub' : ∀ n ∈ rest, n ∈ ops.fieldNames algorithm :=
      fun n hn => hsub n (List.mem_cons_of_mem name hn)
    let step := fun (name : Name) (state : IO × Nat) => (do
      let mut io := state.1
      let mut index := state.2
      let argument := ops.getField algorithm name
      if index > 0 then
        io ← ops.print io ","
      if ops.isAlgorithm argument then
        io ← ops.println io ""
        io ← printAlgorithmTree ops io (ops.toAlgorithm argument) (columns + 1)
      else
        if index > 0 then
          io ← ops.print io " "
        io ← ops.printArgument io argument
      index := index + 1
      pure (ForInStep.yield (io, index)) : Except E (ForInStep (IO × Nat)))
    change (forIn (name :: rest) (io, index) step) = .ok out at h
    rw [List.forIn_cons] at h
    cases hstep : step name (io, index) with
    | error e =>
      rw [hstep] at h; cases h
    | ok stepVal =>
      rw [hstep] at h
      simp only [bind, Except.bind] at h
      have hstepProp : ∃ io3 sStep,
          stepVal = ForInStep.yield (io3, index + 1) ∧
          text io3 = text io ++ sStep ∧ BalancedParentheses sStep := by
        dsimp only [step] at hstep
        by_cases hgt : index > 0
        · simp only [hgt, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hstep
          cases hc1 : ops.print io "," with
          | error e => rw [hc1] at hstep; cases hstep
          | ok io1 =>
            rw [hc1] at hstep; simp only at hstep
            have hs1 := hprint io "," io1 hc1
            have hb1 : BalancedParentheses "," := balanced_of_no_parens rfl rfl
            cases halg : ops.isAlgorithm (ops.getField algorithm name)
            · simp only [halg, Bool.false_eq_true, ↓reduceIte] at hstep
              cases hc2 : ops.print io1 " " with
              | error e => rw [hc2] at hstep; cases hstep
              | ok io2 =>
                rw [hc2] at hstep; simp only at hstep
                have hs2 := hprint io1 " " io2 hc2
                cases hc3 : ops.printArgument io2 (ops.getField algorithm name) with
                | error e => rw [hc3] at hstep; cases hstep
                | ok io3 =>
                  rw [hc3] at hstep
                  injection hstep with heq
                  have hs3 := harg io2 (ops.getField algorithm name) io3 hc3
                  refine ⟨io3, "," ++ " " ++ argumentText (ops.getField algorithm name), heq.symm, ?_, ?_⟩
                  · rw [hs3, hs2, hs1]; simp [String.append_assoc]
                  · exact balanced_append (balanced_append hb1 (balanced_of_no_parens rfl rfl)) (hbalArg (ops.getField algorithm name))
            · simp only [halg, ↓reduceIte] at hstep
              cases hc2 : ops.println io1 "" with
              | error e => rw [hc2] at hstep; cases hstep
              | ok io2 =>
                rw [hc2] at hstep; simp only at hstep
                have hs2 := hprintln io1 "" io2 hc2
                cases hc3 : printAlgorithmTree ops io2 (ops.toAlgorithm (ops.getField algorithm name)) (columns + 1) with
                | error e => rw [hc3] at hstep; cases hstep
                | ok io3 =>
                  rw [hc3] at hstep
                  injection hstep with heq
                  obtain ⟨s3, hs3, hb3⟩ := hchild name hmem halg io2 io3 hc3
                  refine ⟨io3, "," ++ "\n" ++ s3, heq.symm, ?_, ?_⟩
                  · rw [hs3, hs2, hs1]; simp [String.append_assoc]
                  · exact balanced_append (balanced_append hb1 (balanced_of_no_parens rfl rfl)) hb3
        · simp only [hgt, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hstep
          cases halg : ops.isAlgorithm (ops.getField algorithm name)
          · simp only [halg, Bool.false_eq_true, ↓reduceIte] at hstep
            cases hc3 : ops.printArgument io (ops.getField algorithm name) with
            | error e => rw [hc3] at hstep; cases hstep
            | ok io3 =>
              rw [hc3] at hstep
              injection hstep with heq
              have hs3 := harg io (ops.getField algorithm name) io3 hc3
              exact ⟨io3, argumentText (ops.getField algorithm name), heq.symm, hs3, hbalArg (ops.getField algorithm name)⟩
          · simp only [halg, ↓reduceIte] at hstep
            cases hc2 : ops.println io "" with
            | error e => rw [hc2] at hstep; cases hstep
            | ok io2 =>
              rw [hc2] at hstep; simp only at hstep
              have hs2 := hprintln io "" io2 hc2
              cases hc3 : printAlgorithmTree ops io2 (ops.toAlgorithm (ops.getField algorithm name)) (columns + 1) with
              | error e => rw [hc3] at hstep; cases hstep
              | ok io3 =>
                rw [hc3] at hstep
                injection hstep with heq
                obtain ⟨s3, hs3, hb3⟩ := hchild name hmem halg io2 io3 hc3
                refine ⟨io3, "\n" ++ s3, heq.symm, ?_, ?_⟩
                · rw [hs3, hs2]; simp [String.append_assoc]
                · exact balanced_append (balanced_of_no_parens rfl rfl) hb3
      obtain ⟨io3, sStep, rfl, hsStep, hbStep⟩ := hstepProp
      obtain ⟨srest, hsrest, hbrest⟩ :=
        forIn_display_args ops text nameText smallThreshold? argumentText hlaws algorithm columns hchild
          rest hsub' io3 (index + 1) out h
      refine ⟨sStep ++ srest, ?_, balanced_append hbStep hbrest⟩
      rw [hsrest, hsStep, String.append_assoc]

theorem printAlgorithmTree_balanced_depth {IO Alg Name Arg E : Type}
    (ops : AlgorithmDisplayOps IO Alg Name Arg E)
    (text : IO → String) (nameText : Name → String)
    (smallThreshold? : Alg → Option Nat) (argumentText : Arg → String)
    (hlaws : DisplayPrimitiveLaws ops text nameText smallThreshold? argumentText) :
    ∀ (depth : Nat) (algorithm : Alg),
      ops.algorithmDepth algorithm ≤ depth →
      ∀ (io : IO) (columns : Nat) (result : IO),
        printAlgorithmTree ops io algorithm columns = .ok result →
        ∃ suffix, text result = text io ++ suffix ∧ BalancedParentheses suffix
  | 0, algorithm, hdepth, io, columns, result, h => by
    have ⟨hprint, _, _, _, _, hbalType, _⟩ := hlaws
    rw [printAlgorithmTree] at h
    have hchild : ∀ name ∈ ops.fieldNames algorithm,
        ops.isAlgorithm (ops.getField algorithm name) = true →
        ∀ (io : IO) (result : IO),
          printAlgorithmTree ops io (ops.toAlgorithm (ops.getField algorithm name)) (columns + 1) = .ok result →
          ∃ suffix, text result = text io ++ suffix ∧ BalancedParentheses suffix := by
      intro name hmem halg
      have hlt := ops.childDepthLess algorithm name hmem halg
      omega
    let indentation := String.ofList (List.replicate (4 * columns) ' ')
    cases h1 : ops.print io indentation with
    | error e => simp [indentation, h1, bind, Except.bind] at h
    | ok io1 =>
      cases h2 : ops.showType io1 algorithm with
      | error e => simp [indentation, h1, h2, bind, Except.bind] at h
      | ok io2 =>
        cases h3 : ops.print io2 "(" with
        | error e => simp [indentation, h1, h2, h3, bind, Except.bind] at h
        | ok io3 =>
          simp only [indentation, h1, h2, h3, bind, Except.bind] at h
          split at h
          · cases h
          · rename_i out hloop
            have hs1 := hprint io indentation io1 h1
            have hs2 := showType_text ops text nameText smallThreshold? argumentText hlaws io1 algorithm io2 h2
            have hs3 := hprint io2 "(" io3 h3
            have hs4 := hprint out.1 ")" result h
            obtain ⟨sbody, hsbody, hbbody⟩ :=
              forIn_display_args ops text nameText smallThreshold? argumentText hlaws algorithm columns hchild
                (ops.fieldNames algorithm) (fun _ hn => hn) io3 0 out hloop
            have hbindent : BalancedParentheses indentation :=
              balanced_of_no_parens (count_replicate_spaces columns).1 (count_replicate_spaces columns).2
            refine ⟨indentation ++ displayTypeText ops.algorithmTypeName nameText smallThreshold? algorithm ++ ("(" ++ sbody ++ ")"), ?_, ?_⟩
            · rw [hs4, hsbody, hs3, hs2, hs1]; simp [String.append_assoc]
            · exact balanced_append (balanced_append hbindent (hbalType algorithm))
                (balanced_parens_wrap hbbody)
  | depth + 1, algorithm, hdepth, io, columns, result, h => by
    have ⟨hprint, _, _, _, _, hbalType, _⟩ := hlaws
    rw [printAlgorithmTree] at h
    have hchild : ∀ name ∈ ops.fieldNames algorithm,
        ops.isAlgorithm (ops.getField algorithm name) = true →
        ∀ (io : IO) (result : IO),
          printAlgorithmTree ops io (ops.toAlgorithm (ops.getField algorithm name)) (columns + 1) = .ok result →
          ∃ suffix, text result = text io ++ suffix ∧ BalancedParentheses suffix := by
      intro name hmem halg io' result' h'
      have hlt := ops.childDepthLess algorithm name hmem halg
      exact printAlgorithmTree_balanced_depth ops text nameText smallThreshold? argumentText hlaws depth
        (ops.toAlgorithm (ops.getField algorithm name)) (by omega) io' (columns + 1) result' h'
    let indentation := String.ofList (List.replicate (4 * columns) ' ')
    cases h1 : ops.print io indentation with
    | error e => simp [indentation, h1, bind, Except.bind] at h
    | ok io1 =>
      cases h2 : ops.showType io1 algorithm with
      | error e => simp [indentation, h1, h2, bind, Except.bind] at h
      | ok io2 =>
        cases h3 : ops.print io2 "(" with
        | error e => simp [indentation, h1, h2, h3, bind, Except.bind] at h
        | ok io3 =>
          simp only [indentation, h1, h2, h3, bind, Except.bind] at h
          split at h
          · cases h
          · rename_i out hloop
            have hs1 := hprint io indentation io1 h1
            have hs2 := showType_text ops text nameText smallThreshold? argumentText hlaws io1 algorithm io2 h2
            have hs3 := hprint io2 "(" io3 h3
            have hs4 := hprint out.1 ")" result h
            obtain ⟨sbody, hsbody, hbbody⟩ :=
              forIn_display_args ops text nameText smallThreshold? argumentText hlaws algorithm columns hchild
                (ops.fieldNames algorithm) (fun _ hn => hn) io3 0 out hloop
            have hbindent : BalancedParentheses indentation :=
              balanced_of_no_parens (count_replicate_spaces columns).1 (count_replicate_spaces columns).2
            refine ⟨indentation ++ displayTypeText ops.algorithmTypeName nameText smallThreshold? algorithm ++ ("(" ++ sbody ++ ")"), ?_, ?_⟩
            · rw [hs4, hsbody, hs3, hs2, hs1]; simp [String.append_assoc]
            · exact balanced_append (balanced_append hbindent (hbalType algorithm))
                (balanced_parens_wrap hbbody)


/-! ## Proofs and Refutations (Batch 4: BoolSort, CheckSorted, SubArraySort) -/

theorem toList_eq_take_slice_drop {α : Type} (v : Array α) (lo hi : Int)
    (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1) :
    v.toList = v.toList.take (lo - 1).toNat ++ arraySlice v lo hi ++ v.toList.drop hi.toNat := by
  unfold arraySlice
  have hdrop : (v.toList.drop (lo - 1).toNat).drop (hi - lo + 1).toNat = v.toList.drop hi.toNat := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [List.append_assoc, ← hdrop, List.take_append_drop, List.take_append_drop]

theorem take_slice_drop_of_append {α : Type} (v : Array α) (P M Q : List α) (lo hi : Int)
    (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1)
    (hv : v.toList = P ++ M ++ Q)
    (hP : P.length = (lo - 1).toNat)
    (hM : M.length = (hi - lo + 1).toNat) :
    v.toList.take (lo - 1).toNat = P ∧
    arraySlice v lo hi = M ∧
    v.toList.drop hi.toNat = Q := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hv, List.append_assoc, ← hP]
    exact List.take_left
  · unfold arraySlice
    rw [hv, List.append_assoc, ← hP, List.drop_left, ← hM]
    exact List.take_left
  · have hPM : (P ++ M).length = hi.toNat := by
      rw [List.length_append, hP, hM]
      omega
    rw [hv, ← hPM]
    exact List.drop_left

theorem except_bind_ok {ε α β : Type} (x : α) (f : α → Except ε β) :
    (Bind.bind (Except.ok x) f : Except ε β) = f x := rfl

theorem except_pure_ok {ε α : Type} (x : α) :
    (Pure.pure x : Except ε α) = Except.ok x := rfl

theorem forIn_bool_count (values : Array Bool) (b : Bool) :
    ∀ (xs : List Int) (c : Nat),
      (∀ i ∈ xs, 1 ≤ i ∧ i ≤ (values.size : Int)) →
      (forIn xs c fun index count => do
        if (← liftSortJl (arrayRead values index)) == b then
          pure (ForInStep.yield (count + 1))
        else
          pure (ForInStep.yield count)) =
      .ok (c + (xs.filter (fun i => (values[(i - 1).toNat]?.getD false) == b)).length)
  | [], c, _ => by simp [pure, Except.pure]
  | i :: rest, c, hbounds => by
    have hi := hbounds i List.mem_cons_self
    have hiNat : (i - 1).toNat < values.size := by omega
    have hread : arrayRead values i = .ok (values[(i - 1).toNat]'hiNat) := by
      unfold arrayRead
      simp only [hi.1, ↓reduceIte, Array.getElem?_eq_getElem hiNat]
    have hget : values[(i - 1).toNat]?.getD false = values[(i - 1).toNat]'hiNat := by
      rw [Array.getElem?_eq_getElem hiNat]; rfl
    have hrest : ∀ j ∈ rest, 1 ≤ j ∧ j ≤ (values.size : Int) :=
      fun j hj => hbounds j (List.mem_cons_of_mem i hj)
    simp only [List.forIn_cons, hread, liftSortJl_ok, List.filter_cons, hget, except_bind_ok]
    cases hcond : (values[(i - 1).toNat]'hiNat == b)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact forIn_bool_count values b rest c hrest
    · simp only [↓reduceIte, List.length_cons]
      change (forIn rest (c + 1) fun index count => do
        if (← liftSortJl (arrayRead values index)) == b then
          pure (ForInStep.yield (count + 1))
        else
          pure (ForInStep.yield count)) = _
      rw [forIn_bool_count values b rest (c + 1) hrest]
      congr 1; omega

theorem filter_indexRange_eq_count (values : Array Bool) (b : Bool) :
    ((arrayIndexRange 1 values.size).filter
      (fun i => (values[(i - 1).toNat]?.getD false) == b)).length =
    values.toList.count b := by
  have hmap : (arrayIndexRange 1 values.size).map
      (fun i => values[(i - 1).toNat]?.getD false) = values.toList := by
    apply List.ext_getElem
    · simp [arrayIndexRange]
    · intro k hk1 hk2
      simp only [arrayIndexRange, List.getElem_map, List.getElem_range]
      have hk : ((1 + Int.ofNat k) - 1).toNat = k := by
        simp only [Int.ofNat_eq_natCast]; omega
      simp only [hk, Array.getElem?_eq_getElem hk2, Option.getD_some, Array.getElem_toList]
  have hflt : ((arrayIndexRange 1 values.size).filter
      (fun i => (values[(i - 1).toNat]?.getD false) == b)).length =
      (((arrayIndexRange 1 values.size).map
        (fun i => values[(i - 1).toNat]?.getD false)).filter (· == b)).length := by
    rw [List.filter_map, List.length_map]; rfl
  rw [hflt, hmap, List.count_eq_length_filter]

theorem forIn_setSegment (val : Bool) :
    ∀ (xs : List Int) (v : Array Bool),
      (∀ i ∈ xs, 1 ≤ i ∧ i ≤ (v.size : Int)) →
      ∃ v',
        (do
          let mut values := v
          for index in xs do
            values ← liftSortJl (arrayWrite values index val)
          pure values : SortResult (Array Bool)) = .ok v' ∧
        v'.size = v.size ∧
        ∀ k : Nat, k < v.size →
          v'[k]? = if (1 + (k : Int)) ∈ xs then some val else v[k]?
  | [], v, _ => by
    refine ⟨v, rfl, rfl, ?_⟩
    intro k _; simp
  | i :: rest, v, hbounds => by
    have hi := hbounds i List.mem_cons_self
    have hiNat : (i - 1).toNat < v.size := by omega
    let v1 := v.set! (i - 1).toNat val
    have hwrite : arrayWrite v i val = .ok v1 := by
      unfold arrayWrite
      simp only [hi.1, hi.2, and_self, ↓reduceIte]; rfl
    have hsize1 : v1.size = v.size := by simp [v1]
    have hrest : ∀ j ∈ rest, 1 ≤ j ∧ j ≤ (v1.size : Int) := by
      intro j hj; rw [hsize1]; exact hbounds j (List.mem_cons_of_mem i hj)
    obtain ⟨v', hloop, hsize', hget'⟩ := forIn_setSegment val rest v1 hrest
    refine ⟨v', ?_, by rw [hsize', hsize1], ?_⟩
    · simp only [List.forIn_cons, hwrite, liftSortJl_ok, bind, Except.bind, pure, Except.pure]
      exact hloop
    · intro k hk
      rw [hget' k (by omega)]
      by_cases hmem : (1 + (k : Int)) ∈ rest
      · have hmemCons : (1 + (k : Int)) ∈ i :: rest := List.mem_cons_of_mem i hmem
        simp only [hmem, hmemCons, ↓reduceIte]
      · simp only [hmem, Bool.false_eq_true, ↓reduceIte, List.mem_cons, or_false]
        by_cases heq : 1 + (k : Int) = i
        · have hkEq : (i - 1).toNat = k := by omega
          simp only [heq, ↓reduceIte]
          rw [← hkEq]
          simp only [v1, Array.set!, Array.setIfInBounds, hiNat, ↓reduceDIte, Array.getElem?_set, ↓reduceIte]
        · have hkNe : (i - 1).toNat ≠ k := by omega
          simp only [heq, ↓reduceIte, v1, Array.set!, Array.setIfInBounds, hiNat,
            ↓reduceDIte, Array.getElem?_set, hkNe]

theorem count_bool_compl (b : Bool) :
    ∀ (xs : List Bool), xs.count b + xs.count (!b) = xs.length
  | [] => rfl
  | x :: xs => by
    have ih := count_bool_compl b xs
    cases x <;> cases b <;> simp [List.count_cons] at ih ⊢ <;> omega

theorem boolSort_branch (values : Array Bool) (lt : Bool → Bool → Bool)
    (hnt : NegTransOrder lt) (b : Bool)
    (hbb : lt b b = false) (hnot : lt (!b) (!b) = false) (hba : lt (!b) b = false) :
    ∃ result,
      (do
        let (lo, hi, scratch) ← (storageBoolSortOps arrayStorage).rangeAndScratch (1, values.size)
        let mut count := 0
        for index in (storageBoolSortOps arrayStorage).range lo hi do
          if (← (storageBoolSortOps arrayStorage).read values index) == b then
            count := count + 1
        let firstFilled ← (storageBoolSortOps arrayStorage).setSegment values lo ((storageBoolSortOps arrayStorage).firstSegmentEnd lo count) b
        let secondFilled ← (storageBoolSortOps arrayStorage).setSegment firstFilled ((storageBoolSortOps arrayStorage).secondSegmentStart lo count) hi (!b)
        pure ((storageBoolSortOps arrayStorage).returnScratch secondFilled scratch)) = .ok result ∧
      List.Perm values.toList result.toList ∧ SortedValues lt result.toList := by
  have hboundsAll : ∀ i ∈ arrayIndexRange 1 values.size, 1 ≤ i ∧ i ≤ (values.size : Int) := by
    intro i hi; have := mem_arrayIndexRange.1 hi; omega
  have hcnt := forIn_bool_count values b (arrayIndexRange 1 values.size) 0 hboundsAll
  rw [Nat.zero_add, filter_indexRange_eq_count] at hcnt
  let count := values.toList.count b
  have hcountLe : count ≤ values.size := by
    have := count_bool_compl b values.toList
    have hlen : values.toList.length = values.size := Array.length_toList
    omega
  have hb1 : ∀ i ∈ arrayIndexRange 1 (1 + Int.ofNat count - 1), 1 ≤ i ∧ i ≤ (values.size : Int) := by
    intro i hi; have := mem_arrayIndexRange.1 hi; simp only [Int.ofNat_eq_natCast] at this; omega
  obtain ⟨v1, hseg1, hsize1, hget1⟩ :=
    forIn_setSegment b (arrayIndexRange 1 (1 + Int.ofNat count - 1)) values hb1
  have hb2 : ∀ i ∈ arrayIndexRange (1 + Int.ofNat count) values.size, 1 ≤ i ∧ i ≤ (v1.size : Int) := by
    intro i hi; rw [hsize1]; have := mem_arrayIndexRange.1 hi; simp only [Int.ofNat_eq_natCast] at this; omega
  obtain ⟨v2, hseg2, hsize2, hget2⟩ :=
    forIn_setSegment (!b) (arrayIndexRange (1 + Int.ofNat count) values.size) v1 hb2
  have hv2List : v2.toList = List.replicate count b ++ List.replicate (values.size - count) (!b) := by
    apply List.ext_getElem
    · simp [hsize2, hsize1]; omega
    · intro k hk1 hk2
      have hkV : k < values.size := by rw [← hsize1, ← hsize2]; exact hk1
      have h2k := hget2 k (by rw [hsize1]; exact hkV)
      have h1k := hget1 k hkV
      rw [Array.getElem_toList]
      have hv2opt : v2[k]? = some (v2[k]'hk1) := Array.getElem?_eq_getElem hk1
      rw [hv2opt] at h2k
      by_cases hkc : k < count
      · have hnotMem2 : ¬ (1 + (k : Int)) ∈ arrayIndexRange (1 + Int.ofNat count) values.size := by
          rw [mem_arrayIndexRange]; simp only [Int.ofNat_eq_natCast]; omega
        have hmem1 : (1 + (k : Int)) ∈ arrayIndexRange 1 (1 + Int.ofNat count - 1) := by
          rw [mem_arrayIndexRange]; simp only [Int.ofNat_eq_natCast]; omega
        rw [if_neg hnotMem2, h1k, if_pos hmem1] at h2k
        injection h2k with hval
        rw [hval, List.getElem_append_left (by simp [hkc]), List.getElem_replicate]
      · have hmem2 : (1 + (k : Int)) ∈ arrayIndexRange (1 + Int.ofNat count) values.size := by
          rw [mem_arrayIndexRange]; simp only [Int.ofNat_eq_natCast]; omega
        rw [if_pos hmem2] at h2k
        injection h2k with hval
        rw [hval, List.getElem_append_right (by simp; omega), List.getElem_replicate]
  refine ⟨v2, ?_, ?_, ?_⟩
  · dsimp only [storageBoolSortOps, arrayStorage, arrayStorageWith]
    dsimp only [count] at hseg1 hseg2
    simp only [except_bind_ok, hcnt, hseg1, hseg2]
    rfl
  · rw [hv2List, List.perm_iff_count]
    intro a
    have htot := count_bool_compl b values.toList
    have hlen : values.toList.length = values.size := Array.length_toList
    cases a <;> cases b <;>
      simp [List.count_append, List.count_replicate, count] at htot ⊢ <;> omega
  · rw [hv2List, sortedValues_iff_pairwise hnt, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj _
      simp [List.getElem_replicate, hbb]
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj _
      simp [List.getElem_replicate, hnot]
    · intro x hx y hy
      rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
      exact hba



theorem forIn_window_check_ok {V α K O E : Type}
    (indices : IntegerIndexOps K) (get : V → K → Except E α)
    (lt : O → α → α → Bool) (v : V) (order : O) :
    ∀ (xs : List K),
      (∀ i ∈ xs, ∃ current previous, get v i = .ok current ∧ get v (indices.previous i) = .ok previous) →
      ∃ b : Bool,
        (do
          for i in xs do
            if lt order (← get v i) (← get v (indices.previous i)) then
              return false
          pure true : Except E Bool) = .ok b
  | [], _ => ⟨true, rfl⟩
  | i :: rest, hreads => by
    obtain ⟨curr, prev, hcurr, hprev⟩ := hreads i List.mem_cons_self
    have hrest : ∀ j ∈ rest, ∃ current previous, get v j = .ok current ∧
        get v (indices.previous j) = .ok previous :=
      fun j hj => hreads j (List.mem_cons_of_mem i hj)
    simp only [List.forIn_cons, hcurr, hprev, bind, Except.bind, pure, Except.pure]
    cases lt order curr prev
    · simp only [Bool.false_eq_true, ↓reduceIte]
      change ∃ b : Bool, (do
        for j in rest do
          if lt order (← get v j) (← get v (indices.previous j)) then
            return false
        pure true : Except E Bool) = .ok b
      exact forIn_window_check_ok indices get lt v order rest hrest
    · exact ⟨false, rfl⟩

theorem pairwise_of_adjacent {α : Type} {R : α → α → Prop}
    (htr : ∀ a b c, R a b → R b c → R a c) :
    ∀ (l : List α), (∀ k (hk : k + 1 < l.length), R l[k] l[k + 1]) → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | [_], _ => by simp
  | a :: b :: l, hadj => by
    have ih := pairwise_of_adjacent htr (b :: l) (fun k hk => by
      have := hadj (k + 1) (by simp at hk ⊢; omega)
      simpa using this)
    refine List.Pairwise.cons ?_ ih
    intro c hc
    have hab : R a b := hadj 0 (by simp)
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact htr _ _ _ hab ((List.pairwise_cons.1 ih).1 c hc)

theorem windowSorted_whole_imp_sortedValues {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (values : Array α)
    (hw : WindowSorted arrayIndices arrayRead (fun o => o) values 1 values.size lt) :
    SortedValues lt values.toList := by
  rw [sortedValues_iff_pairwise hnt]
  apply pairwise_of_adjacent (R := fun a b => lt b a = false) (fun a b c hab hbc => negTransOrder_not_trans hnt hbc hab)
  intro k hk
  have hkSz : k + 1 < values.size := by simpa using hk
  have hmem : (Int.ofNat k + 2) ∈ arrayIndexRange 2 values.size := by
    rw [mem_arrayIndexRange]; simp only [Int.ofNat_eq_natCast]; omega
  obtain ⟨curr, prev, hcurr, hprev, hlt⟩ := hw (Int.ofNat k + 2) hmem
  have hcEq : arrayRead values (Int.ofNat k + 2) = .ok (values.toList[k + 1]'hk) := by
    unfold arrayRead
    have h1 : 1 ≤ Int.ofNat k + 2 := by simp only [Int.ofNat_eq_natCast]; omega
    have hidx : (Int.ofNat k + 2 - 1).toNat = k + 1 := by simp only [Int.ofNat_eq_natCast]; omega
    simp only [h1, ↓reduceIte, hidx, Array.getElem?_eq_getElem hkSz, Array.getElem_toList]
  have hpEq : arrayRead values (arrayIndices.previous (Int.ofNat k + 2)) =
      .ok (values.toList[k]'(by omega)) := by
    unfold arrayRead arrayIndices
    dsimp only
    have h1 : 1 ≤ Int.ofNat k + 2 - 1 := by simp only [Int.ofNat_eq_natCast]; omega
    have hidx : (Int.ofNat k + 2 - 1 - 1).toNat = k := by simp only [Int.ofNat_eq_natCast]; omega
    simp only [h1, ↓reduceIte, hidx, Array.getElem?_eq_getElem (show k < values.size by omega),
      Array.getElem_toList]
  rw [hcEq] at hcurr; injection hcurr with hc
  rw [hpEq] at hprev; injection hprev with hp
  subst hc hp
  exact hlt

theorem exists_concat_list {α : Type} (l : List α) (k : Nat) (hl : l.length = k + 1) :
    ∃ l' b, l = l' ++ [b] ∧ l'.length = k := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', b, rfl⟩
  · simp at hl
  · refine ⟨l', b, by simp, ?_⟩
    simp at hl; omega

theorem arraySwap_mid {α : Type} (v : Array α) (lo hi : Int) (k : Nat)
    (P B1 M B2 Q : List α) (a b : α)
    (hv : v.toList = P ++ B1 ++ (a :: M ++ [b]) ++ B2 ++ Q)
    (hP : (P.length : Int) + 1 = lo)
    (hB1 : B1.length = k)
    (hB2 : B2.length = k)
    (hX : (B1.length + (M.length + 2) + B2.length : Int) = hi - lo + 1) :
    ∃ v', storageSwap arrayStorage v (lo + Int.ofNat k) (hi - Int.ofNat k) = .ok v' ∧
      v'.toList = P ++ (B1 ++ [b]) ++ M ++ (a :: B2) ++ Q := by
  have hlenV : v.size = P.length + B1.length + (M.length + 2) + B2.length + Q.length := by
    have := congrArg List.length hv
    simp only [Array.length_toList, List.length_append, List.length_cons, List.length_nil] at this
    omega
  have hleft1 : 1 ≤ lo + Int.ofNat k := by simp only [Int.ofNat_eq_natCast]; omega
  have hleft2 : lo + Int.ofNat k ≤ (v.size : Int) := by simp only [Int.ofNat_eq_natCast]; omega
  have hright1 : 1 ≤ hi - Int.ofNat k := by simp only [Int.ofNat_eq_natCast]; omega
  have hright2 : hi - Int.ofNat k ≤ (v.size : Int) := by simp only [Int.ofNat_eq_natCast]; omega
  have hleftIdx : (lo + Int.ofNat k - 1).toNat = (P ++ B1).length := by
    simp only [List.length_append, Int.ofNat_eq_natCast]; omega
  have hrightIdx : (hi - Int.ofNat k - 1).toNat = (P ++ B1 ++ a :: M).length := by
    simp only [List.length_append, List.length_cons, Int.ofNat_eq_natCast]; omega
  have hreadL : arrayRead v (lo + Int.ofNat k) = .ok a := by
    unfold arrayRead
    rw [if_pos hleft1, ← Array.getElem?_toList, hleftIdx]
    have hdecomp : v.toList = (P ++ B1) ++ a :: (M ++ [b] ++ B2 ++ Q) := by
      rw [hv]; simp [List.append_assoc]
    rw [hdecomp, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have hreadR : arrayRead v (hi - Int.ofNat k) = .ok b := by
    unfold arrayRead
    rw [if_pos hright1, ← Array.getElem?_toList, hrightIdx]
    have hdecomp : v.toList = (P ++ B1 ++ a :: M) ++ b :: (B2 ++ Q) := by
      rw [hv]; simp [List.append_assoc]
    rw [hdecomp, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  let v1 := v.set! (lo + Int.ofNat k - 1).toNat b
  have hwrite1 : arrayWrite v (lo + Int.ofNat k) b = .ok v1 := by
    unfold arrayWrite; rw [if_pos ⟨hleft1, hleft2⟩]
  have hv1List : v1.toList = (P ++ B1 ++ b :: M) ++ b :: (B2 ++ Q) := by
    have hdecomp : v.toList = (P ++ B1) ++ a :: (M ++ [b] ++ B2 ++ Q) := by
      rw [hv]; simp [List.append_assoc]
    simp only [v1, Array.toList_set!, hleftIdx, hdecomp,
      List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]
    simp [List.append_assoc]
  let v2 := v1.set! (hi - Int.ofNat k - 1).toNat a
  have hwrite2 : arrayWrite v1 (hi - Int.ofNat k) a = .ok v2 := by
    unfold arrayWrite
    have hv1sz : v1.size = v.size := by simp [v1]
    rw [hv1sz, if_pos ⟨hright1, hright2⟩]
  have hv2List : v2.toList = P ++ (B1 ++ [b]) ++ M ++ (a :: B2) ++ Q := by
    have hlen1 : (P ++ B1 ++ b :: M).length = (P ++ B1 ++ a :: M).length := by simp
    simp only [v2, Array.toList_set!, hrightIdx, ← hlen1, hv1List,
      List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]
    simp [List.append_assoc]
  refine ⟨v2, ?_, hv2List⟩
  unfold storageSwap
  simp only [arrayStorage_getindex, arrayStorage_setindex]
  rw [hreadL, hreadR]
  simp only [liftSortJl, Except.mapError, bind, Except.bind, hwrite1, hwrite2]

theorem range_map_shift {β : Type} (f : Nat → β) :
    ∀ (m k : Nat),
      (List.range (m + 1)).map (fun j => f (k + j)) =
      f k :: (List.range m).map (fun j => f ((k + 1) + j))
  | 0, _ => by simp
  | m + 1, k => by
    rw [List.range_succ, List.map_append, range_map_shift f m k, List.range_succ, List.map_append]
    simp [Nat.add_assoc]
    congr 1; omega

theorem forIn_arrayReverse {α : Type} (lo hi : Int) :
    ∀ (m : Nat) (k : Nat) (v : Array α) (P B1 M B2 Q : List α),
      2 * (k + m) ≤ B1.length + M.length + B2.length →
      v.toList = P ++ B1 ++ M ++ B2 ++ Q →
      (P.length : Int) + 1 = lo →
      B1.length = k →
      B2.length = k →
      (B1.length + M.length + B2.length : Int) = hi - lo + 1 →
      ∃ v',
        (do
          let mut values := v
          for offset in (List.range m).map (fun j => k + j) do
            values ← storageSwap arrayStorage values (lo + Int.ofNat offset) (hi - Int.ofNat offset)
          pure values : SortResult (Array α)) = .ok v' ∧
        ∃ A M' B,
          M = A ++ M' ++ B ∧ A.length = m ∧ B.length = m ∧
          v'.toList = P ++ (B1 ++ B.reverse) ++ M' ++ (A.reverse ++ B2) ++ Q
  | 0, k, v, P, B1, M, B2, Q, _, hv, _, _, _, _ => by
    refine ⟨v, rfl, [], M, [], by simp, rfl, rfl, ?_⟩
    simpa using hv
  | m + 1, k, v, P, B1, M, B2, Q, h2m, hv, hP, hB1, hB2, hX => by
    have hMlen : 2 ≤ M.length := by omega
    obtain ⟨a, M1, rfl⟩ : ∃ a M1, M = a :: M1 := by
      cases M with
      | nil => simp at hMlen
      | cons a M1 => exact ⟨a, M1, rfl⟩
    obtain ⟨M', b, rfl, hM'⟩ := exists_concat_list M1 (M1.length - 1) (by simp at hMlen; omega)
    have hv' : v.toList = P ++ B1 ++ (a :: M' ++ [b]) ++ B2 ++ Q := by
      rw [hv]; simp [List.append_assoc]
    obtain ⟨v1, hswap, hv1⟩ := arraySwap_mid v lo hi k P B1 M' B2 Q a b hv' hP hB1 hB2
      (by simp only [List.length_cons, List.length_append, List.length_nil] at hX; omega)
    have hmap : (List.range (m + 1)).map (fun j => k + j) =
        k :: (List.range m).map (fun j => (k + 1) + j) := range_map_shift id m k
    obtain ⟨v', hloop, A, M'', B, hMdecomp, hA, hB, hv'List⟩ :=
      forIn_arrayReverse lo hi m (k + 1) v1 P (B1 ++ [b]) M' (a :: B2) Q
        (by simp only [List.length_append, List.length_cons, List.length_nil] at h2m ⊢; omega)
        hv1 hP (by simp [hB1]) (by simp [hB2])
        (by simp only [List.length_append, List.length_cons, List.length_nil] at hX ⊢; omega)
    refine ⟨v', ?_, a :: A, M'', B ++ [b], ?_, by simp [hA], by simp [hB], ?_⟩
    · rw [hmap]
      simp only [List.forIn_cons, hswap, bind, Except.bind, pure, Except.pure]
      exact hloop
    · rw [hMdecomp]; simp [List.append_assoc]
    · rw [hv'List]; simp [List.append_assoc]

theorem arrayReverse_spec {α : Type} (v : Array α) (lo hi : Int)
    (P X Q : List α) (hv : v.toList = P ++ X ++ Q)
    (hP : (P.length : Int) + 1 = lo) (hX : (X.length : Int) = hi - lo + 1) :
    ∃ v', storageReverse arrayStorage v lo hi = .ok v' ∧ v'.toList = P ++ X.reverse ++ Q := by
  unfold storageReverse arrayStorage
  have hdiv : (hi - lo + 1).toNat / 2 = X.length / 2 := by omega
  rw [hdiv]
  have hmapId : List.range (X.length / 2) = (List.range (X.length / 2)).map (fun j => 0 + j) := by
    simp
  rw [hmapId]
  obtain ⟨v', hloop, A, M', B, hXdecomp, hA, hB, hv'List⟩ :=
    forIn_arrayReverse lo hi (X.length / 2) 0 v P [] X [] Q
      (by simp; omega) (by simpa using hv) hP rfl rfl (by simpa using hX)
  refine ⟨v', hloop, ?_⟩
  have hMlen : M'.length ≤ 1 := by
    have := congrArg List.length hXdecomp
    simp only [List.length_append, hA, hB] at this
    omega
  have hMrev : M'.reverse = M' := by
    match M', hMlen with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, h => simp at h
  rw [hv'List, hXdecomp]
  simp [hMrev, List.append_assoc]

theorem flatSortViewValues_spec {α : Type} (view : FlatSortView α)
    (h0 : 0 ≤ view.offset)
    (h1 : view.offset + Int.ofNat view.length ≤ (view.parent.storage.size : Int)) :
    ∃ values, flatSortViewValues view = .ok values ∧
      values.toList = arraySlice view.parent.storage (view.offset + 1)
        (view.offset + Int.ofNat view.length) ∧
      values.size = view.length := by
  have hmapM :
      ∀ (k : Nat) (off : Nat),
        off + k ≤ view.length →
        ((List.range k).map (fun j => 1 + Int.ofNat (off + j))).mapM
          (fun index => arrayRead view.parent.storage (view.offset + index)) =
        .ok (((view.parent.storage.toList.drop (view.offset.toNat + off)).take k)) := by
    intro k
    induction k with
    | zero => intro off _; simp [pure, Except.pure]
    | succ k ih =>
      intro off hoff
      have hmap := range_map_shift (fun n => 1 + Int.ofNat n) k off
      rw [hmap, List.mapM_cons]
      have hpos : 1 ≤ view.offset + (1 + Int.ofNat off) := by
        simp only [Int.ofNat_eq_natCast]; omega
      have hidxNat : (view.offset + (1 + Int.ofNat off) - 1).toNat = view.offset.toNat + off := by
        simp only [Int.ofNat_eq_natCast]; omega
      have hltSz : view.offset.toNat + off < view.parent.storage.size := by
        simp only [Int.ofNat_eq_natCast] at h1; omega
      have hread : arrayRead view.parent.storage (view.offset + (1 + Int.ofNat off)) =
          .ok (view.parent.storage.toList[view.offset.toNat + off]'(by simpa using hltSz)) := by
        unfold arrayRead
        rw [if_pos hpos, hidxNat, Array.getElem?_eq_getElem hltSz, Array.getElem_toList]
      rw [hread, ih (off + 1) (by omega)]
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq]
      have hdrop : view.parent.storage.toList.drop (view.offset.toNat + off) =
          (view.parent.storage.toList[view.offset.toNat + off]'(by simpa using hltSz)) ::
            view.parent.storage.toList.drop (view.offset.toNat + (off + 1)) := by
        rw [← Nat.add_assoc, List.drop_eq_getElem_cons (by simpa using hltSz)]
      rw [hdrop]; rfl
  have h0' := hmapM view.length 0 (by omega)
  simp only [Nat.add_zero, Nat.zero_add] at h0'
  unfold flatSortViewValues arrayIndexRange
  have hlenNat : ((view.length : Int) - 1 + 1).toNat = view.length := by omega
  rw [hlenNat, h0']
  simp only [bind, Except.bind, pure, Except.pure]
  have hsliceEq : (view.parent.storage.toList.drop view.offset.toNat).take view.length =
      arraySlice view.parent.storage (view.offset + 1) (view.offset + Int.ofNat view.length) := by
    unfold arraySlice
    have e1 : (view.offset + 1 - 1).toNat = view.offset.toNat := by omega
    have e2 : (view.offset + Int.ofNat view.length - (view.offset + 1) + 1).toNat = view.length := by
      simp only [Int.ofNat_eq_natCast]; omega
    rw [e1, e2]
  refine ⟨_, rfl, hsliceEq, ?_⟩
  rw [List.size_toArray, List.length_take, List.length_drop, Array.length_toList]
  simp only [Int.ofNat_eq_natCast] at h1
  omega

theorem forIn_copyBack {α : Type} (sorted : Array α) (offset : Int) :
    ∀ (m : Nat) (k : Nat) (parent : Array α) (P W1 W2 S1 S2 Q : List α),
      parent.toList = P ++ W1 ++ W2 ++ Q →
      sorted.toList = S1 ++ S2 →
      P.length = offset.toNat →
      0 ≤ offset →
      W1.length = k → S1.length = k →
      W2.length = m → S2.length = m →
      ∃ parent',
        (forIn ((List.range m).map (fun j => 1 + Int.ofNat (k + j))) parent fun index p => do
          let value ← liftSortJl (arrayRead sorted index)
          let p ← liftSortJl (arrayWrite p (offset + index) value)
          pure (ForInStep.yield p)) = .ok parent' ∧
        parent'.toList = P ++ W1 ++ S2 ++ Q
  | 0, k, parent, P, W1, W2, S1, S2, Q, hp, _, _, _, _, _, hW2, hS2 => by
    have hW20 : W2 = [] := List.eq_nil_of_length_eq_zero hW2
    have hS20 : S2 = [] := List.eq_nil_of_length_eq_zero hS2
    subst hW20 hS20
    exact ⟨parent, rfl, hp⟩
  | m + 1, k, parent, P, W1, W2, S1, S2, Q, hp, hs, hP, hoff, hW1, hS1, hW2, hS2 => by
    obtain ⟨w, W2', rfl⟩ : ∃ w W2', W2 = w :: W2' := by
      cases W2 with
      | nil => simp at hW2
      | cons w W2' => exact ⟨w, W2', rfl⟩
    obtain ⟨s, S2', rfl⟩ : ∃ s S2', S2 = s :: S2' := by
      cases S2 with
      | nil => simp at hS2
      | cons s S2' => exact ⟨s, S2', rfl⟩
    have hmap := range_map_shift (fun n => 1 + Int.ofNat n) m k
    have hposS : 1 ≤ 1 + Int.ofNat k := by simp only [Int.ofNat_eq_natCast]; omega
    have hidxS : (1 + Int.ofNat k - 1).toNat = S1.length := by
      simp only [Int.ofNat_eq_natCast]; omega
    have hreadS : arrayRead sorted (1 + Int.ofNat k) = .ok s := by
      unfold arrayRead
      rw [if_pos hposS, ← Array.getElem?_toList, hidxS, hs,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    have hpLen : parent.size = P.length + W1.length + (W2'.length + 1) + Q.length := by
      have := congrArg List.length hp
      simp only [Array.length_toList, List.length_append, List.length_cons] at this
      omega
    have hposP : 1 ≤ offset + (1 + Int.ofNat k) := by simp only [Int.ofNat_eq_natCast]; omega
    have hleP : offset + (1 + Int.ofNat k) ≤ (parent.size : Int) := by
      simp only [Int.ofNat_eq_natCast]; omega
    have hidxP : (offset + (1 + Int.ofNat k) - 1).toNat = (P ++ W1).length := by
      simp only [List.length_append, Int.ofNat_eq_natCast]; omega
    let p1 := parent.set! (offset + (1 + Int.ofNat k) - 1).toNat s
    have hwriteP : arrayWrite parent (offset + (1 + Int.ofNat k)) s = .ok p1 := by
      unfold arrayWrite; rw [if_pos ⟨hposP, hleP⟩]
    have hp1List : p1.toList = P ++ (W1 ++ [s]) ++ W2' ++ Q := by
      have hdecomp : parent.toList = (P ++ W1) ++ w :: (W2' ++ Q) := by
        rw [hp]; simp [List.append_assoc]
      simp only [p1, Array.toList_set!, hidxP, hdecomp,
        List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]
      simp [List.append_assoc]
    obtain ⟨parent', hloop, hp'List⟩ :=
      forIn_copyBack sorted offset m (k + 1) p1 P (W1 ++ [s]) W2' (S1 ++ [s]) S2' Q
        hp1List (by rw [hs]; simp [List.append_assoc]) hP hoff
        (by simp [hW1]) (by simp [hS1]) (by simp at hW2; omega) (by simp at hS2; omega)
    refine ⟨parent', ?_, ?_⟩
    · rw [hmap]
      simp only [List.forIn_cons, hreadS, hwriteP, liftSortJl_ok, bind, Except.bind, pure, Except.pure]
      exact hloop
    · rw [hp'List]; simp [List.append_assoc]

theorem subArraySortCorrect_aux :
    ∀ (α Alg : Type) [Inhabited α] (lt : α → α → Bool)
      (nextAlgorithm : Alg → Alg)
      (sortSlice : Array α → Alg → (α → α → SortResult Bool) → ArraySortKeywords α →
        SortResult (Array α × Option (Array α)))
      (view : FlatSortView α) (algorithm : Alg),
      NegTransOrder lt →
      0 ≤ view.offset → view.offset + Int.ofNat view.length ≤ view.parent.storage.size →
      (∀ (values : Array α) (kw : ArraySortKeywords α),
        1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 → kw.hi ≤ values.size →
        ∃ sorted scratch,
          sortSlice values (nextAlgorithm algorithm) (pureCompare lt) kw = .ok (sorted, scratch) ∧
          sorted.size = values.size ∧
          List.Perm (arraySlice values kw.lo kw.hi) (arraySlice sorted kw.lo kw.hi) ∧
          SortedValues lt (arraySlice sorted kw.lo kw.hi) ∧
          sorted.toList.take (kw.lo - 1).toNat = values.toList.take (kw.lo - 1).toNat ∧
          sorted.toList.drop kw.hi.toNat = values.toList.drop kw.hi.toNat) →
      ∃ result, sortSubArrayUnwrappable
          (flatSubArraySortOpsWithNext view nextAlgorithm sortSlice)
          view algorithm (pureCompare lt) { lo := 1, hi := view.length } = .ok result ∧
        result.offset = view.offset ∧ result.length = view.length ∧
        result.parent.dimensions = view.parent.dimensions ∧
        List.Perm view.parent.storage.toList result.parent.storage.toList ∧
        SortedValues lt (arraySlice result.parent.storage
          (view.offset + 1) (view.offset + Int.ofNat view.length)) ∧
        result.parent.storage.toList.take view.offset.toNat =
          view.parent.storage.toList.take view.offset.toNat ∧
        result.parent.storage.toList.drop (view.offset + Int.ofNat view.length).toNat =
          view.parent.storage.toList.drop (view.offset + Int.ofNat view.length).toNat := by
  intro α Alg _ lt nextAlgorithm sortSlice view algorithm hnt hoff0 hoff1 hslice
  unfold sortSubArrayUnwrappable
  dsimp only [flatSubArraySortOpsWithNext]
  change ∃ result, (do
    let parent := view.parent
    if (true && !decide (parent.dimensions = 1) && decide ((view.length : Int) - 1 < 100)) || !decide (view.offset = 0) then
      let values ← liftSortJl (flatSortViewValues view)
      let (sorted, _) ← sortSlice values (nextAlgorithm algorithm) (pureCompare lt) { lo := 1, hi := view.length }
      let mut parent := view.parent.storage
      for index in arrayIndexRange 1 view.length do
        let value ← liftSortJl (arrayRead sorted index)
        parent ← liftSortJl (arrayWrite parent (view.offset + index) value)
      pure { view with parent := { view.parent with storage := parent } }
    else
      let (sorted, _) ← sortSlice view.parent.storage (nextAlgorithm algorithm) (pureCompare lt) { lo := 1, hi := view.length }
      pure { view with parent := { view.parent with storage := sorted } }) = .ok result ∧ _
  by_cases hbranch :
      ((true && !decide (view.parent.dimensions = 1) &&
        decide ((view.length : Int) - 1 < 100)) || !decide (view.offset = 0)) = true
  · simp only [hbranch, ↓reduceIte]
    obtain ⟨values, hvals, hvalsList, hvalsSz⟩ := flatSortViewValues_spec view hoff0 hoff1
    obtain ⟨sorted, scratch, hsort, hsortSz, hsortPerm, hsortOrd, _, _⟩ :=
      hslice values { lo := 1, hi := view.length }
        (Int.le_refl 1) (by dsimp only; omega) (by dsimp only; rw [hvalsSz]; exact Int.le_refl _)
    dsimp only at hsortPerm hsortOrd
    have hsliceValues : arraySlice values 1 view.length = values.toList := by
      unfold arraySlice
      have e1 : ((1 : Int) - 1).toNat = 0 := rfl
      have e2 : ((view.length : Int) - 1 + 1).toNat = values.toList.length := by
        rw [Array.length_toList, hvalsSz]; omega
      rw [e1, e2, List.drop_zero, List.take_length]
    have hsliceSorted : arraySlice sorted 1 view.length = sorted.toList := by
      unfold arraySlice
      have e1 : ((1 : Int) - 1).toNat = 0 := rfl
      have e2 : ((view.length : Int) - 1 + 1).toNat = sorted.toList.length := by
        rw [Array.length_toList, hsortSz, hvalsSz]; omega
      rw [e1, e2, List.drop_zero, List.take_length]
    rw [hsliceValues, hsliceSorted] at hsortPerm
    rw [hsliceSorted] at hsortOrd
    let P := view.parent.storage.toList.take view.offset.toNat
    let M := arraySlice view.parent.storage (view.offset + 1) (view.offset + Int.ofNat view.length)
    let Q := view.parent.storage.toList.drop (view.offset + Int.ofNat view.length).toNat
    have hdecomp := toList_eq_take_slice_drop view.parent.storage
      (view.offset + 1) (view.offset + Int.ofNat view.length)
      (by omega) (by simp only [Int.ofNat_eq_natCast]; omega)
    have hPeq : (view.offset + 1 - 1).toNat = view.offset.toNat := by omega
    rw [hPeq] at hdecomp
    have hPlen : P.length = view.offset.toNat := by
      simp only [P, List.length_take, Array.length_toList]
      simp only [Int.ofNat_eq_natCast] at hoff1; omega
    have hMlen : M.length = view.length := by
      dsimp only [M]; rw [← hvalsList, Array.length_toList, hvalsSz]
    have hrangeEq : arrayIndexRange 1 view.length =
        (List.range view.length).map (fun j => 1 + Int.ofNat (0 + j)) := by
      unfold arrayIndexRange
      have e : ((view.length : Int) - 1 + 1).toNat = view.length := by omega
      rw [e]; simp
    obtain ⟨parent', hcopy, hp'List⟩ :=
      forIn_copyBack sorted view.offset view.length 0 view.parent.storage P [] M [] sorted.toList Q
        (by simpa [P, M, Q] using hdecomp) (by simp) hPlen hoff0 rfl rfl hMlen
        (by rw [Array.length_toList, hsortSz, hvalsSz])
    simp only [List.append_nil] at hp'List
    have htsd := take_slice_drop_of_append parent' P sorted.toList Q
      (view.offset + 1) (view.offset + Int.ofNat view.length)
      (by omega) (by simp only [Int.ofNat_eq_natCast]; omega)
      hp'List (by rw [hPeq, hPlen])
      (by
        have e : (view.offset + Int.ofNat view.length - (view.offset + 1) + 1).toNat = view.length := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [e, Array.length_toList, hsortSz, hvalsSz])
    rw [hPeq] at htsd
    refine ⟨{ view with parent := { view.parent with storage := parent' } },
      ?_, rfl, rfl, rfl, ?_, ?_, htsd.1, htsd.2.2⟩
    · rw [hvals]
      change (do
        let (sorted, _) ← sortSlice values (nextAlgorithm algorithm) (pureCompare lt) { lo := 1, hi := view.length }
        let mut parent := view.parent.storage
        for index in arrayIndexRange 1 view.length do
          let value ← liftSortJl (arrayRead sorted index)
          parent ← liftSortJl (arrayWrite parent (view.offset + index) value)
        pure { view with parent := { view.parent with storage := parent } }) = .ok _
      rw [hsort]
      change (do
        let mut parent := view.parent.storage
        for index in arrayIndexRange 1 view.length do
          let value ← liftSortJl (arrayRead sorted index)
          parent ← liftSortJl (arrayWrite parent (view.offset + index) value)
        pure { view with parent := { view.parent with storage := parent } }) = .ok _
      rw [hrangeEq]
      dsimp only
      rw [hcopy]
      rfl
    · rw [hdecomp, hp'List]
      have hpermM : List.Perm M sorted.toList := by
        dsimp only [M]; rw [← hvalsList]; exact hsortPerm
      exact List.Perm.append_right Q (List.Perm.append_left P hpermM)
    · rw [htsd.2.1]
      exact hsortOrd
  · simp only [hbranch, Bool.false_eq_true, ↓reduceIte]
    have hoffZero : view.offset = 0 := by
      cases h0 : decide (view.offset = 0)
      · simp [h0] at hbranch
      · exact of_decide_eq_true h0
    obtain ⟨sorted, scratch, hsort, hsortSz, hsortPerm, hsortOrd, htake, hdrop⟩ :=
      hslice view.parent.storage { lo := 1, hi := view.length }
        (Int.le_refl 1) (by dsimp only; omega)
        (by dsimp only; simp only [hoffZero, Int.zero_add, Int.ofNat_eq_natCast] at hoff1; exact hoff1)
    rw [hsort]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · have hd1 := toList_eq_take_slice_drop view.parent.storage 1 view.length (Int.le_refl 1) (by omega)
      have hd2 := toList_eq_take_slice_drop sorted 1 view.length (Int.le_refl 1) (by omega)
      have e0 : ((1 : Int) - 1).toNat = 0 := rfl
      rw [e0, List.take_zero, List.nil_append] at hd1 hd2
      rw [hd1, hd2, hdrop]
      exact List.Perm.append_right _ hsortPerm
    · simp only [hoffZero, Int.zero_add, Int.ofNat_eq_natCast]
      exact hsortOrd
    · simp [hoffZero]
    · simp only [hoffZero, Int.zero_add, Int.ofNat_eq_natCast]
      exact hdrop

/-! ## Proofs and Refutations (Batch 5: Reference Sort, InsertionSort, Legacy Entry Points) -/

abbrev SortedPairwise {α : Type} (lt : α → α → Bool) (l : List α) : Prop :=
  l.Pairwise (fun a b => lt b a = false)

def insAll {α : Type} (lt : α → α → Bool) (S l : List α) : List α :=
  l.foldl (fun acc x => insertStable lt x acc) S

theorem insAll_cons {α : Type} {lt : α → α → Bool} (S : List α) (x : α) (l : List α) :
    insAll lt S (x :: l) = insAll lt (insertStable lt x S) l := rfl

theorem insAll_append {α : Type} {lt : α → α → Bool} (S l l' : List α) :
    insAll lt S (l ++ l') = insAll lt (insAll lt S l) l' :=
  List.foldl_append

theorem sortRef_eq_insAll {α : Type} {lt : α → α → Bool} (l : List α) :
    sortRef lt l = insAll lt [] l := rfl

theorem sortRef_concat {α : Type} {lt : α → α → Bool} (l : List α) (x : α) :
    sortRef lt (l ++ [x]) = insertStable lt x (sortRef lt l) := by
  rw [sortRef_eq_insAll, insAll_append]
  rfl

theorem perm_insertStable {α : Type} (lt : α → α → Bool) (x : α) :
    ∀ (l : List α), List.Perm (x :: l) (insertStable lt x l)
  | [] => List.Perm.refl [x]
  | y :: ys => by
    unfold insertStable
    split
    · exact List.Perm.refl _
    · exact List.Perm.trans (List.Perm.swap y x ys) (List.Perm.cons y (perm_insertStable lt x ys))

theorem perm_insAll {α : Type} (lt : α → α → Bool) :
    ∀ (l S : List α), List.Perm (S ++ l) (insAll lt S l)
  | [], S => by simp [insAll]
  | x :: l, S => by
    rw [insAll_cons]
    have h1 : List.Perm (S ++ (x :: l)) ((x :: S) ++ l) := List.perm_middle
    have h2 : List.Perm ((x :: S) ++ l) (insertStable lt x S ++ l) :=
      List.Perm.append_right l (perm_insertStable lt x S)
    exact List.Perm.trans h1 (List.Perm.trans h2 (perm_insAll lt l (insertStable lt x S)))

theorem perm_sortRef {α : Type} (lt : α → α → Bool) (l : List α) :
    List.Perm l (sortRef lt l) := by
  rw [sortRef_eq_insAll]; simpa using perm_insAll lt l []

theorem mem_insertStable {α : Type} {lt : α → α → Bool} {x e : α} {l : List α} :
    e ∈ insertStable lt x l ↔ e = x ∨ e ∈ l := by
  have hp := perm_insertStable lt x l
  rw [← hp.mem_iff, List.mem_cons]

theorem length_insertStable {α : Type} (lt : α → α → Bool) (x : α) (l : List α) :
    (insertStable lt x l).length = l.length + 1 := by
  have hp := perm_insertStable lt x l
  simpa using hp.length_eq.symm

theorem length_sortRef {α : Type} (lt : α → α → Bool) (l : List α) :
    (sortRef lt l).length = l.length :=
  (perm_sortRef lt l).length_eq.symm

theorem mem_sortRef {α : Type} {lt : α → α → Bool} {e : α} (l : List α) :
    e ∈ sortRef lt l ↔ e ∈ l :=
  (perm_sortRef lt l).symm.mem_iff

theorem negTransOrder_lt_of_lt_of_nlt {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) {a b c : α} (hab : lt a b = true) (hcb : lt c b = false) :
    lt a c = true := by
  cases hac : lt a c
  · have := negTransOrder_not_trans hnt hac hcb
    rw [hab] at this; cases this
  · rfl

theorem negTransOrder_lt_of_nlt_of_lt {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) {a b c : α} (hba : lt b a = false) (hbc : lt b c = true) :
    lt a c = true := by
  cases hac : lt a c
  · have := negTransOrder_not_trans hnt hba hac
    rw [hbc] at this; cases this
  · rfl

theorem sorted_insertStable {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (x : α) :
    ∀ {l : List α}, SortedPairwise lt l → SortedPairwise lt (insertStable lt x l)
  | [], _ => by simp [insertStable]
  | y :: ys, hs => by
    have hs' := List.pairwise_cons.1 hs
    simp only [insertStable]
    split
    · rename_i hxy
      refine List.Pairwise.cons ?_ hs
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact negTransOrder_asymm hnt hxy
      · cases hax : lt a x
        · rfl
        · have := hnt.2.1 a x y hax hxy
          rw [hs'.1 a ha] at this; cases this
    · rename_i hxy
      refine List.Pairwise.cons ?_ (sorted_insertStable hnt x hs'.2)
      intro a ha
      rcases mem_insertStable.1 ha with rfl | ha
      · exact Bool.eq_false_iff.2 hxy
      · exact hs'.1 a ha

theorem sorted_insAll {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) :
    ∀ (l S : List α), SortedPairwise lt S → SortedPairwise lt (insAll lt S l)
  | [], _, hS => hS
  | x :: l, S, hS => sorted_insAll hnt l _ (sorted_insertStable hnt x hS)

theorem sorted_sortRef {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (l : List α) : SortedPairwise lt (sortRef lt l) :=
  sorted_insAll hnt l [] List.Pairwise.nil

theorem insertStable_concat {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (x y : α) :
    ∀ (A : List α),
      SortedPairwise lt (A ++ [y]) →
      insertStable lt x (A ++ [y]) = if lt x y then insertStable lt x A ++ [y] else A ++ [y, x]
  | [], _ => by cases hxy : lt x y <;> simp [insertStable, hxy]
  | z :: A, hs => by
    have hs' : SortedPairwise lt (z :: (A ++ [y])) := hs
    have hs'' := List.pairwise_cons.1 hs'
    have hyz : lt y z = false := hs''.1 y (by simp)
    have ih := insertStable_concat hnt x y A hs''.2
    cases hxz : lt x z
    · cases hxy : lt x y <;> simp [insertStable, hxz, hxy, ih]
    · have hxy : lt x y = true := negTransOrder_lt_of_lt_of_nlt hnt hxz hyz
      simp [insertStable, hxz, hxy]

theorem arrayRead_mid {α : Type} {v : Array α} {P B : List α} {z : α} {i : Int}
    (hv : v.toList = P ++ z :: B) (hlo : 1 ≤ i) (hi : (i - 1).toNat = P.length) :
    arrayRead v i = .ok z := by
  unfold arrayRead
  rw [if_pos hlo, ← Array.getElem?_toList, hi, hv,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

theorem arrayWrite_mid {α : Type} {v : Array α} {P B : List α} {z : α} {i : Int} (x : α)
    (hv : v.toList = P ++ z :: B) (hlo : 1 ≤ i) (hi : i = (P.length : Int) + 1) :
    ∃ v', arrayWrite v i x = .ok v' ∧ v'.toList = P ++ x :: B := by
  have hsz : i ≤ (v.size : Int) := by
    have := congrArg List.length hv
    simp only [Array.length_toList, List.length_append, List.length_cons] at this
    omega
  have hidx : (i - 1).toNat = P.length := by omega
  refine ⟨v.set! P.length x, ?_, ?_⟩
  · unfold arrayWrite
    rw [if_pos ⟨hlo, hsz⟩, hidx]
  · simp only [Array.toList_set!, hv, List.set_append_right _ _ (Nat.le_refl _),
      Nat.sub_self, List.set_cons_zero]

theorem stateT_bind_ok {ε σ α β : Type} (m : StateT σ (Except ε) α)
    (f : α → StateT σ (Except ε) β) (s s' : σ) (a : α)
    (h : m.run s = .ok (a, s')) :
    (Bind.bind m f).run s = (f a).run s' := by
  change Bind.bind (m.run s) (fun x => (f x.1).run x.2) = (f a).run s'
  rw [h]; rfl

theorem insertionShift_array_spec {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (lo : Int) (hlo1 : 1 ≤ lo) (x : α) :
    ∀ (m : Nat) (v : Array α) (j : Int) (P A B : List α) (z : α),
      v.toList = P ++ A ++ z :: B →
      (P.length : Int) + 1 = lo →
      j = lo + (m : Int) →
      A.length = m →
      SortedPairwise lt A →
      ∃ v',
        (do
          let j' ← insertionShift (storageMutationOps arrayStorage)
            (fun (_ : Unit) a b => liftM (pureCompare (ε := SortException) lt a b)) () () lo x (m + 1) j
          (storageMutationOps arrayStorage).set () x j'
          pure (ForInStep.yield PUnit.unit)).run v = .ok (ForInStep.yield PUnit.unit, v') ∧
        v'.toList = P ++ insertStable lt x A ++ B
  | 0, v, j, P, A, B, z, hv, hP, hj, hA, _ => by
    have hA0 : A = [] := List.eq_nil_of_length_eq_zero hA
    subst hA0
    obtain ⟨v', hwr, hv'⟩ := arrayWrite_mid x (i := j) (by simpa using hv) (by omega) (by omega)
    refine ⟨v', ?_, by simpa [insertStable] using hv'⟩
    unfold insertionShift
    have hless : ¬ (storageMutationOps (arrayStorage (α := α))).indices.less lo j = true := by
      dsimp [storageMutationOps, arrayStorage, arrayIndices]; simp [hj]
    rw [if_neg hless]
    have hset : ((storageMutationOps arrayStorage).set () x j).run v = .ok ((), v') := by
      dsimp [storageMutationOps, arrayStorage, arrayStorageWith, StateT.run]; rw [hwr]; rfl
    rw [stateT_bind_ok _ _ v v j rfl, stateT_bind_ok _ _ v v' () hset]
    rfl
  | m + 1, v, j, P, A, B, z, hv, hP, hj, hA, hs => by
    obtain ⟨A', y, rfl, hA'⟩ := exists_concat_list A m hA
    have hs' : SortedPairwise lt A' := (List.pairwise_append.1 hs).1
    have hprevRead : arrayRead v (j - 1) = .ok y :=
      arrayRead_mid (P := P ++ A') (B := z :: B)
        (by rw [hv]; simp [List.append_assoc]) (by omega)
        (by simp only [List.length_append]; omega)
    rw [insertStable_concat hnt x y A' hs]
    unfold insertionShift
    have hless : (storageMutationOps (arrayStorage (α := α))).indices.less lo j = true := by
      dsimp [storageMutationOps, arrayStorage, arrayIndices]; simp [hj]; omega
    rw [if_pos hless]
    have hget : ((storageMutationOps arrayStorage).get () ((storageMutationOps (arrayStorage (α := α))).indices.previous j)).run v =
        .ok (y, v) := by
      dsimp [storageMutationOps, arrayStorage, arrayStorageWith, arrayIndices, StateT.run]; rw [hprevRead]; rfl
    rw [bind_assoc, stateT_bind_ok _ _ v v y hget]
    rw [bind_assoc, stateT_bind_ok _ _ v v (lt x y) rfl]
    cases hxy : lt x y
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨v', hwr, hv'⟩ := arrayWrite_mid x (i := j) (P := P ++ A' ++ [y]) (B := B) (z := z)
        (by rw [hv]; simp [List.append_assoc]) (by omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      have hset : ((storageMutationOps arrayStorage).set () x j).run v = .ok ((), v') := by
        dsimp [storageMutationOps, arrayStorage, arrayStorageWith, StateT.run]; rw [hwr]; rfl
      refine ⟨v', ?_, by simpa [List.append_assoc] using hv'⟩
      rw [stateT_bind_ok _ _ v v j rfl, stateT_bind_ok _ _ v v' () hset]
      rfl
    · simp only [↓reduceIte]
      obtain ⟨v1, hwr1, hv1⟩ := arrayWrite_mid y (i := j) (P := P ++ A' ++ [y]) (B := B) (z := z)
        (by rw [hv]; simp [List.append_assoc]) (by omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      have hset1 : ((storageMutationOps arrayStorage).set () y j).run v = .ok ((), v1) := by
        dsimp [storageMutationOps, arrayStorage, arrayStorageWith, StateT.run]; rw [hwr1]; rfl
      rw [bind_assoc, stateT_bind_ok _ _ v v1 () hset1]
      have hv1' : v1.toList = P ++ A' ++ y :: (y :: B) := by
        rw [hv1]; simp [List.append_assoc]
      obtain ⟨v', hrec, hv'⟩ :=
        insertionShift_array_spec hnt lo hlo1 x m v1 (j - 1) P A' (y :: B) y
          hv1' hP (by omega) hA' hs'
      refine ⟨v', hrec, ?_⟩
      rw [hv']; simp [List.append_assoc]
theorem forIn_insertionSort_array {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (lo : Int) (hlo1 : 1 ≤ lo) (P Q : List α)
    (hP : (P.length : Int) + 1 = lo) :
    ∀ (m : Nat) (k : Nat) (v : Array α) (L R : List α),
      v.toList = P ++ L ++ R ++ Q →
      L.length = k + 1 →
      R.length = m →
      SortedPairwise lt L →
      ∃ v',
        (forIn ((List.range m).map (fun j => (lo + 1) + Int.ofNat (k + j))) PUnit.unit
          fun i _ => do
            let value ← (storageMutationOps arrayStorage).get () i
            let j ← insertionShift (storageMutationOps arrayStorage)
              (fun (_ : Unit) a b => liftM (pureCompare (ε := SortException) lt a b)) () () lo value
              ((storageMutationOps (arrayStorage (α := α))).distance lo i + 1) i
            (storageMutationOps arrayStorage).set () value j
            pure (ForInStep.yield PUnit.unit)).run v = .ok (PUnit.unit, v') ∧
        v'.toList = P ++ insAll lt L R ++ Q
  | 0, k, v, L, R, hv, _, hR, _ => by
    have hR0 : R = [] := List.eq_nil_of_length_eq_zero hR
    subst hR0
    exact ⟨v, rfl, by simpa [insAll] using hv⟩
  | m + 1, k, v, L, R, hv, hL, hR, hsL => by
    obtain ⟨x, R', rfl⟩ : ∃ x R', R = x :: R' := by
      cases R with
      | nil => simp at hR
      | cons x R' => exact ⟨x, R', rfl⟩
    have hmap := range_map_shift (fun n => (lo + 1) + Int.ofNat n) m k
    let i := (lo + 1) + Int.ofNat k
    have hread : arrayRead v i = .ok x :=
      arrayRead_mid (P := P ++ L) (B := R' ++ Q)
        (by rw [hv]; simp [List.append_assoc])
        (by dsimp [i]; omega)
        (by dsimp [i]; simp only [List.length_append]; omega)
    have hdist : (storageMutationOps (arrayStorage (α := α))).distance lo i = k + 1 := by
      dsimp [storageMutationOps, arrayStorage, i]; omega
    obtain ⟨v1, hshift, hv1⟩ :=
      insertionShift_array_spec hnt lo hlo1 x (k + 1) v i P L (R' ++ Q) x
        (by rw [hv]; simp [List.append_assoc]) hP
        (by dsimp [i]; omega) hL hsL
    obtain ⟨v', hrec, hv'⟩ :=
      forIn_insertionSort_array hnt lo hlo1 P Q hP m (k + 1) v1
        (insertStable lt x L) R'
        (by rw [hv1]; simp [List.append_assoc])
        (by rw [length_insertStable, hL])
        (by simp at hR; omega)
        (sorted_insertStable hnt x hsL)
    refine ⟨v', ?_, ?_⟩
    · rw [hmap, List.forIn_cons]
      have hget : ((storageMutationOps arrayStorage).get () i).run v = .ok (x, v) := by
        dsimp [storageMutationOps, arrayStorage, arrayStorageWith, StateT.run]; rw [hread]; rfl
      have hstep :
          (do
            let value ← (storageMutationOps arrayStorage).get () i
            let j ← insertionShift (storageMutationOps arrayStorage)
              (fun (_ : Unit) a b => liftM (pureCompare (ε := SortException) lt a b)) () () lo value
              ((storageMutationOps (arrayStorage (α := α))).distance lo i + 1) i
            (storageMutationOps arrayStorage).set () value j
            pure (ForInStep.yield PUnit.unit)).run v =
          .ok (ForInStep.yield PUnit.unit, v1) := by
        rw [stateT_bind_ok _ _ v v x hget, hdist]
        exact hshift
      rw [stateT_bind_ok _ _ v v1 (ForInStep.yield PUnit.unit) hstep]
      exact hrec
    · rw [hv', insAll_cons]

theorem arrayInsertion_spec {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (v : Array α) (lo hi : Int) (P M Q : List α)
    (hlo1 : 1 ≤ lo) (hv : v.toList = P ++ M ++ Q)
    (hP : (P.length : Int) + 1 = lo) (hM : (M.length : Int) = hi - lo + 1) :
    ∃ v', storageInsertion arrayStorage (pureCompare lt) v lo hi = .ok v' ∧
      v'.toList = P ++ sortRef lt M ++ Q := by
  unfold storageInsertion insertionSort
  dsimp only
  cases M with
  | nil =>
    have hrange : (storageMutationOps (arrayStorage (α := α))).indices.range
        ((storageMutationOps (arrayStorage (α := α))).indices.addOne lo) hi = [] := by
      dsimp [storageMutationOps, arrayStorage, arrayIndices, arrayIndexRange]
      simp only [ List.length_nil ] at hM
      have hzero : (hi - (lo + 1) + 1).toNat = 0 := by omega
      rw [hzero]; rfl
    rw [hrange]
    refine ⟨v, rfl, ?_⟩
    simpa [sortRef] using hv
  | cons first rest =>
    have hrange : (storageMutationOps (arrayStorage (α := α))).indices.range
        ((storageMutationOps (arrayStorage (α := α))).indices.addOne lo) hi =
        (List.range rest.length).map (fun j => (lo + 1) + Int.ofNat (0 + j)) := by
      dsimp [storageMutationOps, arrayStorage, arrayIndices, arrayIndexRange]
      simp only [List.length_cons] at hM
      have hlen : (hi - (lo + 1) + 1).toNat = rest.length := by omega
      rw [hlen]; simp
    rw [hrange]
    obtain ⟨v', hloop, hv'⟩ :=
      forIn_insertionSort_array hnt lo hlo1 P Q hP rest.length 0 v [first] rest
        (by rw [hv]; simp [List.append_assoc]) rfl rfl (by simp)
    refine ⟨v', ?_, ?_⟩
    · rw [stateT_bind_ok _ _ v v' PUnit.unit hloop]
      rfl
    · rw [hv', sortRef_eq_insAll, insAll_cons]
      rfl

theorem arrayInsertion_whole {α : Type} [Inhabited α] {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (values : Array α) :
    ∃ result,
      storageInsertion arrayStorage (pureCompare lt) values 1 values.size = .ok result ∧
      List.Perm values.toList result.toList ∧
      SortedValues lt result.toList := by
  obtain ⟨result, hins, hlist⟩ :=
    arrayInsertion_spec hnt values 1 values.size [] values.toList []
      (Int.le_refl 1) (by simp) rfl (by simp)
  simp only [List.nil_append, List.append_nil] at hlist
  refine ⟨result, hins, ?_, ?_⟩
  · rw [hlist]; exact perm_sortRef lt values.toList
  · rw [hlist, sortedValues_iff_pairwise hnt]; exact sorted_sortRef hnt values.toList







/-- Julia's documented `AbstractVector` interface for one-based storage: `length(v)` counts the
elements `elems v`, `v[i]` returns element `i` for `1 ≤ i ≤ length(v)` and throws `BoundsError`
otherwise, and `v[i] = x` replaces exactly element `i` (throwing `BoundsError` out of range). -/
structure StorageLaws {V α : Type} (S : VectorStorage V α) (elems : V → List α) : Prop where
  length_eq : ∀ v, S.length v = (elems v).length
  getindex_eq : ∀ v i, S.getindex v i = arrayRead (elems v).toArray i
  setindex_ok : ∀ v i x, 1 ≤ i → i ≤ ((elems v).length : Int) →
    ∃ v', S.setindex v i x = .ok v' ∧ elems v' = (elems v).set (i - 1).toNat x
  setindex_error : ∀ v i x, ¬ (1 ≤ i ∧ i ≤ ((elems v).length : Int)) →
    S.setindex v i x = .error .boundsError
  firstindex_eq : ∀ v, S.firstindex v = 1

theorem arrayStorage_laws {α : Type} : StorageLaws (arrayStorage (α := α)) Array.toList where
  firstindex_eq := fun v => rfl
  length_eq := fun v => by simp
  getindex_eq := fun v i => by simp
  setindex_ok := fun v i x h1 h2 => by
    refine ⟨v.set! (i - 1).toNat x, ?_, by simp [Array.toList_set!]⟩
    simp only [arrayStorage_setindex, arrayWrite]
    rw [if_pos ⟨h1, by simpa using h2⟩]
  setindex_error := fun v i x h => by
    simp only [arrayStorage_setindex, arrayWrite]
    rw [if_neg (by simpa using h)]

section Storage

variable {V α : Type} {S : VectorStorage V α} {E : V → List α}

theorem storage_read_mid (L : StorageLaws S E) {v : V} {P B : List α} {z : α} {i : Int}
    (hv : E v = P ++ z :: B) (hlo : 1 ≤ i) (hi : (i - 1).toNat = P.length) :
    S.getindex v i = .ok z := by
  rw [L.getindex_eq]
  unfold arrayRead
  rw [if_pos hlo, List.getElem?_toArray, hi, hv,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]

theorem storage_write_mid (L : StorageLaws S E) {v : V} {P B : List α} {z : α} {i : Int}
    (x : α) (hv : E v = P ++ z :: B) (hlo : 1 ≤ i) (hi : i = (P.length : Int) + 1) :
    ∃ v', S.setindex v i x = .ok v' ∧ E v' = P ++ x :: B := by
  have hsz : i ≤ ((E v).length : Int) := by
    rw [hv]; simp only [List.length_append, List.length_cons]; omega
  obtain ⟨v', hset, hv'⟩ := L.setindex_ok v i x hlo hsz
  refine ⟨v', hset, ?_⟩
  have hidx : (i - 1).toNat = P.length := by omega
  rw [hv', hidx, hv, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

theorem storage_length (L : StorageLaws S E) (v : V) : S.length v = (E v).length :=
  L.length_eq v

theorem storage_lastindex (L : StorageLaws S E) (v : V) :
    S.lastindex v = ((E v).length : Int) := by
  simp [VectorStorage.lastindex, L.firstindex_eq v, L.length_eq v] <;> omega

theorem storageCheckBounds_ok (L : StorageLaws S E) {v : V} {lo hi : Int}
    (h : 1 ≤ lo ∧ hi ≤ ((E v).length : Int) ∨ hi < lo) :
    storageCheckBounds S v lo hi = .ok () := by
  rw [storageCheckBounds_eq, L.firstindex_eq v, storage_lastindex L v, if_pos (by omega)]

/-! ### `InsertionSort` on any storage -/

theorem insertionShift_storage_spec (L : StorageLaws S E) {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (lo : Int) (hlo1 : 1 ≤ lo) (x : α) :
    ∀ (m : Nat) (v : V) (j : Int) (P A B : List α) (z : α),
      E v = P ++ A ++ z :: B →
      (P.length : Int) + 1 = lo →
      j = lo + (m : Int) →
      A.length = m →
      SortedPairwise lt A →
      ∃ v',
        (do
          let j' ← insertionShift (storageMutationOps S)
            (fun (_ : Unit) a b => liftM (pureCompare (ε := SortException) lt a b)) () () lo x (m + 1) j
          (storageMutationOps S).set () x j'
          pure (ForInStep.yield PUnit.unit)).run v = .ok (ForInStep.yield PUnit.unit, v') ∧
        E v' = P ++ insertStable lt x A ++ B
  | 0, v, j, P, A, B, z, hv, hP, hj, hA, _ => by
    have hA0 : A = [] := List.eq_nil_of_length_eq_zero hA
    subst hA0
    obtain ⟨v', hwr, hv'⟩ := storage_write_mid L x (i := j) (by simpa using hv) (by omega)
      (by omega)
    refine ⟨v', ?_, by simpa [insertStable] using hv'⟩
    unfold insertionShift
    have hless : ¬ (storageMutationOps S).indices.less lo j = true := by
      dsimp [storageMutationOps, arrayIndices]; simp [hj]
    rw [if_neg hless]
    have hset : ((storageMutationOps S).set () x j).run v = .ok ((), v') := by
      dsimp [storageMutationOps, StateT.run]; rw [hwr]; rfl
    rw [stateT_bind_ok _ _ v v j rfl, stateT_bind_ok _ _ v v' () hset]
    rfl
  | m + 1, v, j, P, A, B, z, hv, hP, hj, hA, hs => by
    obtain ⟨A', y, rfl, hA'⟩ := exists_concat_list A m hA
    have hs' : SortedPairwise lt A' := (List.pairwise_append.1 hs).1
    have hprevRead : S.getindex v (j - 1) = .ok y :=
      storage_read_mid L (P := P ++ A') (B := z :: B)
        (by rw [hv]; simp [List.append_assoc]) (by omega)
        (by simp only [List.length_append]; omega)
    rw [insertStable_concat hnt x y A' hs]
    unfold insertionShift
    have hless : (storageMutationOps S).indices.less lo j = true := by
      dsimp [storageMutationOps, arrayIndices]; simp [hj]; omega
    rw [if_pos hless]
    have hget : ((storageMutationOps S).get () ((storageMutationOps S).indices.previous j)).run v =
        .ok (y, v) := by
      dsimp [storageMutationOps, arrayIndices, StateT.run]; rw [hprevRead]; rfl
    rw [bind_assoc, stateT_bind_ok _ _ v v y hget]
    rw [bind_assoc, stateT_bind_ok _ _ v v (lt x y) rfl]
    cases hxy : lt x y
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨v', hwr, hv'⟩ := storage_write_mid L x (i := j) (P := P ++ A' ++ [y]) (B := B)
        (z := z) (by rw [hv]; simp [List.append_assoc]) (by omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      have hset : ((storageMutationOps S).set () x j).run v = .ok ((), v') := by
        dsimp [storageMutationOps, StateT.run]; rw [hwr]; rfl
      refine ⟨v', ?_, by simpa [List.append_assoc] using hv'⟩
      rw [stateT_bind_ok _ _ v v j rfl, stateT_bind_ok _ _ v v' () hset]
      rfl
    · simp only [↓reduceIte]
      obtain ⟨v1, hwr1, hv1⟩ := storage_write_mid L y (i := j) (P := P ++ A' ++ [y]) (B := B)
        (z := z) (by rw [hv]; simp [List.append_assoc]) (by omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      have hset1 : ((storageMutationOps S).set () y j).run v = .ok ((), v1) := by
        dsimp [storageMutationOps, StateT.run]; rw [hwr1]; rfl
      rw [bind_assoc, stateT_bind_ok _ _ v v1 () hset1]
      have hv1' : E v1 = P ++ A' ++ y :: (y :: B) := by
        rw [hv1]; simp [List.append_assoc]
      obtain ⟨v', hrec, hv'⟩ :=
        insertionShift_storage_spec L hnt lo hlo1 x m v1 (j - 1) P A' (y :: B) y
          hv1' hP (by omega) hA' hs'
      refine ⟨v', hrec, ?_⟩
      rw [hv']; simp [List.append_assoc]

theorem forIn_insertionSort_storage (L : StorageLaws S E) {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (lo : Int) (hlo1 : 1 ≤ lo) (P Q : List α)
    (hP : (P.length : Int) + 1 = lo) :
    ∀ (m : Nat) (k : Nat) (v : V) (L' R : List α),
      E v = P ++ L' ++ R ++ Q →
      L'.length = k + 1 →
      R.length = m →
      SortedPairwise lt L' →
      ∃ v',
        (forIn ((List.range m).map (fun j => (lo + 1) + Int.ofNat (k + j))) PUnit.unit
          fun i _ => do
            let value ← (storageMutationOps S).get () i
            let j ← insertionShift (storageMutationOps S)
              (fun (_ : Unit) a b => liftM (pureCompare (ε := SortException) lt a b)) () () lo value
              ((storageMutationOps S).distance lo i + 1) i
            (storageMutationOps S).set () value j
            pure (ForInStep.yield PUnit.unit)).run v = .ok (PUnit.unit, v') ∧
        E v' = P ++ insAll lt L' R ++ Q
  | 0, k, v, L', R, hv, _, hR, _ => by
    have hR0 : R = [] := List.eq_nil_of_length_eq_zero hR
    subst hR0
    exact ⟨v, rfl, by simpa [insAll] using hv⟩
  | m + 1, k, v, L', R, hv, hL, hR, hsL => by
    obtain ⟨x, R', rfl⟩ : ∃ x R', R = x :: R' := by
      cases R with
      | nil => simp at hR
      | cons x R' => exact ⟨x, R', rfl⟩
    have hmap := range_map_shift (fun n => (lo + 1) + Int.ofNat n) m k
    let i := (lo + 1) + Int.ofNat k
    have hread : S.getindex v i = .ok x :=
      storage_read_mid L (P := P ++ L') (B := R' ++ Q)
        (by rw [hv]; simp [List.append_assoc])
        (by dsimp [i]; omega)
        (by dsimp [i]; simp only [List.length_append]; omega)
    have hdist : (storageMutationOps S).distance lo i = k + 1 := by
      dsimp [storageMutationOps, i]; omega
    obtain ⟨v1, hshift, hv1⟩ :=
      insertionShift_storage_spec L hnt lo hlo1 x (k + 1) v i P L' (R' ++ Q) x
        (by rw [hv]; simp [List.append_assoc]) hP
        (by dsimp [i]; omega) hL hsL
    obtain ⟨v', hrec, hv'⟩ :=
      forIn_insertionSort_storage L hnt lo hlo1 P Q hP m (k + 1) v1
        (insertStable lt x L') R'
        (by rw [hv1]; simp [List.append_assoc])
        (by rw [length_insertStable, hL])
        (by simp at hR; omega)
        (sorted_insertStable hnt x hsL)
    refine ⟨v', ?_, ?_⟩
    · rw [hmap, List.forIn_cons]
      have hget : ((storageMutationOps S).get () i).run v = .ok (x, v) := by
        dsimp [storageMutationOps, StateT.run]; rw [hread]; rfl
      have hstep :
          (do
            let value ← (storageMutationOps S).get () i
            let j ← insertionShift (storageMutationOps S)
              (fun (_ : Unit) a b => liftM (pureCompare (ε := SortException) lt a b)) () () lo value
              ((storageMutationOps S).distance lo i + 1) i
            (storageMutationOps S).set () value j
            pure (ForInStep.yield PUnit.unit)).run v =
          .ok (ForInStep.yield PUnit.unit, v1) := by
        rw [stateT_bind_ok _ _ v v x hget, hdist]
        exact hshift
      rw [stateT_bind_ok _ _ v v1 (ForInStep.yield PUnit.unit) hstep]
      exact hrec
    · rw [hv', insAll_cons]

/-- `InsertionSort` on the window `lo:hi` of any `AbstractVector` storage replaces the window
by its stable sorted permutation and leaves the other elements unchanged. -/
theorem storageInsertion_spec (L : StorageLaws S E) {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (v : V) (lo hi : Int) (P M Q : List α)
    (hlo1 : 1 ≤ lo) (hv : E v = P ++ M ++ Q)
    (hP : (P.length : Int) + 1 = lo) (hM : (M.length : Int) = hi - lo + 1) :
    ∃ v', storageInsertion S (pureCompare lt) v lo hi = .ok v' ∧
      E v' = P ++ sortRef lt M ++ Q := by
  unfold storageInsertion insertionSort
  dsimp only
  cases M with
  | nil =>
    have hrange : (storageMutationOps S).indices.range
        ((storageMutationOps S).indices.addOne lo) hi = [] := by
      dsimp [storageMutationOps, arrayIndices, arrayIndexRange]
      simp only [List.length_nil] at hM
      have hzero : (hi - (lo + 1) + 1).toNat = 0 := by omega
      rw [hzero]; rfl
    rw [hrange]
    refine ⟨v, rfl, ?_⟩
    simpa [sortRef] using hv
  | cons first rest =>
    have hrange : (storageMutationOps S).indices.range
        ((storageMutationOps S).indices.addOne lo) hi =
        (List.range rest.length).map (fun j => (lo + 1) + Int.ofNat (0 + j)) := by
      dsimp [storageMutationOps, arrayIndices, arrayIndexRange]
      simp only [List.length_cons] at hM
      have hlen : (hi - (lo + 1) + 1).toNat = rest.length := by omega
      rw [hlen]; simp
    rw [hrange]
    obtain ⟨v', hloop, hv'⟩ :=
      forIn_insertionSort_storage L hnt lo hlo1 P Q hP rest.length 0 v [first] rest
        (by rw [hv]; simp [List.append_assoc]) rfl rfl (by simp)
    refine ⟨v', ?_, ?_⟩
    · rw [stateT_bind_ok _ _ v v' PUnit.unit hloop]
      rfl
    · rw [hv', sortRef_eq_insAll, insAll_cons]
      rfl

end Storage

/-! ## Sort outcomes and stability -/

section Outcome

variable {α : Type}

/-- `x` and `y` are equivalent under the strict order `lt`. -/
def sameClass (lt : α → α → Bool) (x y : α) : Bool := !lt x y && !lt y x

/-- `after` keeps every equivalence class of `before` in its original relative order. -/
def StableWrt (lt : α → α → Bool) (before after : List α) : Prop :=
  ∀ x, after.filter (sameClass lt x) = before.filter (sameClass lt x)

/-- What a sorting algorithm promises for a window: a sorted permutation, which keeps equivalent
elements in their original relative order when the algorithm is stable. -/
def SortOutcome (lt : α → α → Bool) (stable : Bool) (before after : List α) : Prop :=
  List.Perm after before ∧ SortedPairwise lt after ∧ (stable = true → StableWrt lt before after)

theorem sameClass_iff {lt : α → α → Bool} {x y : α} :
    sameClass lt x y = true ↔ lt x y = false ∧ lt y x = false := by
  simp [sameClass]

theorem sameClass_self {lt : α → α → Bool} (hnt : NegTransOrder lt) (x : α) :
    sameClass lt x x = true :=
  sameClass_iff.2 ⟨hnt.1 x, hnt.1 x⟩

theorem sameClass_comm (lt : α → α → Bool) (x y : α) : sameClass lt x y = sameClass lt y x := by
  simp [sameClass, Bool.and_comm]

theorem sameClass_trans {lt : α → α → Bool} (hnt : NegTransOrder lt) {x y z : α}
    (hxy : sameClass lt x y = true) (hyz : sameClass lt y z = true) :
    sameClass lt x z = true := by
  rw [sameClass_iff] at *
  exact ⟨negTransOrder_not_trans hnt hxy.1 hyz.1, negTransOrder_not_trans hnt hyz.2 hxy.2⟩

theorem lt_congr_left {lt : α → α → Bool} (hnt : NegTransOrder lt) {x y : α} (z : α)
    (h : sameClass lt x y = true) : lt x z = lt y z := by
  rw [sameClass_iff] at h
  cases hxz : lt x z <;> cases hyz : lt y z
  · rfl
  · rcases hnt.2.2 y x z hyz with h1 | h1
    · rw [h.2] at h1; cases h1
    · rw [hxz] at h1; cases h1
  · rcases hnt.2.2 x y z hxz with h1 | h1
    · rw [h.1] at h1; cases h1
    · rw [hyz] at h1; cases h1
  · rfl

theorem lt_congr_right {lt : α → α → Bool} (hnt : NegTransOrder lt) {x y : α} (z : α)
    (h : sameClass lt x y = true) : lt z x = lt z y := by
  rw [sameClass_iff] at h
  cases hzx : lt z x <;> cases hzy : lt z y
  · rfl
  · rcases hnt.2.2 z x y hzy with h1 | h1
    · rw [hzx] at h1; cases h1
    · rw [h.1] at h1; cases h1
  · rcases hnt.2.2 z y x hzx with h1 | h1
    · rw [hzy] at h1; cases h1
    · rw [h.2] at h1; cases h1
  · rfl

theorem insertStable_filter {lt : α → α → Bool} (hnt : NegTransOrder lt) (y x : α) :
    ∀ (S : List α), SortedPairwise lt S →
      (insertStable lt y S).filter (sameClass lt x) =
        S.filter (sameClass lt x) ++ (if sameClass lt x y then [y] else [])
  | [], _ => by by_cases h : sameClass lt x y = true <;> simp [insertStable, h]
  | z :: S, hs => by
    have hs' := List.pairwise_cons.1 hs
    unfold insertStable
    by_cases hyz : lt y z = true
    · rw [if_pos hyz]
      have hgt : ∀ w ∈ z :: S, lt y w = true := by
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hyz
        · exact negTransOrder_lt_of_lt_of_nlt hnt hyz (hs'.1 w hw)
      by_cases hxy : sameClass lt x y = true
      · have hnone : (z :: S).filter (sameClass lt x) = [] := by
          rw [List.filter_eq_nil_iff]
          intro w hw hxw
          have hyw := sameClass_trans hnt (by rwa [sameClass_comm] at hxy) hxw
          rw [sameClass_iff, hgt w hw] at hyw
          exact Bool.noConfusion hyw.1
        rw [List.filter_cons, if_pos hxy, hnone, if_pos hxy]
        rfl
      · rw [List.filter_cons, if_neg hxy, if_neg hxy, List.append_nil]
    · rw [if_neg hyz, List.filter_cons, List.filter_cons, insertStable_filter hnt y x S hs'.2]
      split <;> simp

theorem insAll_filter {lt : α → α → Bool} (hnt : NegTransOrder lt) (x : α) :
    ∀ (l S : List α), SortedPairwise lt S →
      (insAll lt S l).filter (sameClass lt x) =
        S.filter (sameClass lt x) ++ l.filter (sameClass lt x)
  | [], S, _ => by simp [insAll]
  | y :: l, S, hS => by
    rw [insAll_cons, insAll_filter hnt x l _ (sorted_insertStable hnt y hS),
      insertStable_filter hnt y x S hS, List.filter_cons]
    by_cases h : sameClass lt x y = true <;> simp [h]

theorem sortRef_outcome {lt : α → α → Bool} (hnt : NegTransOrder lt) (s : Bool) (l : List α) :
    SortOutcome lt s l (sortRef lt l) :=
  ⟨(perm_sortRef lt l).symm, sorted_sortRef hnt l, fun _ x => by
    rw [sortRef_eq_insAll, insAll_filter hnt x l [] List.Pairwise.nil]; simp⟩

theorem outcome_of_sorted {lt : α → α → Bool} (s : Bool) {l : List α}
    (h : SortedPairwise lt l) : SortOutcome lt s l l :=
  ⟨List.Perm.refl l, h, fun _ _ => rfl⟩

theorem outcome_weaken {lt : α → α → Bool} {s : Bool} {l l' : List α}
    (h : SortOutcome lt true l l') : SortOutcome lt s l l' :=
  ⟨h.1, h.2.1, fun _ => h.2.2 rfl⟩

theorem outcome_reverse_of_strict {lt : α → α → Bool} (hnt : NegTransOrder lt) (s : Bool)
    {l : List α} (h : l.Pairwise (fun a b => lt b a = true)) :
    SortOutcome lt s l l.reverse := by
  refine ⟨List.reverse_perm l, ?_, fun _ x => ?_⟩
  · unfold SortedPairwise
    rw [List.pairwise_reverse]
    exact h.imp fun hba => negTransOrder_asymm hnt hba
  · rw [List.filter_reverse]
    have hF : (l.filter (sameClass lt x)).Pairwise (fun a b => lt b a = true) := h.filter _
    have hmem : ∀ a ∈ l.filter (sameClass lt x), sameClass lt x a = true :=
      fun a ha => (List.mem_filter.1 ha).2
    generalize l.filter (sameClass lt x) = F at hF hmem
    match F, hF, hmem with
    | [], _, _ => rfl
    | [_], _, _ => rfl
    | a :: b :: rest, hF, hmem =>
      have hba : lt b a = true := (List.pairwise_cons.1 hF).1 b (by simp)
      have hab := sameClass_trans hnt
        (by rw [sameClass_comm]; exact hmem a (by simp)) (hmem b (by simp))
      rw [sameClass_iff, hba] at hab
      exact Bool.noConfusion hab.2

theorem sorted_pivot_append {lt : α → α → Bool} (hnt : NegTransOrder lt) {L R : List α} {p : α}
    (hL : SortedPairwise lt L) (hR : SortedPairwise lt R)
    (hLp : ∀ a ∈ L, lt p a = false) (hpR : ∀ b ∈ R, lt b p = false) :
    SortedPairwise lt (L ++ p :: R) := by
  unfold SortedPairwise at *
  rw [List.pairwise_append]
  refine ⟨hL, List.Pairwise.cons hpR hR, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact hLp a ha
  · exact negTransOrder_not_trans hnt (hpR b hb) (hLp a ha)

/-- Elements of the window `B ++ p :: A` that `partition!` sends below the pivot `p`: those
before it that are not greater, then those after it that are less. -/
def partLeft (lt : α → α → Bool) (p : α) (B A : List α) : List α :=
  B.filter (fun y => !lt p y) ++ A.filter (fun y => lt y p)

/-- Elements that `partition!` sends above the pivot `p`. -/
def partRight (lt : α → α → Bool) (p : α) (B A : List α) : List α :=
  B.filter (fun y => lt p y) ++ A.filter (fun y => !lt y p)

theorem partition_perm (lt : α → α → Bool) (p : α) (B A : List α) :
    List.Perm (partLeft lt p B A ++ p :: partRight lt p B A) (B ++ p :: A) := by
  unfold partLeft partRight
  refine List.perm_middle.trans (List.Perm.trans ?_ List.perm_middle.symm)
  refine List.Perm.cons p ?_
  have hB : List.Perm (B.filter (fun y => !lt p y) ++ B.filter (fun y => lt p y)) B := by
    have := List.filter_append_perm (fun y => lt p y) B
    exact List.perm_append_comm.trans (by simpa using this)
  have hA : List.Perm (A.filter (fun y => lt y p) ++ A.filter (fun y => !lt y p)) A :=
    List.filter_append_perm (fun y => lt y p) A
  calc List.Perm _ (B.filter (fun y => !lt p y) ++ (B.filter (fun y => lt p y) ++
        (A.filter (fun y => lt y p) ++ A.filter (fun y => !lt y p)))) := by
        rw [List.append_assoc]
        exact List.Perm.append_left _ (List.perm_append_comm_assoc _ _ _)
    _ = (B.filter (fun y => !lt p y) ++ B.filter (fun y => lt p y)) ++
        (A.filter (fun y => lt y p) ++ A.filter (fun y => !lt y p)) := by
        rw [List.append_assoc]
    List.Perm _ (B ++ A) := List.Perm.append hB hA

theorem filter_class_and_true {lt : α → α → Bool} (x : α) (f : α → Bool) (l : List α)
    (hf : ∀ y, sameClass lt x y = true → f y = true) :
    l.filter (fun a => sameClass lt x a && f a) = l.filter (sameClass lt x) := by
  refine List.filter_congr fun y _ => ?_
  cases hxy : sameClass lt x y
  · rfl
  · rw [hf y hxy]; rfl

theorem filter_class_and_false {lt : α → α → Bool} (x : α) (f : α → Bool) (l : List α)
    (hf : ∀ y, sameClass lt x y = true → f y = false) :
    l.filter (fun a => sameClass lt x a && f a) = [] := by
  rw [List.filter_eq_nil_iff]
  intro y _ hy
  simp only [Bool.and_eq_true] at hy
  rw [hf y hy.1] at hy
  exact Bool.noConfusion hy.2

theorem partition_outcome {lt : α → α → Bool} (hnt : NegTransOrder lt) {s : Bool} {p : α}
    {B A L' R' : List α}
    (hL : SortOutcome lt s (partLeft lt p B A) L') (hR : SortOutcome lt s (partRight lt p B A) R') :
    SortOutcome lt s (B ++ p :: A) (L' ++ p :: R') := by
  refine ⟨((hL.1.append (List.Perm.cons p hR.1))).trans (partition_perm lt p B A), ?_, ?_⟩
  · refine sorted_pivot_append hnt hL.2.1 hR.2.1 ?_ ?_
    · intro a ha
      rcases List.mem_append.1 (hL.1.mem_iff.1 ha) with ha | ha
      · simpa using (List.mem_filter.1 ha).2
      · exact negTransOrder_asymm hnt (by simpa using (List.mem_filter.1 ha).2)
    · intro b hb
      rcases List.mem_append.1 (hR.1.mem_iff.1 hb) with hb | hb
      · exact negTransOrder_asymm hnt (by simpa using (List.mem_filter.1 hb).2)
      · simpa using (List.mem_filter.1 hb).2
  · intro hs x
    rw [List.filter_append, List.filter_cons, hL.2.2 hs x, hR.2.2 hs x, List.filter_append,
      List.filter_cons]
    unfold partLeft partRight
    simp only [List.filter_append, List.filter_filter]
    by_cases hxp : sameClass lt x p = true
    · have hc : ∀ y, sameClass lt x y = true → lt p y = false ∧ lt y p = false := fun y hy =>
        sameClass_iff.1 (sameClass_trans hnt (by rwa [sameClass_comm] at hxp) hy)
      have hB1 : B.filter (fun a => sameClass lt x a && !lt p a) = B.filter (sameClass lt x) :=
        filter_class_and_true x _ B fun y hy => by simp [(hc y hy).1]
      have hA1 : A.filter (fun a => sameClass lt x a && lt a p) = [] :=
        filter_class_and_false x _ A fun y hy => (hc y hy).2
      have hB2 : B.filter (fun a => sameClass lt x a && lt p a) = [] :=
        filter_class_and_false x _ B fun y hy => (hc y hy).1
      have hA2 : A.filter (fun a => sameClass lt x a && !lt a p) = A.filter (sameClass lt x) :=
        filter_class_and_true x _ A fun y hy => by simp [(hc y hy).2]
      rw [hB1, hA1, hB2, hA2]
      simp [hxp]
    · have htri : lt x p = true ∨ lt p x = true := by
        rw [sameClass_iff] at hxp
        cases h1 : lt x p <;> cases h2 : lt p x <;> simp_all
      simp only [hxp, Bool.false_eq_true, ↓reduceIte]
      rcases htri with hlt | hlt
      · have hc : ∀ y, sameClass lt x y = true → lt p y = false ∧ lt y p = true := fun y hy =>
          ⟨by rw [← lt_congr_right hnt p hy]; exact negTransOrder_asymm hnt hlt,
            by rw [← lt_congr_left hnt p hy]; exact hlt⟩
        have hB1 : B.filter (fun a => sameClass lt x a && !lt p a) = B.filter (sameClass lt x) :=
          filter_class_and_true x _ B fun y hy => by simp [(hc y hy).1]
        have hA1 : A.filter (fun a => sameClass lt x a && lt a p) = A.filter (sameClass lt x) :=
          filter_class_and_true x _ A fun y hy => (hc y hy).2
        have hB2 : B.filter (fun a => sameClass lt x a && lt p a) = [] :=
          filter_class_and_false x _ B fun y hy => (hc y hy).1
        have hA2 : A.filter (fun a => sameClass lt x a && !lt a p) = [] :=
          filter_class_and_false x _ A fun y hy => by simp [(hc y hy).2]
        rw [hB1, hA1, hB2, hA2]
        simp [hxp]
      · have hc : ∀ y, sameClass lt x y = true → lt p y = true ∧ lt y p = false := fun y hy =>
          ⟨by rw [← lt_congr_right hnt p hy]; exact hlt,
            by rw [← lt_congr_left hnt p hy]; exact negTransOrder_asymm hnt hlt⟩
        have hB1 : B.filter (fun a => sameClass lt x a && !lt p a) = [] :=
          filter_class_and_false x _ B fun y hy => by simp [(hc y hy).1]
        have hA1 : A.filter (fun a => sameClass lt x a && lt a p) = [] :=
          filter_class_and_false x _ A fun y hy => (hc y hy).2
        have hB2 : B.filter (fun a => sameClass lt x a && lt p a) = B.filter (sameClass lt x) :=
          filter_class_and_true x _ B fun y hy => (hc y hy).1
        have hA2 : A.filter (fun a => sameClass lt x a && !lt a p) = A.filter (sameClass lt x) :=
          filter_class_and_true x _ A fun y hy => by simp [(hc y hy).2]
        rw [hB1, hA1, hB2, hA2]
        simp [hxp]

end Outcome

/-! ### Total comparators as effectful comparators

A comparator obeying the strict-weak-order contract returns on every pair (`effect_pure_cases`),
so the effectful outcome predicates of such a comparator are the Boolean outcome predicates. -/

section EffectBridge

variable {ε α : Type}

theorem comparisonFalse_pure (p : α → α → Bool) (x y : α) :
    comparisonFalse (pureCompare (ε := ε) p) x y = !p x y := by
  unfold comparisonFalse
  cases h : p x y <;> simp [pureCompare, h]

theorem comparisonTrue_pure (p : α → α → Bool) (x y : α) :
    comparisonTrue (pureCompare (ε := ε) p) x y = p x y := by
  unfold comparisonTrue
  cases h : p x y <;> simp [pureCompare, h]

theorem comparisonTrue_pure_fun (p : α → α → Bool) :
    comparisonTrue (pureCompare (ε := ε) p) = p := by
  funext x y
  exact comparisonTrue_pure p x y

theorem effectStableWrt_pure (p : α → α → Bool) (before after : List α) :
    EffectStableWrt (pureCompare (ε := ε) p) before after ↔ StableWrt p before after := by
  have hclass : ∀ x, (fun y => comparisonFalse (pureCompare (ε := ε) p) x y &&
      comparisonFalse (pureCompare (ε := ε) p) y x) = sameClass p x := by
    intro x
    funext y
    simp only [comparisonFalse_pure, sameClass]
  unfold EffectStableWrt StableWrt
  constructor
  · intro h x
    rw [← hclass x]
    exact h x
  · intro h x
    rw [hclass x]
    exact h x

theorem effectPairwise_pure (p : α → α → Bool) (l : List α) :
    l.Pairwise (fun a b => pureCompare (ε := ε) p b a = .ok false) ↔ SortedPairwise p l := by
  simp only [SortedPairwise, pureCompare, Except.ok.injEq]

theorem effectSortOutcome_pure (p : α → α → Bool) (s : Bool) (before after : List α) :
    EffectSortOutcome (pureCompare (ε := ε) p) s before after ↔ SortOutcome p s before after := by
  unfold EffectSortOutcome SortOutcome
  rw [effectStableWrt_pure, effectPairwise_pure]

theorem effectSortedValues_pure (p : α → α → Bool) :
    ∀ l : List α, EffectSortedValues (pureCompare (ε := ε) p) l ↔ SortedValues p l
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | a :: b :: rest => by
    simp only [EffectSortedValues, SortedValues]
    rw [effectSortedValues_pure p (b :: rest)]
    simp only [pureCompare, Except.ok.injEq]

theorem effectSortpermOrdered_pure (p : α → α → Bool) (values : List α) (indices : List Nat) :
    EffectSortpermOrdered (pureCompare (ε := ε) p) values indices ↔
      SortpermOrdered p values indices := by
  simp only [EffectSortpermOrdered, SortpermOrdered, pureCompare, Except.ok.injEq]

end EffectBridge


/-! ## Swaps, reversal and copies on any storage -/

section Storage2

variable {V α : Type} {S : VectorStorage V α} {E : V → List α}

theorem storageSwap_mid (L : StorageLaws S E) (v : V) (lo hi : Int) (k : Nat)
    (P B1 M B2 Q : List α) (a b : α)
    (hv : E v = P ++ B1 ++ (a :: M ++ [b]) ++ B2 ++ Q)
    (hP : (P.length : Int) + 1 = lo) (hB1 : B1.length = k) (hB2 : B2.length = k)
    (hX : (B1.length + (M.length + 2) + B2.length : Int) = hi - lo + 1) :
    ∃ v', storageSwap S v (lo + Int.ofNat k) (hi - Int.ofNat k) = .ok v' ∧
      E v' = P ++ (B1 ++ [b]) ++ M ++ (a :: B2) ++ Q := by
  have hreadL : S.getindex v (lo + Int.ofNat k) = .ok a :=
    storage_read_mid L (P := P ++ B1) (B := M ++ [b] ++ B2 ++ Q)
      (by rw [hv]; simp [List.append_assoc]) (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [List.length_append, Int.ofNat_eq_natCast]; omega)
  have hreadR : S.getindex v (hi - Int.ofNat k) = .ok b :=
    storage_read_mid L (P := P ++ B1 ++ a :: M) (B := B2 ++ Q)
      (by rw [hv]; simp [List.append_assoc])
      (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [List.length_append, List.length_cons, Int.ofNat_eq_natCast]; omega)
  obtain ⟨v1, hw1, hv1⟩ := storage_write_mid L b (v := v) (i := lo + Int.ofNat k)
    (P := P ++ B1) (B := M ++ [b] ++ B2 ++ Q) (z := a)
    (by rw [hv]; simp [List.append_assoc]) (by simp only [Int.ofNat_eq_natCast]; omega)
    (by simp only [List.length_append, Int.ofNat_eq_natCast]; omega)
  obtain ⟨v2, hw2, hv2⟩ := storage_write_mid L a (v := v1) (i := hi - Int.ofNat k)
    (P := P ++ B1 ++ b :: M) (B := B2 ++ Q) (z := b)
    (by rw [hv1]; simp [List.append_assoc])
    (by simp only [Int.ofNat_eq_natCast]; omega)
    (by simp only [List.length_append, List.length_cons, Int.ofNat_eq_natCast]; omega)
  refine ⟨v2, ?_, ?_⟩
  · unfold storageSwap
    rw [hreadL, hreadR]
    simp only [liftSortJl, Except.mapError, bind, Except.bind, hw1, hw2]
  · rw [hv2]; simp [List.append_assoc]

theorem forIn_storageReverse (L : StorageLaws S E) (lo hi : Int) :
    ∀ (m : Nat) (k : Nat) (v : V) (P B1 M B2 Q : List α),
      2 * (k + m) ≤ B1.length + M.length + B2.length →
      E v = P ++ B1 ++ M ++ B2 ++ Q →
      (P.length : Int) + 1 = lo →
      B1.length = k →
      B2.length = k →
      (B1.length + M.length + B2.length : Int) = hi - lo + 1 →
      ∃ v',
        (do
          let mut values := v
          for offset in (List.range m).map (fun j => k + j) do
            values ← storageSwap S values (lo + Int.ofNat offset) (hi - Int.ofNat offset)
          pure values : SortResult V) = .ok v' ∧
        ∃ A M' B,
          M = A ++ M' ++ B ∧ A.length = m ∧ B.length = m ∧
          E v' = P ++ (B1 ++ B.reverse) ++ M' ++ (A.reverse ++ B2) ++ Q
  | 0, k, v, P, B1, M, B2, Q, _, hv, _, _, _, _ => by
    refine ⟨v, rfl, [], M, [], by simp, rfl, rfl, ?_⟩
    simpa using hv
  | m + 1, k, v, P, B1, M, B2, Q, h2m, hv, hP, hB1, hB2, hX => by
    have hMlen : 2 ≤ M.length := by omega
    obtain ⟨a, M1, rfl⟩ : ∃ a M1, M = a :: M1 := by
      cases M with
      | nil => simp at hMlen
      | cons a M1 => exact ⟨a, M1, rfl⟩
    obtain ⟨M', b, rfl, hM'⟩ := exists_concat_list M1 (M1.length - 1) (by simp at hMlen; omega)
    have hv' : E v = P ++ B1 ++ (a :: M' ++ [b]) ++ B2 ++ Q := by
      rw [hv]; simp [List.append_assoc]
    obtain ⟨v1, hswap, hv1⟩ := storageSwap_mid L v lo hi k P B1 M' B2 Q a b hv' hP hB1 hB2
      (by simp only [List.length_cons, List.length_append, List.length_nil] at hX; omega)
    have hmap : (List.range (m + 1)).map (fun j => k + j) =
        k :: (List.range m).map (fun j => (k + 1) + j) := range_map_shift id m k
    obtain ⟨v', hloop, A, M'', B, hMdecomp, hA, hB, hv'List⟩ :=
      forIn_storageReverse L lo hi m (k + 1) v1 P (B1 ++ [b]) M' (a :: B2) Q
        (by simp only [List.length_append, List.length_cons, List.length_nil] at h2m ⊢; omega)
        hv1 hP (by simp [hB1]) (by simp [hB2])
        (by simp only [List.length_append, List.length_cons, List.length_nil] at hX ⊢; omega)
    refine ⟨v', ?_, a :: A, M'', B ++ [b], ?_, by simp [hA], by simp [hB], ?_⟩
    · rw [hmap]
      simp only [List.forIn_cons, hswap, bind, Except.bind, pure, Except.pure]
      exact hloop
    · rw [hMdecomp]; simp [List.append_assoc]
    · rw [hv'List]; simp [List.append_assoc]

/-- `reverse!(v, lo, hi)` reverses exactly the window `lo:hi`. -/
theorem storageReverse_spec (L : StorageLaws S E) (v : V) (lo hi : Int)
    (P X Q : List α) (hv : E v = P ++ X ++ Q)
    (hP : (P.length : Int) + 1 = lo) (hX : (X.length : Int) = hi - lo + 1) :
    ∃ v', storageReverse S v lo hi = .ok v' ∧ E v' = P ++ X.reverse ++ Q := by
  unfold storageReverse
  have hdiv : (hi - lo + 1).toNat / 2 = X.length / 2 := by omega
  rw [hdiv]
  have hmapId : List.range (X.length / 2) =
      (List.range (X.length / 2)).map (fun j => 0 + j) := by simp
  rw [hmapId]
  obtain ⟨v', hloop, A, M', B, hXdecomp, hA, hB, hv'List⟩ :=
    forIn_storageReverse L lo hi (X.length / 2) 0 v P [] X [] Q
      (by simp; omega) (by simpa using hv) hP rfl rfl (by simpa using hX)
  refine ⟨v', hloop, ?_⟩
  have hMlen : M'.length ≤ 1 := by
    have := congrArg List.length hXdecomp
    simp only [List.length_append, hA, hB] at this
    omega
  have hMrev : M'.reverse = M' := by
    match M', hMlen with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: _, h => simp at h
  rw [hv'List, hXdecomp]
  simp [hMrev, List.append_assoc]

theorem forIn_storageCopy (L : StorageLaws S E) (source : Array α) (first sourceFirst : Int) :
    ∀ (m k : Nat) (v : V) (P R Q SP SD SR SQ : List α),
      E v = P ++ SD ++ R ++ Q → source.toList = SP ++ SD ++ SR ++ SQ →
      (P.length : Int) + 1 = first → (SP.length : Int) + 1 = sourceFirst →
      SD.length = k → R.length = m → SR.length = m →
      ∃ v',
        (forIn ((List.range m).map (fun j => k + j)) v fun offset d => do
          let value ← liftSortJl (arrayRead source (sourceFirst + Int.ofNat offset))
          let d ← liftSortJl (S.setindex d (first + Int.ofNat offset) value)
          pure (ForInStep.yield d)) = .ok v' ∧
        E v' = P ++ SD ++ SR ++ Q
  | 0, k, v, P, R, Q, SP, SD, SR, SQ, hv, _, _, _, _, hR, hSR => by
    have hR0 : R = [] := List.eq_nil_of_length_eq_zero hR
    have hSR0 : SR = [] := List.eq_nil_of_length_eq_zero hSR
    subst hR0 hSR0
    exact ⟨v, rfl, by simpa using hv⟩
  | m + 1, k, v, P, R, Q, SP, SD, SR, SQ, hv, hs, hP, hSP, hSD, hR, hSR => by
    obtain ⟨r, R', rfl⟩ : ∃ r R', R = r :: R' := by
      cases R with
      | nil => simp at hR
      | cons r R' => exact ⟨r, R', rfl⟩
    obtain ⟨s, SR', rfl⟩ : ∃ s SR', SR = s :: SR' := by
      cases SR with
      | nil => simp at hSR
      | cons s SR' => exact ⟨s, SR', rfl⟩
    have hmap : (List.range (m + 1)).map (fun j => k + j) =
        k :: (List.range m).map (fun j => (k + 1) + j) := range_map_shift id m k
    have hread : arrayRead source (sourceFirst + Int.ofNat k) = .ok s :=
      storage_read_mid arrayStorage_laws (v := source) (P := SP ++ SD) (B := SR' ++ SQ)
        (by rw [hs]; simp [List.append_assoc]) (by simp only [Int.ofNat_eq_natCast]; omega)
        (by simp only [List.length_append, Int.ofNat_eq_natCast]; omega)
    obtain ⟨v1, hw, hv1⟩ := storage_write_mid L s (v := v) (i := first + Int.ofNat k)
      (P := P ++ SD) (B := R' ++ Q) (z := r)
      (by rw [hv]; simp [List.append_assoc]) (by simp only [Int.ofNat_eq_natCast]; omega)
      (by simp only [List.length_append, Int.ofNat_eq_natCast]; omega)
    obtain ⟨v', hloop, hv'⟩ :=
      forIn_storageCopy L source first sourceFirst m (k + 1) v1 P R' Q SP (SD ++ [s]) SR' SQ
        (by rw [hv1]; simp [List.append_assoc]) (by rw [hs]; simp [List.append_assoc])
        hP hSP (by simp [hSD]) (by simp at hR; omega) (by simp at hSR; omega)
    refine ⟨v', ?_, ?_⟩
    · rw [hmap]
      simp only [List.forIn_cons, hread, hw, liftSortJl, Except.mapError, bind, Except.bind, pure, Except.pure]
      exact hloop
    · rw [hv']; simp [List.append_assoc]

/-- `copyto!(v, first, t, sourceFirst, n)` copies `n` scratch elements into the window of `v`
starting at `first` and leaves the rest of `v` unchanged. -/
theorem storageCopyFromArray_spec (L : StorageLaws S E) (v : V) (first : Int) (source : Array α)
    (sourceFirst : Int) (P R Q SP SR SQ : List α)
    (hv : E v = P ++ R ++ Q) (hs : source.toList = SP ++ SR ++ SQ)
    (hP : (P.length : Int) + 1 = first) (hSP : (SP.length : Int) + 1 = sourceFirst)
    (hR : R.length = SR.length) :
    ∃ v', storageCopyFromArray S v first source sourceFirst SR.length = .ok v' ∧
      E v' = P ++ SR ++ Q := by
  unfold storageCopyFromArray
  have hmapId : List.range SR.length = (List.range SR.length).map (fun j => 0 + j) := by simp
  rw [hmapId]
  obtain ⟨v', hloop, hv'⟩ := forIn_storageCopy L source first sourceFirst SR.length 0 v P R Q
    SP [] SR SQ (by simpa using hv) (by simpa using hs) hP hSP rfl hR rfl
  refine ⟨v', ?_, by simpa using hv'⟩
  dsimp only
  rw [hloop]
  rfl

end Storage2

/-! ## `partition!` into scratch space -/

section Partition

variable {Target Source PivotDest α : Type}

/-- The `Int` index arithmetic and direct comparison that both `partition!` instances use. -/
structure IntPartitionIndices
    (ops : ScratchPartitionOps Target Source PivotDest Int α (α → α → SortResult Bool) JuliaLean.base.sort.SortException) : Prop where
  lessValue : ∀ o, ops.lessValue o = o
  lessIndex : ∀ a b, ops.lessIndex a b = decide (a < b)
  nextIndex : ∀ a, ops.nextIndex a = a + 1
  subtractIndex : ∀ a b, ops.subtractIndex a b = a - b
  addBoolToIndex : ∀ a yes, ops.addBoolToIndex a yes = a + if yes then 1 else 0
  addPivotOffset : ∀ a b, ops.addPivotOffset a b = a + b
  distance : ∀ a b, ops.distance a b = (b - a).toNat

/-- Writes into the partition target replace exactly one element. -/
def TargetWriteLaw
    (ops : ScratchPartitionOps Target Source PivotDest Int α (α → α → SortResult Bool) JuliaLean.base.sort.SortException)
    (ET : Target → List α) : Prop :=
  ∀ tg i x, 1 ≤ i → i ≤ ((ET tg).length : Int) →
    ∃ tg', ops.writeTarget tg i x = .ok tg' ∧ ET tg' = (ET tg).set (i - 1).toNat x

theorem targetWrite_mid
    {ops : ScratchPartitionOps Target Source PivotDest Int α (α → α → SortResult Bool) JuliaLean.base.sort.SortException}
    {ET : Target → List α} (hW : TargetWriteLaw ops ET) {tg : Target} {P Q : List α} {z : α}
    {i : Int} (x : α) (ht : ET tg = P ++ z :: Q) (hi : i = (P.length : Int) + 1) :
    ∃ tg', ops.writeTarget tg i x = .ok tg' ∧ ET tg' = P ++ x :: Q := by
  obtain ⟨tg', hw, ht'⟩ := hW tg i x (by omega)
    (by rw [ht]; simp only [List.length_append, List.length_cons]; omega)
  refine ⟨tg', hw, ?_⟩
  rw [ht', ht, show (i - 1).toNat = P.length by omega,
    List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self, List.set_cons_zero]

theorem filter_concat_single (f : α → Bool) (D : List α) (x : α) :
    (D ++ [x]).filter f = D.filter f ++ (if f x then [x] else []) := by
  rw [List.filter_append]; by_cases h : f x = true <;> simp [h]

theorem partitionBefore_spec
    (ops : ScratchPartitionOps Target Source PivotDest Int α
      (α → α → SortResult Bool) SortException)
    (hI : IntPartitionIndices ops) (ET : Target → List α) (hW : TargetWriteLaw ops ET)
    (source : Source) (order : α → α → Bool) (reverse : Bool) (p : α)
    (lo0 hi o0 pivotIndex : Int) (W B pre post : List α)
    (hread : ∀ (k : Nat) (x : α), W[k]? = some x → ops.readSource source (lo0 + k) = .ok x)
    (hB : B = W.take (pivotIndex - lo0).toNat) (hpi : lo0 ≤ pivotIndex) (hpihi : pivotIndex ≤ hi)
    (hn : (W.length : Int) = hi - lo0 + 1) (hpre : (pre.length : Int) + 1 = lo0 - o0)
    (gR : α → Bool) (hgR : gR = fun x => if reverse then !order x p else order p x) :
    ∀ (X D M : List α) (target : Target) (fuel : Nat),
      D ++ X = B → X.length < fuel →
      ET target = pre ++ ((D.filter (fun x => !gR x)) ++ M ++ (D.filter gR).reverse) ++ post →
      (D.filter (fun x => !gR x)).length + M.length + (D.filter gR).length = W.length →
      ∃ target' M',
        partitionScratchBeforeLoop ops pivotIndex hi (pureCompare order) source reverse p fuel target
          (lo0 + D.length) (o0 + (D.filter gR).length) =
          .ok (target', pivotIndex, o0 + (B.filter gR).length) ∧
        ET target' = pre ++ ((B.filter (fun x => !gR x)) ++ M' ++ (B.filter gR).reverse) ++ post ∧
        (B.filter (fun x => !gR x)).length + M'.length + (B.filter gR).length = W.length := by
  have hBlen : (B.length : Int) = pivotIndex - lo0 := by
    rw [hB, List.length_take]; omega
  intro X
  induction X with
  | nil =>
    intro D M target fuel hD hfuel ht hlen
    simp only [List.append_nil] at hD
    subst hD
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    refine ⟨target, M, ?_, ht, hlen⟩
    have hlo : lo0 + (D.length : Int) = pivotIndex := by omega
    unfold partitionScratchBeforeLoop
    rw [hI.lessIndex, hlo]
    simp; rfl
  | cons x X ih =>
    intro D M target fuel hD hfuel ht hlen
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hDlen : (D.length : Int) < pivotIndex - lo0 := by
      have := congrArg List.length hD
      simp only [List.length_append, List.length_cons] at this; omega
    have hsplit : (D.filter (fun x => !gR x)).length + (D.filter gR).length = D.length := by
      have := (List.filter_append_perm gR D).length_eq
      simp only [List.length_append] at this
      omega
    have hread' : ops.readSource source (lo0 + D.length) = .ok x := by
      apply hread
      rw [← List.getElem?_take_of_lt (j := (pivotIndex - lo0).toNat) (by omega), ← hB, ← hD,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    have hMpos : 0 < M.length := by
      have := congrArg List.length hD
      simp only [List.length_append, List.length_cons] at this
      omega
    unfold partitionScratchBeforeLoop
    rw [hI.lessIndex, if_pos (by simp; omega)]
    simp only [hread', bind, Except.bind, pure, Except.pure, hI.lessValue, pureCompare,
      hI.subtractIndex, hI.addBoolToIndex, hI.nextIndex]
    have hgx : (if reverse then !order x p else order p x) = gR x := by rw [hgR]
    cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] at hgx ⊢ <;> rw [hgx]
    all_goals
      cases hg : gR x
      · obtain ⟨m, M', rfl⟩ : ∃ m M', M = m :: M' := by
          cases M with
          | nil => simp at hMpos
          | cons m M' => exact ⟨m, M', rfl⟩
        obtain ⟨tg', hw, ht'⟩ := targetWrite_mid hW
          (i := lo0 + D.length - (o0 + (D.filter gR).length))
          (P := pre ++ D.filter (fun x => !gR x)) (Q := M' ++ (D.filter gR).reverse ++ post)
          (z := m) x (by rw [ht]; simp [List.append_assoc])
          (by simp only [List.length_append]; omega)
        simp only [Bool.false_eq_true, ↓reduceIte, hw]
        have hD' : (D ++ [x]) ++ X = B := by rw [← hD]; simp
        obtain ⟨tg'', M'', hrun, ht'', hlen''⟩ := ih (D ++ [x]) M' tg' f hD'
          (by simp at hfuel; omega)
          (by rw [ht', filter_concat_single, filter_concat_single]; simp [hg, List.append_assoc])
          (by rw [filter_concat_single, filter_concat_single]; simp [hg] at hlen ⊢; omega)
        refine ⟨tg'', M'', ?_, ht'', hlen''⟩
        rw [← hrun, filter_concat_single]
        simp [hg]
        congr 1; omega
      · obtain ⟨M', m, rfl, -⟩ := exists_concat_list M (M.length - 1) (by omega)
        obtain ⟨tg', hw, ht'⟩ := targetWrite_mid hW (i := hi - (o0 + (D.filter gR).length))
          (P := pre ++ D.filter (fun x => !gR x) ++ M') (Q := (D.filter gR).reverse ++ post)
          (z := m) x (by rw [ht]; simp [List.append_assoc])
          (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢; omega)
        simp only [↓reduceIte, hw]
        have hD' : (D ++ [x]) ++ X = B := by rw [← hD]; simp
        obtain ⟨tg'', M'', hrun, ht'', hlen''⟩ := ih (D ++ [x]) M' tg' f hD'
          (by simp at hfuel; omega)
          (by rw [ht', filter_concat_single, filter_concat_single]; simp [hg, List.append_assoc])
          (by rw [filter_concat_single, filter_concat_single]
              simp only [List.length_append, List.length_cons, List.length_nil] at hlen
              simp [hg]; omega)
        refine ⟨tg'', M'', ?_, ht'', hlen''⟩
        rw [← hrun, filter_concat_single]
        simp [hg]
        congr 1 <;> omega

theorem partitionAfter_spec
    (ops : ScratchPartitionOps Target Source PivotDest Int α
      (α → α → SortResult Bool) SortException)
    (hI : IntPartitionIndices ops) (ET : Target → List α) (hW : TargetWriteLaw ops ET)
    (source : Source) (order : α → α → Bool) (reverse : Bool) (p : α)
    (lo0 hi o0 pivotIndex : Int) (W A pre post L0 R0 : List α)
    (hread : ∀ (k : Nat) (x : α), W[k]? = some x → ops.readSource source (lo0 + k) = .ok x)
    (hA : A = W.drop ((pivotIndex - lo0).toNat + 1)) (hpi : lo0 ≤ pivotIndex)
    (hpihi : pivotIndex ≤ hi)
    (hn : (W.length : Int) = hi - lo0 + 1) (hpre : (pre.length : Int) + 1 = lo0 - o0)
    (hLR : ((L0.length + R0.length : Nat) : Int) = pivotIndex - lo0)
    (gA : α → Bool) (hgA : gA = fun x => if reverse then order p x else !order x p) :
    ∀ (X D M : List α) (target : Target) (fuel : Nat),
      D ++ X = A → X.length < fuel →
      ET target = pre ++ ((L0 ++ D.filter (fun x => !gA x)) ++ M ++
        (R0 ++ D.filter gA).reverse) ++ post →
      (L0 ++ D.filter (fun x => !gA x)).length + M.length + (R0 ++ D.filter gA).length =
        W.length →
      ∃ target' M',
        partitionScratchAfterLoop ops hi (pureCompare order) source reverse p fuel target
          (pivotIndex + D.length) (o0 + (R0 ++ D.filter gA).length) =
          .ok (target', hi, o0 + (R0 ++ A.filter gA).length) ∧
        ET target' = pre ++ ((L0 ++ A.filter (fun x => !gA x)) ++ M' ++
          (R0 ++ A.filter gA).reverse) ++ post ∧
        (L0 ++ A.filter (fun x => !gA x)).length + M'.length + (R0 ++ A.filter gA).length =
          W.length := by
  have hAlen : (A.length : Int) = hi - pivotIndex := by
    rw [hA, List.length_drop]; omega
  intro X
  induction X with
  | nil =>
    intro D M target fuel hD hfuel ht hlen
    simp only [List.append_nil] at hD
    subst hD
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    refine ⟨target, M, ?_, ht, hlen⟩
    have hlo : pivotIndex + (D.length : Int) = hi := by omega
    unfold partitionScratchAfterLoop
    rw [hI.lessIndex, hlo]
    simp; rfl
  | cons x X ih =>
    intro D M target fuel hD hfuel ht hlen
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hDlen : (D.length : Int) < hi - pivotIndex := by
      have := congrArg List.length hD
      simp only [List.length_append, List.length_cons] at this; omega
    have hsplit : (D.filter (fun x => !gA x)).length + (D.filter gA).length = D.length := by
      have := (List.filter_append_perm gA D).length_eq
      simp only [List.length_append] at this
      omega
    have hread' : ops.readSource source (pivotIndex + D.length + 1) = .ok x := by
      have hidx : pivotIndex + (D.length : Int) + 1 =
          lo0 + (((pivotIndex - lo0).toNat + 1 + D.length : Nat) : Int) := by omega
      rw [hidx]
      apply hread
      rw [← List.getElem?_drop, ← hA, ← hD,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
    have hMpos : 0 < M.length := by
      have := congrArg List.length hD
      simp only [List.length_append, List.length_cons] at this
      simp only [List.length_append] at hlen
      omega
    unfold partitionScratchAfterLoop
    rw [hI.lessIndex, if_pos (by simp; omega)]
    simp only [hI.nextIndex, hread', bind, Except.bind, pure, Except.pure, hI.lessValue,
      pureCompare, hI.subtractIndex, hI.addBoolToIndex]
    have hgx : (if reverse then order p x else !order x p) = gA x := by rw [hgA]
    cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] at hgx ⊢ <;> rw [hgx]
    all_goals
      cases hg : gA x
      · obtain ⟨m, M', rfl⟩ : ∃ m M', M = m :: M' := by
          cases M with
          | nil => simp at hMpos
          | cons m M' => exact ⟨m, M', rfl⟩
        obtain ⟨tg', hw, ht'⟩ := targetWrite_mid hW
          (i := pivotIndex + D.length - (o0 + (R0 ++ D.filter gA).length))
          (P := pre ++ (L0 ++ D.filter (fun x => !gA x)))
          (Q := M' ++ (R0 ++ D.filter gA).reverse ++ post)
          (z := m) x (by rw [ht]; simp [List.append_assoc])
          (by simp only [List.length_append]; omega)
        simp only [Bool.false_eq_true, ↓reduceIte, hw]
        have hD' : (D ++ [x]) ++ X = A := by rw [← hD]; simp
        obtain ⟨tg'', M'', hrun, ht'', hlen''⟩ := ih (D ++ [x]) M' tg' f hD'
          (by simp at hfuel; omega)
          (by rw [ht', filter_concat_single, filter_concat_single]; simp [hg, List.append_assoc])
          (by rw [filter_concat_single, filter_concat_single]; simp [hg] at hlen ⊢; omega)
        refine ⟨tg'', M'', ?_, ht'', hlen''⟩
        rw [← hrun, filter_concat_single]
        simp [hg]
        congr 1; omega
      · obtain ⟨M', m, rfl, -⟩ := exists_concat_list M (M.length - 1) (by omega)
        obtain ⟨tg', hw, ht'⟩ := targetWrite_mid hW
          (i := hi - (o0 + (R0 ++ D.filter gA).length))
          (P := pre ++ (L0 ++ D.filter (fun x => !gA x)) ++ M')
          (Q := (R0 ++ D.filter gA).reverse ++ post)
          (z := m) x (by rw [ht]; simp [List.append_assoc])
          (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢; omega)
        simp only [↓reduceIte, hw]
        have hD' : (D ++ [x]) ++ X = A := by rw [← hD]; simp
        obtain ⟨tg'', M'', hrun, ht'', hlen''⟩ := ih (D ++ [x]) M' tg' f hD'
          (by simp at hfuel; omega)
          (by rw [ht', filter_concat_single, filter_concat_single]; simp [hg, List.append_assoc])
          (by rw [filter_concat_single, filter_concat_single]
              simp only [List.length_append, List.length_cons, List.length_nil] at hlen
              simp [hg]; omega)
        refine ⟨tg'', M'', ?_, ht'', hlen''⟩
        rw [← hrun, filter_concat_single]
        simp [hg]
        congr 1 <;> omega

/-- Elements before the pivot that `partition!` sends above it. -/
def goesRightBefore (order : α → α → Bool) (reverse : Bool) (p x : α) : Bool :=
  if reverse then !order x p else order p x

/-- Elements after the pivot that `partition!` sends above it. -/
def goesRightAfter (order : α → α → Bool) (reverse : Bool) (p x : α) : Bool :=
  if reverse then order p x else !order x p

theorem partitionScratch_core
    (ops : ScratchPartitionOps Target Source PivotDest Int α
      (α → α → SortResult Bool) SortException)
    (hI : IntPartitionIndices ops) (ET : Target → List α) (hW : TargetWriteLaw ops ET)
    (target : Target) (lo hi o0 pio : Int) (order : α → α → Bool) (source : Source)
    (reverse : Bool) (pivotDest : PivotDest) (W pre M0 post : List α)
    (hread : ∀ (k : Nat) (x : α), W[k]? = some x → ops.readSource source (lo + k) = .ok x)
    (hn : (W.length : Int) = hi - lo + 1) (pi : Int) (hpiv : ops.pivotIndex lo hi = .ok pi)
    (hpilo : lo ≤ pi) (hpihi : pi ≤ hi)
    (ht : ET target = pre ++ M0 ++ post) (hM0 : M0.length = W.length)
    (hpre : (pre.length : Int) + 1 = lo - o0) :
    ∃ B p A target' m,
      W = B ++ p :: A ∧ (B.length : Int) = pi - lo ∧
      ET target' = pre ++ ((B.filter (fun x => !goesRightBefore order reverse p x) ++
        A.filter (fun x => !goesRightAfter order reverse p x)) ++ [m] ++
        (B.filter (goesRightBefore order reverse p) ++
          A.filter (goesRightAfter order reverse p)).reverse) ++ post ∧
      ∀ res, ops.writePivot target' pivotDest
          (hi - (o0 + (B.filter (goesRightBefore order reverse p) ++
            A.filter (goesRightAfter order reverse p)).length) + pio) p = .ok res →
        partitionScratch ops target lo hi o0 (pureCompare order) source reverse pivotDest pio =
          .ok (res.1, res.2, hi - (o0 + (B.filter (goesRightBefore order reverse p) ++
            A.filter (goesRightAfter order reverse p)).length) + pio) := by
  have hk : (pi - lo).toNat < W.length := by omega
  let B := W.take (pi - lo).toNat
  let p := W[(pi - lo).toNat]
  let A := W.drop ((pi - lo).toNat + 1)
  have hW' : W = B ++ p :: A := by
    simp only [B, p, A]
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hBlen : (B.length : Int) = pi - lo := by
    simp only [B, List.length_take]; omega
  have hpread : ops.readSource source pi = .ok p := by
    have := hread (pi - lo).toNat p (List.getElem?_eq_getElem hk)
    rwa [show lo + ((pi - lo).toNat : Int) = pi by omega] at this
  obtain ⟨t1, M1, hrun1, ht1, hlen1⟩ :=
    partitionBefore_spec ops hI ET hW source order reverse p lo hi o0 pi W B pre post hread rfl
      hpilo hpihi hn hpre (goesRightBefore order reverse p) rfl B [] M0 target
      ((pi - lo).toNat + 1) (by simp) (by simp only [B, List.length_take]; omega)
      (by simpa using ht) (by simpa using hM0)
  obtain ⟨t2, M2, hrun2, ht2, hlen2⟩ :=
    partitionAfter_spec ops hI ET hW source order reverse p lo hi o0 pi W A pre post
      (B.filter (fun x => !goesRightBefore order reverse p x))
      (B.filter (goesRightBefore order reverse p)) hread rfl hpilo hpihi hn hpre
      (by have := (List.filter_append_perm (goesRightBefore order reverse p) B).length_eq
          simp only [List.length_append] at this; omega)
      (goesRightAfter order reverse p) rfl A [] M1 t1 ((hi - pi).toNat + 1) (by simp)
      (by simp only [A, List.length_drop]; omega)
      (by simpa using ht1) (by simpa using hlen1)
  have hM2 : M2.length = 1 := by
    have h1 := (List.filter_append_perm (goesRightBefore order reverse p) B).length_eq
    have h2 := (List.filter_append_perm (goesRightAfter order reverse p) A).length_eq
    have h3 := congrArg List.length hW'
    simp only [List.length_append, List.length_cons] at h1 h2 h3 hlen2
    omega
  obtain ⟨m, rfl⟩ : ∃ m, M2 = [m] := by
    match M2, hM2 with
    | [m], _ => exact ⟨m, rfl⟩
  refine ⟨B, p, A, t2, m, hW', hBlen, by simpa [List.append_assoc] using ht2, ?_⟩
  intro res hres
  have hrun1' : partitionScratchBeforeLoop ops pi hi (pureCompare order) source reverse p
      ((pi - lo).toNat + 1) target lo o0 =
      .ok (t1, pi, o0 + (B.filter (goesRightBefore order reverse p)).length) := by
    simpa using hrun1
  have hrun2' : partitionScratchAfterLoop ops hi (pureCompare order) source reverse p
      ((hi - pi).toNat + 1) t1
      pi (o0 + (B.filter (goesRightBefore order reverse p)).length) =
      .ok (t2, hi, o0 + (B.filter (goesRightBefore order reverse p) ++
        A.filter (goesRightAfter order reverse p)).length) := by
    simpa using hrun2
  unfold partitionScratch
  simp only [hpiv, hpread, bind, Except.bind, hI.distance, hrun1', hrun2', hI.addPivotOffset,
    hI.subtractIndex, hres]
  rfl

end Partition

/-! ## ScratchQuickSort -/

section ScratchQuick

variable {V α : Type} {S : VectorStorage V α} {E : V → List α}

theorem storage_read_window (L : StorageLaws S E) {v : V} {P W Q : List α}
    (hv : E v = P ++ W ++ Q) (lo : Int) (hP : (P.length : Int) + 1 = lo) :
    ∀ (k : Nat) (x : α), W[k]? = some x → S.getindex v (lo + k) = .ok x := by
  intro k x hk
  have hklt : k < W.length := (List.getElem?_eq_some_iff.1 hk).1
  rw [L.getindex_eq]
  unfold arrayRead
  rw [if_pos (by omega), List.getElem?_toArray, show (lo + (k : Int) - 1).toNat = P.length + k by omega,
    hv, List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hklt, hk]

theorem vectorTargetPartition_indices (pivot : Int → Int → Int) :
    IntPartitionIndices (vectorTargetPartitionOps S pivot) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩

theorem scratchTargetPartition_indices (pivot : Int → Int → Int) :
    IntPartitionIndices (scratchTargetPartitionOps S pivot) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩

/-- `partition!(v, lo+offset, hi+offset, offset, o, t, rev, v, 0)`: the window's elements move
from scratch into the vector around the pivot, which lands at its final index. -/
theorem vectorTargetPartition_spec (L : StorageLaws S E) (pivot : Int → Int → Int)
    (hpivot : ∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b)
    (v : V) (t : Array α) (lo hi offset : Int) (order : α → α → Bool) (reverse : Bool)
    (P Wv Q TP Wt TQ : List α) (hv : E v = P ++ Wv ++ Q) (ht : t.toList = TP ++ Wt ++ TQ)
    (hP : (P.length : Int) + 1 = lo) (hTP : (TP.length : Int) + 1 = lo + offset)
    (hWv : Wv.length = Wt.length) (hn : (Wt.length : Int) = hi - lo + 1) (hlohi : lo ≤ hi) :
    ∃ B p A v',
      Wt = B ++ p :: A ∧
      E v' = P ++ ((B.filter (fun x => !goesRightBefore order reverse p x) ++
        A.filter (fun x => !goesRightAfter order reverse p x)) ++ [p] ++
        (B.filter (goesRightBefore order reverse p) ++
          A.filter (goesRightAfter order reverse p)).reverse) ++ Q ∧
      partitionScratch (vectorTargetPartitionOps S pivot) v (lo + offset) (hi + offset) offset
        (pureCompare order) t reverse v 0 =
        .ok (v', v', lo + (B.filter (fun x => !goesRightBefore order reverse p x) ++
          A.filter (fun x => !goesRightAfter order reverse p x)).length) := by
  have hW : TargetWriteLaw (vectorTargetPartitionOps S pivot) E := by
    intro tg i x h1 h2
    obtain ⟨tg', hw, hE⟩ := L.setindex_ok tg i x h1 h2
    exact ⟨tg', by simp [vectorTargetPartitionOps, hw], hE⟩
  have hread : ∀ (k : Nat) (x : α), Wt[k]? = some x →
      (vectorTargetPartitionOps S pivot).readSource t (lo + offset + k) = .ok x := by
    intro k x hk
    have hr := storage_read_window arrayStorage_laws ht (lo + offset) hTP k x hk
    change arrayRead t (lo + offset + k) = .ok x at hr
    change liftSortJl (arrayRead t (lo + offset + k)) = .ok x
    rw [hr, liftSortJl_ok]
  obtain ⟨hp1, hp2⟩ := hpivot (lo + offset) (hi + offset) (by omega)
  obtain ⟨B, p, A, t2, m, hWt, hBlen, ht2, hres⟩ :=
    partitionScratch_core (vectorTargetPartitionOps S pivot) (vectorTargetPartition_indices pivot)
      E hW v (lo + offset) (hi + offset) offset 0 order t reverse v Wt P Wv Q hread (by omega)
      (pivot (lo + offset) (hi + offset)) rfl hp1 hp2 hv hWv (by omega)
  have hlens := congrArg List.length hWt
  have h1 := (List.filter_append_perm (goesRightBefore order reverse p) B).length_eq
  have h2 := (List.filter_append_perm (goesRightAfter order reverse p) A).length_eq
  simp only [List.length_append, List.length_cons] at hlens h1 h2
  obtain ⟨v', hw, hv'⟩ := storage_write_mid L p (v := t2)
    (i := hi + offset - (offset + (B.filter (goesRightBefore order reverse p) ++
      A.filter (goesRightAfter order reverse p)).length) + 0)
    (P := P ++ (B.filter (fun x => !goesRightBefore order reverse p x) ++
      A.filter (fun x => !goesRightAfter order reverse p x)))
    (B := (B.filter (goesRightBefore order reverse p) ++
      A.filter (goesRightAfter order reverse p)).reverse ++ Q) (z := m)
    (by rw [ht2]; simp [List.append_assoc]) (by simp only [List.length_append]; omega)
    (by simp only [List.length_append]; omega)
  refine ⟨B, p, A, v', hWt, by rw [hv']; simp [List.append_assoc], ?_⟩
  have hrun := hres (v', v') (by
    show (do let updated ← liftSortJl (S.setindex t2 _ p); pure (updated, updated)) = _
    rw [hw]; rfl)
  rw [hrun]
  have hjeq : hi + offset - (offset + ((B.filter (goesRightBefore order reverse p) ++
      A.filter (goesRightAfter order reverse p)).length : Int)) + 0 =
      lo + ((B.filter (fun x => !goesRightBefore order reverse p x) ++
        A.filter (fun x => !goesRightAfter order reverse p x)).length : Int) := by
    simp only [List.length_append, Int.natCast_add]; omega
  rw [hjeq]

/-- `partition!(t, lo, hi, -offset, o, v, rev, v, -offset)`: the window's elements move from the
vector into scratch around the pivot, which is written into the vector at its final index. -/
theorem scratchTargetPartition_spec (L : StorageLaws S E) (pivot : Int → Int → Int)
    (hpivot : ∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b)
    (v : V) (t : Array α) (lo hi offset : Int) (order : α → α → Bool) (reverse : Bool)
    (P Wv Q TP Wt TQ : List α) (hv : E v = P ++ Wv ++ Q) (ht : t.toList = TP ++ Wt ++ TQ)
    (hP : (P.length : Int) + 1 = lo) (hTP : (TP.length : Int) + 1 = lo + offset)
    (hWv : Wv.length = Wt.length) (hn : (Wv.length : Int) = hi - lo + 1) (hlohi : lo ≤ hi) :
    ∃ B p A t' v' m,
      Wv = B ++ p :: A ∧
      t'.toList = TP ++ ((B.filter (fun x => !goesRightBefore order reverse p x) ++
        A.filter (fun x => !goesRightAfter order reverse p x)) ++ [m] ++
        (B.filter (goesRightBefore order reverse p) ++
          A.filter (goesRightAfter order reverse p)).reverse) ++ TQ ∧
      E v' = P ++ Wv.set (B.filter (fun x => !goesRightBefore order reverse p x) ++
        A.filter (fun x => !goesRightAfter order reverse p x)).length p ++ Q ∧
      partitionScratch (scratchTargetPartitionOps S pivot) t lo hi (-offset) (pureCompare order) v
        reverse v
        (-offset) =
        .ok (t', v', lo + (B.filter (fun x => !goesRightBefore order reverse p x) ++
          A.filter (fun x => !goesRightAfter order reverse p x)).length) := by
  have hW : TargetWriteLaw (scratchTargetPartitionOps S pivot) Array.toList := by
    intro tg i x h1 h2
    obtain ⟨tg', hw, hE⟩ := arrayStorage_laws.setindex_ok tg i x h1 h2
    refine ⟨tg', ?_, hE⟩
    change liftSortJl (arrayWrite tg i x) = .ok tg'
    change arrayWrite tg i x = .ok tg' at hw
    rw [hw, liftSortJl_ok]
  have hread : ∀ (k : Nat) (x : α), Wv[k]? = some x →
      (scratchTargetPartitionOps S pivot).readSource v (lo + k) = .ok x := by
    intro k x hk
    have hr := storage_read_window L hv lo hP k x hk
    simpa [scratchTargetPartitionOps, hr]
  obtain ⟨hp1, hp2⟩ := hpivot lo hi hlohi
  obtain ⟨B, p, A, t2, m, hWv', hBlen, ht2, hres⟩ :=
    partitionScratch_core (scratchTargetPartitionOps S pivot)
      (scratchTargetPartition_indices pivot) Array.toList hW t lo hi (-offset) (-offset) order v
      reverse v Wv TP Wt TQ hread hn (pivot lo hi) rfl hp1 hp2 ht hWv.symm (by omega)
  have hlens := congrArg List.length hWv'
  have h1 := (List.filter_append_perm (goesRightBefore order reverse p) B).length_eq
  have h2 := (List.filter_append_perm (goesRightAfter order reverse p) A).length_eq
  simp only [List.length_append, List.length_cons] at hlens h1 h2
  have hj : (B.filter (fun x => !goesRightBefore order reverse p x) ++
      A.filter (fun x => !goesRightAfter order reverse p x)).length < Wv.length := by
    simp only [List.length_append]; omega
  obtain ⟨v', hw, hv'⟩ := L.setindex_ok v
    (hi - (-offset + (B.filter (goesRightBefore order reverse p) ++
      A.filter (goesRightAfter order reverse p)).length) + -offset) p
    (by simp only [List.length_append]; omega)
    (by rw [hv]; simp only [List.length_append] at hj ⊢; omega)
  refine ⟨B, p, A, t2, v', m, hWv', by simpa [List.append_assoc] using ht2, ?_, ?_⟩
  · rw [hv', hv]
    have hidx : (hi - (-offset + ((B.filter (goesRightBefore order reverse p) ++
        A.filter (goesRightAfter order reverse p)).length : Int)) + -offset - 1).toNat =
        P.length + (B.filter (fun x => !goesRightBefore order reverse p x) ++
          A.filter (fun x => !goesRightAfter order reverse p x)).length := by
      simp only [List.length_append] at hj ⊢; omega
    rw [hidx, List.append_assoc, List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left,
      List.set_append_left _ _ hj, List.append_assoc]
  · have hrun := hres (t2, v') (by
      show (do let updated ← liftSortJl (S.setindex v _ p); pure (t2, updated)) = _
      rw [hw]; rfl)
    rw [hrun]
    have hjeq : hi - (-offset + ((B.filter (goesRightBefore order reverse p) ++
        A.filter (goesRightAfter order reverse p)).length : Int)) + -offset =
        lo + ((B.filter (fun x => !goesRightBefore order reverse p x) ++
          A.filter (fun x => !goesRightAfter order reverse p x)).length : Int) := by
      simp only [List.length_append, Int.natCast_add]; omega
    rw [hjeq]

/-- Elements of a stored window that `partition!` keeps below the pivot, in stored order. -/
def storedLeft (order : α → α → Bool) (reverse : Bool) (p : α) (B A : List α) : List α :=
  B.filter (fun x => !goesRightBefore order reverse p x) ++
    A.filter (fun x => !goesRightAfter order reverse p x)

/-- Elements of a stored window that `partition!` sends above the pivot, in stored order. -/
def storedRight (order : α → α → Bool) (reverse : Bool) (p : α) (B A : List α) : List α :=
  B.filter (goesRightBefore order reverse p) ++ A.filter (goesRightAfter order reverse p)

theorem stored_lengths (order : α → α → Bool) (reverse : Bool) (p : α) (B A : List α) :
    (storedLeft order reverse p B A).length + (storedRight order reverse p B A).length =
      B.length + A.length := by
  have h1 := (List.filter_append_perm (goesRightBefore order reverse p) B).length_eq
  have h2 := (List.filter_append_perm (goesRightAfter order reverse p) A).length_eq
  simp only [storedLeft, storedRight, List.length_append] at h1 h2 ⊢
  omega

/-- A window whose elements are stored reversed when `reverse` is set: partitioning the stored
window and sorting both sides gives a sorted (and, for stable inner sorts, stable) outcome for the
window's logical order. -/
theorem scratch_partition_outcome {lt : α → α → Bool} (hnt : NegTransOrder lt) {s : Bool}
    (rev : Bool) (p : α) (B A Wl Wu : List α)
    (hl : SortOutcome lt s
      (if rev then (storedLeft lt rev p B A).reverse else storedLeft lt rev p B A) Wl)
    (hu : SortOutcome lt s
      (if rev then (storedRight lt rev p B A).reverse else storedRight lt rev p B A) Wu) :
    SortOutcome lt s (if rev then (B ++ p :: A).reverse else B ++ p :: A) (Wl ++ p :: Wu) := by
  have hbf : goesRightBefore lt false p = fun x => lt p x := by funext x; simp [goesRightBefore]
  have haf : goesRightAfter lt false p = fun x => !lt x p := by funext x; simp [goesRightAfter]
  have hbt : goesRightBefore lt true p = fun x => !lt x p := by funext x; simp [goesRightBefore]
  have hat : goesRightAfter lt true p = fun x => lt p x := by funext x; simp [goesRightAfter]
  cases rev
  · have hL : storedLeft lt false p B A = partLeft lt p B A := by
      simp [storedLeft, partLeft, hbf, haf]
    have hR : storedRight lt false p B A = partRight lt p B A := by
      simp [storedRight, partRight, hbf, haf]
    simp only [Bool.false_eq_true, ↓reduceIte] at hl hu ⊢
    rw [hL] at hl; rw [hR] at hu
    exact partition_outcome hnt hl hu
  · have hL : (storedLeft lt true p B A).reverse = partLeft lt p A.reverse B.reverse := by
      simp [storedLeft, partLeft, hbt, hat, List.filter_reverse]
    have hR : (storedRight lt true p B A).reverse = partRight lt p A.reverse B.reverse := by
      simp [storedRight, partRight, hbt, hat, List.filter_reverse]
    simp only [↓reduceIte] at hl hu ⊢
    rw [hL] at hl; rw [hR] at hu
    rw [show (B ++ p :: A).reverse = A.reverse ++ p :: B.reverse by simp]
    exact partition_outcome hnt hl hu

/-- The window `lo:hi` of `before` is replaced by an outcome of sorting it. -/
def WindowOutcome (lt : α → α → Bool) (s : Bool) (before after : List α) (lo hi : Int) : Prop :=
  ∃ P W Q W', before = P ++ W ++ Q ∧ (P.length : Int) + 1 = lo ∧
    (W.length : Int) = hi - lo + 1 ∧ after = P ++ W' ++ Q ∧ SortOutcome lt s W W'

theorem window_decomp_unique {P W Q P' W' Q' : List α} (h : P ++ W ++ Q = P' ++ W' ++ Q')
    (hP : P.length = P'.length) (hW : W.length = W'.length) : P = P' ∧ W = W' ∧ Q = Q' := by
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨rfl, h2⟩ := List.append_inj h hP
  obtain ⟨rfl, rfl⟩ := List.append_inj h2 hW
  exact ⟨rfl, rfl, rfl⟩

theorem windowOutcome_at {lt : α → α → Bool} {s : Bool} {P W Q after : List α} {lo hi : Int}
    (h : WindowOutcome lt s (P ++ W ++ Q) after lo hi) (hP : (P.length : Int) + 1 = lo)
    (hW : (W.length : Int) = hi - lo + 1) :
    ∃ W', after = P ++ W' ++ Q ∧ SortOutcome lt s W W' := by
  obtain ⟨P', W'', Q', W', hb, hP', hW', ha, ho⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := window_decomp_unique hb (by omega) (by omega)
  exact ⟨W', ha, ho⟩

theorem outcome_nil {lt : α → α → Bool} (s : Bool) : SortOutcome lt s [] [] :=
  ⟨List.Perm.refl _, List.Pairwise.nil, fun _ _ => rfl⟩

theorem split_at_index (l : List α) (k : Nat) (hk : k < l.length) :
    ∃ a b c, l = a ++ b :: c ∧ a.length = k :=
  ⟨l.take k, l[k], l.drop (k + 1), by rw [← List.drop_eq_getElem_cons hk, List.take_append_drop],
    by simp; omega⟩

section Fields

variable [Inhabited α] (S : VectorStorage V α) (pivot : Int → Int → Int)
  (sortNext : V → Algorithm (BracketSortTarget Int) Int → (α → α → SortResult Bool) →
    ArraySortKeywords α → SortResult (V × Option (Array α)))

theorem sq_lessIndex :
    (storageScratchQuickOps S pivot sortNext).lessIndex = fun lo hi => decide (lo < hi) := rfl
theorem sq_distance :
    (storageScratchQuickOps S pivot sortNext).distance = fun lo hi => (hi - lo).toNat := rfl
theorem sq_smallThreshold : (storageScratchQuickOps S pivot sortNext).smallThreshold = 20 := rfl
theorem sq_partitionInVector :
    (storageScratchQuickOps S pivot sortNext).partitionInVector =
      vectorTargetPartitionOps S pivot := rfl
theorem sq_partitionInScratch :
    (storageScratchQuickOps S pivot sortNext).partitionInScratch =
      scratchTargetPartitionOps S pivot := rfl
theorem sq_addIndex : (storageScratchQuickOps S pivot sortNext).addIndex = Int.add := rfl
theorem sq_zeroIndex : (storageScratchQuickOps S pivot sortNext).zeroIndex = 0 := rfl
theorem sq_negateIndex : (storageScratchQuickOps S pivot sortNext).negateIndex = Int.neg := rfl
theorem sq_lowBound (lo hi : Option Int) (next : Algorithm (BracketSortTarget Int) Int) :
    (storageScratchQuickOps S pivot sortNext).lowBound (.scratchQuickSort lo hi next) = lo := rfl
theorem sq_highBound (lo hi : Option Int) (next : Algorithm (BracketSortTarget Int) Int) :
    (storageScratchQuickOps S pivot sortNext).highBound (.scratchQuickSort lo hi next) = hi := rfl
theorem sq_nextAlgorithm (lo hi : Option Int) (next : Algorithm (BracketSortTarget Int) Int) :
    (storageScratchQuickOps S pivot sortNext).nextAlgorithm (.scratchQuickSort lo hi next) =
      next := rfl
theorem sq_previousIndex :
    (storageScratchQuickOps S pivot sortNext).previousIndex = fun i => i - 1 := rfl
theorem sq_nextIndex : (storageScratchQuickOps S pivot sortNext).nextIndex = fun i => i + 1 := rfl
theorem sq_withBounds :
    (storageScratchQuickOps S pivot sortNext).withBounds =
      fun keywords lo hi => { keywords with lo, hi } := rfl
theorem sq_windowLength :
    (storageScratchQuickOps S pivot sortNext).windowLength = fun lo hi => (hi - lo + 1).toNat :=
  rfl
theorem sq_copyTo :
    (storageScratchQuickOps S pivot sortNext).copyTo = storageCopyFromArray S := rfl
theorem sq_reverse : (storageScratchQuickOps S pivot sortNext).reverse = storageReverse S := rfl
theorem sq_sortNext : (storageScratchQuickOps S pivot sortNext).sortNext = sortNext := rfl
theorem sq_rangeAndScratch :
    (storageScratchQuickOps S pivot sortNext).rangeAndScratch =
      fun keywords => .ok (keywords.lo, keywords.hi, keywords.scratch) := rfl
theorem sq_makeScratch :
    (storageScratchQuickOps S pivot sortNext).makeScratch = fun existing _ length =>
      match existing with
      | none => liftSortJl (makeScratchNothing arrayScratchOps length)
      | some backing => liftSortJl (makeScratchSame arrayScratchOps backing length) := rfl
theorem sq_oneMinus : (storageScratchQuickOps S pivot sortNext).oneMinus = fun i => 1 - i := rfl
theorem sq_withScratch :
    (storageScratchQuickOps S pivot sortNext).withScratch =
      fun keywords scratch => { keywords with scratch := some scratch } := rfl

end Fields

theorem int_add_eq (a b : Int) : Int.add a b = a + b := rfl
theorem int_neg_eq (a : Int) : Int.neg a = -a := rfl

theorem scratchQuickLoop_spec [Inhabited α] (L : StorageLaws S E) {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (pivot : Int → Int → Int)
    (hpivot : ∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b)
    (sortNext : V → Algorithm (BracketSortTarget Int) Int → (α → α → SortResult Bool) →
      ArraySortKeywords α → SortResult (V × Option (Array α)))
    (next : Algorithm (BracketSortTarget Int) Int) (s : Bool)
    (hnext : ∀ (v : V) (kw : ArraySortKeywords α), 1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 →
      kw.hi ≤ ((E v).length : Int) →
      ∃ v' sc, sortNext v next (pureCompare lt) kw = .ok (v', sc) ∧
        WindowOutcome lt s (E v) (E v') kw.lo kw.hi) :
    ∀ (fuel : Nat) (v : V) (t : Array α) (lo hi offset : Int) (kw : ArraySortKeywords α)
      (scratch : Option (Array α)) (swap rev : Bool) (Lg P Wv Q TP Wt TQ : List α),
      E v = P ++ Wv ++ Q → t.toList = TP ++ Wt ++ TQ →
      (P.length : Int) + 1 = lo → (TP.length : Int) + 1 = lo + offset →
      Wv.length = Lg.length → Wt.length = Lg.length → (Lg.length : Int) = hi - lo + 1 →
      Lg.length + 1 ≤ fuel →
      (if swap then Wt else Wv) = (if rev then Lg.reverse else Lg) →
      ∃ v' t' sc W' Wt',
        sortScratchQuickLoop (storageScratchQuickOps S pivot sortNext)
          (.scratchQuickSort none none next) (pureCompare lt) fuel v t lo hi offset kw scratch
          swap rev =
          .ok (v', t', sc) ∧
        E v' = P ++ W' ++ Q ∧ SortOutcome lt s Lg W' ∧ t'.toList = TP ++ Wt' ++ TQ ∧
        Wt'.length = Lg.length := by
  intro fuel
  induction fuel with
  | zero =>
    intro v t lo hi offset kw scratch swap rev Lg P Wv Q TP Wt TQ _ _ _ _ _ _ _ hfuel
    omega
  | succ f ih =>
    intro v t lo hi offset kw scratch swap rev Lg P Wv Q TP Wt TQ hv ht hP hTP hWv hWt hLg
      hfuel hst
    unfold sortScratchQuickLoop
    by_cases hbig : lo < hi ∧ 20 < (hi - lo).toNat
    · have hcond : ((storageScratchQuickOps S pivot sortNext).lessIndex lo hi &&
          decide ((storageScratchQuickOps S pivot sortNext).distance lo hi >
            (storageScratchQuickOps S pivot sortNext).smallThreshold)) = true := by
        show (decide (lo < hi) && decide ((hi - lo).toNat > 20)) = true
        simp [hbig.1, hbig.2]
      rw [if_pos hcond, sq_distance]
      simp only [sq_partitionInVector, sq_partitionInScratch, sq_addIndex, sq_zeroIndex,
        sq_negateIndex, sq_lowBound, sq_highBound, sq_previousIndex, sq_nextIndex,
        sq_withBounds, int_add_eq, int_neg_eq]
      -- after partitioning, the two sides are sorted recursively, smaller side first
      have hcont : ∀ (v1 : V) (t1 : Array α) (swap' : Bool) (B A : List α) (p : α)
          (XL XU YL YU : List α) (y : α),
          (if rev then Lg.reverse else Lg) = B ++ p :: A →
          E v1 = P ++ XL ++ p :: XU ++ Q → t1.toList = TP ++ YL ++ y :: YU ++ TQ →
          XL.length = (storedLeft lt rev p B A).length →
          XU.length = (storedRight lt rev p B A).length →
          YL.length = (storedLeft lt rev p B A).length →
          YU.length = (storedRight lt rev p B A).length →
          (if swap' then YL else XL) = storedLeft lt rev p B A →
          (if swap' then YU else XU) = (storedRight lt rev p B A).reverse →
          ∃ v' t' sc W' Wt',
            (if (lo + (storedLeft lt rev p B A).length - lo).toNat <
                (hi - (lo + (storedLeft lt rev p B A).length)).toNat then do
              let (sorted, temporary, _) ← sortScratchQuickLoop
                (storageScratchQuickOps S pivot sortNext) (.scratchQuickSort none none next)
                (pureCompare lt) f v1 t1 lo (lo + (storedLeft lt rev p B A).length - 1) offset
                { kw with lo := lo, hi := lo + (storedLeft lt rev p B A).length - 1 } scratch
                swap' rev
              sortScratchQuickLoop (storageScratchQuickOps S pivot sortNext)
                (.scratchQuickSort none none next) (pureCompare lt) f sorted temporary
                (lo + (storedLeft lt rev p B A).length + 1) hi offset kw scratch swap' !rev
            else do
              let (sorted, temporary, _) ← sortScratchQuickLoop
                (storageScratchQuickOps S pivot sortNext) (.scratchQuickSort none none next)
                (pureCompare lt) f v1 t1 (lo + (storedLeft lt rev p B A).length + 1) hi offset
                { kw with lo := lo + (storedLeft lt rev p B A).length + 1, hi := hi } scratch
                swap' !rev
              sortScratchQuickLoop (storageScratchQuickOps S pivot sortNext)
                (.scratchQuickSort none none next) (pureCompare lt) f sorted temporary lo
                (lo + (storedLeft lt rev p B A).length - 1) offset kw scratch swap' rev) =
              .ok (v', t', sc) ∧
            E v' = P ++ W' ++ Q ∧ SortOutcome lt s Lg W' ∧ t'.toList = TP ++ Wt' ++ TQ ∧
            Wt'.length = Lg.length := by
        intro v1 t1 swap' B A p XL XU YL YU y hLg' hv1 ht1 hXL hXU hYL hYU hdL hdU
        have hlens := stored_lengths lt rev p B A
        have hBA : Lg.length = B.length + A.length + 1 := by
          have := congrArg List.length hLg'
          cases rev <;> simp at this <;> omega
        have hLgEq : Lg = if rev then (B ++ p :: A).reverse else B ++ p :: A := by
          cases rev
          · simpa using hLg'
          · simp only [↓reduceIte] at hLg' ⊢; rw [← hLg', List.reverse_reverse]
        let Ll := if rev then (storedLeft lt rev p B A).reverse else storedLeft lt rev p B A
        let Lu := if rev then (storedRight lt rev p B A).reverse else storedRight lt rev p B A
        have hLl : Ll.length = (storedLeft lt rev p B A).length := by
          simp only [Ll]; cases rev <;> simp
        have hLu : Lu.length = (storedRight lt rev p B A).length := by
          simp only [Lu]; cases rev <;> simp
        have hstL : (if swap' then YL else XL) = (if rev then Ll.reverse else Ll) := by
          rw [hdL]; simp only [Ll]; cases rev <;> simp
        have hstU : (if swap' then YU else XU) = (if !rev then Lu.reverse else Lu) := by
          rw [hdU]; simp only [Lu]; cases rev <;> simp
        by_cases hcmp : (lo + ((storedLeft lt rev p B A).length : Int) - lo).toNat <
            (hi - (lo + (storedLeft lt rev p B A).length)).toNat
        · rw [if_pos hcmp]
          obtain ⟨v2, t2, sc2, Wl, Wtl, hrun2, hv2, hol, ht2, hWtl⟩ :=
            ih v1 t1 lo (lo + (storedLeft lt rev p B A).length - 1) offset
              { kw with lo := lo, hi := lo + (storedLeft lt rev p B A).length - 1 } scratch swap'
              rev Ll P XL (p :: XU ++ Q) TP YL (y :: YU ++ TQ)
              (by rw [hv1]; simp [List.append_assoc]) (by rw [ht1]; simp [List.append_assoc])
              hP hTP (by omega) (by omega) (by omega) (by omega) hstL
          have hWl : Wl.length = (storedLeft lt rev p B A).length := by
            rw [hol.1.length_eq, hLl]
          obtain ⟨v3, t3, sc3, Wu, Wtu, hrun3, hv3, hou, ht3, hWtu⟩ :=
            ih v2 t2 (lo + (storedLeft lt rev p B A).length + 1) hi offset kw scratch swap' (!rev)
              Lu (P ++ Wl ++ [p]) XU Q (TP ++ Wtl ++ [y]) YU TQ
              (by rw [hv2]; simp [List.append_assoc]) (by rw [ht2]; simp [List.append_assoc])
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by omega) (by omega) (by omega) (by omega) hstU
          refine ⟨v3, t3, sc3, Wl ++ p :: Wu, Wtl ++ y :: Wtu, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hrun2, except_bind_ok]
            exact hrun3
          · rw [hv3]; simp [List.append_assoc]
          · rw [hLgEq]
            exact scratch_partition_outcome hnt rev p B A Wl Wu hol
              (by cases rev <;> simpa [Lu] using hou)
          · rw [ht3]; simp [List.append_assoc]
          · simp only [List.length_append, List.length_cons]; omega
        · rw [if_neg hcmp]
          obtain ⟨v2, t2, sc2, Wu, Wtu, hrun2, hv2, hou, ht2, hWtu⟩ :=
            ih v1 t1 (lo + (storedLeft lt rev p B A).length + 1) hi offset
              { kw with lo := lo + (storedLeft lt rev p B A).length + 1, hi := hi } scratch swap'
              (!rev) Lu (P ++ XL ++ [p]) XU Q (TP ++ YL ++ [y]) YU TQ
              (by rw [hv1]; simp [List.append_assoc]) (by rw [ht1]; simp [List.append_assoc])
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by simp only [List.length_append, List.length_singleton]; omega)
              (by omega) (by omega) (by omega) (by omega) hstU
          obtain ⟨v3, t3, sc3, Wl, Wtl, hrun3, hv3, hol, ht3, hWtl⟩ :=
            ih v2 t2 lo (lo + (storedLeft lt rev p B A).length - 1) offset kw scratch swap' rev Ll
              P XL (p :: Wu ++ Q) TP YL (y :: Wtu ++ TQ)
              (by rw [hv2]; simp [List.append_assoc]) (by rw [ht2]; simp [List.append_assoc])
              hP hTP (by omega) (by omega) (by omega) (by omega) hstL
          refine ⟨v3, t3, sc3, Wl ++ p :: Wu, Wtl ++ y :: Wtu, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hrun2, except_bind_ok]
            exact hrun3
          · rw [hv3]; simp [List.append_assoc]
          · rw [hLgEq]
            exact scratch_partition_outcome hnt rev p B A Wl Wu hol
              (by cases rev <;> simpa [Lu] using hou)
          · rw [ht3]; simp [List.append_assoc]
          · have := hol.1.length_eq
            simp only [List.length_append, List.length_cons]; omega
      have hlohi : lo ≤ hi := Int.le_of_lt hbig.1
      cases swap
      · -- elements move from the vector into scratch
        simp only [Bool.false_eq_true, ↓reduceIte] at hst ⊢
        obtain ⟨B, p, A, t1, v1, m, hWv', ht1, hv1, hrun⟩ :=
          scratchTargetPartition_spec L pivot hpivot v t lo hi offset lt rev P Wv Q TP Wt TQ hv ht
            hP hTP (by omega) (by omega) hlohi
        have hlens := stored_lengths lt rev p B A
        have hWvlen := congrArg List.length hWv'
        simp only [List.length_append, List.length_cons] at hWvlen
        obtain ⟨a, b, c, hsplit, ha⟩ :=
          split_at_index Wv (storedLeft lt rev p B A).length (by omega)
        have hset : Wv.set (storedLeft lt rev p B A).length p = a ++ p :: c := by
          rw [hsplit, ← ha, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
            List.set_cons_zero]
        have hclen : c.length = (storedRight lt rev p B A).length := by
          have := congrArg List.length hsplit
          simp only [List.length_append, List.length_cons] at this; omega
        obtain ⟨v', t', sc, W', Wt', hr, h1, h2, h3, h4⟩ :=
          hcont v1 t1 (!false) B A p a c (storedLeft lt rev p B A)
            (storedRight lt rev p B A).reverse m (by rw [← hst, hWv'])
            (by rw [hv1]; simp only [storedLeft] at hset ⊢; rw [hset]; simp [List.append_assoc])
            (by rw [ht1]; simp [storedLeft, storedRight, List.append_assoc]) ha hclen rfl
            (by simp) (by simp) (by simp)
        refine ⟨v', t', sc, W', Wt', ?_, h1, h2, h3, h4⟩
        rw [hrun, except_bind_ok, except_pure_ok, except_bind_ok]
        exact hr
      · -- elements move from scratch into the vector
        simp only [↓reduceIte] at hst ⊢
        obtain ⟨B, p, A, v1, hWt', hv1, hrun⟩ :=
          vectorTargetPartition_spec L pivot hpivot v t lo hi offset lt rev P Wv Q TP Wt TQ hv ht
            hP hTP (by omega) (by omega) hlohi
        have hlens := stored_lengths lt rev p B A
        have hWtlen := congrArg List.length hWt'
        simp only [List.length_append, List.length_cons] at hWtlen
        obtain ⟨a, b, c, hsplit, ha⟩ :=
          split_at_index Wt (storedLeft lt rev p B A).length (by omega)
        have hclen : c.length = (storedRight lt rev p B A).length := by
          have := congrArg List.length hsplit
          simp only [List.length_append, List.length_cons] at this; omega
        obtain ⟨v', t', sc, W', Wt', hr, h1, h2, h3, h4⟩ :=
          hcont v1 t (!true) B A p (storedLeft lt rev p B A) (storedRight lt rev p B A).reverse
            a c b (by rw [← hst, hWt'])
            (by rw [hv1]; simp [storedLeft, storedRight, List.append_assoc])
            (by rw [ht, hsplit]; simp [List.append_assoc]) rfl (by simp) ha hclen (by simp)
            (by simp)
        refine ⟨v', t', sc, W', Wt', ?_, h1, h2, h3, h4⟩
        rw [hrun, except_bind_ok, except_pure_ok, except_bind_ok]
        exact hr
    · -- a short window goes back to the vector in logical order and is sorted by `next`
      have hcond : ¬ ((storageScratchQuickOps S pivot sortNext).lessIndex lo hi &&
          decide ((storageScratchQuickOps S pivot sortNext).distance lo hi >
            (storageScratchQuickOps S pivot sortNext).smallThreshold)) = true := by
        show ¬ (decide (lo < hi) && decide ((hi - lo).toNat > 20)) = true
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact hbig
      rw [if_neg hcond, sq_lessIndex]
      simp only [sq_copyTo, sq_reverse, sq_sortNext, sq_nextAlgorithm, sq_withBounds,
        sq_windowLength, sq_addIndex, int_add_eq]
      by_cases hempty : hi < lo
      · have hLg0 : Lg = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hLg0
        have hWv0 : Wv = [] := List.eq_nil_of_length_eq_zero hWv
        have hWt0 : Wt = [] := List.eq_nil_of_length_eq_zero hWt
        subst hWv0 hWt0
        refine ⟨v, t, scratch, [], [], ?_, by simpa using hv, outcome_nil s, by simpa using ht, rfl⟩
        simp [hempty]; rfl
      · simp only [hempty, decide_false, Bool.false_eq_true, ↓reduceIte]
        -- bring the window into the vector
        obtain ⟨v1, hrun1, hv1⟩ : ∃ v1,
            (if swap then storageCopyFromArray S v lo t (lo + offset) (hi - lo + 1).toNat
              else pure v) = .ok v1 ∧ E v1 = P ++ (if swap then Wt else Wv) ++ Q := by
          cases swap
          · exact ⟨v, rfl, by simpa using hv⟩
          · have hlen : (hi - lo + 1).toNat = Wt.length := by omega
            rw [hlen]
            obtain ⟨v1, hrun, hv1⟩ := storageCopyFromArray_spec L v lo t (lo + offset) P Wv Q TP
              Wt TQ hv ht hP hTP (by omega)
            exact ⟨v1, by simpa using hrun, by simpa using hv1⟩
        -- undo the reversed storage
        obtain ⟨v2, hrun2, hv2⟩ : ∃ v2,
            (if rev then storageReverse S v1 lo hi else pure v1) = .ok v2 ∧
            E v2 = P ++ Lg ++ Q := by
          cases rev
          · refine ⟨v1, rfl, ?_⟩
            rw [hv1]; simpa using hst
          · obtain ⟨v2, hrun, hv2⟩ := storageReverse_spec L v1 lo hi P
              (if swap then Wt else Wv) Q hv1 hP (by cases swap <;> simp <;> omega)
            refine ⟨v2, by simpa using hrun, ?_⟩
            rw [hv2, hst]; simp
        obtain ⟨v3, sc3, hrun3, hout⟩ := hnext v2 { kw with lo := lo, hi := hi }
          (show 1 ≤ lo by omega) (show lo ≤ hi + 1 by omega)
          (show hi ≤ ((E v2).length : Int) by rw [hv2]; simp only [List.length_append]; omega)
        obtain ⟨W', hv3, hW'⟩ := windowOutcome_at (by rw [← hv2]; exact hout) hP hLg
        refine ⟨v3, t, sc3, W', Wt, ?_, hv3, hW', ht, hWt⟩
        cases swap <;> cases rev <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrun1 hrun2 ⊢ <;>
          rw [hrun1, except_bind_ok, hrun2, except_bind_ok, hrun3] <;> rfl

theorem arrayMakeScratch_ok [Inhabited α] (existing : Option (Array α)) (n : Nat) :
    ∃ backing : Array α, n ≤ backing.size ∧
      (match existing with
        | none => makeScratchNothing arrayScratchOps n
        | some backing => makeScratchSame arrayScratchOps backing n) = .ok (backing, backing) := by
  cases existing with
  | none => exact ⟨Array.replicate n default, by simp, rfl⟩
  | some b =>
    by_cases h : n > b.size
    · refine ⟨b ++ Array.replicate (n - b.size) default, by simp; omega, ?_⟩
      simp only [makeScratchSame, arrayScratchOps, h, ↓reduceIte]; rfl
    · refine ⟨b, by omega, ?_⟩
      simp only [makeScratchSame, arrayScratchOps, h, ↓reduceIte]; rfl

/-- `ScratchQuickSort()` on the window `lo:hi` of any storage: it allocates or reuses scratch
space and returns an outcome of sorting the window that is stable when the small-window
algorithm `next` is. -/
theorem sortScratchQuick_spec [Inhabited α] (L : StorageLaws S E) {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (pivot : Int → Int → Int)
    (hpivot : ∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b)
    (sortNext : V → Algorithm (BracketSortTarget Int) Int → (α → α → SortResult Bool) →
      ArraySortKeywords α → SortResult (V × Option (Array α)))
    (next : Algorithm (BracketSortTarget Int) Int) (s : Bool)
    (hnext : ∀ (v : V) (kw : ArraySortKeywords α), 1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 →
      kw.hi ≤ ((E v).length : Int) →
      ∃ v' sc, sortNext v next (pureCompare lt) kw = .ok (v', sc) ∧
        WindowOutcome lt s (E v) (E v') kw.lo kw.hi)
    (v : V) (kw : ArraySortKeywords α) (P W Q : List α) (hv : E v = P ++ W ++ Q)
    (hP : (P.length : Int) + 1 = kw.lo) (hW : (W.length : Int) = kw.hi - kw.lo + 1) :
    ∃ v' sc W', sortScratchQuick (storageScratchQuickOps S pivot sortNext) v
        (.scratchQuickSort none none next) (pureCompare lt) kw = .ok (v', sc) ∧
      E v' = P ++ W' ++ Q ∧ SortOutcome lt s W W' := by
  obtain ⟨t, ht, hmake⟩ := arrayMakeScratch_ok kw.scratch (kw.hi - kw.lo + 1).toNat
  have hsplit : t.toList = [] ++ t.toList.take W.length ++ t.toList.drop W.length := by simp
  obtain ⟨v', t', sc, W', Wt', hrun, hv', hout, -, -⟩ :=
    scratchQuickLoop_spec L hnt pivot hpivot sortNext next s hnext
      ((kw.hi - kw.lo + 1).toNat + 2) v t kw.lo kw.hi (1 - kw.lo)
      { kw with scratch := some t } (some t) false false W P W Q [] (t.toList.take W.length)
      (t.toList.drop W.length) hv hsplit (by omega) (by simp only [List.length_nil]; omega) rfl
      (by simp; omega) hW (by omega) rfl
  refine ⟨v', sc, W', ?_, hv', hout⟩
  unfold sortScratchQuick
  simp only [sq_rangeAndScratch, sq_makeScratch, sq_windowLength, sq_oneMinus, sq_withScratch,
    except_bind_ok]
  cases hsc : kw.scratch <;> simp only [hsc] at hmake ⊢ <;>
    simp only [hmake, liftSortJl_ok, bind, Except.bind, pure, Except.pure, hrun]

end ScratchQuick

theorem effectWindowOutcome_pure {ε α : Type} (p : α → α → Bool) (s : Bool)
    (before after : List α) (lo hi : Int) :
    EffectWindowOutcome (pureCompare (ε := ε) p) s before after lo hi ↔
      WindowOutcome p s before after lo hi := by
  unfold EffectWindowOutcome WindowOutcome
  simp only [effectSortOutcome_pure]


/-! ## Sorting a window through the source `_sort!` dispatch -/

section Dispatch

variable {V α : Type} {S : VectorStorage V α} {E : V → List α}

theorem window_split (l : List α) {lo hi : Int} (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1)
    (h3 : hi ≤ (l.length : Int)) :
    ∃ P W Q, l = P ++ W ++ Q ∧ (P.length : Int) + 1 = lo ∧ (W.length : Int) = hi - lo + 1 := by
  refine ⟨l.take (lo - 1).toNat, (l.drop (lo - 1).toNat).take (hi - lo + 1).toNat,
    (l.drop (lo - 1).toNat).drop (hi - lo + 1).toNat, ?_, ?_, ?_⟩
  · rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  · rw [List.length_take, Nat.min_eq_left (by omega)]; omega
  · rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]; omega

theorem insertion_window (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (v : V) {lo hi : Int} (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1) (h3 : hi ≤ ((E v).length : Int)) :
    ∃ v', storageInsertion S (pureCompare lt) v lo hi = .ok v' ∧
      WindowOutcome lt true (E v) (E v') lo hi := by
  obtain ⟨P, W, Q, hv, hP, hW⟩ := window_split (E v) h1 h2 h3
  obtain ⟨v', hrun, hv'⟩ := storageInsertion_spec L hnt v lo hi P W Q h1 hv hP hW
  exact ⟨v', hrun, P, W, Q, sortRef lt W, hv, hP, hW, hv', sortRef_outcome hnt true W⟩

theorem sourceSortWindow_insertion [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int) (v : V) (lt : α → α → SortResult Bool)
    (kw : ArraySortKeywords α) :
    sourceSortWindow S numeric pivot v .insertion lt kw =
      (do let sorted ← storageInsertion S lt v kw.lo kw.hi; pure (sorted, kw.scratch)) := by
  unfold sourceSortWindow
  rfl

theorem sourceSortWindow_scratchQuick [Inhabited α] (S : VectorStorage V α)
    (numeric : BracketNumerics) (pivot : Int → Int → Int) (v : V)
    (next : Algorithm (BracketSortTarget Int) Int) (lt : α → α → SortResult Bool)
    (kw : ArraySortKeywords α) :
    sourceSortWindow S numeric pivot v (.scratchQuickSort none none next) lt kw =
      sortScratchQuick
        (storageScratchQuickOps S pivot (sourceSortLoop S numeric pivot (next.depth + 16)))
        v (.scratchQuickSort none none next) lt kw := by
  unfold sourceSortWindow
  rw [show (Algorithm.scratchQuickSort none none next).depth + 16 = (next.depth + 16) + 1 by
    simp only [Algorithm.depth] <;> omega]
  rfl

theorem scratchQuick_window [Inhabited α] (L : StorageLaws S E) (numeric : BracketNumerics)
    (pivot : Int → Int → Int) {lt : α → α → Bool} (next : Algorithm (BracketSortTarget Int) Int)
    (s : Bool) (hnt : NegTransOrder lt) (hpivot : ∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b)
    (hnext : ∀ (v : V) (kw : ArraySortKeywords α), 1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 →
      kw.hi ≤ ((E v).length : Int) →
      ∃ v' sc, sourceSortWindow S numeric pivot v next (pureCompare lt) kw = .ok (v', sc) ∧
        WindowOutcome lt s (E v) (E v') kw.lo kw.hi)
    (v : V) (kw : ArraySortKeywords α) (h1 : 1 ≤ kw.lo) (h2 : kw.lo ≤ kw.hi + 1)
    (h3 : kw.hi ≤ ((E v).length : Int)) :
    ∃ v' sc, sourceSortWindow S numeric pivot v (.scratchQuickSort none none next)
        (pureCompare lt) kw = .ok (v', sc) ∧
      WindowOutcome lt s (E v) (E v') kw.lo kw.hi := by
  obtain ⟨P, W, Q, hv, hP, hW⟩ := window_split (E v) h1 h2 h3
  obtain ⟨v', sc, W', hrun, hv', hout⟩ := sortScratchQuick_spec L hnt pivot hpivot
    (sourceSortLoop S numeric pivot (next.depth + 16)) next s hnext v kw P W Q hv hP hW
  refine ⟨v', sc, ?_, P, W, Q, W', hv, hP, hW, hv', hout⟩
  rw [sourceSortWindow_scratchQuick]
  exact hrun

end Dispatch

/-- `_sort!(v, InsertionSort, o; lo, hi)`, reached through the source `_sort!` dispatch, works on
every one-based vector storage obeying the `AbstractVector` indexing laws: for every strict weak
order it replaces the window `lo:hi` by a stable sorted permutation of itself, keeps the
elements outside the window and returns the scratch keyword unchanged. -/
def InsertionSortStable : Prop :=
  ∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α), StorageLaws S E →
  ∀ (numeric : BracketNumerics) (pivot : Int → Int → Int) (lt : α → α → SortResult Bool) (v : V)
    (kw : ArraySortKeywords α), EffectNegTransOrder lt → 1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 →
    kw.hi ≤ ((E v).length : Int) →
    ∃ v', sourceSortWindow S numeric pivot v .insertion lt kw = .ok (v', kw.scratch) ∧
      EffectWindowOutcome lt true (E v) (E v') kw.lo kw.hi


/-- `_sort!(v, ScratchQuickSort(next), o; lo, hi)` without target bounds, reached through the
source `_sort!` dispatch on any one-based vector storage obeying the `AbstractVector` indexing
laws: for every strict weak order and every pivot rule choosing an index in the current window,
it replaces the window `lo:hi` by a sorted permutation of itself, keeps the elements outside the
window, and is stable whenever its small-window algorithm `next` is. With the default small
algorithm `InsertionSort` it is stable unconditionally. -/
def ScratchQuickSortStable : Prop :=
  (∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α), StorageLaws S E →
    ∀ (numeric : BracketNumerics) (pivot : Int → Int → Int) (lt : α → α → SortResult Bool)
      (next : Algorithm (BracketSortTarget Int) Int) (s : Bool),
      EffectNegTransOrder lt → (∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b) →
      (∀ (v : V) (kw : ArraySortKeywords α), 1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 →
        kw.hi ≤ ((E v).length : Int) →
        ∃ v' sc, sourceSortWindow S numeric pivot v next lt kw = .ok (v', sc) ∧
          EffectWindowOutcome lt s (E v) (E v') kw.lo kw.hi) →
      ∀ (v : V) (kw : ArraySortKeywords α), 1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 →
        kw.hi ≤ ((E v).length : Int) →
        ∃ v' sc, sourceSortWindow S numeric pivot v (.scratchQuickSort none none next) lt kw =
            .ok (v', sc) ∧ EffectWindowOutcome lt s (E v) (E v') kw.lo kw.hi) ∧
  (∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α), StorageLaws S E →
    ∀ (numeric : BracketNumerics) (pivot : Int → Int → Int) (lt : α → α → SortResult Bool),
      EffectNegTransOrder lt → (∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b) →
      ∀ (v : V) (kw : ArraySortKeywords α), 1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 →
        kw.hi ≤ ((E v).length : Int) →
        ∃ v' sc, sourceSortWindow S numeric pivot v (.scratchQuickSort none none .insertion) lt
            kw = .ok (v', sc) ∧ EffectWindowOutcome lt true (E v) (E v') kw.lo kw.hi)


/-! ## Pointwise reasoning about one-based storage -/

section Pointwise

variable {V α : Type} {S : VectorStorage V α} {E : V → List α}

/-- Element `i` (one-based) of a list. -/
def posAt (l : List α) (i : Int) : Option α := l[(i - 1).toNat]?


/-- `l'` has the length of `l` and agrees with it outside the window `lo:hi`. -/
def Frame (l l' : List α) (lo hi : Int) : Prop :=
  l'.length = l.length ∧ ∀ i : Int, 1 ≤ i → (i < lo ∨ hi < i) → posAt l' i = posAt l i

theorem posAt_some {l : List α} {i : Int} (h1 : 1 ≤ i) (h2 : i ≤ (l.length : Int)) :
    ∃ x, posAt l i = some x :=
  ⟨l[(i - 1).toNat]'(by omega), List.getElem?_eq_some_iff.2 ⟨by omega, rfl⟩⟩

theorem storage_read_at (L : StorageLaws S E) {v : V} {i : Int} {x : α} (h1 : 1 ≤ i)
    (h : posAt (E v) i = some x) : S.getindex v i = .ok x := by
  rw [L.getindex_eq]
  unfold arrayRead
  rw [if_pos h1, List.getElem?_toArray]
  unfold posAt at h
  rw [h]

theorem posAt_set {l : List α} {i j : Int} {x : α} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hjn : j ≤ (l.length : Int)) :
    posAt (l.set (j - 1).toNat x) i = if i = j then some x else posAt l i := by
  unfold posAt
  rw [List.getElem?_set]
  by_cases h : i = j
  · subst h
    simp <;> omega
  · rw [if_neg (show (j - 1).toNat ≠ (i - 1).toNat by omega), if_neg h]

theorem perm_swap_at {l : List α} {a b : Int} {x y : α}
    (hx : posAt l a = some x) (hy : posAt l b = some y) :
    ((l.set (a - 1).toNat y).set (b - 1).toNat x).Perm l := by
  unfold posAt at hx hy
  obtain ⟨ha', rfl⟩ := List.getElem?_eq_some_iff.1 hx
  obtain ⟨hb', rfl⟩ := List.getElem?_eq_some_iff.1 hy
  exact List.set_set_perm ha' hb'

theorem Frame.refl (l : List α) (lo hi : Int) : Frame l l lo hi := ⟨rfl, fun _ _ _ => rfl⟩

theorem Frame.trans {l1 l2 l3 : List α} {lo hi : Int} (h12 : Frame l1 l2 lo hi)
    (h23 : Frame l2 l3 lo hi) : Frame l1 l3 lo hi :=
  ⟨h23.1.trans h12.1, fun i h1 h => (h23.2 i h1 h).trans (h12.2 i h1 h)⟩

theorem Frame.mono {l l' : List α} {lo hi lo' hi' : Int} (h : Frame l l' lo hi)
    (h1 : lo' ≤ lo) (h2 : hi ≤ hi') : Frame l l' lo' hi' :=
  ⟨h.1, fun i hi1 hout => h.2 i hi1 (by omega)⟩

theorem frame_set {l : List α} {lo hi j : Int} (x : α) (hj1 : lo ≤ j) (hj2 : j ≤ hi)
    (h1 : 1 ≤ lo) (hjn : j ≤ (l.length : Int)) : Frame l (l.set (j - 1).toNat x) lo hi :=
  ⟨by simp, fun i hi1 hout => by
    rw [posAt_set hi1 (by omega) hjn, if_neg (show ¬ i = j by omega)]⟩

theorem list_split3 (l : List α) {lo hi : Int} (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1)
    (h3 : hi ≤ (l.length : Int)) :
    l = l.take (lo - 1).toNat ++ seg l lo hi ++ l.drop hi.toNat := by
  have hd : l.drop hi.toNat = (l.drop (lo - 1).toNat).drop (hi - lo + 1).toNat := by
    rw [List.drop_drop]; congr 1; omega
  rw [hd, seg, List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem Frame.take_eq {l l' : List α} {lo hi : Int} (h : Frame l l' lo hi) (h1 : 1 ≤ lo) :
    l'.take (lo - 1).toNat = l.take (lo - 1).toNat := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_take, List.getElem?_take]
  split
  · have hk := h.2 ((k : Int) + 1) (by omega) (Or.inl (by omega))
    unfold posAt at hk
    rw [show ((k : Int) + 1 - 1).toNat = k by omega] at hk
    exact hk
  · rfl

theorem Frame.drop_eq {l l' : List α} {lo hi : Int} (h : Frame l l' lo hi) (h0 : 0 ≤ hi) :
    l'.drop hi.toNat = l.drop hi.toNat := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_drop, List.getElem?_drop]
  have hk := h.2 (((hi.toNat + k : Nat) : Int) + 1) (by omega) (Or.inr (by omega))
  unfold posAt at hk
  rw [show (((hi.toNat + k : Nat) : Int) + 1 - 1).toNat = hi.toNat + k by omega] at hk
  exact hk

theorem Frame.seg_eq {l l' : List α} {lo hi a b : Int} (h : Frame l l' lo hi) (ha : 1 ≤ a)
    (hd : b < lo ∨ hi < a) : seg l' a b = seg l a b := by
  apply List.ext_getElem?
  intro k
  unfold seg
  rw [List.getElem?_take, List.getElem?_take]
  split
  · rw [List.getElem?_drop, List.getElem?_drop]
    have hk := h.2 (a + k) (by omega) (by omega)
    unfold posAt at hk
    rw [show (a + k - 1).toNat = (a - 1).toNat + k by omega] at hk
    exact hk
  · rfl

theorem Frame.seg_perm {l l' : List α} {lo hi : Int} (h : Frame l l' lo hi) (hp : l'.Perm l)
    (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1) (h3 : hi ≤ (l.length : Int)) :
    (seg l' lo hi).Perm (seg l lo hi) := by
  have e := list_split3 l h1 h2 h3
  have e' := list_split3 l' h1 h2 (by rw [h.1]; exact h3)
  rw [h.take_eq h1, h.drop_eq (by omega)] at e'
  have key : (l.take (lo - 1).toNat ++ seg l' lo hi ++ l.drop hi.toNat).Perm
      (l.take (lo - 1).toNat ++ seg l lo hi ++ l.drop hi.toNat) := by
    rw [← e', ← e]; exact hp
  exact (List.perm_append_left_iff _).1 ((List.perm_append_right_iff _).1 key)

theorem seg_decomp {P M Q : List α} {lo hi : Int} (hP : (P.length : Int) + 1 = lo)
    (hM : (M.length : Int) = hi - lo + 1) : seg (P ++ M ++ Q) lo hi = M := by
  unfold seg
  rw [List.append_assoc, List.drop_left' (l₁ := P) (show P.length = (lo - 1).toNat by omega),
    List.take_left' (l₁ := M) (show M.length = (hi - lo + 1).toNat by omega)]

theorem frame_of_decomp {P M M' Q : List α} {lo hi : Int} (hP : (P.length : Int) + 1 = lo)
    (hM : M'.length = M.length) (hMl : (M.length : Int) = hi - lo + 1) :
    Frame (P ++ M ++ Q) (P ++ M' ++ Q) lo hi := by
  refine ⟨by simp [hM], fun i h1 hout => ?_⟩
  unfold posAt
  rcases hout with h | h
  · rw [List.append_assoc, List.append_assoc,
      List.getElem?_append_left (show (i - 1).toNat < P.length by omega),
      List.getElem?_append_left (show (i - 1).toNat < P.length by omega)]
  · rw [List.getElem?_append_right (show (P ++ M').length ≤ (i - 1).toNat by simp; omega),
      List.getElem?_append_right (show (P ++ M).length ≤ (i - 1).toNat by simp; omega)]
    simp only [List.length_append, hM]

theorem mem_seg {l : List α} {lo hi : Int} {x : α} (h1 : 1 ≤ lo) :
    x ∈ seg l lo hi ↔ ∃ i, lo ≤ i ∧ i ≤ hi ∧ posAt l i = some x := by
  unfold seg posAt
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨k, hk⟩
    rw [List.getElem?_take] at hk
    split at hk
    · rw [List.getElem?_drop] at hk
      refine ⟨lo + k, by omega, by omega, ?_⟩
      rw [show (lo + k - 1).toNat = (lo - 1).toNat + k by omega]
      exact hk
    · cases hk
  · rintro ⟨i, hlo, hhi, hx⟩
    refine ⟨(i - lo).toNat, ?_⟩
    rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop,
      show (lo - 1).toNat + (i - lo).toNat = (i - 1).toNat by omega]
    exact hx

theorem seg_length_le (l : List α) (lo hi : Int) : (seg l lo hi).length ≤ (hi - lo + 1).toNat := by
  unfold seg; rw [List.length_take]; omega

theorem pairwise_of_length_le_one {R : α → α → Prop} : ∀ {l : List α}, l.length ≤ 1 → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | _ :: _ :: _, h => by simp at h

theorem seg_short_sorted (lt : α → α → Bool) (l : List α) {lo hi : Int} (h : hi ≤ lo) :
    SortedPairwise lt (seg l lo hi) :=
  pairwise_of_length_le_one (Nat.le_trans (seg_length_le l lo hi) (by omega))

theorem seg_append (l : List α) {lo m hi : Int} (h1 : 1 ≤ lo) (h2 : lo ≤ m + 1) (h3 : m ≤ hi) :
    seg l lo hi = seg l lo m ++ seg l (m + 1) hi := by
  unfold seg
  rw [show (hi - lo + 1).toNat = (m - lo + 1).toNat + (hi - (m + 1) + 1).toNat by omega,
    List.take_add, List.drop_drop, show (m + 1 - 1).toNat = (lo - 1).toNat + (m - lo + 1).toNat by omega]

theorem seg_single {l : List α} {j : Int} {x : α} (h1 : 1 ≤ j) (h : posAt l j = some x) :
    seg l j j = [x] := by
  apply List.ext_getElem?
  intro k
  unfold seg
  rw [List.getElem?_take]
  cases k with
  | zero =>
    rw [if_pos (by omega), List.getElem?_drop, Nat.add_zero]
    exact h
  | succ k =>
    rw [if_neg (by omega)]
    rfl

theorem seg_pivot (l : List α) {lo j hi : Int} {x : α} (h1 : 1 ≤ lo) (hj1 : lo ≤ j) (hj2 : j ≤ hi)
    (h : posAt l j = some x) :
    seg l lo hi = seg l lo (j - 1) ++ x :: seg l (j + 1) hi := by
  rw [seg_append l h1 (show lo ≤ j - 1 + 1 by omega) (show j - 1 ≤ hi by omega),
    show j - 1 + 1 = j by omega, seg_append l (show 1 ≤ j by omega) (show j ≤ j + 1 - 1 + 1 by omega)
      (show j + 1 - 1 ≤ hi by omega), show j + 1 - 1 = j by omega, seg_single (by omega) h]
  rfl

theorem windowOutcome_of_frame {lt : α → α → Bool} {l l' : List α} {lo hi : Int}
    (h : Frame l l' lo hi) (hp : l'.Perm l) (hs : SortedPairwise lt (seg l' lo hi))
    (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1) (h3 : hi ≤ (l.length : Int)) :
    WindowOutcome lt false l l' lo hi := by
  refine ⟨l.take (lo - 1).toNat, seg l lo hi, l.drop hi.toNat, seg l' lo hi,
    list_split3 l h1 h2 h3, ?_, ?_, ?_, ⟨h.seg_perm hp h1 h2 h3, hs, fun h => by cases h⟩⟩
  · rw [List.length_take, Nat.min_eq_left (by omega)]; omega
  · unfold seg; rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]; omega
  · have e' := list_split3 l' h1 h2 (by rw [h.1]; exact h3)
    rw [h.take_eq h1, h.drop_eq (by omega)] at e'
    exact e'

end Pointwise

/-! ## Legacy `QuickSort` on any storage -/

section LegacyQuick

variable {V α : Type} {S : VectorStorage V α} {E : V → List α}

theorem scanLeft_succ (lt : α → α → Bool) (v : V) (p : α) (fuel : Nat) (i : Int) (x : α) :
    partitionScanLeft (storageQuickOps S (pureCompare lt)) v p () (fuel + 1) i x =
      if lt x p then (do
        let x' ← liftSortJl (S.getindex v (i + 1))
        partitionScanLeft (storageQuickOps S (pureCompare lt)) v p () fuel (i + 1) x')
      else pure (i, x) := rfl

theorem scanRight_succ (lt : α → α → Bool) (v : V) (p : α) (fuel : Nat) (j : Int) (x : α) :
    partitionScanRight (storageQuickOps S (pureCompare lt)) v p () (fuel + 1) j x =
      if lt p x then (do
        let x' ← liftSortJl (S.getindex v (j - 1))
        partitionScanRight (storageQuickOps S (pureCompare lt)) v p () fuel (j - 1) x')
      else pure (j, x) := rfl

theorem partLoop_succ (lt : α → α → Bool) (lo hi : Int) (p : α) (fuel : Nat) (v : V)
    (i j : Int) :
    partitionVectorLoop (storageQuickOps S (pureCompare lt)) lo hi p () (fuel + 1) v i j = (do
      let x0 ← liftSortJl (S.getindex v (i + 1))
      let (i2, x2) ← partitionScanLeft (storageQuickOps S (pureCompare lt)) v p ()
        ((hi - (i + 1)).toNat + 2) (i + 1) x0
      let y0 ← liftSortJl (S.getindex v (j - 1))
      let (j2, y2) ← partitionScanRight (storageQuickOps S (pureCompare lt)) v p ()
        ((j - 1 - lo).toNat + 2) (j - 1) y0
      if !decide (i2 < j2) then
        pure (v, j2)
      else
        let v ← liftSortJl (S.setindex v i2 y2)
        let v ← liftSortJl (S.setindex v j2 x2)
        partitionVectorLoop (storageQuickOps S (pureCompare lt)) lo hi p () fuel v i2 j2) := rfl

theorem partitionVector_eq (lt : α → α → Bool) (v : V) (lo hi : Int) :
    partitionVector (storageQuickOps S (pureCompare lt)) v lo hi () = (do
      let (v1, p) ← selectPivot (storageQuickOps S (pureCompare lt)) v lo hi ()
      let (v2, j) ← partitionVectorLoop (storageQuickOps S (pureCompare lt)) lo hi p ()
        ((hi - lo).toNat + 2) v1 lo hi
      let r ← liftSortJl (S.getindex v2 j)
      let v3 ← liftSortJl (S.setindex v2 j p)
      let v4 ← liftSortJl (S.setindex v3 lo r)
      pure (v4, j)) := rfl

theorem selectPivot_eq (lt : α → α → Bool) (v : V) (lo hi : Int) :
    selectPivot (storageQuickOps S (pureCompare lt)) v lo hi () = (do
      let a ← liftSortJl (S.getindex v lo)
      let b ← liftSortJl (S.getindex v (lo + (hi - lo) / 2))
      let v ← if lt a b then do
          let v ← liftSortJl (S.setindex v lo b)
          liftSortJl (S.setindex v (lo + (hi - lo) / 2) a)
        else pure v
      let c ← liftSortJl (S.getindex v hi)
      let x ← liftSortJl (S.getindex v lo)
      let v ← if lt c x then do
          let y ← liftSortJl (S.getindex v (lo + (hi - lo) / 2))
          if lt c y then do
            let v ← liftSortJl (S.setindex v hi x)
            let v ← liftSortJl (S.setindex v lo y)
            liftSortJl (S.setindex v (lo + (hi - lo) / 2) c)
          else do
            let v ← liftSortJl (S.setindex v hi x)
            liftSortJl (S.setindex v lo c)
        else pure v
      let p ← liftSortJl (S.getindex v lo)
      pure (v, p)) := rfl

theorem quickLoop_succ (lt : α → α → Bool) (fuel : Nat) (v : V) (lo hi : Int) :
    quickSortRangeLoop (storageQuickOps S (pureCompare lt)) () (fuel + 1) v lo hi =
      if decide (lo < hi) then
        if (hi - lo).toNat ≤ 20 then storageInsertion S (pureCompare lt) v lo hi
        else (do
          let (v1, j) ← partitionVector (storageQuickOps S (pureCompare lt)) v lo hi ()
          if (j - lo).toNat < (hi - j).toNat then do
            let v2 ← if decide (lo < j - 1) then
                quickSortRangeLoop (storageQuickOps S (pureCompare lt)) () fuel v1 lo (j - 1)
              else pure v1
            quickSortRangeLoop (storageQuickOps S (pureCompare lt)) () fuel v2 (j + 1) hi
          else do
            let v2 ← if decide (j + 1 < hi) then
                quickSortRangeLoop (storageQuickOps S (pureCompare lt)) () fuel v1 (j + 1) hi
              else pure v1
            quickSortRangeLoop (storageQuickOps S (pureCompare lt)) () fuel v2 lo (j - 1))
      else pure v := rfl

theorem scanLeft_spec (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (v : V) (p : α) (s : Int) (hs1 : 1 ≤ s) (hsn : s ≤ ((E v).length : Int))
    (hstop : ∀ y, posAt (E v) s = some y → lt y p = false) :
    ∀ (fuel : Nat) (i : Int) (x : α), 1 ≤ i → i ≤ s → s - i < fuel → posAt (E v) i = some x →
      ∃ i' x', partitionScanLeft (storageQuickOps S (pureCompare lt)) v p () fuel i x =
        .ok (i', x') ∧
        i ≤ i' ∧ i' ≤ s ∧ posAt (E v) i' = some x' ∧ lt x' p = false ∧
        ∀ k y, i ≤ k → k < i' → posAt (E v) k = some y → lt y p = true
  | 0, i, x, _, his, hf, _ => by omega
  | fuel + 1, i, x, hi1, his, hf, hx => by
    rw [scanLeft_succ]
    by_cases hlt : lt x p = true
    · have his' : i < s := by
        rcases Int.lt_or_eq_of_le his with h | h
        · exact h
        · subst h; rw [hstop x hx] at hlt; cases hlt
      obtain ⟨x2, hx2⟩ := posAt_some (l := E v) (i := i + 1) (by omega) (by omega)
      obtain ⟨i', x', hrun, h1, h2, h3, h4, h5⟩ :=
        scanLeft_spec L hnt v p s hs1 hsn hstop fuel (i + 1) x2 (by omega) (by omega) (by omega) hx2
      refine ⟨i', x', ?_, by omega, h2, h3, h4, ?_⟩
      · rw [if_pos hlt, storage_read_at L (by omega) hx2, liftSortJl_ok, except_bind_ok]
        exact hrun
      · intro k y hk1 hk2 hy
        by_cases hk : k = i
        · subst hk; rw [hx] at hy; cases hy; exact hlt
        · exact h5 k y (by omega) hk2 hy
    · refine ⟨i, x, ?_, Int.le_refl _, his, hx, by simpa using hlt, fun k y h1 h2 _ => by omega⟩
      rw [if_neg hlt]
      rfl

theorem scanRight_spec (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (v : V) (p : α) (s : Int) (hs1 : 1 ≤ s)
    (hstop : ∀ y, posAt (E v) s = some y → lt p y = false) :
    ∀ (fuel : Nat) (j : Int) (x : α), s ≤ j → j - s < fuel → posAt (E v) j = some x →
      ∃ j' x', partitionScanRight (storageQuickOps S (pureCompare lt)) v p () fuel j x =
        .ok (j', x') ∧
        s ≤ j' ∧ j' ≤ j ∧ posAt (E v) j' = some x' ∧ lt p x' = false ∧
        ∀ k y, j' < k → k ≤ j → posAt (E v) k = some y → lt p y = true
  | 0, j, x, hsj, hf, _ => by omega
  | fuel + 1, j, x, hsj, hf, hx => by
    rw [scanRight_succ]
    by_cases hlt : lt p x = true
    · have hsj' : s < j := by
        rcases Int.lt_or_eq_of_le hsj with h | h
        · exact h
        · subst h; rw [hstop x hx] at hlt; cases hlt
      have hjn : j ≤ ((E v).length : Int) := by
        unfold posAt at hx
        have := (List.getElem?_eq_some_iff.1 hx).1
        omega
      obtain ⟨x2, hx2⟩ := posAt_some (l := E v) (i := j - 1) (by omega) (by omega)
      obtain ⟨j', x', hrun, h1, h2, h3, h4, h5⟩ :=
        scanRight_spec L hnt v p s hs1 hstop fuel (j - 1) x2 (by omega) (by omega) hx2
      refine ⟨j', x', ?_, h1, by omega, h3, h4, ?_⟩
      · rw [if_pos hlt, storage_read_at L (by omega) hx2, liftSortJl_ok, except_bind_ok]
        exact hrun
      · intro k y hk1 hk2 hy
        by_cases hk : k = j
        · subst hk; rw [hx] at hy; cases hy; exact hlt
        · exact h5 k y hk1 (by omega) hy
    · refine ⟨j, x, ?_, hsj, Int.le_refl _, hx, by simpa using hlt, fun k y h1 h2 _ => by omega⟩
      rw [if_neg hlt]
      rfl

/-- Invariant of the Hoare partition loop: the pivot sits at `lo`, everything in `lo+1:i` is
not above it and everything in `j:hi` is not below it. -/
structure PartInv (lt : α → α → Bool) (l : List α) (p : α) (lo hi i j : Int) : Prop where
  lo1 : 1 ≤ lo
  hin : hi ≤ (l.length : Int)
  loi : lo ≤ i
  ij : i < j
  jhi : j ≤ hi
  piv : posAt l lo = some p
  left : ∀ k y, lo < k → k ≤ i → posAt l k = some y → lt p y = false
  right : ∀ k y, j ≤ k → k ≤ hi → posAt l k = some y → lt y p = false

theorem partLoop_spec (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (lo hi : Int) (p : α) :
    ∀ (fuel : Nat) (v : V) (i j : Int), PartInv lt (E v) p lo hi i j → j - i < fuel →
      ∃ v' j', partitionVectorLoop (storageQuickOps S (pureCompare lt)) lo hi p () fuel v i j =
        .ok (v', j') ∧
        (E v').Perm (E v) ∧ Frame (E v) (E v') lo hi ∧ lo ≤ j' ∧ j' < hi ∧
        posAt (E v') lo = some p ∧
        (∀ k y, lo < k → k ≤ j' → posAt (E v') k = some y → lt p y = false) ∧
        (∀ k y, j' < k → k ≤ hi → posAt (E v') k = some y → lt y p = false)
  | 0, v, i, j, hI, hf => by have := hI.ij; omega
  | fuel + 1, v, i, j, hI, hf => by
    have hlo1 := hI.lo1
    have hhin := hI.hin
    have hloi := hI.loi
    have hij := hI.ij
    have hjhi := hI.jhi
    rw [partLoop_succ]
    obtain ⟨x0, hx0⟩ := posAt_some (l := E v) (i := i + 1) (by omega) (by omega)
    obtain ⟨yj, hyj⟩ := posAt_some (l := E v) (i := j) (by omega) (by omega)
    obtain ⟨i2, x2, hrunL, hi2a, hi2b, hx2, hx2p, hscanL⟩ :=
      scanLeft_spec L hnt v p j (by omega) (by omega) (fun y hy => hI.right j y (Int.le_refl _) hjhi hy)
        ((hi - (i + 1)).toNat + 2) (i + 1) x0 (by omega) (by omega) (by omega) hx0
    rw [storage_read_at L (by omega) hx0, liftSortJl_ok, except_bind_ok, hrunL, except_bind_ok]
    dsimp only
    -- the right scan stops at `i2 - 1` at the latest
    have hstopR : ∀ y, posAt (E v) (i2 - 1) = some y → lt p y = false := by
      intro y hy
      by_cases hc : i2 - 1 = lo
      · rw [hc, hI.piv] at hy; cases hy; exact hnt.1 p
      · by_cases hc2 : i2 - 1 ≤ i
        · exact hI.left (i2 - 1) y (by omega) hc2 hy
        · exact negTransOrder_asymm hnt (hscanL (i2 - 1) y (by omega) (by omega) hy)
    obtain ⟨y0, hy0⟩ := posAt_some (l := E v) (i := j - 1) (by omega) (by omega)
    obtain ⟨j2, y2, hrunR, hj2a, hj2b, hy2, hy2p, hscanR⟩ :=
      scanRight_spec L hnt v p (i2 - 1) (by omega) hstopR ((j - 1 - lo).toNat + 2) (j - 1) y0
        (by omega) (by omega) hy0
    rw [storage_read_at L (by omega) hy0, liftSortJl_ok, except_bind_ok, hrunR, except_bind_ok]
    dsimp only
    by_cases hcross : i2 < j2
    · -- swap and continue
      rw [if_neg (by simp [hcross])]
      obtain ⟨v1, hw1, hv1⟩ := L.setindex_ok v i2 y2 (by omega) (by omega)
      obtain ⟨v2, hw2, hv2⟩ := L.setindex_ok v1 j2 x2 (by omega)
        (by rw [hv1, List.length_set]; omega)
      have hlen2 : (E v2).length = (E v).length := by rw [hv2, hv1]; simp
      have hpos2 : ∀ k, 1 ≤ k → posAt (E v2) k =
          if k = j2 then some x2 else if k = i2 then some y2 else posAt (E v) k := by
        intro k hk
        rw [hv2, posAt_set hk (by omega) (by rw [hv1, List.length_set]; omega), hv1,
          posAt_set hk (by omega) (by omega)]
      have hI2 : PartInv lt (E v2) p lo hi i2 j2 := by
        refine ⟨hlo1, by omega, by omega, hcross, by omega, ?_, ?_, ?_⟩
        · rw [hpos2 lo hlo1, if_neg (by omega), if_neg (by omega)]; exact hI.piv
        · intro k y hk1 hk2 hy
          rw [hpos2 k (by omega), if_neg (by omega)] at hy
          by_cases hki : k = i2
          · rw [if_pos hki] at hy; cases hy; exact hy2p
          · rw [if_neg hki] at hy
            by_cases hk3 : k ≤ i
            · exact hI.left k y hk1 hk3 hy
            · exact negTransOrder_asymm hnt (hscanL k y (by omega) (by omega) hy)
        · intro k y hk1 hk2 hy
          rw [hpos2 k (by omega)] at hy
          by_cases hkj : k = j2
          · rw [if_pos hkj] at hy; cases hy; exact hx2p
          · rw [if_neg hkj, if_neg (by omega)] at hy
            by_cases hk3 : j ≤ k
            · exact hI.right k y hk3 hk2 hy
            · exact negTransOrder_asymm hnt (hscanR k y (by omega) (by omega) hy)
      obtain ⟨v', j', hrun, hp, hfr, h1, h2, h3, h4, h5⟩ :=
        partLoop_spec L hnt lo hi p fuel v2 i2 j2 hI2 (by omega)
      refine ⟨v', j', ?_, ?_, ?_, h1, h2, h3, h4, h5⟩
      · rw [hw1, liftSortJl_ok, except_bind_ok, hw2, liftSortJl_ok, except_bind_ok]
        exact hrun
      · refine hp.trans ?_
        rw [hv2, hv1]; exact perm_swap_at hx2 hy2
      · refine Frame.trans ?_ hfr
        rw [hv2, hv1]
        exact (frame_set y2 (by omega) (by omega) hlo1 (by omega)).trans
          (frame_set x2 (by omega) (by omega) hlo1 (by simp; omega))
    · -- the scans crossed: stop
      rw [if_pos (by simp; omega)]
      refine ⟨v, j2, rfl, List.Perm.refl _, Frame.refl _ _ _, by omega, by omega, hI.piv, ?_, ?_⟩
      · intro k y hk1 hk2 hy
        by_cases hk3 : k ≤ i
        · exact hI.left k y hk1 hk3 hy
        · by_cases hk4 : k < i2
          · exact negTransOrder_asymm hnt (hscanL k y (by omega) hk4 hy)
          · have hk5 : k = j2 := by omega
            subst hk5; rw [hy2] at hy; cases hy; exact hy2p
      · intro k y hk1 hk2 hy
        by_cases hk3 : j ≤ k
        · exact hI.right k y hk3 hk2 hy
        · exact negTransOrder_asymm hnt (hscanR k y hk1 (by omega) hy)

theorem selectPivot_spec (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (v : V) (lo hi : Int) (h1 : 1 ≤ lo) (h2 : lo + 2 ≤ hi) (h3 : hi ≤ ((E v).length : Int)) :
    ∃ v' p c, selectPivot (storageQuickOps S (pureCompare lt)) v lo hi () = .ok (v', p) ∧
      (E v').Perm (E v) ∧ Frame (E v) (E v') lo hi ∧ posAt (E v') lo = some p ∧
      posAt (E v') hi = some c ∧ lt c p = false := by
  rw [selectPivot_eq]
  have hmi1 : lo < lo + (hi - lo) / 2 := by omega
  have hmi2 : lo + (hi - lo) / 2 < hi := by omega
  generalize hm : lo + (hi - lo) / 2 = m at hmi1 hmi2 ⊢
  obtain ⟨a, ha⟩ := posAt_some (l := E v) (i := lo) h1 (by omega)
  obtain ⟨b, hb⟩ := posAt_some (l := E v) (i := m) (by omega) (by omega)
  rw [storage_read_at L h1 ha, liftSortJl_ok, except_bind_ok,
    storage_read_at L (by omega) hb, liftSortJl_ok, except_bind_ok]
  -- the second comparison, for any vector produced by the first one
  have rest : ∀ (v1 : V) (x y : α), (E v1).Perm (E v) → Frame (E v) (E v1) lo hi →
      posAt (E v1) lo = some x → posAt (E v1) m = some y → lt x y = false →
      ∃ v' p c, (do
          let c ← liftSortJl (S.getindex v1 hi)
          let x ← liftSortJl (S.getindex v1 lo)
          let v ← if lt c x then do
              let y ← liftSortJl (S.getindex v1 m)
              if lt c y then do
                let v ← liftSortJl (S.setindex v1 hi x)
                let v ← liftSortJl (S.setindex v lo y)
                liftSortJl (S.setindex v m c)
              else do
                let v ← liftSortJl (S.setindex v1 hi x)
                liftSortJl (S.setindex v lo c)
            else pure v1
          let p ← liftSortJl (S.getindex v lo)
          pure (v, p) : SortResult (V × α)) = .ok (v', p) ∧
        (E v').Perm (E v) ∧ Frame (E v) (E v') lo hi ∧ posAt (E v') lo = some p ∧
        posAt (E v') hi = some c ∧ lt c p = false := by
    intro v1 x y hp1 hf1 hx hy hxy
    have hlen1 : (E v1).length = (E v).length := hf1.1
    obtain ⟨c, hc⟩ := posAt_some (l := E v1) (i := hi) (by omega) (by omega)
    rw [storage_read_at L (by omega) hc, liftSortJl_ok, except_bind_ok,
      storage_read_at L h1 hx, liftSortJl_ok, except_bind_ok]
    by_cases hcx : lt c x = true
    · rw [if_pos hcx, storage_read_at L (by omega) hy, liftSortJl_ok, except_bind_ok]
      by_cases hcy : lt c y = true
      · rw [if_pos hcy]
        obtain ⟨w1, hw1, hv1⟩ := L.setindex_ok v1 hi x (by omega) (by omega)
        obtain ⟨w2, hw2, hv2⟩ := L.setindex_ok w1 lo y h1 (by rw [hv1]; simp; omega)
        obtain ⟨w3, hw3, hv3⟩ := L.setindex_ok w2 m c (by omega) (by rw [hv2, hv1]; simp; omega)
        have hpw2 : posAt (E w2) lo = some y := by
          rw [hv2, posAt_set h1 h1 (by rw [hv1]; simp; omega), if_pos rfl]
        have hpw3 : posAt (E w3) lo = some y := by
          rw [hv3, posAt_set h1 (by omega) (by rw [hv2, hv1]; simp; omega), if_neg (by omega)]
          exact hpw2
        refine ⟨w3, y, x, ?_, ?_, ?_, hpw3, ?_, hxy⟩
        · rw [hw1, liftSortJl_ok, except_bind_ok, hw2, liftSortJl_ok, except_bind_ok,
            hw3, liftSortJl_ok, except_bind_ok]
          exact (show (do let p ← liftSortJl (S.getindex w3 lo); pure (w3, p) :
              SortResult (V × α)) = .ok (w3, y) by
            rw [storage_read_at L h1 hpw3, liftSortJl_ok]; rfl)
        · -- a 3-cycle is two swaps
          have hs1 : ((E v1).set (hi - 1).toNat x |>.set (lo - 1).toNat c).Perm (E v1) :=
            perm_swap_at hc hx
          have hc' : posAt ((E v1).set (hi - 1).toNat x |>.set (lo - 1).toNat c) lo = some c := by
            rw [posAt_set h1 h1 (by simp; omega), if_pos rfl]
          have hy' : posAt ((E v1).set (hi - 1).toNat x |>.set (lo - 1).toNat c) m = some y := by
            rw [posAt_set (by omega) h1 (by simp; omega), if_neg (by omega),
              posAt_set (by omega) (by omega) (by omega), if_neg (by omega)]
            exact hy
          have hs2 := perm_swap_at hc' hy'
          rw [List.set_set] at hs2
          rw [hv3, hv2, hv1]
          exact (hs2.trans hs1).trans hp1
        · rw [hv3, hv2, hv1]
          refine hf1.trans ((frame_set x (by omega) (Int.le_refl _) h1 (by omega)).trans
            ((frame_set y (Int.le_refl _) (by omega) h1 (by simp; omega)).trans
            (frame_set c (by omega) (by omega) h1 (by simp; omega))))
        · rw [hv3, posAt_set (by omega) (by omega) (by rw [hv2, hv1]; simp; omega),
            if_neg (by omega), hv2, posAt_set (by omega) h1 (by rw [hv1]; simp; omega),
            if_neg (by omega), hv1, posAt_set (by omega) (by omega) (by omega), if_pos rfl]
      · rw [if_neg hcy]
        obtain ⟨w1, hw1, hv1⟩ := L.setindex_ok v1 hi x (by omega) (by omega)
        obtain ⟨w2, hw2, hv2⟩ := L.setindex_ok w1 lo c h1 (by rw [hv1]; simp; omega)
        have hpw2 : posAt (E w2) lo = some c := by
          rw [hv2, posAt_set h1 h1 (by rw [hv1]; simp; omega), if_pos rfl]
        refine ⟨w2, c, x, ?_, ?_, ?_, hpw2, ?_, negTransOrder_asymm hnt hcx⟩
        · rw [hw1, liftSortJl_ok, except_bind_ok, hw2, liftSortJl_ok, except_bind_ok]
          exact (show (do let p ← liftSortJl (S.getindex w2 lo); pure (w2, p) :
              SortResult (V × α)) = .ok (w2, c) by
            rw [storage_read_at L h1 hpw2, liftSortJl_ok]; rfl)
        · rw [hv2, hv1]; exact (perm_swap_at hc hx).trans hp1
        · rw [hv2, hv1]
          exact hf1.trans ((frame_set x (by omega) (Int.le_refl _) h1 (by omega)).trans
            (frame_set c (Int.le_refl _) (by omega) h1 (by simp; omega)))
        · rw [hv2, posAt_set (by omega) h1 (by rw [hv1]; simp; omega), if_neg (by omega), hv1,
            posAt_set (by omega) (by omega) (by omega), if_pos rfl]
    · rw [if_neg hcx]
      refine ⟨v1, x, c, ?_, hp1, hf1, hx, hc, by simpa using hcx⟩
      rw [except_pure_ok, except_bind_ok]
      exact (show (do let p ← liftSortJl (S.getindex v1 lo); pure (v1, p) :
          SortResult (V × α)) = .ok (v1, x) by
        rw [storage_read_at L h1 hx, liftSortJl_ok]; rfl)
  -- the first comparison
  by_cases hab : lt a b = true
  · obtain ⟨w1, hw1, hv1⟩ := L.setindex_ok v lo b h1 (by omega)
    obtain ⟨w2, hw2, hv2⟩ := L.setindex_ok w1 m a (by omega) (by rw [hv1]; simp; omega)
    rw [if_pos hab, hw1, liftSortJl_ok, except_bind_ok, hw2, liftSortJl_ok, except_bind_ok]
    obtain ⟨v', p, c, hrun, hrest⟩ := rest w2 b a
      (by rw [hv2, hv1]; exact perm_swap_at ha hb)
      (by rw [hv2, hv1]
          exact (frame_set b (Int.le_refl _) (by omega) h1 (by omega)).trans
            (frame_set a (by omega) (by omega) h1 (by simp; omega)))
      (by rw [hv2, posAt_set h1 (by omega) (by rw [hv1]; simp; omega), if_neg (by omega), hv1,
            posAt_set h1 h1 (by omega), if_pos rfl])
      (by rw [hv2, posAt_set (by omega) (by omega) (by rw [hv1]; simp; omega), if_pos rfl])
      (negTransOrder_asymm hnt hab)
    exact ⟨v', p, c, hrun, hrest⟩
  · rw [if_neg hab, except_pure_ok, except_bind_ok]
    obtain ⟨v', p, c, hrun, hrest⟩ := rest v a b (List.Perm.refl _) (Frame.refl _ _ _) ha hb
      (by simpa using hab)
    exact ⟨v', p, c, hrun, hrest⟩

theorem partitionVector_spec (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (v : V) (lo hi : Int) (h1 : 1 ≤ lo) (h2 : lo + 2 ≤ hi) (h3 : hi ≤ ((E v).length : Int)) :
    ∃ v' j p, partitionVector (storageQuickOps S (pureCompare lt)) v lo hi () = .ok (v', j) ∧
      (E v').Perm (E v) ∧ Frame (E v) (E v') lo hi ∧ lo ≤ j ∧ j ≤ hi ∧
      posAt (E v') j = some p ∧
      (∀ y ∈ seg (E v') lo (j - 1), lt p y = false) ∧
      (∀ y ∈ seg (E v') (j + 1) hi, lt y p = false) := by
  rw [partitionVector_eq]
  obtain ⟨v1, p, c, hsel, hp1, hf1, hpl, hpc, hcp⟩ := selectPivot_spec L hnt v lo hi h1 h2 h3
  rw [hsel, except_bind_ok]
  dsimp only
  have hlen1 : (E v1).length = (E v).length := hf1.1
  have hI : PartInv lt (E v1) p lo hi lo hi := by
    refine ⟨h1, by omega, Int.le_refl _, by omega, Int.le_refl _, hpl,
      fun k y hk1 hk2 _ => by omega, ?_⟩
    intro k y hk1 hk2 hy
    rw [show k = hi by omega, hpc] at hy; cases hy; exact hcp
  obtain ⟨v2, j, hloop, hp2, hf2, hj1, hj2, hpl2, hleft, hright⟩ :=
    partLoop_spec L hnt lo hi p ((hi - lo).toNat + 2) v1 lo hi hI (by omega)
  rw [hloop, except_bind_ok]
  dsimp only
  have hlen2 : (E v2).length = (E v).length := by rw [hf2.1, hlen1]
  obtain ⟨r, hr⟩ := posAt_some (l := E v2) (i := j) (by omega) (by omega)
  obtain ⟨w3, hw3, hv3⟩ := L.setindex_ok v2 j p (by omega) (by omega)
  obtain ⟨w4, hw4, hv4⟩ := L.setindex_ok w3 lo r h1 (by rw [hv3]; simp; omega)
  rw [storage_read_at L (by omega) hr, liftSortJl_ok, except_bind_ok,
    hw3, liftSortJl_ok, except_bind_ok, hw4, liftSortJl_ok, except_bind_ok]
  have hpos4 : ∀ k, 1 ≤ k → posAt (E w4) k =
      if k = lo then some r else if k = j then some p else posAt (E v2) k := by
    intro k hk
    rw [hv4, posAt_set hk h1 (by rw [hv3]; simp; omega), hv3, posAt_set hk (by omega) (by omega)]
  refine ⟨w4, j, p, rfl, ?_, ?_, hj1, by omega, ?_, ?_, ?_⟩
  · rw [hv4, hv3]; exact ((perm_swap_at hr hpl2).trans hp2).trans hp1
  · rw [hv4, hv3]
    exact hf1.trans (hf2.trans ((frame_set p hj1 (by omega) h1 (by omega)).trans
      (frame_set r (Int.le_refl _) (by omega) h1 (by simp; omega))))
  · rw [hpos4 j (by omega)]
    by_cases hjl : j = lo
    · rw [if_pos hjl]; rw [hjl, hpl2] at hr; cases hr; rfl
    · rw [if_neg hjl, if_pos rfl]
  · intro y hy
    obtain ⟨k, hk1, hk2, hk⟩ := (mem_seg h1).1 hy
    rw [hpos4 k (by omega)] at hk
    by_cases hkl : k = lo
    · rw [if_pos hkl] at hk; cases hk
      exact hleft j r (by omega) (Int.le_refl _) hr
    · rw [if_neg hkl, if_neg (show ¬ k = j by omega)] at hk
      exact hleft k y (by omega) (by omega) hk
  · intro y hy
    obtain ⟨k, hk1, hk2, hk⟩ := (mem_seg (by omega)).1 hy
    rw [hpos4 k (by omega), if_neg (by omega), if_neg (by omega)] at hk
    exact hright k y (by omega) hk2 hk

theorem quickLoop_spec (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt) :
    ∀ (fuel : Nat) (v : V) (lo hi : Int), 1 ≤ lo → hi ≤ ((E v).length : Int) → hi - lo < fuel →
      ∃ v', quickSortRangeLoop (storageQuickOps S (pureCompare lt)) () fuel v lo hi = .ok v' ∧
        (E v').Perm (E v) ∧ Frame (E v) (E v') lo hi ∧ SortedPairwise lt (seg (E v') lo hi) := by
  intro fuel
  induction fuel with
  | zero =>
    intro v lo hi h1 h3 hf
    refine ⟨v, ?_, List.Perm.refl _, Frame.refl _ _ _, seg_short_sorted lt _ (by omega)⟩
    simp [quickSortRangeLoop, storageQuickOps, pure, Except.pure, show ¬ lo < hi by omega]
  | succ fuel ih =>
    intro v lo hi h1 h3 hf
    rw [quickLoop_succ]
    by_cases hlh : lo < hi
    · rw [if_pos (by simpa using hlh)]
      by_cases hsmall : (hi - lo).toNat ≤ 20
      · rw [if_pos hsmall]
        obtain ⟨P, W, Q, hv, hP, hW⟩ := window_split (E v) h1 (by omega) h3
        obtain ⟨v', hrun, hv'⟩ := storageInsertion_spec L hnt v lo hi P W Q h1 hv hP hW
        refine ⟨v', hrun, ?_, ?_, ?_⟩
        · rw [hv', hv]
          exact List.Perm.append_right _ (List.Perm.append_left _ (perm_sortRef lt W).symm)
        · rw [hv', hv]; exact frame_of_decomp hP (length_sortRef lt W) hW
        · rw [hv', seg_decomp hP (by rw [length_sortRef]; exact hW)]
          exact sorted_sortRef hnt W
      · rw [if_neg hsmall]
        obtain ⟨v1, j, p, hpart, hp1, hf1, hj1, hj2, hpj, hL, hR⟩ :=
          partitionVector_spec L hnt v lo hi h1 (by omega) h3
        rw [hpart, except_bind_ok]
        dsimp only
        have hlen1 : (E v1).length = (E v).length := hf1.1
        -- sorting one side through the guarded recursive call
        have maybe : ∀ (w : V) (a b : Int) (K : V → SortResult V), 1 ≤ a →
            b ≤ ((E w).length : Int) → b - a < fuel →
            ∃ w', (if decide (a < b) then (do
                let w2 ← quickSortRangeLoop (storageQuickOps S (pureCompare lt)) () fuel w a b
                K w2) else (do let w2 ← pure w; K w2)) = K w' ∧
              (E w').Perm (E w) ∧ Frame (E w) (E w') a b ∧
              SortedPairwise lt (seg (E w') a b) := by
          intro w a b K ha hb hab
          by_cases hc : a < b
          · rw [if_pos (by simpa using hc)]
            obtain ⟨w', hrun, hrest⟩ := ih w a b ha hb hab
            rw [hrun, except_bind_ok]
            exact ⟨w', rfl, hrest⟩
          · rw [if_neg (by simpa using hc), except_pure_ok, except_bind_ok]
            exact ⟨w, rfl, List.Perm.refl _, Frame.refl _ _ _, seg_short_sorted lt _ (by omega)⟩
        -- combining the two sorted sides around the pivot
        have combine : ∀ (w2 w3 : V), Frame (E v1) (E w2) lo (j - 1) →
            (E w2).Perm (E v1) → Frame (E w2) (E w3) (j + 1) hi → (E w3).Perm (E w2) →
            SortedPairwise lt (seg (E w2) lo (j - 1)) →
            SortedPairwise lt (seg (E w3) (j + 1) hi) →
            SortedPairwise lt (seg (E w3) lo hi) := by
          intro w2 w3 f2 p2 f3 p3 s2 s3
          have hl2 : (E w2).length = (E v).length := by rw [f2.1, hlen1]
          have hpj3 : posAt (E w3) j = some p := by
            rw [f3.2 j (by omega) (Or.inl (by omega)), f2.2 j (by omega) (Or.inr (by omega))]
            exact hpj
          rw [seg_pivot (E w3) h1 hj1 hj2 hpj3, f3.seg_eq h1 (Or.inl (by omega))]
          have hperm2 := f2.seg_perm p2 h1 (by omega) (by omega)
          have hperm3 := f3.seg_perm p3 (by omega) (by omega) (by omega)
          rw [f2.seg_eq (by omega) (Or.inr (by omega))] at hperm3
          refine sorted_pivot_append hnt s2 s3 ?_ ?_
          · intro y hy; exact hL y (hperm2.mem_iff.1 hy)
          · intro y hy; exact hR y (hperm3.mem_iff.1 hy)
        by_cases hside : (j - lo).toNat < (hi - j).toNat
        · rw [if_pos hside]
          obtain ⟨w2, hm2, p2, f2, s2⟩ := maybe v1 lo (j - 1)
            (fun v2 => quickSortRangeLoop (storageQuickOps S (pureCompare lt)) () fuel v2
              (j + 1) hi) h1
            (by omega) (by omega)
          rw [hm2]
          have hl2 : (E w2).length = (E v).length := by rw [f2.1, hlen1]
          obtain ⟨w3, hm3, p3, f3, s3⟩ := ih w2 (j + 1) hi (by omega) (by omega) (by omega)
          refine ⟨w3, hm3, (p3.trans p2).trans hp1, ?_, combine w2 w3 f2 p2 f3 p3 s2 s3⟩
          exact hf1.trans ((f2.mono (Int.le_refl _) (by omega)).trans
            (f3.mono (by omega) (Int.le_refl _)))
        · rw [if_neg hside]
          obtain ⟨w2, hm2, p2, f2, s2⟩ := maybe v1 (j + 1) hi
            (fun v2 => quickSortRangeLoop (storageQuickOps S (pureCompare lt)) () fuel v2 lo
              (j - 1))
            (by omega) (by omega) (by omega)
          rw [hm2]
          have hl2 : (E w2).length = (E v).length := by rw [f2.1, hlen1]
          obtain ⟨w3, hm3, p3, f3, s3⟩ := ih w2 lo (j - 1) h1 (by omega) (by omega)
          refine ⟨w3, hm3, (p3.trans p2).trans hp1, ?_, ?_⟩
          · exact hf1.trans ((f2.mono (by omega) (Int.le_refl _)).trans
              (f3.mono (Int.le_refl _) (by omega)))
          · -- the right side was sorted first, then the left side
            have hpj3 : posAt (E w3) j = some p := by
              rw [f3.2 j (by omega) (Or.inr (by omega)), f2.2 j (by omega) (Or.inl (by omega))]
              exact hpj
            rw [seg_pivot (E w3) h1 hj1 hj2 hpj3,
              f3.seg_eq (a := j + 1) (b := hi) (by omega) (Or.inr (by omega))]
            have hperm2 := f2.seg_perm p2 (by omega) (by omega) (by omega)
            have hperm3 := f3.seg_perm p3 h1 (by omega) (by omega)
            rw [f2.seg_eq h1 (Or.inl (by omega))] at hperm3
            refine sorted_pivot_append hnt s3 s2 ?_ ?_
            · intro y hy; exact hL y (hperm3.mem_iff.1 hy)
            · intro y hy; exact hR y (hperm2.mem_iff.1 hy)
    · rw [if_neg (by simpa using hlh)]
      exact ⟨v, rfl, List.Perm.refl _, Frame.refl _ _ _, seg_short_sorted lt _ (by omega)⟩

/-- `sort!(v, lo, hi, QuickSort, o)` on any storage obeying the `AbstractVector` laws: for a
valid window it returns a sorted permutation of the window and leaves the rest alone. -/
theorem legacyQuick_window (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (v : V) (lo hi : Int) (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1) (h3 : hi ≤ ((E v).length : Int)) :
    ∃ v', legacyQuickSortBang (storageQuickOps S (pureCompare lt)) v lo hi () = .ok v' ∧
      WindowOutcome lt false (E v) (E v') lo hi := by
  obtain ⟨v', hrun, hp, hf, hs⟩ := quickLoop_spec L hnt ((hi - lo).toNat + 2) v lo hi h1 h3
    (by omega)
  refine ⟨v', ?_, windowOutcome_of_frame hf hp hs h1 h2 h3⟩
  unfold legacyQuickSortBang quickSortRange
  rw [show (storageQuickOps S (pureCompare lt)).checkBounds =
      fun values lo hi => liftSortJl (storageCheckBounds S values lo hi) from rfl]
  dsimp only
  rw [storageCheckBounds_ok L (by omega), liftSortJl_ok, except_bind_ok]
  exact hrun

end LegacyQuick

/-! ## Legacy `MergeSort` on any storage -/

section LegacyMerge

variable {V α : Type} {S : VectorStorage V α} {E : V → List α}

/-- The left-biased merge of two lists: an element of the right list moves ahead only when it
is strictly less than the current left element. -/
def mergeRef (lt : α → α → Bool) : List α → List α → List α
  | [], r => r
  | a :: l, [] => a :: l
  | a :: l, b :: r =>
    if lt b a then b :: mergeRef lt (a :: l) r else a :: mergeRef lt l (b :: r)
termination_by l r => l.length + r.length

theorem mergeRef_nil_left (lt : α → α → Bool) (r : List α) : mergeRef lt [] r = r := by
  rw [mergeRef]

theorem mergeRef_nil_right (lt : α → α → Bool) (l : List α) : mergeRef lt l [] = l := by
  cases l with
  | nil => rw [mergeRef]
  | cons a l => rw [mergeRef]

theorem mergeRef_cons_cons (lt : α → α → Bool) (a b : α) (l r : List α) :
    mergeRef lt (a :: l) (b :: r) =
      if lt b a then b :: mergeRef lt (a :: l) r else a :: mergeRef lt l (b :: r) := by
  rw [mergeRef]

theorem mergeRef_props {lt : α → α → Bool} (hnt : NegTransOrder lt) :
    ∀ (n : Nat) (l r : List α), l.length + r.length ≤ n →
      (mergeRef lt l r).Perm (l ++ r) ∧
      (SortedPairwise lt l → SortedPairwise lt r → SortedPairwise lt (mergeRef lt l r)) ∧
      (SortedPairwise lt l → ∀ x, (mergeRef lt l r).filter (sameClass lt x) =
        l.filter (sameClass lt x) ++ r.filter (sameClass lt x)) := by
  intro n
  induction n with
  | zero =>
    intro l r h
    have hl : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hr : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hl hr
    rw [mergeRef_nil_left]
    exact ⟨List.Perm.refl _, fun _ h => h, fun _ _ => rfl⟩
  | succ n ih =>
    intro l r h
    match l, r with
    | [], r =>
      rw [mergeRef_nil_left]
      exact ⟨List.Perm.refl _, fun _ h => h, fun _ _ => rfl⟩
    | a :: l, [] =>
      rw [mergeRef_nil_right]
      exact ⟨by simp, fun h _ => h, fun _ _ => by simp⟩
    | a :: l, b :: r =>
      rw [mergeRef_cons_cons]
      by_cases hba : lt b a = true
      · rw [if_pos hba]
        obtain ⟨hp, hs, hst⟩ := ih (a :: l) r (by simp at h ⊢; omega)
        refine ⟨?_, ?_, ?_⟩
        · refine (List.Perm.cons b hp).trans ?_
          simpa using (List.perm_middle (a := b) (l₁ := a :: l) (l₂ := r)).symm
        · intro hl hr
          refine List.Pairwise.cons ?_ (hs hl (List.pairwise_cons.1 hr).2)
          intro z hz
          rcases List.mem_append.1 (hp.mem_iff.1 hz) with hz | hz
          · rcases List.mem_cons.1 hz with rfl | hz
            · exact negTransOrder_asymm hnt hba
            · exact negTransOrder_not_trans hnt ((List.pairwise_cons.1 hl).1 z hz)
                (negTransOrder_asymm hnt hba)
          · exact (List.pairwise_cons.1 hr).1 z hz
        · intro hl x
          by_cases hxb : sameClass lt x b = true
          · have hnone : (a :: l).filter (sameClass lt x) = [] := by
              rw [List.filter_eq_nil_iff]
              intro z hz hxz
              have hbz : sameClass lt b z = true :=
                sameClass_trans hnt (by rw [sameClass_comm]; exact hxb) hxz
              have hza : lt z a = false := by
                rcases List.mem_cons.1 hz with rfl | hz
                · exact hnt.1 z
                · exact (List.pairwise_cons.1 hl).1 z hz
              rw [sameClass_iff, negTransOrder_lt_of_lt_of_nlt hnt hba hza] at hbz
              exact Bool.noConfusion hbz.1
            rw [List.filter_cons_of_pos hxb, hst hl x, hnone, List.filter_cons_of_pos hxb,
              List.nil_append, List.nil_append]
          · rw [List.filter_cons_of_neg hxb, hst hl x, List.filter_cons_of_neg hxb]
      · rw [if_neg hba]
        have hba' : lt b a = false := by simpa using hba
        obtain ⟨hp, hs, hst⟩ := ih l (b :: r) (by simp at h ⊢; omega)
        refine ⟨?_, ?_, ?_⟩
        · simpa using List.Perm.cons a hp
        · intro hl hr
          refine List.Pairwise.cons ?_ (hs (List.pairwise_cons.1 hl).2 hr)
          intro z hz
          rcases List.mem_append.1 (hp.mem_iff.1 hz) with hz | hz
          · exact (List.pairwise_cons.1 hl).1 z hz
          · rcases List.mem_cons.1 hz with rfl | hz
            · exact hba'
            · exact negTransOrder_not_trans hnt ((List.pairwise_cons.1 hr).1 z hz) hba'
        · intro hl x
          by_cases hxa : sameClass lt x a = true
          · rw [List.filter_cons_of_pos hxa, List.filter_cons_of_pos hxa,
              hst (List.pairwise_cons.1 hl).2 x, List.cons_append]
          · rw [List.filter_cons_of_neg hxa, List.filter_cons_of_neg hxa,
              hst (List.pairwise_cons.1 hl).2 x]

theorem merge_outcome {lt : α → α → Bool} (hnt : NegTransOrder lt) {WL WR WL' WR' : List α}
    (hL : SortOutcome lt true WL WL') (hR : SortOutcome lt true WR WR') :
    SortOutcome lt true (WL ++ WR) (mergeRef lt WL' WR') := by
  obtain ⟨hp, hs, hst⟩ := mergeRef_props hnt (WL'.length + WR'.length) WL' WR' (Nat.le_refl _)
  refine ⟨hp.trans (List.Perm.append hL.1 hR.1), hs hL.2.1 hR.2.1, fun _ x => ?_⟩
  rw [hst hL.2.1 x, List.filter_append, hL.2.2 rfl x, hR.2.2 rfl x]

variable [Inhabited α]
theorem copyLoop_succ (lt : α → α → Bool) (v : V) (m : Int) (fuel : Nat) (t : Array α)
    (i j : Int) :
    mergeCopyTempLoop (storageMergeOps S (pureCompare lt)) v m (fuel + 1) t i j =
      if decide (j ≤ m) then (do
        let value ← liftSortJl (S.getindex v j)
        let t ← liftSortJl (arrayWrite t i value)
        mergeCopyTempLoop (storageMergeOps S (pureCompare lt)) v m fuel t (i + 1) (j + 1))
      else pure (t, j) := rfl

theorem bothLoop_succ (lt : α → α → Bool) (t : Array α) (hi : Int) (fuel : Nat) (v : V)
    (i j k : Int) :
    mergeBothLoop (storageMergeOps S (pureCompare lt)) t hi () (fuel + 1) v i j k =
      if (decide (k < j) && decide (j ≤ hi)) = true then (do
        let right ← liftSortJl (S.getindex v j)
        let left ← liftSortJl (arrayRead t i)
        if lt right left then do
          let v ← liftSortJl (S.setindex v k right)
          mergeBothLoop (storageMergeOps S (pureCompare lt)) t hi () fuel v i (j + 1) (k + 1)
        else do
          let v ← liftSortJl (S.setindex v k left)
          mergeBothLoop (storageMergeOps S (pureCompare lt)) t hi () fuel v (i + 1) j (k + 1))
      else pure (v, i, j, k) := rfl

theorem leftLoop_succ (lt : α → α → Bool) (t : Array α) (j : Int) (fuel : Nat) (v : V)
    (i k : Int) :
    mergeLeftLoop (storageMergeOps S (pureCompare lt)) t j (fuel + 1) v i k =
      if decide (k < j) then (do
        let value ← liftSortJl (arrayRead t i)
        let v ← liftSortJl (S.setindex v k value)
        mergeLeftLoop (storageMergeOps S (pureCompare lt)) t j fuel v (i + 1) (k + 1))
      else pure v := rfl

theorem kernel_succ (lt : α → α → Bool) (fuel : Nat) (v : V) (lo hi : Int)
    (temp : Option (Array α)) :
    legacyMergeSortKernelLoop (storageMergeOps S (pureCompare lt)) () () (fuel + 1) v lo hi temp =
      if decide (lo < hi) then
        if (hi - lo).toNat ≤ 20 then storageInsertion S (pureCompare lt) v lo hi
        else (do
          let t0 ← match temp with
            | none => (Except.ok (Array.replicate ((lo + (hi - lo) / 2 - lo).toNat + 1)
                default) : SortResult (Array α))
            | some existing => pure existing
          let t ← if t0.size < (lo + (hi - lo) / 2 - lo).toNat + 1 then
              (Except.ok (t0 ++ Array.replicate ((lo + (hi - lo) / 2 - lo).toNat + 1 - t0.size)
                default) : SortResult (Array α))
            else pure t0
          (Except.ok () : SortResult Unit)
          let v ← legacyMergeSortKernelLoop (storageMergeOps S (pureCompare lt)) () () fuel v lo
            (lo + (hi - lo) / 2) (some t)
          let v ← legacyMergeSortKernelLoop (storageMergeOps S (pureCompare lt)) () () fuel v
            (lo + (hi - lo) / 2 + 1) hi (some t)
          let (t, j) ← mergeCopyTempLoop (storageMergeOps S (pureCompare lt)) v
            (lo + (hi - lo) / 2) ((lo + (hi - lo) / 2 - lo).toNat + 2) t 1 lo
          let (v, i, j, k) ← mergeBothLoop (storageMergeOps S (pureCompare lt)) t hi ()
            ((hi - lo).toNat + 2) v 1 j lo
          mergeLeftLoop (storageMergeOps S (pureCompare lt)) t j ((hi - lo).toNat + 2) v i k)
      else pure v := by
  rw [legacyMergeSortKernelLoop]
  cases temp <;> rfl

theorem array_read_mid {t : Array α} {P B : List α} {z : α} {i : Int}
    (ht : t.toList = P ++ z :: B) (hi : i = (P.length : Int) + 1) : arrayRead t i = .ok z :=
  storage_read_mid arrayStorage_laws (v := t) ht (by omega) (by omega)

theorem array_write_mid {t : Array α} {P B : List α} {z : α} {i : Int} (x : α)
    (ht : t.toList = P ++ z :: B) (hi : i = (P.length : Int) + 1) :
    ∃ t', arrayWrite t i x = .ok t' ∧ t'.toList = P ++ x :: B :=
  storage_write_mid arrayStorage_laws (v := t) x ht (by omega) hi

theorem copyLoop_spec (L : StorageLaws S E) (lt : α → α → Bool) (P R : List α) (lo m : Int)
    (hlo : (P.length : Int) + 1 = lo) :
    ∀ (fuel : Nat) (v : V) (t : Array α) (i j : Int) (C1 C2 D : List α),
      E v = P ++ C1 ++ C2 ++ R → t.toList = C1 ++ D → C2.length ≤ D.length →
      i = (C1.length : Int) + 1 → j = lo + C1.length → m = j + C2.length - 1 →
      C2.length < fuel →
      ∃ t', mergeCopyTempLoop (storageMergeOps S (pureCompare lt)) v m fuel t i j =
        .ok (t', m + 1) ∧
        t'.toList = C1 ++ C2 ++ D.drop C2.length := by
  intro fuel
  induction fuel with
  | zero => intro v t i j C1 C2 D _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro v t i j C1 C2 D hv ht hCD hi hj hm hf
    rw [copyLoop_succ]
    match C2, D, hCD with
    | [], D, _ =>
      rw [if_neg (by simp at hm ⊢; omega)]
      refine ⟨t, ?_, by simpa using ht⟩
      rw [show j = m + 1 by simp at hm; omega]; rfl
    | c :: C2, d :: D, hCD =>
      rw [if_pos (by simp at hm ⊢; omega)]
      have hread : S.getindex v j = .ok c :=
        storage_read_mid L (P := P ++ C1) (B := C2 ++ R) (by rw [hv]; simp [List.append_assoc])
          (by omega) (by simp; omega)
      obtain ⟨t1, hw, ht1⟩ := array_write_mid (P := C1) (B := D) c (by rw [ht]) hi
      rw [hread, liftSortJl_ok, except_bind_ok, hw, liftSortJl_ok, except_bind_ok]
      obtain ⟨t', hrun, ht'⟩ := ih v t1 (i + 1) (j + 1) (C1 ++ [c]) C2 D
        (by rw [hv]; simp [List.append_assoc]) (by rw [ht1]; simp [List.append_assoc])
        (by simp at hCD; omega) (by simp; omega) (by simp; omega) (by simp at hm; omega)
        (by simp at hf; omega)
      exact ⟨t', hrun, by rw [ht']; simp [List.append_assoc]⟩

theorem bothLoop_spec (L : StorageLaws S E) {lt : α → α → Bool} (t : Array α)
    (P Q T2 : List α) (lo hi : Int) (hlo : (P.length : Int) + 1 = lo) :
    ∀ (fuel : Nat) (v : V) (i j k : Int) (M X LL RR T1 : List α),
      E v = P ++ M ++ X ++ RR ++ Q → t.toList = T1 ++ LL ++ T2 → X.length = LL.length →
      i = (T1.length : Int) + 1 → k = lo + M.length → j = k + X.length →
      hi = j + RR.length - 1 → LL.length + RR.length < fuel →
      ∃ v' i' j' k' M' X' LL' RR' T1',
        mergeBothLoop (storageMergeOps S (pureCompare lt)) t hi () fuel v i j k =
          .ok (v', i', j', k') ∧
        E v' = P ++ M' ++ X' ++ RR' ++ Q ∧ t.toList = T1' ++ LL' ++ T2 ∧
        X'.length = LL'.length ∧ i' = (T1'.length : Int) + 1 ∧ k' = lo + M'.length ∧
        j' = k' + X'.length ∧ hi = j' + RR'.length - 1 ∧
        M' ++ mergeRef lt LL' RR' = M ++ mergeRef lt LL RR ∧ (LL' = [] ∨ RR' = []) := by
  intro fuel
  induction fuel with
  | zero => intro v i j k M X LL RR T1 _ _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro v i j k M X LL RR T1 hv ht hX hiT hk hj hhi hf
    rw [bothLoop_succ]
    match LL, RR, X, hX with
    | [], RR, [], _ =>
      rw [if_neg (by simp at hj ⊢; omega)]
      exact ⟨v, i, j, k, M, [], [], RR, T1, rfl, hv, ht, rfl, hiT, hk, hj, hhi, rfl, Or.inl rfl⟩
    | l :: LL, [], X, hX =>
      rw [if_neg (by simp at hhi ⊢; omega)]
      exact ⟨v, i, j, k, M, X, l :: LL, [], T1, rfl, hv, ht, hX, hiT, hk, hj, hhi, rfl,
        Or.inr rfl⟩
    | l :: LL, r :: RR, x0 :: X, hX =>
      have hX' : X.length = LL.length := by simpa using hX
      have hj' : j = k + X.length + 1 := by simp at hj; omega
      have hhi' : hi = j + RR.length := by simp at hhi; omega
      have hf' : LL.length + RR.length + 2 < fuel + 1 := by simp at hf; omega
      rw [if_pos (by simp; omega)]
      have hreadR : S.getindex v j = .ok r :=
        storage_read_mid L (P := P ++ M ++ x0 :: X) (B := RR ++ Q)
          (by rw [hv]; simp [List.append_assoc]) (by omega) (by simp; omega)
      have hreadL : arrayRead t i = .ok l := array_read_mid (P := T1) (B := LL ++ T2)
        (by rw [ht]; simp [List.append_assoc]) hiT
      rw [hreadR, liftSortJl_ok, except_bind_ok, hreadL, liftSortJl_ok, except_bind_ok]
      by_cases hrl : lt r l = true
      · rw [if_pos hrl]
        obtain ⟨v1, hw, hv1⟩ := storage_write_mid L (v := v) (i := k) (P := P ++ M)
          (B := X ++ r :: RR ++ Q) (z := x0) r (by rw [hv]; simp [List.append_assoc])
          (by omega) (by simp; omega)
        rw [hw, liftSortJl_ok, except_bind_ok]
        obtain ⟨v', i', j', k', M', X', LL', RR', T1', hrun, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
          ih v1 i (j + 1) (k + 1) (M ++ [r]) (X ++ [r]) (l :: LL) RR T1
            (by rw [hv1]; simp [List.append_assoc]) ht (by simp; omega) hiT
            (by simp; omega) (by simp; omega) (by omega) (by simp; omega)
        refine ⟨v', i', j', k', M', X', LL', RR', T1', hrun, h1, h2, h3, h4, h5, h6, h7, ?_, h9⟩
        rw [h8, mergeRef_cons_cons, if_pos hrl]; simp
      · rw [if_neg hrl]
        obtain ⟨v1, hw, hv1⟩ := storage_write_mid L (v := v) (i := k) (P := P ++ M)
          (B := X ++ r :: RR ++ Q) (z := x0) l (by rw [hv]; simp [List.append_assoc])
          (by omega) (by simp; omega)
        rw [hw, liftSortJl_ok, except_bind_ok]
        obtain ⟨v', i', j', k', M', X', LL', RR', T1', hrun, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
          ih v1 (i + 1) j (k + 1) (M ++ [l]) X LL (r :: RR) (T1 ++ [l])
            (by rw [hv1]; simp [List.append_assoc]) (by rw [ht]; simp [List.append_assoc])
            hX' (by simp; omega) (by simp; omega) (by omega) hhi (by simp; omega)
        refine ⟨v', i', j', k', M', X', LL', RR', T1', hrun, h1, h2, h3, h4, h5, h6, h7, ?_, h9⟩
        rw [h8, mergeRef_cons_cons, if_neg hrl]; simp

theorem leftLoop_spec (L : StorageLaws S E) (lt : α → α → Bool) (t : Array α)
    (P Q T2 : List α) (lo : Int) (hlo : (P.length : Int) + 1 = lo) :
    ∀ (fuel : Nat) (v : V) (i j k : Int) (M X LL T1 : List α),
      E v = P ++ M ++ X ++ Q → t.toList = T1 ++ LL ++ T2 → X.length = LL.length →
      i = (T1.length : Int) + 1 → k = lo + M.length → j = k + X.length → LL.length < fuel →
      ∃ v', mergeLeftLoop (storageMergeOps S (pureCompare lt)) t j fuel v i k = .ok v' ∧
        E v' = P ++ M ++ LL ++ Q := by
  intro fuel
  induction fuel with
  | zero => intro v i j k M X LL T1 _ _ _ _ _ _ hf; omega
  | succ fuel ih =>
    intro v i j k M X LL T1 hv ht hX hi hk hj hf
    rw [leftLoop_succ]
    match LL, X, hX with
    | [], [], _ =>
      rw [if_neg (by simp at hj ⊢; omega)]
      exact ⟨v, rfl, by simpa using hv⟩
    | l :: LL, x0 :: X, hX =>
      have hX' : X.length = LL.length := by simpa using hX
      have hj' : j = k + X.length + 1 := by simp at hj; omega
      rw [if_pos (by simp; omega)]
      have hreadL : arrayRead t i = .ok l := array_read_mid (P := T1) (B := LL ++ T2)
        (by rw [ht]; simp [List.append_assoc]) hi
      obtain ⟨v1, hw, hv1⟩ := storage_write_mid L (v := v) (i := k) (P := P ++ M)
        (B := X ++ Q) (z := x0) l (by rw [hv]; simp [List.append_assoc]) (by omega)
        (by simp; omega)
      rw [hreadL, liftSortJl_ok, except_bind_ok, hw, liftSortJl_ok, except_bind_ok]
      obtain ⟨v', hrun, hv'⟩ := ih v1 (i + 1) j (k + 1) (M ++ [l]) X LL (T1 ++ [l])
        (by rw [hv1]; simp [List.append_assoc]) (by rw [ht]; simp [List.append_assoc])
        hX' (by simp; omega) (by simp; omega) (by omega) (by simp at hf; omega)
      exact ⟨v', hrun, by rw [hv']; simp [List.append_assoc]⟩

theorem kernel_spec (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt) :
    ∀ (fuel : Nat) (v : V) (lo hi : Int) (temp : Option (Array α)) (P W Q : List α),
      E v = P ++ W ++ Q → (P.length : Int) + 1 = lo → (W.length : Int) = hi - lo + 1 →
      hi - lo < fuel →
      ∃ v' W', legacyMergeSortKernelLoop (storageMergeOps S (pureCompare lt)) () () fuel v lo hi
          temp =
          .ok v' ∧ E v' = P ++ W' ++ Q ∧ SortOutcome lt true W W' := by
  intro fuel
  induction fuel with
  | zero =>
    intro v lo hi temp P W Q hv hP hW hf
    have hW0 : W = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hW0
    refine ⟨v, [], ?_, hv, outcome_nil true⟩
    simp [legacyMergeSortKernelLoop, storageMergeOps, storageQuickOps, pure, Except.pure,
      show ¬ lo < hi by omega]
  | succ fuel ih =>
    intro v lo hi temp P W Q hv hP hW hf
    rw [kernel_succ]
    by_cases hlh : lo < hi
    · rw [if_pos (by simpa using hlh)]
      by_cases hsmall : (hi - lo).toNat ≤ 20
      · rw [if_pos hsmall]
        obtain ⟨v', hrun, hv'⟩ := storageInsertion_spec L hnt v lo hi P W Q (by omega) hv hP hW
        exact ⟨v', sortRef lt W, hrun, hv', sortRef_outcome hnt true W⟩
      · rw [if_neg hsmall]
        generalize hm : lo + (hi - lo) / 2 = m
        have hm1 : lo ≤ m := by omega
        have hm2 : m < hi := by omega
        obtain ⟨WL, WR, rfl, hWL⟩ : ∃ WL WR, W = WL ++ WR ∧ (WL.length : Int) = m - lo + 1 :=
          ⟨W.take (m - lo + 1).toNat, W.drop (m - lo + 1).toNat, by simp,
            by rw [List.length_take, Nat.min_eq_left (by omega)]; omega⟩
        have hWR : (WR.length : Int) = hi - m := by simp at hW; omega
        have rest : ∀ t : Array α, (m - lo).toNat + 1 ≤ t.size → ∃ v' W', (do
            (Except.ok () : SortResult Unit)
            let v ← legacyMergeSortKernelLoop (storageMergeOps S (pureCompare lt)) () () fuel v lo
              m (some t)
            let v ← legacyMergeSortKernelLoop (storageMergeOps S (pureCompare lt)) () () fuel v
              (m + 1) hi (some t)
            let (t, j) ← mergeCopyTempLoop (storageMergeOps S (pureCompare lt)) v m
              ((m - lo).toNat + 2) t 1 lo
            let (v, i, j, k) ← mergeBothLoop (storageMergeOps S (pureCompare lt)) t hi ()
              ((hi - lo).toNat + 2) v 1 j lo
            mergeLeftLoop (storageMergeOps S (pureCompare lt)) t j ((hi - lo).toNat + 2) v i k :
              SortResult V) =
              .ok v' ∧ E v' = P ++ W' ++ Q ∧ SortOutcome lt true (WL ++ WR) W' := by
          intro t ht
          rw [except_bind_ok]
          obtain ⟨v1, WL', hk1, hv1, ho1⟩ := ih v lo m (some t) P WL (WR ++ Q)
            (by rw [hv]; simp [List.append_assoc]) hP hWL (by omega)
          rw [hk1, except_bind_ok]
          have hWL' : (WL'.length : Int) = m - lo + 1 := by rw [ho1.1.length_eq]; exact hWL
          obtain ⟨v2, WR', hk2, hv2, ho2⟩ := ih v1 (m + 1) hi (some t) (P ++ WL') WR Q
            (by rw [hv1]; simp [List.append_assoc]) (by simp; omega) (by omega) (by omega)
          rw [hk2, except_bind_ok]
          have hWR' : (WR'.length : Int) = hi - m := by rw [ho2.1.length_eq]; exact hWR
          obtain ⟨t1, hc, ht1⟩ := copyLoop_spec L lt P (WR' ++ Q) lo m hP
            ((m - lo).toNat + 2) v2 t 1 lo [] WL' t.toList
            (by rw [hv2]; simp [List.append_assoc]) (by simp) (by simp; omega) (by simp)
            (by simp) (by omega) (by omega)
          rw [hc, except_bind_ok]
          dsimp only
          obtain ⟨v3, i3, j3, k3, M3, X3, LL3, RR3, T13, hb, hv3, ht3, hX3, hi3, hk3, hj3, hhi3,
              hmerge, hend⟩ :=
            bothLoop_spec L (lt := lt) t1 P Q (t.toList.drop WL'.length) lo hi hP
              ((hi - lo).toNat + 2) v2 1 (m + 1) lo [] WL' WL' WR' []
              (by rw [hv2]; simp [List.append_assoc]) ht1 rfl (by simp)
              (by simp) (by omega) (by omega) (by omega)
          rw [hb, except_bind_ok]
          dsimp only
          obtain ⟨v4, hl, hv4⟩ := leftLoop_spec L lt t1 P (RR3 ++ Q) (t.toList.drop WL'.length)
            lo hP ((hi - lo).toNat + 2) v3 i3 j3 k3 M3 X3 LL3 T13
            (by rw [hv3]; simp [List.append_assoc]) ht3 hX3 hi3 hk3 hj3 (by
              have h1 := congrArg List.length ht3
              have h2 := congrArg List.length ht1
              simp at h1 h2
              omega)
          refine ⟨v4, mergeRef lt WL' WR', hl, ?_, merge_outcome hnt ho1 ho2⟩
          rw [hv4]
          have hmerge' : M3 ++ mergeRef lt LL3 RR3 = mergeRef lt WL' WR' := by
            rw [hmerge]; rfl
          rcases hend with hL3 | hR3
          · subst hL3
            have hX0 : X3 = [] := List.eq_nil_of_length_eq_zero hX3
            subst hX0
            rw [mergeRef_nil_left] at hmerge'
            rw [← hmerge']; simp [List.append_assoc]
          · subst hR3
            rw [mergeRef_nil_right] at hmerge'
            rw [← hmerge']; simp [List.append_assoc]
        cases temp with
        | none =>
          dsimp only
          rw [except_bind_ok, if_neg (by simp), except_pure_ok, except_bind_ok]
          obtain ⟨v', W', hrun, hrest⟩ := rest (Array.replicate ((m - lo).toNat + 1) default)
            (by simp)
          exact ⟨v', W', hrun, hrest⟩
        | some e =>
          dsimp only
          rw [except_pure_ok, except_bind_ok]
          by_cases hsz : e.size < (m - lo).toNat + 1
          · rw [if_pos hsz, except_bind_ok]
            obtain ⟨v', W', hrun, hrest⟩ :=
              rest (e ++ Array.replicate ((m - lo).toNat + 1 - e.size) default) (by simp; omega)
            exact ⟨v', W', hrun, hrest⟩
          · rw [if_neg hsz, except_pure_ok, except_bind_ok]
            obtain ⟨v', W', hrun, hrest⟩ := rest e (by omega)
            exact ⟨v', W', hrun, hrest⟩
    · rw [if_neg (by simpa using hlh)]
      have hW1 : W.length ≤ 1 := by omega
      exact ⟨v, W, rfl, hv, outcome_of_sorted true (pairwise_of_length_le_one hW1)⟩

/-- `sort!(v, lo, hi, MergeSort, o)` on any storage obeying the `AbstractVector` laws: for a valid
window it returns a stable sorted permutation of the window and leaves the rest alone. -/
theorem legacyMerge_window (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (v : V) (lo hi : Int) (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1) (h3 : hi ≤ ((E v).length : Int)) :
    ∃ v', legacyMergeSortBang (storageMergeOps S (pureCompare lt)) v lo hi () () = .ok v' ∧
      WindowOutcome lt true (E v) (E v') lo hi := by
  obtain ⟨P, W, Q, hv, hP, hW⟩ := window_split (E v) h1 h2 h3
  obtain ⟨v', W', hrun, hv', ho⟩ := kernel_spec L hnt ((hi - lo).toNat + 2) v lo hi none P W Q
    hv hP hW (by omega)
  refine ⟨v', ?_, P, W, Q, W', hv, hP, hW, hv', ho⟩
  unfold legacyMergeSortBang legacyMergeSortKernel
  rw [show (storageMergeOps S (pureCompare lt)).quick.checkBounds =
      fun values lo hi => liftSortJl (storageCheckBounds S values lo hi) from rfl]
  dsimp only
  rw [storageCheckBounds_ok L (by omega), liftSortJl_ok, except_bind_ok]
  exact hrun

end LegacyMerge

/-! ## Sorted-window checks and the whole `_sort!` dispatch on any storage -/

section Master

variable {V α : Type} {S : VectorStorage V α} {E : V → List α}

theorem posAt_mid_get {P W Q : List α} (k : Nat) (hk : k < W.length) :
    posAt (P ++ W ++ Q) ((P.length : Int) + 1 + (k : Int)) = some W[k] := by
  unfold posAt
  have h : ((P.length : Int) + 1 + (k : Int) - 1).toNat = P.length + k := by omega
  rw [h, List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk, List.getElem?_eq_getElem hk]

/-- `_issorted(v, lo, hi, o)` on a valid window of any storage returns a Boolean; `true` means no
element of the window is `o`-less than its predecessor. -/
theorem issortedWindow_spec (L : StorageLaws S E) (R : α → α → Bool) (v : V) (P W Q : List α)
    (lo hi : Int) (hv : E v = P ++ W ++ Q) (hP : (P.length : Int) + 1 = lo)
    (hW : (W.length : Int) = hi - lo + 1) :
    ∃ b, storageIssortedWindow arrayIndices
        (fun current low high => liftSortJl (storageCheckBounds S current low high))
        (fun current index => liftSortJl (S.getindex current index))
        (fun o => o) v lo hi (pureCompare R) =
        .ok b ∧ (b = true → ∀ k (hk : k + 1 < W.length), R W[k + 1] W[k] = false) := by
  have hlen : ((E v).length : Int) = P.length + W.length + Q.length := by
    rw [hv]; simp only [List.length_append]; omega
  have hchk : liftSortJl (storageCheckBounds S v lo hi) = .ok () := by
    rw [storageCheckBounds_ok L (by omega)]
    rfl
  have hreads : ∀ i ∈ arrayIndices.range (arrayIndices.addOne lo) hi, ∃ current previous,
      liftSortJl (S.getindex v i) = .ok current ∧
        liftSortJl (S.getindex v (arrayIndices.previous i)) = .ok previous := by
    intro i hi'
    simp only [arrayIndices, mem_arrayIndexRange] at hi' ⊢
    obtain ⟨x, hx⟩ := posAt_some (l := E v) (i := i) (by omega) (by omega)
    obtain ⟨y, hy⟩ := posAt_some (l := E v) (i := i - 1) (by omega) (by omega)
    refine ⟨x, y, ?_, ?_⟩
    · rw [storage_read_at L (by omega) hx]; rfl
    · rw [storage_read_at L (by omega) hy]; rfl
  obtain ⟨b, hb⟩ := forIn_window_check_ok arrayIndices
    (fun current index => liftSortJl (S.getindex current index)) (fun o => o) v R _ hreads
  refine ⟨b, ?_, ?_⟩
  · unfold storageIssortedWindow
    simpa only [hchk, pureCompare, bind, Except.bind] using hb
  · rintro rfl k hk
    obtain ⟨c, p, hc, hp, hf⟩ :=
      (forIn_window_check arrayIndices
        (fun current index => liftSortJl (S.getindex current index)) (fun o => o) v R _ hreads).1 hb
        ((P.length : Int) + 1 + ((k + 1 : Nat) : Int))
        (by simp only [arrayIndices, mem_arrayIndexRange]; omega)
    have hprev : arrayIndices.previous ((P.length : Int) + 1 + ((k + 1 : Nat) : Int)) =
        (P.length : Int) + 1 + (k : Int) := by simp only [arrayIndices]; omega
    have hc' : liftSortJl (S.getindex v
        ((P.length : Int) + 1 + ((k + 1 : Nat) : Int))) = .ok W[k + 1] := by
      rw [storage_read_at L (by omega)
        (show posAt (E v) ((P.length : Int) + 1 + ((k + 1 : Nat) : Int)) = some W[k + 1] by
          rw [hv]; exact posAt_mid_get (k + 1) hk)]
      rfl
    have hp' : liftSortJl (S.getindex v ((P.length : Int) + 1 + (k : Int))) = .ok W[k] := by
      rw [storage_read_at L (by omega)
        (show posAt (E v) ((P.length : Int) + 1 + (k : Int)) = some W[k] by
          rw [hv]; exact posAt_mid_get k (by omega))]
      rfl
    rw [hc'] at hc
    rw [hprev, hp'] at hp
    cases hc; cases hp
    exact hf

theorem sorted_of_adjacent {lt : α → α → Bool} (hnt : NegTransOrder lt) (W : List α)
    (h : ∀ k (hk : k + 1 < W.length), lt W[k + 1] W[k] = false) : SortedPairwise lt W :=
  pairwise_of_adjacent (R := fun a b => lt b a = false)
    (fun _ _ _ hab hbc => negTransOrder_not_trans hnt hbc hab) W h

theorem reverse_sorted_of_adjacent {lt : α → α → Bool} (hnt : NegTransOrder lt) (W : List α)
    (h : ∀ k (hk : k + 1 < W.length), lt W[k] W[k + 1] = false) :
    SortedPairwise lt W.reverse := by
  unfold SortedPairwise
  rw [List.pairwise_reverse]
  exact pairwise_of_adjacent (R := fun a b => lt a b = false)
    (fun _ _ _ hab hbc => negTransOrder_not_trans hnt hab hbc) W h

theorem strict_of_adjacent {lt : α → α → Bool} (hnt : NegTransOrder lt) (W : List α)
    (h : ∀ k (hk : k + 1 < W.length), lt W[k + 1] W[k] = true) :
    W.Pairwise (fun a b => lt b a = true) :=
  pairwise_of_adjacent (R := fun a b => lt b a = true)
    (fun _ _ _ hab hbc => hnt.2.1 _ _ _ hbc hab) W h

theorem windowOutcome_mono {lt : α → α → Bool} {s s' : Bool} {l l' : List α} {lo hi : Int}
    (hs : s' = true → s = true) (h : WindowOutcome lt s l l' lo hi) :
    WindowOutcome lt s' l l' lo hi := by
  obtain ⟨P, W, Q, W', h1, h2, h3, h4, ho⟩ := h
  exact ⟨P, W, Q, W', h1, h2, h3, h4, ho.1, ho.2.1, fun h => ho.2.2 (hs h)⟩

theorem windowOutcome_sorted {lt : α → α → Bool} (s : Bool) {P W Q : List α} {lo hi : Int}
    (hP : (P.length : Int) + 1 = lo) (hW : (W.length : Int) = hi - lo + 1)
    (h : SortedPairwise lt W) : WindowOutcome lt s (P ++ W ++ Q) (P ++ W ++ Q) lo hi :=
  ⟨P, W, Q, W, rfl, hP, hW, rfl, outcome_of_sorted s h⟩

/-- A window outcome over the whole vector is an outcome of sorting the whole vector. -/
theorem windowOutcome_whole {lt : α → α → Bool} {s : Bool} {l l' : List α}
    (h : WindowOutcome lt s l l' 1 (l.length : Int)) : SortOutcome lt s l l' := by
  obtain ⟨P, W, Q, W', hb, hP, hW, ha, ho⟩ := h
  have hP0 : P = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hlen : l.length = P.length + W.length + Q.length := by
    rw [hb]; simp only [List.length_append]
  have hQ0 : Q = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hP0 hQ0
  simp only [List.nil_append, List.append_nil] at hb ha
  subst hb ha
  exact ho

theorem negTransOrder_flip {lt : α → α → Bool} (hnt : NegTransOrder lt) :
    NegTransOrder (fun a b => lt b a) :=
  ⟨hnt.1, fun a b c h1 h2 => hnt.2.1 c b a h2 h1, fun a b c h1 => (hnt.2.2 c b a h1).symm⟩

variable [Inhabited α] (numeric : BracketNumerics) (pivot : Int → Int → Int)

theorem loop_subArray (fuel : Nat) (v : V) (next : Algorithm (BracketSortTarget Int) Int)
    (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v (.subArray next) (pureCompare lt) kw =
      sourceSortLoop S numeric pivot fuel v next (pureCompare lt) kw := rfl

theorem loop_missing (fuel : Nat) (v : V) (next : Algorithm (BracketSortTarget Int) Int)
    (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v (.missing next) (pureCompare lt) kw =
      sourceSortLoop S numeric pivot fuel v next (pureCompare lt) kw := rfl

theorem loop_bool (fuel : Nat) (v : V) (next : Algorithm (BracketSortTarget Int) Int)
    (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v (.boolOptimization next) (pureCompare lt) kw =
      sourceSortLoop S numeric pivot fuel v next (pureCompare lt) kw := rfl

theorem loop_ieee (fuel : Nat) (v : V) (next : Algorithm (BracketSortTarget Int) Int)
    (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v (.ieeeFloat next) (pureCompare lt) kw =
      sourceSortLoop S numeric pivot fuel v next (pureCompare lt) kw := rfl

theorem loop_uint (fuel : Nat) (v : V) (yes no : Algorithm (BracketSortTarget Int) Int)
    (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v (.isUIntMappable yes no) (pureCompare lt) kw =
      sourceSortLoop S numeric pivot fuel v no (pureCompare lt) kw := rfl

theorem loop_counting (fuel : Nat) (v : V) (cnt next : Algorithm (BracketSortTarget Int) Int)
    (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v (.considerCounting cnt next) (pureCompare lt) kw =
      sourceSortLoop S numeric pivot fuel v next (pureCompare lt) kw := rfl

theorem loop_defaultStable (fuel : Nat) (v : V) (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v .defaultStable (pureCompare lt) kw =
      sourceSortLoop S numeric pivot fuel v defaultVectorAlgorithms (pureCompare lt) kw := rfl

theorem loop_defaultUnstable (fuel : Nat) (v : V) (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v .defaultUnstable (pureCompare lt) kw =
      sourceSortLoop S numeric pivot fuel v defaultVectorAlgorithms (pureCompare lt) kw := rfl

theorem loop_small (fuel : Nat) (v : V) (threshold : Nat)
    (a b : Algorithm (BracketSortTarget Int) Int) (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v (.small threshold a b) (pureCompare lt) kw =
      sourceSortLoop S numeric pivot fuel v
        (if decide (kw.hi - kw.lo < Int.ofNat threshold) = true then a else b)
        (pureCompare lt) kw := rfl

theorem loop_insertion (fuel : Nat) (v : V) (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v .insertion (pureCompare lt) kw =
      (do let sorted ← storageInsertion S (pureCompare lt) v kw.lo kw.hi
          pure (sorted, kw.scratch)) := rfl

theorem loop_quick (fuel : Nat) (v : V) (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v .quick (pureCompare lt) kw =
      (do let sorted ← legacyQuickSortBang (storageQuickOps S (pureCompare lt)) v kw.lo kw.hi ()
          pure (sorted, kw.scratch)) := rfl

theorem loop_merge (fuel : Nat) (v : V) (lt : α → α → Bool) (kw : ArraySortKeywords α) :
    sourceSortLoop S numeric pivot (fuel + 1) v .merge (pureCompare lt) kw =
      (do let sorted ← legacyMergeSortBang (storageMergeOps S (pureCompare lt)) v kw.lo kw.hi () ()
          pure (sorted, kw.scratch)) := rfl

theorem loop_checkSorted (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (fuel : Nat) (next : Algorithm (BracketSortTarget Int) Int) (s : Bool) (v : V)
    (kw : ArraySortKeywords α) (h1 : 1 ≤ kw.lo) (h2 : kw.lo ≤ kw.hi + 1)
    (h3 : kw.hi ≤ ((E v).length : Int))
    (hnext : ∃ v' sc, sourceSortLoop S numeric pivot fuel v next (pureCompare lt) kw = .ok (v', sc) ∧
      WindowOutcome lt s (E v) (E v') kw.lo kw.hi) :
    ∃ v' sc, sourceSortLoop S numeric pivot (fuel + 1) v (.checkSorted next)
        (pureCompare lt) kw =
        .ok (v', sc) ∧ WindowOutcome lt false (E v) (E v') kw.lo kw.hi := by
  obtain ⟨v1, sc1, hrun1, hout1⟩ := hnext
  obtain ⟨P, W, Q, hv, hP, hW⟩ := window_split (E v) h1 h2 h3
  obtain ⟨b, hb, hbs⟩ := issortedWindow_spec L lt v P W Q kw.lo kw.hi hv hP hW
  obtain ⟨b2, hb2, hbs2⟩ :=
    issortedWindow_spec L (fun a b => lt b a) v P W Q kw.lo kw.hi hv hP hW
  rw [sourceSortLoop]
  unfold sortCheckSorted storageCheckSortedOps
  simp only [bind, Except.bind, pure, Except.pure, hb]
  cases b
  ·
    by_cases hbig : Int.sub kw.hi kw.lo ≥ 500
    · simp only [hbig, ↓reduceIte, pureCompare, bind, Except.bind,
        pure, Except.pure, hb2]
      cases b2
      · simp only [Bool.false_eq_true, ↓reduceIte, hrun1]
        exact ⟨v1, sc1, rfl, windowOutcome_mono (fun h => by cases h) hout1⟩
      ·
        obtain ⟨v', hrev, hv'⟩ := storageReverse_spec L v kw.lo kw.hi P W Q hv hP hW
        simp only [hrev]
        exact ⟨v', kw.scratch, rfl, P, W, Q, W.reverse, hv, hP, hW, hv', List.reverse_perm W,
          reverse_sorted_of_adjacent hnt W (fun k hk => hbs2 rfl k hk), fun h => by cases h⟩
    · simp only [hbig, ↓reduceIte, hrun1]
      exact ⟨v1, sc1, rfl, windowOutcome_mono (fun h => by cases h) hout1⟩
  ·
    refine ⟨v, kw.scratch, rfl, ?_⟩
    rw [hv]
    exact windowOutcome_sorted false hP hW (sorted_of_adjacent hnt W (fun k hk => hbs rfl k hk))

theorem loop_stableCheck (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (fuel : Nat) (next : Algorithm (BracketSortTarget Int) Int) (s : Bool) (v : V)
    (kw : ArraySortKeywords α) (h1 : 1 ≤ kw.lo) (h2 : kw.lo ≤ kw.hi + 1)
    (h3 : kw.hi ≤ ((E v).length : Int))
    (hnext : ∃ v' sc, sourceSortLoop S numeric pivot fuel v next (pureCompare lt) kw = .ok (v', sc) ∧
      WindowOutcome lt s (E v) (E v') kw.lo kw.hi) :
    ∃ v' sc, sourceSortLoop S numeric pivot (fuel + 1) v (.stableCheckSorted next)
        (pureCompare lt) kw =
        .ok (v', sc) ∧ WindowOutcome lt s (E v) (E v') kw.lo kw.hi := by
  obtain ⟨v1, sc1, hrun1, hout1⟩ := hnext
  obtain ⟨P, W, Q, hv, hP, hW⟩ := window_split (E v) h1 h2 h3
  obtain ⟨b, hb, hbs⟩ := issortedWindow_spec L lt v P W Q kw.lo kw.hi hv hP hW
  obtain ⟨b2, hb2, hbs2⟩ :=
    issortedWindow_spec L (fun a b => !lt a b) v P W Q kw.lo kw.hi hv hP hW
  rw [sourceSortLoop]
  unfold sortStableCheck storageStableCheckOps
  simp only [bind, Except.bind, pure, Except.pure, hb]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, pureCompare, bind, Except.bind,
      pure, Except.pure, hb2]
    cases b2
    · simp only [Bool.false_eq_true, ↓reduceIte, hrun1]
      exact ⟨v1, sc1, rfl, hout1⟩
    ·
      obtain ⟨v', hrev, hv'⟩ := storageReverse_spec L v kw.lo kw.hi P W Q hv hP hW
      simp only [hrev]
      exact ⟨v', kw.scratch, rfl, P, W, Q, W.reverse, hv, hP, hW, hv',
        outcome_reverse_of_strict hnt s
          (strict_of_adjacent hnt W (fun k hk => by simpa using hbs2 rfl k hk))⟩
  ·
    refine ⟨v, kw.scratch, rfl, ?_⟩
    rw [hv]
    exact windowOutcome_sorted s hP hW (sorted_of_adjacent hnt W (fun k hk => hbs rfl k hk))

/-- Whether `_sort!` with this algorithm is stable on an element type with no specialised
`Missing`, `Bool`, `IEEEFloat` or `UIntMappable` method. `CheckSorted` and `QuickSort` are not:
`CheckSorted` reverses non-increasing windows of at least 501 elements. -/
def genericStable : Algorithm (BracketSortTarget Int) Int → Bool
  | .insertion | .merge | .defaultStable | .defaultUnstable => true
  | .subArray next | .missing next | .boolOptimization next | .ieeeFloat next
  | .stableCheckSorted next | .scratchQuickSort _ _ next | .considerCounting _ next =>
    genericStable next
  | .small _ first second => genericStable first && genericStable second
  | .isUIntMappable _ no => genericStable no
  | _ => false

/-- Dispatch depth that `sourceSortLoop` needs on the generic element path; the default
algorithms expand into nine nested dispatches. -/
def genericFuel : Algorithm (BracketSortTarget Int) Int → Nat
  | .defaultStable | .defaultUnstable => 10
  | .subArray next | .missing next | .boolOptimization next | .ieeeFloat next
  | .checkSorted next | .stableCheckSorted next | .scratchQuickSort _ _ next
  | .considerCounting _ next | .isUIntMappable _ next => genericFuel next + 1
  | .small _ first second => max (genericFuel first) (genericFuel second) + 1
  | _ => 1

theorem genericFuel_le (alg : Algorithm (BracketSortTarget Int) Int) :
    genericFuel alg ≤ alg.depth + 9 := by
  induction alg <;> simp only [genericFuel, Algorithm.depth] <;> omega

/-- Running `sort` on every valid window `kw.lo:kw.hi` of a storage value succeeds and replaces
the window by an outcome of sorting it (stable when `s`), leaving the rest unchanged. -/
def SortsWindow (S : VectorStorage V α) (E : V → List α) (lt : α → α → Bool)
    (sort : V → ArraySortKeywords α → SortResult (V × Option (Array α))) (s : Bool) : Prop :=
  ∀ (v : V) (kw : ArraySortKeywords α), 1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 →
    kw.hi ≤ ((E v).length : Int) →
    ∃ v' sc, sort v kw = .ok (v', sc) ∧ WindowOutcome lt s (E v) (E v') kw.lo kw.hi

theorem sourceSortLoop_sorts (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (hpivot : ∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b) :
    ∀ (fuel : Nat) (alg : Algorithm (BracketSortTarget Int) Int),
      isFullSortAlgorithm alg = true → genericFuel alg ≤ fuel →
      SortsWindow S E lt
        (fun v kw => sourceSortLoop S numeric pivot fuel v alg (pureCompare lt) kw)
        (genericStable alg)
  | 0, alg, _, hf => by
    exfalso
    cases alg <;> simp [genericFuel] at hf
  | fuel + 1, alg, hfull, hf => by
    have ih := sourceSortLoop_sorts L hnt hpivot fuel
    intro v kw h1 h2 h3
    cases alg
    case insertion =>
      obtain ⟨v', hrun, hout⟩ := insertion_window L hnt v h1 h2 h3
      refine ⟨v', kw.scratch, ?_, hout⟩
      show sourceSortLoop S numeric pivot (fuel + 1) v .insertion (pureCompare lt) kw = _
      rw [loop_insertion, hrun]; rfl
    case quick =>
      obtain ⟨v', hrun, hout⟩ := legacyQuick_window L hnt v kw.lo kw.hi h1 h2 h3
      refine ⟨v', kw.scratch, ?_, hout⟩
      show sourceSortLoop S numeric pivot (fuel + 1) v .quick (pureCompare lt) kw = _
      rw [loop_quick, hrun]; rfl
    case merge =>
      obtain ⟨v', hrun, hout⟩ := legacyMerge_window L hnt v kw.lo kw.hi h1 h2 h3
      refine ⟨v', kw.scratch, ?_, hout⟩
      show sourceSortLoop S numeric pivot (fuel + 1) v .merge (pureCompare lt) kw = _
      rw [loop_merge, hrun]; rfl
    case defaultStable =>
      have h9 : genericFuel (defaultVectorAlgorithms : Algorithm (BracketSortTarget Int) Int) = 9 :=
        rfl
      simp only [genericFuel] at hf
      obtain ⟨v', sc, hrun, hout⟩ := ih defaultVectorAlgorithms rfl (by omega) v kw h1 h2 h3
      refine ⟨v', sc, ?_, hout⟩
      show sourceSortLoop S numeric pivot (fuel + 1) v .defaultStable (pureCompare lt) kw = _
      rw [loop_defaultStable]; exact hrun
    case defaultUnstable =>
      have h9 : genericFuel (defaultVectorAlgorithms : Algorithm (BracketSortTarget Int) Int) = 9 :=
        rfl
      simp only [genericFuel] at hf
      obtain ⟨v', sc, hrun, hout⟩ := ih defaultVectorAlgorithms rfl (by omega) v kw h1 h2 h3
      refine ⟨v', sc, ?_, hout⟩
      show sourceSortLoop S numeric pivot (fuel + 1) v .defaultUnstable (pureCompare lt) kw = _
      rw [loop_defaultUnstable]; exact hrun
    case subArray next =>
      simp only [genericFuel] at hf
      obtain ⟨v', sc, hrun, hout⟩ := ih next hfull (by omega) v kw h1 h2 h3
      refine ⟨v', sc, ?_, hout⟩
      show sourceSortLoop S numeric pivot (fuel + 1) v (.subArray next) (pureCompare lt) kw = _
      rw [loop_subArray]; exact hrun
    case missing next =>
      simp only [genericFuel] at hf
      obtain ⟨v', sc, hrun, hout⟩ := ih next hfull (by omega) v kw h1 h2 h3
      refine ⟨v', sc, ?_, hout⟩
      show sourceSortLoop S numeric pivot (fuel + 1) v (.missing next) (pureCompare lt) kw = _
      rw [loop_missing]; exact hrun
    case boolOptimization next =>
      simp only [genericFuel] at hf
      obtain ⟨v', sc, hrun, hout⟩ := ih next hfull (by omega) v kw h1 h2 h3
      refine ⟨v', sc, ?_, hout⟩
      show sourceSortLoop S numeric pivot (fuel + 1) v (.boolOptimization next) (pureCompare lt) kw = _
      rw [loop_bool]; exact hrun
    case ieeeFloat next =>
      simp only [genericFuel] at hf
      obtain ⟨v', sc, hrun, hout⟩ := ih next hfull (by omega) v kw h1 h2 h3
      refine ⟨v', sc, ?_, hout⟩
      show sourceSortLoop S numeric pivot (fuel + 1) v (.ieeeFloat next) (pureCompare lt) kw = _
      rw [loop_ieee]; exact hrun
    case isUIntMappable yes no =>
      simp only [genericFuel] at hf
      obtain ⟨v', sc, hrun, hout⟩ := ih no hfull (by omega) v kw h1 h2 h3
      refine ⟨v', sc, ?_, hout⟩
      show sourceSortLoop S numeric pivot (fuel + 1) v (.isUIntMappable yes no)
        (pureCompare lt) kw = _
      rw [loop_uint]; exact hrun
    case considerCounting cnt next =>
      simp only [genericFuel] at hf
      obtain ⟨v', sc, hrun, hout⟩ := ih next hfull (by omega) v kw h1 h2 h3
      refine ⟨v', sc, ?_, hout⟩
      show sourceSortLoop S numeric pivot (fuel + 1) v (.considerCounting cnt next)
        (pureCompare lt) kw = _
      rw [loop_counting]; exact hrun
    case small threshold a b =>
      have hab : isFullSortAlgorithm a = true ∧ isFullSortAlgorithm b = true := by
        simpa [isFullSortAlgorithm] using hfull
      simp only [genericFuel] at hf
      by_cases hsm : kw.hi - kw.lo < Int.ofNat threshold
      · obtain ⟨v', sc, hrun, hout⟩ := ih a hab.1 (by omega) v kw h1 h2 h3
        refine ⟨v', sc, ?_, windowOutcome_mono (fun h => ?_) hout⟩
        · show sourceSortLoop S numeric pivot (fuel + 1) v (.small threshold a b)
            (pureCompare lt) kw = _
          rw [loop_small, if_pos (decide_eq_true hsm)]; exact hrun
        · simp only [genericStable, Bool.and_eq_true] at h; exact h.1
      · obtain ⟨v', sc, hrun, hout⟩ := ih b hab.2 (by omega) v kw h1 h2 h3
        refine ⟨v', sc, ?_, windowOutcome_mono (fun h => ?_) hout⟩
        · show sourceSortLoop S numeric pivot (fuel + 1) v (.small threshold a b)
            (pureCompare lt) kw = _
          rw [loop_small, if_neg (by simpa using hsm)]; exact hrun
        · simp only [genericStable, Bool.and_eq_true] at h; exact h.2
    case checkSorted next =>
      simp only [genericFuel] at hf
      exact loop_checkSorted numeric pivot L hnt fuel next (genericStable next) v kw h1 h2 h3
        (ih next hfull (by omega) v kw h1 h2 h3)
    case stableCheckSorted next =>
      simp only [genericFuel] at hf
      exact loop_stableCheck numeric pivot L hnt fuel next (genericStable next) v kw h1 h2 h3
        (ih next hfull (by omega) v kw h1 h2 h3)
    case scratchQuickSort lo hi next =>
      have hq : (lo = none ∧ hi = none) ∧ isFullSortAlgorithm next = true := by
        simpa [isFullSortAlgorithm] using hfull
      obtain ⟨⟨rfl, rfl⟩, hfn⟩ := hq
      simp only [genericFuel] at hf
      obtain ⟨P, W, Q, hv, hP, hW⟩ := window_split (E v) h1 h2 h3
      obtain ⟨v', sc, W', hrun, hv', hout⟩ := sortScratchQuick_spec L hnt pivot hpivot
        (sourceSortLoop S numeric pivot fuel) next (genericStable next)
        (ih next hfn (by omega)) v kw P W Q hv hP hW
      exact ⟨v', sc, hrun, P, W, Q, W', hv, hP, hW, hv', hout⟩
    all_goals exact absurd hfull (by simp [isFullSortAlgorithm])

/-- The source `_sort!` dispatch through `sourceSortWindow`, for every algorithm that sorts on
its own, on any storage obeying the `AbstractVector` laws. -/
theorem sourceSortWindow_sorts (L : StorageLaws S E) {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (hpivot : ∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b)
    (alg : Algorithm (BracketSortTarget Int) Int) (hfull : isFullSortAlgorithm alg = true) :
    SortsWindow S E lt
      (fun v kw => sourceSortWindow S numeric pivot v alg (pureCompare lt) kw)
      (genericStable alg) :=
  sourceSortLoop_sorts numeric pivot L hnt hpivot (alg.depth + 16) alg hfull
    (by have := genericFuel_le alg; omega)


end Master

/-! ## Whole-vector sorting through the dispatch -/

section Whole

variable {V α : Type} [Inhabited α] {S : VectorStorage V α} {E : V → List α}

theorem isFull_applyInitial (alg : Algorithm (BracketSortTarget Int) Int)
    (h : isFullSortAlgorithm alg = true) :
    isFullSortAlgorithm (sourceApplyInitialOptimizations alg) = true := by
  cases alg <;> first | rfl | exact h

theorem negTransOrder_effective {lt : α → α → Bool} (hnt : NegTransOrder lt) (reverse : Option Bool) :
    NegTransOrder (if reverse = some true then fun a b => lt b a else lt) := by
  split
  · exact negTransOrder_flip hnt
  · exact hnt

/-- `sort!(v; alg, lt, rev)` with the source `_sort!` dispatch on any storage obeying the
`AbstractVector` laws, for an algorithm that sorts on its own. -/
theorem sortVectorBang_sorts (L : StorageLaws S E) (numeric : BracketNumerics)
    (pivot : Int → Int → Int) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (hpivot : ∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b)
    (alg : Algorithm (BracketSortTarget Int) Int) (hfull : isFullSortAlgorithm alg = true)
    (v : V) (reverse : Option Bool) (scratch : Option (Array α)) :
    ∃ result, sortVectorBang (sourceVectorSortOps S numeric pivot) v alg (pureCompare lt) ()
        reverse (pureCompare lt) scratch = .ok result ∧
      SortOutcome (if reverse = some true then fun a b => lt b a else lt)
        (genericStable (sourceApplyInitialOptimizations alg)) (E v) (E result) := by
  obtain ⟨v', sc, hrun, hout⟩ := sourceSortWindow_sorts numeric pivot L
    (negTransOrder_effective hnt reverse) hpivot (sourceApplyInitialOptimizations alg)
    (isFull_applyInitial alg hfull) v { lo := 1, hi := Int.ofNat (S.length v), scratch := scratch }
    (Int.le_refl 1) (by simp only [Int.ofNat_eq_natCast]; omega) (by simp [L.length_eq])
  refine ⟨v', ?_, windowOutcome_whole (by rw [L.length_eq] at hout; exact hout)⟩
  have hla : S.lastindex v = Int.ofNat (S.length v) := by
    simp [storage_lastindex L v, L.length_eq]
  have heffective :
      (if reverse = some true then
          fun a b => pureCompare (ε := SortException) lt b a
        else pureCompare (ε := SortException) lt) =
        pureCompare (ε := SortException)
          (if reverse = some true then fun a b => lt b a else lt) := by
    rw [pureCompare_swap, pureCompare_ite]
  simp only [sortVectorBang, sourceVectorSortOps, sourceSortBang, L.firstindex_eq v, hla,
    heffective, hrun]
  rfl

end Whole


/-- `sort!(v, lo, hi, QuickSort, o)`, the legacy `QuickSortAlg` method, on any one-based storage
obeying the `AbstractVector` laws: for every strict weak order and every window `lo:hi` inside
the vector it returns a sorted permutation of the window and leaves the elements outside the
window unchanged. -/
def QuickSortCorrect : Prop :=
  ∀ (V α : Type) (S : VectorStorage V α) (E : V → List α), StorageLaws S E →
  ∀ (lt : α → α → SortResult Bool) (v : V) (lo hi : Int), EffectNegTransOrder lt →
    1 ≤ lo → lo ≤ hi + 1 → hi ≤ ((E v).length : Int) →
    ∃ v', legacyQuickSortBang (storageQuickOps S lt) v lo hi () = .ok v' ∧
      EffectWindowOutcome lt false (E v) (E v') lo hi


/-- `sort!(v, lo, hi, MergeSort, o)`, the legacy `MergeSortAlg` method, on any one-based storage
obeying the `AbstractVector` laws: for every strict weak order and every window `lo:hi` inside
the vector it returns a stable sorted permutation of the window (equivalent elements keep their
relative order) and leaves the elements outside the window unchanged. -/
def MergeSortStable : Prop :=
  ∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α), StorageLaws S E →
  ∀ (lt : α → α → SortResult Bool) (v : V) (lo hi : Int), EffectNegTransOrder lt →
    1 ≤ lo → lo ≤ hi + 1 → hi ≤ ((E v).length : Int) →
    ∃ v', legacyMergeSortBang (storageMergeOps S lt) v lo hi () () = .ok v' ∧
      EffectWindowOutcome lt true (E v) (E v') lo hi


/-- `CheckSorted(next)` and `StableCheckSorted(next)`, reached through the source `_sort!`
dispatch on any storage obeying the `AbstractVector` laws, for every continuation algorithm
`next` that sorts on its own: each sorts every valid window and leaves the rest of the vector
unchanged. `StableCheckSorted(next)` is stable whenever `next` is; `CheckSorted` promises no
stability because it reverses non-increasing windows of more than 500 elements. -/
def CheckSortedCorrect : Prop :=
  ∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α), StorageLaws S E →
  ∀ (numeric : BracketNumerics) (pivot : Int → Int → Int) (lt : α → α → SortResult Bool)
    (next : Algorithm (BracketSortTarget Int) Int),
    EffectNegTransOrder lt → (∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b) →
    isFullSortAlgorithm next = true →
    (∀ (v : V) (kw : ArraySortKeywords α), 1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 →
      kw.hi ≤ ((E v).length : Int) →
      ∃ v' sc, sourceSortWindow S numeric pivot v (.checkSorted next) lt kw = .ok (v', sc) ∧
        EffectWindowOutcome lt false (E v) (E v') kw.lo kw.hi) ∧
    (∀ (v : V) (kw : ArraySortKeywords α), 1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 →
      kw.hi ≤ ((E v).length : Int) →
      ∃ v' sc, sourceSortWindow S numeric pivot v (.stableCheckSorted next) lt kw =
          .ok (v', sc) ∧
        EffectWindowOutcome lt (genericStable next) (E v) (E v') kw.lo kw.hi)


/-- `sort(v; alg, lt, rev)` copies `v` and sorts the copy with `sort!`. On any storage obeying the
`AbstractVector` laws, for every strict weak order, every pivot rule choosing an index in the
current window, and every algorithm that sorts on its own, the result is a permutation of `v`
sorted by the effective order (`lt` reversed when `rev == true`), and it keeps equivalent
elements in their original order whenever the algorithm (after `InitialOptimizations`) is
stable. -/
def SortVectorSortedPermutation : Prop :=
  ∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α), StorageLaws S E →
  ∀ (numeric : BracketNumerics) (lt : α → α → SortResult Bool) (pivot : Int → Int → Int) (values : V)
      (algorithm : Algorithm (BracketSortTarget Int) Int) (reverse : Option Bool)
      (scratch : Option (Array α)),
    EffectNegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    let effective := if reverse = some true then fun a b => lt b a else lt
    let vectorOps := sourceVectorSortOps S numeric pivot
    let copyOps : SortCopyOps V JuliaLean.base.sort.SortException (Option (Array α)) := {
      copyMutable := fun source => .ok source
      sortBang := fun source selectedScratch =>
        sortVectorBang vectorOps source algorithm lt () reverse lt selectedScratch
    }
    ∃ result, sortVector copyOps values scratch = .ok result ∧
      List.Perm (E values) (E result) ∧ EffectSortedValues effective (E result) ∧
      (genericStable (sourceApplyInitialOptimizations algorithm) = true →
        EffectStableWrt effective (E values) (E result))


/-- `sort!(v)` and `sort(v)` with the default algorithm `DEFAULT_STABLE`, on any storage obeying
the `AbstractVector` laws whose element type has no specialised method: for every strict weak
order and pivot rule choosing an index in the current window, both return the same permutation
of `v`, sorted by the effective order and stable (equivalent elements keep their original
relative order). -/
def SortDefaultStable : Prop :=
  ∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α), StorageLaws S E →
  ∀ (numeric : BracketNumerics) (lt : α → α → SortResult Bool) (pivot : Int → Int → Int) (values : V)
      (reverse : Option Bool),
    EffectNegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    let effective := if reverse = some true then fun a b => lt b a else lt
    let vectorOps := sourceVectorSortOps S numeric pivot
    let copyOps : SortCopyOps V JuliaLean.base.sort.SortException (Option (Array α)) := {
      copyMutable := fun source => .ok source
      sortBang := fun source selectedScratch =>
        sortVectorBang vectorOps source (defalgArray source) lt () reverse lt selectedScratch
    }
    ∃ result,
      sortVectorBang vectorOps values (defalgArray values) lt () reverse lt none = .ok result ∧
      sortVector copyOps values none = .ok result ∧
      List.Perm (E values) (E result) ∧ EffectSortedValues effective (E result) ∧
      EffectStableWrt effective (E values) (E result)


/-- The checked sorting entry points never fail once their window passed `checkbounds`: on any
storage obeying the `AbstractVector` laws, if `checkbounds(v, lo:hi)` succeeds (an empty window,
or `1 ≤ lo` and `hi ≤ length(v)`), then `_issorted(v, lo, hi, o)`, `_sort!(v, InsertionSort, o;
lo, hi)` and `sort!(v, lo, hi, QuickSort, o)` all return without throwing. -/
def CheckedWindowsInBounds : Prop :=
  ∀ (V α : Type) (S : VectorStorage V α) (E : V → List α), StorageLaws S E →
  ∀ (lt : α → α → SortResult Bool) (v : V) (lo hi : Int),
    storageCheckBounds S v lo hi = .ok () → EffectNegTransOrder lt →
    (∃ b, storageIssortedWindow arrayIndices
      (fun current low high => liftSortJl (storageCheckBounds S current low high))
      (fun current index => liftSortJl (S.getindex current index))
      (fun _ => lt) v lo hi () = .ok b) ∧
    (∃ v', storageInsertion S lt v lo hi = .ok v') ∧
    (∃ v', legacyQuickSortBang (storageQuickOps S lt) v lo hi () = .ok v')


/-! ## Tuple merge sort -/

section TupleSort

variable {α : Type} [Inhabited α]

theorem mergeAnyNTupleLoop_ref (lt : α → α → Bool) :
    ∀ (fuel : Nat) (left right : AnyNTuple α),
      left.2.val.length + right.2.val.length < fuel →
      ∃ merged, mergeAnyNTupleLoop (pureCompare lt) fuel left right = .ok merged ∧
        merged.2.val = mergeRef lt left.2.val right.2.val
  | 0, _, _, hfuel => by omega
  | fuel + 1, ⟨m, ⟨xs, hxs⟩⟩, ⟨n, ⟨ys, hys⟩⟩, hfuel => by
    unfold mergeAnyNTupleLoop
    cases xs with
    | nil =>
      cases ys with
      | nil => exact ⟨⟨m, ⟨[], hxs⟩⟩, rfl, (mergeRef_nil_left lt []).symm⟩
      | cons y ys' => exact ⟨⟨n, ⟨y :: ys', hys⟩⟩, rfl, (mergeRef_nil_left lt _).symm⟩
    | cons x xs' =>
      cases ys with
      | nil => exact ⟨⟨m, ⟨x :: xs', hxs⟩⟩, rfl, (mergeRef_nil_right lt _).symm⟩
      | cons y ys' =>
        dsimp only [mergeTupleNonempty, List.headD_cons, List.tail_cons, pureCompare, bind,
          Except.bind]
        by_cases hlt : lt y x = true
        · simp only [hlt, ↓reduceIte]
          obtain ⟨rest, hrec, hval⟩ := mergeAnyNTupleLoop_ref lt fuel
            ⟨m, ⟨x :: xs', hxs⟩⟩ ⟨n - 1, ⟨ys', by simp at hys; omega⟩⟩
            (by simp at hfuel ⊢; omega)
          rw [hrec]
          simp only [bind, Except.bind, pure, Except.pure]
          refine ⟨_, rfl, ?_⟩
          show y :: rest.2.val = _
          rw [hval, mergeRef_cons_cons, if_pos hlt]
        · have hltF : lt y x = false := Bool.eq_false_iff.2 hlt
          simp only [hltF, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨rest, hrec, hval⟩ := mergeAnyNTupleLoop_ref lt fuel
            ⟨m - 1, ⟨xs', by simp at hxs; omega⟩⟩ ⟨n, ⟨y :: ys', hys⟩⟩
            (by simp at hfuel ⊢; omega)
          rw [hrec]
          simp only [bind, Except.bind, pure, Except.pure]
          refine ⟨_, rfl, ?_⟩
          show x :: rest.2.val = _
          rw [hval, mergeRef_cons_cons, if_neg hlt]

/-- The recursive tuple merge sort is a stable sort. -/
theorem mergeSortTuple_outcome {lt : α → α → Bool} (hnt : NegTransOrder lt) :
    (t : AnyNTuple α) →
      ∃ r, mergeSortTupleRecursive (anyNTupleMergeOps (pureCompare lt)) t () = .ok r ∧
        SortOutcome lt true t.2.val r.2.val
  | ⟨m, ⟨xs, hxs⟩⟩ => by
    rw [mergeSortTupleRecursive]
    by_cases hsmall : xs.length ≤ 1
    · rw [dif_pos (show (anyNTupleMergeOps (pureCompare lt)).length
        ⟨m, ⟨xs, hxs⟩⟩ ≤ 1 from hsmall)]
      exact ⟨⟨m, ⟨xs, hxs⟩⟩, rfl, outcome_of_sorted true (pairwise_of_length_le_one hsmall)⟩
    · rw [dif_neg (show ¬ (anyNTupleMergeOps (pureCompare lt)).length
        ⟨m, ⟨xs, hxs⟩⟩ ≤ 1 from hsmall)]
      obtain ⟨rL, hL, oL⟩ := mergeSortTuple_outcome hnt
        ⟨(xs.take (xs.length / 2)).length, ⟨xs.take (xs.length / 2), rfl⟩⟩
      obtain ⟨rR, hR, oR⟩ := mergeSortTuple_outcome hnt
        ⟨(xs.drop (xs.length / 2)).length, ⟨xs.drop (xs.length / 2), rfl⟩⟩
      obtain ⟨mg, hmg, hval⟩ := mergeAnyNTupleLoop_ref lt
        (rL.2.val.length + rR.2.val.length + 1) rL rR (by omega)
      refine ⟨mg, ?_, ?_⟩
      · show (do
          let sortedLeft ← mergeSortTupleRecursive (anyNTupleMergeOps (pureCompare lt))
            ⟨(xs.take (xs.length / 2)).length, ⟨xs.take (xs.length / 2), rfl⟩⟩ ()
          let sortedRight ← mergeSortTupleRecursive (anyNTupleMergeOps (pureCompare lt))
            ⟨(xs.drop (xs.length / 2)).length, ⟨xs.drop (xs.length / 2), rfl⟩⟩ ()
          mergeAnyNTupleLoop (pureCompare lt)
            (sortedLeft.2.val.length + sortedRight.2.val.length + 1)
            sortedLeft sortedRight) = _
        rw [hL, hR]
        exact hmg
      · rw [hval]
        have h := merge_outcome hnt oL oR
        rwa [List.take_append_drop] at h
termination_by t => t.2.val.length
decreasing_by
  all_goals simp only [List.length_take, List.length_drop]; omega

theorem mergeSortNTuple_outcome {lt : α → α → Bool} (hnt : NegTransOrder lt) {n : Nat}
    (tuple : NTuple n α) :
    ∃ result, mergeSortNTuple (pureCompare lt) tuple = .ok result ∧
      SortOutcome lt true tuple.val result.val := by
  obtain ⟨r, hr, ho⟩ := mergeSortTuple_outcome hnt ⟨n, tuple⟩
  have hlen : r.2.val.length = n := by rw [ho.1.length_eq]; exact tuple.property
  refine ⟨⟨r.2.val, hlen⟩, ?_, ho⟩
  unfold mergeSortNTuple
  rw [hr]
  simp only [bind, Except.bind, pure, Except.pure]
  rw [dif_pos hlen]

end TupleSort

/-- `sort(x::NTuple; lt, rev, scratch)` with the default algorithm: for every strict weak order,
every pivot rule choosing an index in the current window and every scratch vector, it returns a
permutation of the tuple sorted by the effective order and stable (equivalent elements keep their
original relative order), both through the unrolled merge sort used for at most nine elements and
through `_sort!` on a copied vector for longer tuples. -/
def TupleSortStable : Prop :=
  ∀ (n : Nat) (α : Type) [Inhabited α] (lt : α → α → SortResult Bool)
      (pivot : Int → Int → Int) (keys : NTuple n α) (reverse : Option Bool)
      (scratch : Option (Array α)),
    EffectNegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    let effective := if reverse = some true then fun a b => lt b a else lt
    ∃ result,
      sortTupleTop (nTuplePublicOps n pivot) keys (defalgOther keys) lt () reverse lt scratch =
        .ok result ∧
      List.Perm keys.val result.val ∧ EffectSortedValues effective result.val ∧
      EffectStableWrt effective keys.val result.val

theorem tupleSortStable_proven : TupleSortStable := by
  intro n α _ lt pivot keys reverse scratch hnt hpivot
  obtain ⟨p, hp, rfl⟩ := effect_pure_cases hnt
  have hnte := negTransOrder_effective hp reverse
  have heffective :
      (if reverse = some true then
          fun a b => pureCompare (ε := SortException) p b a
        else pureCompare (ε := SortException) p) =
        pureCompare (ε := SortException)
          (if reverse = some true then fun a b => p b a else p) := by
    rw [pureCompare_swap, pureCompare_ite]
  obtain ⟨result, hcore, hout⟩ : ∃ result,
      sortTupleCore (nTupleCoreOps n pivot) keys .defaultStable
        (pureCompare (if reverse = some true then fun a b => p b a else p)) scratch =
          .ok result ∧
      SortOutcome (if reverse = some true then fun a b => p b a else p) true keys.val
        result.val := by
    unfold sortTupleCore
    by_cases hbig : (nTupleCoreOps (α := α) n pivot).length keys > 9
    · rw [if_pos hbig]
      obtain ⟨v', sc, hrun, hwin⟩ := sourceSortWindow_sorts defaultBracketNumerics pivot
        arrayStorage_laws hnte hpivot .defaultStable rfl keys.val.toArray
        { lo := 1, hi := Int.ofNat keys.val.toArray.size, scratch := scratch } (Int.le_refl 1)
        (by simp only [Int.ofNat_eq_natCast]; omega) (by simp)
      have hw : SortOutcome (if reverse = some true then fun a b => p b a else p) true
          keys.val v'.toList := by
        have := windowOutcome_whole (l := keys.val.toArray.toList) (by simpa using hwin)
        simpa [genericStable] using this
      have hlen : v'.toList.length = n := by rw [hw.1.length_eq]; exact keys.property
      refine ⟨⟨v'.toList, hlen⟩, ?_, hw⟩
      simp only [nTupleCoreOps, sourceSortBang, bind, Except.bind, hrun, pure, Except.pure]
      rw [dif_pos hlen]
    · rw [if_neg hbig]
      exact mergeSortNTuple_outcome hnte keys
  refine ⟨result, ?_, hout.1.symm, ?_, ?_⟩
  · unfold sortTupleTop
    simp only [nTuplePublicOps, defalgOther, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure, id, heffective, hcore]
  · rw [heffective]
    exact (effectSortedValues_pure _ _).2 ((sortedValues_iff_pairwise hnte _).2 hout.2.1)
  · rw [heffective]
    exact (effectStableWrt_pure _ _ _).2 (hout.2.2 rfl)


/-! ## `sort_chunks!` -/

section Chunks

variable {α : Type} [Inhabited α]

/-- The chunk starts `first, first + W, …` of `k` consecutive chunks of width `W`. -/
def chunkStarts (first : Int) (W : Nat) : Nat → List Int
  | 0 => []
  | k + 1 => first :: chunkStarts (first + W) W k

theorem range_map_chunkStarts (W : Nat) :
    ∀ (k : Nat) (first : Int),
      (List.range k).map (fun i => first + Int.ofNat (i * W)) = chunkStarts first W k
  | 0, _ => rfl
  | k + 1, first => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, chunkStarts,
      ← range_map_chunkStarts W k (first + W)]
    simp only [Int.ofNat_eq_natCast, Nat.zero_mul, Int.natCast_zero, Int.add_zero,
      Function.comp_def, Nat.succ_mul, Int.natCast_add]
    congr 1
    apply List.map_congr_left
    intro i _
    omega

theorem chunk_starts (pivot : Int → Int → Int) {W : Nat} (hW : 0 < W) (first : Int) (k : Nat) :
    (arrayChunkLoopOps (α := α) pivot).starts first W (first - 1 + Int.ofNat (k * W)) =
      .ok (chunkStarts first W k) := by
  simp only [arrayChunkLoopOps]
  rw [if_neg (by omega)]
  cases k with
  | zero =>
    rw [if_pos (by simp only [Nat.zero_mul, Int.ofNat_eq_natCast, Int.natCast_zero]; omega)]
    rfl
  | succ k =>
    rw [if_neg (by simp only [Int.ofNat_eq_natCast, Nat.succ_mul, Int.natCast_add]; omega)]
    have hdiv : (first - 1 + Int.ofNat ((k + 1) * W) - first) / Int.ofNat W + 1 =
        ((k + 1 : Nat) : Int) := by
      have h1 : first - 1 + Int.ofNat ((k + 1) * W) - first =
          ((W : Int) - 1) + (k : Int) * (W : Int) := by
        simp only [Int.ofNat_eq_natCast, Nat.succ_mul, Int.natCast_add, Int.natCast_mul]
        omega
      rw [h1, Int.ofNat_eq_natCast, Int.add_mul_ediv_right _ _ (by omega),
        Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      simp only [Int.natCast_add, Int.natCast_one]; omega
    rw [hdiv, Int.toNat_natCast, range_map_chunkStarts]

/-- Each slice of `after` is an outcome of sorting the matching slice of `before` (a sorted
permutation, stable when `stable`), and both have the same number of slices. -/
def SlicesOutcome (lt : α → α → Bool) (stable : Bool) :
    List (List α) → List (List α) → Prop
  | [], [] => True
  | row :: rows, row' :: rows' => SortOutcome lt stable row row' ∧ SlicesOutcome lt stable rows rows'
  | _, _ => False

theorem slicesOutcome_length {lt : α → α → Bool} {s : Bool} :
    ∀ {rows sorted : List (List α)}, SlicesOutcome lt s rows sorted →
      sorted.length = rows.length ∧ sorted.flatten.length = rows.flatten.length
  | [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, [], h => absurd h id
  | [], _ :: _, h => absurd h id
  | r :: rs, r' :: rs', h => by
    obtain ⟨h1, h2⟩ := slicesOutcome_length h.2
    simp only [List.length_cons, List.flatten_cons, List.length_append, h1, h2,
      h.1.1.length_eq, and_self]

theorem slicesOutcome_rows {lt : α → α → Bool} {s : Bool} {W : Nat} :
    ∀ {rows sorted : List (List α)}, SlicesOutcome lt s rows sorted →
      (∀ row ∈ rows, row.length = W) → ∀ row ∈ sorted, row.length = W
  | [], [], _, _ => fun _ h => absurd h List.not_mem_nil
  | _ :: _, [], h, _ => absurd h id
  | [], _ :: _, h, _ => absurd h id
  | r :: rs, r' :: rs', h, hrows => by
    intro row hrow
    rcases List.mem_cons.1 hrow with rfl | hrow
    · rw [h.1.1.length_eq]; exact hrows r List.mem_cons_self
    · exact slicesOutcome_rows h.2 (fun x hx => hrows x (List.mem_cons_of_mem r hx)) row hrow

theorem forIn_chunks (g : Array α → Int → SortResult (Array α)) (W : Nat)
    (lt : α → α → Bool) (s : Bool)
    (hg : ∀ (v : Array α) (P R Post : List α), v.toList = P ++ R ++ Post → R.length = W →
      ∃ v' R', g v ((P.length : Int) + 1) = .ok v' ∧ v'.toList = P ++ R' ++ Post ∧
        SortOutcome lt s R R') :
    ∀ (rows : List (List α)) (v : Array α) (P : List α) (first : Int),
      (P.length : Int) + 1 = first → v.toList = P ++ rows.flatten →
      (∀ row ∈ rows, row.length = W) →
      ∃ v' sorted,
        forIn (chunkStarts first W rows.length) v
          (fun lo r => g r lo >>= fun v => pure (ForInStep.yield v)) = .ok v' ∧
        v'.toList = P ++ sorted.flatten ∧ SlicesOutcome lt s rows sorted
  | [], v, P, _, _, hv, _ => ⟨v, [], rfl, by simpa using hv, trivial⟩
  | row :: rows, v, P, first, hfirst, hv, hrows => by
    obtain ⟨v1, R', hg1, hv1, ho⟩ := hg v P row rows.flatten
      (by rw [hv]; simp [List.append_assoc]) (hrows row List.mem_cons_self)
    have hlen : R'.length = W := by rw [ho.1.length_eq]; exact hrows row List.mem_cons_self
    obtain ⟨v', sorted, hfor, hv', hall⟩ := forIn_chunks g W lt s hg rows v1 (P ++ R')
      (first + W) (by simp only [List.length_append]; omega)
      (by simp [hv1, List.append_assoc])
      (fun r hr => hrows r (List.mem_cons_of_mem row hr))
    refine ⟨v', R' :: sorted, ?_, by rw [hv']; simp [List.append_assoc], ho, hall⟩
    simp only [List.length_cons, chunkStarts, List.forIn_cons]
    rw [← hfirst, hg1]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [hfirst]
    exact hfor

theorem chunks_withScratch_eq {V K N Alg O Scratch E : Type}
    (ops : SortChunksLoopOps V K N Alg O Scratch E) (v : V) (n : N) (alg : Alg) (order : O)
    (sc : Scratch) (first last : K) :
    sortChunksWithScratch ops v n alg order sc first last =
      (ops.starts first n last >>= fun starts => forIn starts v
        (fun lo r => ops.sortWithScratch r alg order lo (ops.chunkEnd lo n) sc >>= fun v =>
          pure (ForInStep.yield v)) >>= fun s => pure s) := rfl

variable (pivot : Int → Int → Int) {order : α → α → Bool} (hnt : NegTransOrder order)
  (hpivot : ∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b)
  (alg : Algorithm (BracketSortTarget Int) Int) (hfull : isFullSortAlgorithm alg = true)

include hnt hpivot hfull in
/-- One `_sort!(Av, alg, order, (; lo, hi = lo + n - 1, scratch))` call on the chunk that starts
after `P`. -/
theorem chunk_window (W : Nat) (sc : Option (Array α)) (v : Array α) (P R Post : List α)
    (hv : v.toList = P ++ R ++ Post) (hR : R.length = W) :
    ∃ v' sc' R', sourceSortWindow arrayStorage defaultBracketNumerics pivot v alg
        (pureCompare order)
        { lo := (P.length : Int) + 1, hi := (P.length : Int) + 1 + Int.ofNat W - 1,
          scratch := sc } = .ok (v', sc') ∧
      v'.toList = P ++ R' ++ Post ∧ SortOutcome order (genericStable alg) R R' := by
  obtain ⟨v', sc', hrun, hwin⟩ := sourceSortWindow_sorts defaultBracketNumerics pivot
    arrayStorage_laws hnt hpivot alg hfull v
    { lo := (P.length : Int) + 1, hi := (P.length : Int) + 1 + Int.ofNat W - 1, scratch := sc }
    (by simp only; omega) (by simp only [Int.ofNat_eq_natCast]; omega)
    (by simp only [hv, List.length_append, Int.ofNat_eq_natCast]; omega)
  rw [hv] at hwin
  obtain ⟨R', hv', ho⟩ := windowOutcome_at hwin rfl
    (by simp only [Int.ofNat_eq_natCast]; omega)
  exact ⟨v', sc', R', hrun, hv', ho⟩

include hnt hpivot hfull in
theorem chunks_withScratch_sorts {W : Nat} (hW : 0 < W) (sc : Array α) :
    ∀ (rows : List (List α)) (v : Array α) (P : List α) (first last : Int),
      (P.length : Int) + 1 = first → last = first - 1 + Int.ofNat (rows.length * W) →
      v.toList = P ++ rows.flatten → (∀ row ∈ rows, row.length = W) →
      ∃ v' sorted,
        sortChunksWithScratch (arrayChunkLoopOps pivot) v W alg (pureCompare order) sc first last =
          .ok v' ∧
        v'.toList = P ++ sorted.flatten ∧ SlicesOutcome order (genericStable alg) rows sorted := by
  intro rows v P first last hfirst hlast hv hrows
  have hg : ∀ (v : Array α) (P R Post : List α), v.toList = P ++ R ++ Post → R.length = W →
      ∃ v' R', (arrayChunkLoopOps (α := α) pivot).sortWithScratch v alg (pureCompare order)
          ((P.length : Int) + 1)
          ((arrayChunkLoopOps (α := α) pivot).chunkEnd ((P.length : Int) + 1) W) sc = .ok v' ∧
        v'.toList = P ++ R' ++ Post ∧ SortOutcome order (genericStable alg) R R' := by
    intro v P R Post hv hR
    obtain ⟨v', sc', R', hrun, hv', ho⟩ := chunk_window pivot hnt hpivot alg hfull W (some sc)
      v P R Post hv hR
    refine ⟨v', R', ?_, hv', ho⟩
    simp only [arrayChunkLoopOps, sourceSortBang, hrun, bind, Except.bind, pure, Except.pure]
  obtain ⟨v', sorted, hfor, hv', hall⟩ := forIn_chunks (fun r lo =>
      (arrayChunkLoopOps pivot).sortWithScratch r alg (pureCompare order) lo
        ((arrayChunkLoopOps pivot).chunkEnd lo W) sc) W order (genericStable alg) hg
    rows v P first hfirst hv hrows
  refine ⟨v', sorted, ?_, hv', hall⟩
  rw [chunks_withScratch_eq, hlast, chunk_starts pivot hW]
  show (forIn (chunkStarts first W rows.length) v _ >>=
    fun s => (pure s : SortResult (Array α))) = _
  rw [hfor]
  rfl

include hnt hpivot hfull in
theorem chunks_noScratch_loop {W : Nat} (hW : 0 < W) :
    ∀ (rows : List (List α)) (v : Array α) (P : List α) (first last : Int),
      (P.length : Int) + 1 = first → last = first - 1 + Int.ofNat (rows.length * W) →
      v.toList = P ++ rows.flatten → (∀ row ∈ rows, row.length = W) →
      ∃ v' sorted,
        sortChunksNoScratch.loop (arrayChunkLoopOps pivot) W alg (pureCompare order) last v
            (chunkStarts first W rows.length) = .ok v' ∧
        v'.toList = P ++ sorted.flatten ∧ SlicesOutcome order (genericStable alg) rows sorted
  | [], v, P, _, _, _, _, hv, _ => ⟨v, [], rfl, by simpa using hv, trivial⟩
  | row :: rows, v, P, first, last, hfirst, hlast, hv, hrows => by
    obtain ⟨v1, sc1, R', hrun, hv1, ho⟩ := chunk_window pivot hnt hpivot alg hfull W none v P
      row rows.flatten (by rw [hv]; simp [List.append_assoc]) (hrows row List.mem_cons_self)
    have hlen : R'.length = W := by rw [ho.1.length_eq]; exact hrows row List.mem_cons_self
    have hrun' : (arrayChunkLoopOps (α := α) pivot).sortWithoutScratch v alg
        (pureCompare order) first
        ((arrayChunkLoopOps (α := α) pivot).chunkEnd first W) = .ok (v1, sc1) := by
      simp only [arrayChunkLoopOps]; rw [← hfirst]; exact hrun
    have hP' : ((P ++ R').length : Int) + 1 = first + W := by
      simp only [List.length_append]; omega
    have hlast' : last = first + W - 1 + Int.ofNat (rows.length * W) := by
      rw [hlast]; simp only [List.length_cons, Int.ofNat_eq_natCast, Nat.succ_mul,
        Int.natCast_add]; omega
    have hv1' : v1.toList = (P ++ R') ++ rows.flatten := by simp [hv1, List.append_assoc]
    have hrows' : ∀ r ∈ rows, r.length = W := fun r hr => hrows r (List.mem_cons_of_mem row hr)
    simp only [List.length_cons, chunkStarts]
    rw [sortChunksNoScratch.loop, hrun']
    simp only [bind, Except.bind]
    cases sc1 with
    | none =>
      obtain ⟨v', sorted, hloop, hv', hall⟩ :=
        chunks_noScratch_loop hW rows v1 (P ++ R') (first + W) last hP' hlast' hv1' hrows'
      exact ⟨v', R' :: sorted, hloop, by rw [hv']; simp [List.append_assoc], ho, hall⟩
    | some s =>
      obtain ⟨v', sorted, hrun2, hv', hall⟩ := chunks_withScratch_sorts pivot hnt hpivot alg
        hfull hW s rows v1 (P ++ R') (first + W) last hP' hlast' hv1' hrows'
      exact ⟨v', R' :: sorted, hrun2, by rw [hv']; simp [List.append_assoc], ho, hall⟩

theorem length_flatten_rows {W : Nat} :
    ∀ (rows : List (List α)), (∀ row ∈ rows, row.length = W) →
      rows.flatten.length = rows.length * W
  | [], _ => by simp
  | row :: rows, h => by
    simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul,
      h row List.mem_cons_self,
      length_flatten_rows rows (fun r hr => h r (List.mem_cons_of_mem row hr))]
    omega

include hnt hpivot hfull in
/-- `sort_chunks!(Av, n, alg, order, scratch)` on a vector made of whole chunks of width `n`
sorts every chunk, with or without scratch space. -/
theorem sortChunksDispatch_sorts {W : Nat} (hW : 0 < W) (rows : List (List α))
    (values : Array α) (scratch : Option (Array α)) (hrows : ∀ row ∈ rows, row.length = W)
    (hv : values.toList = rows.flatten) :
    ∃ result sorted,
      sortChunksDispatch (arrayChunkDispatchOps pivot) values W alg (pureCompare order) scratch =
        .ok result ∧
      result.toList = sorted.flatten ∧ SlicesOutcome order (genericStable alg) rows sorted := by
  have hsize : Int.ofNat values.size = 1 - 1 + Int.ofNat (rows.length * W) := by
    rw [← length_flatten_rows rows hrows, ← hv]; simp
  have hv0 : values.toList = [] ++ rows.flatten := hv
  cases scratch with
  | none =>
    obtain ⟨v', sorted, hloop, hv', hall⟩ := chunks_noScratch_loop pivot hnt hpivot alg hfull hW
      rows values [] 1 (Int.ofNat values.size) rfl hsize hv0 hrows
    have hstarts : (arrayChunkLoopOps (α := α) pivot).starts 1 W (Int.ofNat values.size) =
        .ok (chunkStarts 1 W rows.length) := by
      rw [hsize]; exact chunk_starts pivot hW 1 rows.length
    refine ⟨v', sorted, ?_, by simpa using hv', hall⟩
    show sortChunksNoScratch (arrayChunkLoopOps pivot) values W alg (pureCompare order) 1
      (Int.ofNat values.size) = _
    unfold sortChunksNoScratch
    rw [hstarts]
    exact hloop
  | some sc =>
    obtain ⟨v', sorted, hrun, hv', hall⟩ := chunks_withScratch_sorts pivot hnt hpivot alg hfull
      hW sc rows values [] 1 (Int.ofNat values.size) rfl hsize hv0 hrows
    exact ⟨v', sorted, hrun, by simpa using hv', hall⟩

omit [Inhabited α] in
theorem sliceRows_flatten {W : Nat} :
    ∀ (rows : List (List α)), (∀ row ∈ rows, row.length = W) →
      sliceRows W rows.length rows.flatten = rows
  | [], _ => rfl
  | row :: rows, h => by
    have hrow := h row List.mem_cons_self
    have ih := sliceRows_flatten rows (fun r hr => h r (List.mem_cons_of_mem row hr))
    unfold sliceRows at ih ⊢
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [Nat.zero_mul, List.drop_zero, List.flatten_cons]
    rw [List.take_left' hrow]
    congr 1
    conv => rhs; rw [← ih]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.succ_mul]
    rw [show i * W + W = row.length + i * W by omega, List.drop_append,
      List.drop_eq_nil_of_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

theorem dimensionCopy_sorts {A Axes : Type} (layout : DimensionArrayLayout A α Axes)
    (hlaws : DimensionLayoutLaws layout) (pivot : Int → Int → Int) {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (hpivot : ∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b)
    (array : A) (dimension : Nat) (algorithm : Algorithm (BracketSortTarget Int) Int)
    (hfull : isFullSortAlgorithm algorithm = true) (reverse : Option Bool)
    (scratch : Option (Array α)) (h1 : 1 ≤ dimension) (h2 : dimension ≤ layout.ndims array)
    (hpos : 0 < layout.axisLength array dimension) :
    ∃ result, sortArrayDimension (dimensionArrayOps layout pivot)
        array dimension algorithm (pureCompare lt) () reverse (pureCompare lt) scratch =
          .ok result ∧
      layout.axes result = layout.axes array ∧
      SlicesOutcome (if reverse = some true then fun a b => lt b a else lt)
        (genericStable (sourceApplyInitialOptimizations algorithm))
        (layout.slices array dimension) (layout.slices result dimension) := by
  obtain ⟨hrowsLen, hcase⟩ := hlaws array dimension h1 h2
  have hnte := negTransOrder_effective hnt reverse
  have heffective :
      (if reverse = some true then
          fun a b => pureCompare (ε := SortException) lt b a
        else pureCompare (ε := SortException) lt) =
        pureCompare (ε := SortException)
          (if reverse = some true then fun a b => lt b a else lt) := by
    rw [pureCompare_swap, pureCompare_ite]
  obtain ⟨result, sorted, hrun, hres, hout⟩ := sortChunksDispatch_sorts pivot hnte hpivot
    (sourceApplyInitialOptimizations algorithm) (isFull_applyInitial algorithm hfull) hpos
    (layout.slices array dimension) (layout.slices array dimension).flatten.toArray scratch
    hrowsLen (by simp)
  have hsize : result.size = (layout.slices array dimension).flatten.length := by
    rw [← Array.length_toList, hres]; exact (slicesOutcome_length hout).2
  have hslices : sliceRows (layout.axisLength array dimension)
      (layout.slices array dimension).length result.toList = sorted := by
    rw [hres, ← (slicesOutcome_length hout).1]
    exact sliceRows_flatten sorted (slicesOutcome_rows hout hrowsLen)
  unfold sortArrayDimension
  by_cases hd : dimension = 1
  · rw [if_pos hd] at hcase
    obtain ⟨hcopy, hreshape⟩ := hcase
    obtain ⟨final, hfinal, haxes, hsl⟩ := hreshape result hsize
    refine ⟨final, ?_, haxes, by rw [hsl, hslices]; exact hout⟩
    have hne : (dimension != (dimensionArrayOps layout pivot).dimensionOne) = false := by
      simp [dimensionArrayOps, hd]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    simp only [dimensionArrayOps, hcopy, liftSortJl_ok, bind, Except.bind]
    rw [heffective, hrun]
    simpa only [hfinal, liftSortJl_ok]
  · rw [if_neg hd] at hcase
    obtain ⟨permuted, hperm, hvec, hrestore⟩ := hcase
    obtain ⟨final, hfinal, haxes, hsl⟩ := hrestore result hsize
    refine ⟨final, ?_, haxes, by rw [hsl, hslices]; exact hout⟩
    have hne : (dimension != (dimensionArrayOps layout pivot).dimensionOne) = true := by
      simp [dimensionArrayOps, hd]
    simp only [hne, ↓reduceIte]
    simp only [dimensionArrayOps, hperm, hvec, liftSortJl_ok, bind, Except.bind]
    rw [heffective, hrun]
    simpa only [hfinal, liftSortJl_ok]

end Chunks

theorem effectSlicesOutcome_pure {ε α : Type} [Inhabited α] (p : α → α → Bool) (s : Bool) :
    ∀ rows sorted : List (List α),
      EffectSlicesOutcome (pureCompare (ε := ε) p) s rows sorted ↔ SlicesOutcome p s rows sorted
  | [], [] => Iff.rfl
  | [], _ :: _ => Iff.rfl
  | _ :: _, [] => Iff.rfl
  | row :: rows, row' :: rows' => by
    simp only [EffectSlicesOutcome, SlicesOutcome]
    rw [effectSortOutcome_pure, effectSlicesOutcome_pure p s rows rows']


def SortDimsChecked : Prop :=
  ∀ (A α Axes Index K : Type) [Inhabited α] (layout : SliceArrayLayout A α Axes Index K)
      (pivot : Int → Int → Int) (lt : α → α → SortResult Bool) (array : A) (dimension : Int)
      (algorithm : Algorithm (BracketSortTarget Int) Int) (reverse : Option Bool),
    SliceLayoutLaws layout → EffectNegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    let ops := sliceArrayOps layout pivot
    let valid := 1 ≤ dimension ∧ dimension ≤ Int.ofNat (layout.ndims array)
    (valid →
      (dimension = 1 ∨ layout.axisLength array dimension.toNat < 30 ∨
        layout.slices array dimension.toNat ≠ []) →
      ∃ result, sortBangDimensions ops array dimension algorithm lt () reverse lt none true =
          .ok result ∧
        layout.axes result = layout.axes array ∧
        EffectSlicesOutcome (if reverse = some true then fun a b => lt b a else lt)
          (genericStable (sourceApplyInitialOptimizations algorithm))
          (layout.slices array dimension.toNat) (layout.slices result dimension.toNat)) ∧
    (¬ valid →
      sortBangDimensions ops array dimension algorithm lt () reverse lt none true =
        .error (.jl (.argumentError "dimension out of range")))


/-- `sort_chunks!(Av, n, alg, order, scratch)` on a `Vector` whose length is a multiple of the
chunk width `n` (as in its only caller, `sort(A; dims)`, where `n = size(A, dims)`): for every
strict weak order, pivot rule choosing an index in the current window, algorithm that sorts on its
own and scratch argument (`nothing` or a vector), it succeeds and replaces every consecutive chunk
of `n` elements by a sorted permutation of that chunk, stable when the algorithm is stable. -/
def ChunkSortCorrect : Prop :=
  ∀ (α : Type) [Inhabited α] (pivot : Int → Int → Int) (values : Array α)
      (rows : List (List α)) (width : Nat) (algorithm : Algorithm (BracketSortTarget Int) Int)
      (order : α → α → SortResult Bool) (scratch : Option (Array α)),
    0 < width → EffectNegTransOrder order →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    (∀ row ∈ rows, row.length = width) → values.toList = rows.flatten →
    ∃ result sorted,
      sortChunksDispatch (arrayChunkDispatchOps pivot) values width algorithm order scratch =
        .ok result ∧
      result.toList = sorted.flatten ∧
      EffectSlicesOutcome order (genericStable algorithm) rows sorted

theorem chunkSortCorrect_proven : ChunkSortCorrect := by
  intro α _ pivot values rows width algorithm order scratch hW hnt hpivot hfull hrows hv
  obtain ⟨p, hp, rfl⟩ := effect_pure_cases hnt
  obtain ⟨result, sorted, hrun, hres, hout⟩ :=
    sortChunksDispatch_sorts pivot hp hpivot algorithm hfull hW rows values scratch hrows hv
  exact ⟨result, sorted, hrun, hres,
    (effectSlicesOutcome_pure p (genericStable algorithm) rows sorted).2 hout⟩

/-- `sort(A; dims, alg, lt, rev, scratch)` for a dimension of positive length, on any array whose
layout obeys the documented `A[:]`/`reshape` and `permutedims`/`vec` laws: for every strict weak
order, pivot rule choosing an index in the current window and algorithm that sorts on its own, it
returns an array with the same axes whose every slice along `dims` is a sorted permutation of the
original slice under the effective order, stable whenever the algorithm after
`InitialOptimizations` is stable. -/
def MultidimensionalCopyCorrect : Prop :=
  ∀ (A α Axes : Type) [Inhabited α] (layout : DimensionArrayLayout A α Axes)
      (pivot : Int → Int → Int) (lt : α → α → SortResult Bool) (array : A) (dimension : Nat)
      (algorithm : Algorithm (BracketSortTarget Int) Int) (reverse : Option Bool)
      (scratch : Option (Array α)),
    DimensionLayoutLaws layout → EffectNegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    1 ≤ dimension → dimension ≤ layout.ndims array →
    0 < layout.axisLength array dimension →
    ∃ result, sortArrayDimension (dimensionArrayOps layout pivot)
        array dimension algorithm lt () reverse lt scratch = .ok result ∧
      layout.axes result = layout.axes array ∧
      EffectSlicesOutcome (if reverse = some true then fun a b => lt b a else lt)
        (genericStable (sourceApplyInitialOptimizations algorithm))
        (layout.slices array dimension) (layout.slices result dimension)

theorem multidimensionalCopyCorrect_proven : MultidimensionalCopyCorrect := by
  intro A α Axes _ layout pivot lt array dimension algorithm reverse scratch hlaws hnt hpivot
    hfull h1 h2 hpos
  obtain ⟨p, hp, rfl⟩ := effect_pure_cases hnt
  obtain ⟨result, hrun, haxes, hout⟩ := dimensionCopy_sorts layout hlaws pivot hp hpivot
    array dimension algorithm hfull reverse scratch h1 h2 hpos
  have heffective :
      (if reverse = some true then
          fun a b => pureCompare (ε := SortException) p b a
        else pureCompare (ε := SortException) p) =
        pureCompare (ε := SortException)
          (if reverse = some true then fun a b => p b a else p) := by
    rw [pureCompare_swap, pureCompare_ite]
  refine ⟨result, ?_, haxes, ?_⟩
  · simpa only [heffective] using hrun
  · rw [heffective]
    exact (effectSlicesOutcome_pure _ _ _ _).2 hout

/-- `sort(A; dims)` when `size(A, dims) == 0` (an empty array, which `sort!(A; dims)` sorts
without complaint): it should return an array with the same axes. -/
def DimensionCopyEmptyAxis : Prop :=
  ∀ (A α Axes : Type) [Inhabited α] (layout : DimensionArrayLayout A α Axes)
      (pivot : Int → Int → Int) (lt : α → α → SortResult Bool) (array : A) (dimension : Nat)
      (algorithm : Algorithm (BracketSortTarget Int) Int) (reverse : Option Bool)
      (scratch : Option (Array α)),
    DimensionLayoutLaws layout → EffectNegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    1 ≤ dimension → dimension ≤ layout.ndims array →
    layout.axisLength array dimension = 0 →
    ∃ result, sortArrayDimension (dimensionArrayOps layout pivot)
        array dimension algorithm lt () reverse lt scratch = .ok result ∧
      layout.axes result = layout.axes array

/-- Column-major `0 × c` matrices, identified by their column count `c`. -/
def emptyRowsLayout (α : Type) : DimensionArrayLayout Nat α Nat where
  ndims := fun _ => 2
  axisLength := fun c d => if d = 1 then 0 else c
  permute := fun c _ => .ok c
  vectorize := fun _ => .ok #[]
  copyLinear := fun _ => .ok #[]
  inversePermutation := id
  restorePermuted := fun c _ _ => .ok c
  reshapeOriginalAxes := fun c _ => .ok c
  axes := id
  slices := fun c d => if d = 1 then List.replicate c [] else []

theorem emptyRowsLayout_laws (α : Type) : DimensionLayoutLaws (emptyRowsLayout α) := by
  intro c dimension h1 h2
  simp only [emptyRowsLayout] at h2 ⊢
  by_cases hd : dimension = 1
  · subst hd
    refine ⟨fun row hrow => by simp at hrow; simp [hrow], ?_⟩
    simp only [↓reduceIte]
    refine ⟨by simp, fun updated hsize => ⟨c, rfl, rfl, ?_⟩⟩
    have hu : updated.toList = [] := by
      apply List.eq_nil_of_length_eq_zero; simpa using hsize
    simp only [sliceRows, hu, List.drop_nil, List.take_nil]
    rw [List.map_const', List.length_range, List.length_replicate]
  · refine ⟨fun row hrow => by simp [hd] at hrow, ?_⟩
    simp only [hd, ↓reduceIte]
    refine ⟨c, rfl, by simp, fun updated _ => ⟨c, rfl, rfl, by simp [sliceRows]⟩⟩

theorem dimensionCopyEmptyAxis_refuted : ¬ DimensionCopyEmptyAxis := by
  intro h
  obtain ⟨result, hrun, _⟩ := h Nat Int Nat (emptyRowsLayout Int) juliaPivot intCompare 3 1
    .defaultStable none none (emptyRowsLayout_laws Int) intCompare_order juliaPivot_bounds
    rfl (by decide) (by decide) rfl
  have herr : sortArrayDimension (dimensionArrayOps (emptyRowsLayout Int) juliaPivot) 3 1
      .defaultStable intCompare () none intCompare none =
        .error (.jl (.argumentError "step cannot be zero")) := rfl
  rw [herr] at hrun
  cases hrun

/-! ## Legacy entry points and partial sorting on any storage -/

/-- The legacy `sort!(v, lo, hi, InsertionSort, o)` entry points (with and without a scratch
argument) and `sort!(v, InsertionSort, o)`, on any one-based storage obeying the `AbstractVector`
laws: for every strict weak order and window `lo:hi` inside the vector they all return the same
vector, whose window is a stable sorted permutation of the original window with the rest
unchanged (the whole vector for `sort!(v, a, o)`); a nonempty window with `lo < 1` or
`hi > length(v)` throws `BoundsError` for every legacy algorithm. -/
def LegacyInvalidWindowRejected : Prop :=
  (∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α)
      (lt : α → α → SortResult Bool) (values : V) (scratch : Array α) (lo hi : Int),
    StorageLaws S E → EffectNegTransOrder lt →
    1 ≤ lo → lo ≤ hi + 1 → hi ≤ ((E values).length : Int) →
    (∃ result,
      legacySortBounds (storageLegacyOps S lt) values lo hi .insertion () = .ok result ∧
      legacySortIgnoredScratch (storageLegacyOps S lt) values lo hi .insertion () () =
        .ok result ∧
      legacySortWithScratch (storageLegacyOps S lt) values lo hi .insertion () scratch =
        .ok result ∧
      EffectWindowOutcome lt true (E values) (E result) lo hi) ∧
    (∃ wholeResult,
      legacySortWhole (storageLegacyOps S lt) values .insertion () = .ok wholeResult ∧
      EffectSortOutcome lt true (E values) (E wholeResult))) ∧
  (∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α)
      (lt : α → α → SortResult Bool) (values : V) (scratch : Array α) (algorithm : LegacyArrayAlgorithm)
      (lo hi : Int),
    StorageLaws S E → lo ≤ hi → (lo < 1 ∨ ((E values).length : Int) < hi) →
    legacySortBounds (storageLegacyOps S lt) values lo hi algorithm () = .error (.jl .boundsError) ∧
    legacySortIgnoredScratch (storageLegacyOps S lt) values lo hi algorithm () () =
      .error (.jl .boundsError) ∧
    legacySortWithScratch (storageLegacyOps S lt) values lo hi algorithm () scratch =
      .error (.jl .boundsError))


/-- `_sort!(v, a, o, kw)` for the legacy algorithms: with no recorded entry algorithm it runs the
legacy `sort!` method, so on any lawful storage `InsertionSort` returns the stably sorted window
with the rest unchanged; when the keywords record that `_sort!` was entered from `sort!` with the
same algorithm, it throws the "not defined for this algorithm" `ArgumentError` instead of
recursing. -/
def LegacyDispatchRejectsCycles : Prop :=
  (∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α)
      (lt : α → α → SortResult Bool) (values : V) (lo hi : Int) (scratch : Option (Array α)),
    StorageLaws S E → EffectNegTransOrder lt →
    1 ≤ lo → lo ≤ hi + 1 → hi ≤ ((E values).length : Int) →
    let ops : LegacyDispatchOps V Int LegacyArrayAlgorithm Unit
        (LegacyArrayKeywords α) (Option (Array α)) JuliaLean.base.sort.SortException := {
      getKeywords := fun kw => .ok (kw.lo, kw.hi, kw.scratch, kw.entry)
      sameAlgorithm := BEq.beq
      undefinedAlgorithm := fun _ _ _ =>
        .jl (.argumentError "Base.Sort._sort! is not defined for this algorithm")
      legacySort := fun current lo' hi' alg ord =>
        legacySortBounds (storageLegacyOps S lt) current lo' hi' alg ord
    }
    ∃ expected,
      legacySortDispatch ops values .insertion () ⟨lo, hi, scratch, none⟩ =
        .ok (expected, scratch) ∧
      EffectWindowOutcome lt true (E values) (E expected) lo hi) ∧
  (∀ (V K Alg O Kws Scratch : Type)
      (ops : LegacyDispatchOps V K Alg O Kws Scratch JlError)
      (vector : V) (algorithm entry : Alg) (order : O) (keywords : Kws)
      (lo hi : K) (scratch : Scratch) (message : String),
    ops.getKeywords keywords = .ok (lo, hi, scratch, some entry) →
    ops.sameAlgorithm entry algorithm = true →
    ops.undefinedAlgorithm vector algorithm order = .argumentError message →
    legacySortDispatch ops vector algorithm order keywords =
      .error (.argumentError message))


/-- The elements `maybeview` returns, as a list: `[v[k]]` for an index, the selected elements for a
range. -/
def partialResultList {α : Type} : PartialResult α → List α
  | .element value => [value]
  | .elements values => values

/-- `partialsort!(v, k)` and `partialsort(v, k)` on any lawful storage: for every strict weak
order and every target (an index, a unit range or a stepped range) inside the vector, both return
the elements a full sort would place at the target positions. -/
def PartialSortRangeCorrect : Prop :=
  ∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α)
      (lt : α → α → SortResult Bool) (pivot : Int → Int → Int) (values : V)
      (target : BracketSortTarget Int),
    StorageLaws S E → EffectNegTransOrder lt →
    (E values).length ≤ IntTy.max .i64 →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    (∀ index, index ∈ bracketTargetIndices target →
      1 ≤ index ∧ index ≤ ((E values).length : Int)) →
    let expected := sortRef (comparisonTrue lt) (E values)
    let selected := (bracketTargetIndices target).filterMap fun index =>
      expected[(index - 1).toNat]?
    ∃ result,
      partialSortBang (storagePartialSortOps S defaultBracketNumerics pivot) values target lt none =
        .ok result ∧
      partialSort (storagePartialSortOps S defaultBracketNumerics pivot) (fun source => .ok source)
        (fun (less : α → α → SortResult Bool) (_ : Unit) (_ : Option Bool) _ => less)
        values target lt () none lt
        { lo := 1, hi := S.length values, scratch := none } = .ok result ∧
      partialResultList result = selected


/-- `partialsort!(v, k)` with an empty stepped target range returns an empty collection, on any
lawful storage and element type. -/
def PartialSortEmptyRange : Prop :=
  ∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α)
      (lt : α → α → SortResult Bool) (pivot : Int → Int → Int) (values : V)
      (first step last : Int),
    StorageLaws S E → EffectNegTransOrder lt →
    partialSortBang (storagePartialSortOps S defaultBracketNumerics pivot) values
      (.ordinal first step last 0) lt none = .ok (.elements [])


/-- `sort!(v, PartialQuickSort(lo:hi), o)` (the legacy `_partialquicksort!`) on any lawful storage
places at every target position the element a full sort would put there, including stepped and
reversed target ranges. -/
def LegacyPartialRangeCorrect : Prop :=
  ∀ (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α)
      (lt : α → α → SortResult Bool) (values : V) (first step last : Int) (length : Nat),
    StorageLaws S E → EffectNegTransOrder lt → step ≠ 0 →
    let target := (List.range length).map fun index => first + Int.ofNat index * step
    (∀ index, index ∈ target → 1 ≤ index ∧ index ≤ ((E values).length : Int)) →
    0 < length →
    last = first + Int.ofNat (length - 1) * step →
    let expected := sortRef (comparisonTrue lt) (E values)
    ∃ result,
      legacyPartialQuickSortBang (storagePartialQuickOps S lt)
        values 1 (Int.ofNat (S.length values)) (first, last) () = .ok result ∧
      target.filterMap (fun index => (E result)[(index - 1).toNat]?) =
        target.filterMap (fun index => expected[(index - 1).toNat]?)


/-- `send_to_end!(f, v; lo, hi)` returns for every window `lo ≤ hi` of any lawful storage (it is
documented to operate on `view(v, lo:hi)`). -/
def SendToEndInBounds : Prop :=
  ∀ (V α : Type) (S : VectorStorage V α) (E : V → List α) (predicate : α → Bool) (values : V)
      (lo hi : Int),
    StorageLaws S E → lo ≤ hi →
    ∃ last result,
      (sendToEndBang (storageSendToEndOps S)
        (fun value => fun state => .ok (predicate value, state))
        ⟨1, 1, S.length values⟩ (some lo) (some hi)).run values = .ok (last, result)


/-- `partialsortperm(v, k)` and `partialsortperm!(ix, v, k)` on any lawful storage, with index
vectors of any fixed-width integer type able to hold the target positions: for every strict weak
order, both return the indices that a stable full `sortperm` would place at the target positions
(`partialsortperm!` whenever its index type can hold every index of `v`). -/
def PartialSortpermIndexTypeCorrect : Prop :=
  ∀ (t : IntTy) (V α : Type) [Inhabited α] (S : VectorStorage V α) (E : V → List α)
      (less : α → α → SortResult Bool) (values : V) (target : BracketSortTarget Int)
      (pivot : Int → Int → Int) (reverse : Option Bool),
    StorageLaws S E → EffectNegTransOrder less →
    (bracketTargetIndices target).Nodup →
    ((E values).length : Int) ≤ IntTy.max .i64 →
    (∀ index, index ∈ bracketTargetIndices target →
      1 ≤ index ∧ index ≤ ((E values).length : Int) ∧ IntTy.min t ≤ index ∧
        index ≤ IntTy.max t) →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    let effective := if reverse = some true then fun a b => less b a else less
    let ops := storagePartialSortpermOps S t pivot
    let initial := Array.replicate (S.length values) (JInt.wrap t 0)
    ∃ result,
      partialSortperm ops values target less () reverse effective false = .ok result ∧
      (((E values).length : Int) ≤ IntTy.max t →
        partialSortpermBang ops initial values target less () reverse
          effective false = .ok result) ∧
      let indices := oneBasedIndices (E values).length
      let expected := sortRef (fun a b =>
        let left := (E values)[a - 1]?.getD default
        let right := (E values)[b - 1]?.getD default
        comparisonTrue effective left right ||
          (comparisonFalse effective right left && decide (a < b))) indices
      result.map (fun value => value.val) =
        (bracketTargetIndices target).filterMap fun index =>
          (expected[(index - 1).toNat]?).map Int.ofNat


/-! ## `sort!(A; dims)` -/

section SortDims

theorem applyInitial_idem (a : Algorithm (BracketSortTarget Int) Int) :
    sourceApplyInitialOptimizations (sourceApplyInitialOptimizations a) =
      sourceApplyInitialOptimizations a := by
  cases a <;> rfl

theorem forIn_skip {A D E : Type} (F : D → A → Except E (ForInStep A)) :
    ∀ (ds : List D) (cur : A), (∀ d ∈ ds, F d cur = .ok (.yield cur)) →
      forIn ds cur F = .ok cur
  | [], _, _ => rfl
  | d :: ds, cur, h => by
    rw [List.forIn_cons, h d List.mem_cons_self]
    exact forIn_skip F ds cur (fun d' hd' => h d' (List.mem_cons_of_mem d hd'))

variable {A α Axes Index K : Type} [Inhabited α] (layout : SliceArrayLayout A α Axes Index K)
  (pivot : Int → Int → Int)

/-- The facts the slice-sorting loops of `sort!(A; dims)` use about one array and dimension. -/
structure SliceFacts (array : A) (dimension : Nat) (indices : List Index)
    (sortRow : Array α → SortResult (Array α)) (lt : α → α → Bool) (s : Bool) : Prop where
  rows : ∀ row ∈ layout.slices array dimension, row.length = layout.axisLength array dimension
  count : (layout.slices array dimension).length = indices.length
  len : ∀ current, layout.axes current = layout.axes array →
    (layout.slices current dimension).length = indices.length
  view : ∀ current, layout.axes current = layout.axes array →
    ∀ (i : Nat) index row, indices[i]? = some index →
      (layout.slices current dimension)[i]? = some row →
      layout.view current (sliceSelectors layout current dimension index) = .ok row.toArray
  write : ∀ current, layout.axes current = layout.axes array →
    ∀ (i : Nat) index (updated : Array α), indices[i]? = some index →
      updated.size = layout.axisLength array dimension →
      ∃ result, layout.writeView current
          (sliceSelectors layout current dimension index) updated = .ok result ∧
        layout.axes result = layout.axes current ∧
        layout.slices result dimension =
          (layout.slices current dimension).set i updated.toList
  sort : ∀ row : List α, ∃ sorted, sortRow row.toArray = .ok sorted ∧ SortOutcome lt s row sorted.toList

theorem slicesOutcome_append {lt : α → α → Bool} {s : Bool} :
    ∀ {rows sorted : List (List α)} (row row' : List α), SlicesOutcome lt s rows sorted →
      SortOutcome lt s row row' → SlicesOutcome lt s (row :: rows) (row' :: sorted)
  | _, _, _, _, h, ho => ⟨ho, h⟩

theorem set_append_cons {β : Type} (done rest : List β) (x y : β) :
    (done ++ x :: rest).set done.length y = (done ++ [y]) ++ rest := by
  induction done with
  | nil => rfl
  | cons a done ih => simp [ih]

theorem getElem?_append_cons {β : Type} (done rest : List β) (x : β) :
    (done ++ x :: rest)[done.length]? = some x := by
  simp

theorem view_eq (current : A) (dimension : Nat) (index : Index) :
    (sliceArrayOps layout pivot).getView current dimension index =
      liftSortJl (layout.view current (sliceSelectors layout current dimension index)) := rfl

theorem setView_eq (current : A) (dimension : Nat) (index : Index) (values : Array α) :
    (sliceArrayOps layout pivot).setView current dimension index values =
      liftSortJl (layout.writeView current (sliceSelectors layout current dimension index) values) := rfl

theorem sliceLoopDirect {array : A} {dimension : Nat} {indices : List Index}
    {lt : α → α → Bool} {s : Bool} (alg : Algorithm (BracketSortTarget Int) Int)
    (scratch : Option (Array α))
    (hf : SliceFacts layout array dimension indices
      (fun row => (sliceArrayOps layout pivot).sortBang row alg (pureCompare lt) scratch) lt s) :
    ∀ (rest : List Index) (k : Nat) (current : A) (done : List (List α)),
      rest = indices.drop k → done.length = k → layout.axes current = layout.axes array →
      layout.slices current dimension = done ++ (layout.slices array dimension).drop k →
      ∃ final sortedRest,
        forIn rest current (fun index r => do
          let view ← (sliceArrayOps layout pivot).getView r dimension index
          let sorted ← (sliceArrayOps layout pivot).sortBang view alg (pureCompare lt) scratch
          let result ← (sliceArrayOps layout pivot).setView r dimension index sorted
          pure (ForInStep.yield result)) = .ok final ∧
        layout.axes final = layout.axes array ∧
        layout.slices final dimension = done ++ sortedRest ∧
        SlicesOutcome lt s ((layout.slices array dimension).drop k) sortedRest
  | [], k, current, done, hrest, hk, hax, hsl => by
    have hlen := hf.count
    have : (layout.slices array dimension).drop k = [] := by
      apply List.eq_nil_of_length_eq_zero
      have h0 : (indices.drop k).length = 0 := by rw [← hrest]; rfl
      simp only [List.length_drop] at h0 ⊢; omega
    refine ⟨current, [], rfl, hax, by rw [hsl, this], by rw [this]; trivial⟩
  | index :: rest, k, current, done, hrest, hk, hax, hsl => by
    have hidx : indices[k]? = some index := by
      have h := congrArg List.head? hrest
      simp only [List.head?_cons, List.head?_drop] at h
      exact h.symm
    have hrest' : rest = indices.drop (k + 1) := by
      have h := congrArg List.tail hrest
      simp only [List.tail_cons, List.tail_drop] at h
      exact h
    obtain ⟨row, rows', hdrop⟩ : ∃ row rows', (layout.slices array dimension).drop k =
        row :: rows' := by
      have hlt : k < (layout.slices array dimension).length := by
        rw [hf.count]; exact (List.getElem?_eq_some_iff.1 hidx).1
      exact ⟨_, _, List.drop_eq_getElem_cons hlt⟩
    have hrowmem : row ∈ layout.slices array dimension :=
      List.mem_of_mem_drop (i := k) (by rw [hdrop]; exact List.mem_cons_self)
    have hview := hf.view current hax k index row hidx (by rw [hsl, hdrop, ← hk]; simp)
    obtain ⟨sorted, hsort, ho⟩ := hf.sort row
    have hsize : sorted.size = layout.axisLength array dimension := by
      rw [← Array.length_toList, ho.1.length_eq]; exact hf.rows row hrowmem
    obtain ⟨r1, hw, hax1, hsl1⟩ := hf.write current hax k index sorted hidx hsize
    have hdrop' : (layout.slices array dimension).drop (k + 1) = rows' := by
      rw [← List.drop_drop, hdrop]; rfl
    obtain ⟨final, sortedRest, hfor, hfax, hfsl, hfo⟩ :=
      sliceLoopDirect alg scratch hf rest (k + 1) r1 (done ++ [sorted.toList]) hrest'
        (by simp [hk]) (by rw [hax1, hax])
        (by rw [hsl1, hsl, hdrop, hdrop', ← hk, set_append_cons])
    refine ⟨final, sorted.toList :: sortedRest, ?_, hfax, by rw [hfsl]; simp, ?_⟩
    · rw [List.forIn_cons]
      simp only [view_eq, hview, liftSortJl_ok, bind, Except.bind, hsort, setView_eq, hw]
      exact hfor
    · rw [hdrop]; rw [hdrop'] at hfo; exact ⟨ho, hfo⟩

theorem copyFrom_eq (current : A) (dimension : Nat) (index : Index) (values : Array α) :
    (sliceArrayOps layout pivot).copyFrom current dimension index values =
      liftSortJl (layout.writeView current (sliceSelectors layout current dimension index) values) := rfl

theorem sliceLoopTemp {array : A} {dimension : Nat} {indices : List Index}
    {lt : α → α → Bool} {s : Bool} (alg : Algorithm (BracketSortTarget Int) Int)
    (scratch : Option (Array α))
    (hf : SliceFacts layout array dimension indices
      (fun row => (sliceArrayOps layout pivot).sortBang row alg (pureCompare lt) scratch) lt s) :
    ∀ (rest : List Index) (k : Nat) (current : A) (temp : Array α) (done : List (List α)),
      rest = indices.drop k → done.length = k → layout.axes current = layout.axes array →
      temp.size = layout.axisLength array dimension →
      layout.slices current dimension = done ++ (layout.slices array dimension).drop k →
      ∃ final temp' sortedRest,
        forIn rest (current, temp) (fun index (r : A × Array α) => do
          let view ← (sliceArrayOps layout pivot).getView r.fst dimension index
          let temporary ← (sliceArrayOps layout pivot).copyInto r.snd view
          let temporary ← (sliceArrayOps layout pivot).sortBang temporary alg
            (pureCompare lt) scratch
          let result ← (sliceArrayOps layout pivot).copyFrom r.fst dimension index temporary
          pure (ForInStep.yield (result, temporary))) = .ok (final, temp') ∧
        layout.axes final = layout.axes array ∧
        layout.slices final dimension = done ++ sortedRest ∧
        SlicesOutcome lt s ((layout.slices array dimension).drop k) sortedRest
  | [], k, current, temp, done, hrest, hk, hax, _, hsl => by
    have hlen := hf.count
    have : (layout.slices array dimension).drop k = [] := by
      apply List.eq_nil_of_length_eq_zero
      have h0 : (indices.drop k).length = 0 := by rw [← hrest]; rfl
      simp only [List.length_drop] at h0 ⊢; omega
    refine ⟨current, temp, [], rfl, hax, by rw [hsl, this], by rw [this]; trivial⟩
  | index :: rest, k, current, temp, done, hrest, hk, hax, htemp, hsl => by
    have hidx : indices[k]? = some index := by
      have h := congrArg List.head? hrest
      simp only [List.head?_cons, List.head?_drop] at h
      exact h.symm
    have hrest' : rest = indices.drop (k + 1) := by
      have h := congrArg List.tail hrest
      simp only [List.tail_cons, List.tail_drop] at h
      exact h
    obtain ⟨row, rows', hdrop⟩ : ∃ row rows', (layout.slices array dimension).drop k =
        row :: rows' := by
      have hlt : k < (layout.slices array dimension).length := by
        rw [hf.count]; exact (List.getElem?_eq_some_iff.1 hidx).1
      exact ⟨_, _, List.drop_eq_getElem_cons hlt⟩
    have hrowmem : row ∈ layout.slices array dimension :=
      List.mem_of_mem_drop (i := k) (by rw [hdrop]; exact List.mem_cons_self)
    have hview := hf.view current hax k index row hidx (by rw [hsl, hdrop, ← hk]; simp)
    have hcopy : (sliceArrayOps layout pivot).copyInto temp row.toArray = .ok row.toArray := by
      simp only [sliceArrayOps]
      rw [if_pos (by rw [htemp, List.size_toArray, hf.rows row hrowmem])]
    obtain ⟨sorted, hsort, ho⟩ := hf.sort row
    have hsize : sorted.size = layout.axisLength array dimension := by
      rw [← Array.length_toList, ho.1.length_eq]; exact hf.rows row hrowmem
    obtain ⟨r1, hw, hax1, hsl1⟩ := hf.write current hax k index sorted hidx hsize
    have hdrop' : (layout.slices array dimension).drop (k + 1) = rows' := by
      rw [← List.drop_drop, hdrop]; rfl
    obtain ⟨final, temp', sortedRest, hfor, hfax, hfsl, hfo⟩ :=
      sliceLoopTemp alg scratch hf rest (k + 1) r1 sorted (done ++ [sorted.toList]) hrest'
        (by simp [hk]) (by rw [hax1, hax]) hsize
        (by rw [hsl1, hsl, hdrop, hdrop', ← hk, set_append_cons])
    refine ⟨final, temp', sorted.toList :: sortedRest, ?_, hfax, by rw [hfsl]; simp, ?_⟩
    · rw [List.forIn_cons]
      simp only [view_eq, hview, liftSortJl_ok, bind, Except.bind, hcopy, hsort, copyFrom_eq, hw]
      exact hfor
    · rw [hdrop]; rw [hdrop'] at hfo; exact ⟨ho, hfo⟩

theorem forIn_one {A D E : Type} (F : D → A → Except E (ForInStep A))
    (post : List D) (x : D)
    (cur res : A) (hx : F x cur = .ok (.yield res))
    (hpost : ∀ d ∈ post, ∀ c, F d c = .ok (.yield c)) :
    ∀ (pre : List D), (∀ d ∈ pre, ∀ c, F d c = .ok (.yield c)) →
      forIn (pre ++ x :: post) cur F = .ok res
  | [], _ => by
    rw [List.nil_append, List.forIn_cons, hx]
    exact forIn_skip F post res (fun d hd => hpost d hd res)
  | d :: pre, hpre => by
    rw [List.cons_append, List.forIn_cons, hpre d List.mem_cons_self cur]
    exact forIn_one F post x cur res hx hpost pre (fun d' hd' => hpre d' (List.mem_cons_of_mem d hd'))

theorem sortBangDimensions_eq {A V D Index Alg L B O Scratch E : Type}
    (ops : SortBangDimensionsOps A V D Index Alg L B O Scratch E) (array : A) (dimension : Int)
    (algorithm : Alg) (less : L) (byFn : B) (rev : Option Bool) (order : O)
    (scratch : Scratch) :
    sortBangDimensions ops array dimension algorithm less byFn rev order scratch false =
      (if (!(decide (1 ≤ dimension) &&
          decide (dimension ≤ Int.ofNat (ops.dimensionCount array)))) = true then
        .error ops.dimensionError
      else
        forIn (ops.dimensionValues (ops.dimensionCount array)) array (fun d result =>
          if (Int.ofNat (ops.dimensionValue d) == dimension) = true then do
            let indices ← ops.cartesianIndices result d
            if (ops.dimensionValue d == 1 ||
                decide (ops.size result (ops.dimensionValue d) < 30)) = true then do
              let r ← forIn indices result (fun index r => do
                let view ← ops.getView r d index
                let sorted ← ops.sortBang view (ops.applyInitialOptimizations algorithm)
                  (ops.ordering less byFn rev order) scratch
                let result ← ops.setView r d index sorted
                pure (ForInStep.yield result))
              pure (ForInStep.yield r)
            else do
              let first ← ops.firstIndex indices
              let firstView ← ops.getView result d first
              let temporary ← ops.similar firstView
              let r ← forIn indices (result, temporary) (fun index (r : A × V) => do
                let view ← ops.getView r.fst d index
                let temporary ← ops.copyInto r.snd view
                let temporary ← ops.sortBang temporary (ops.applyInitialOptimizations algorithm)
                  (ops.ordering less byFn rev order) scratch
                let result ← ops.copyFrom r.fst d index temporary
                pure (ForInStep.yield (result, temporary)))
              pure (ForInStep.yield r.fst)
          else pure (ForInStep.yield result)) >>= fun r => pure r) := rfl


end SortDims

/-- `sort!(A; dims, alg, lt, rev, scratch)` on any array whose slice views obey the documented
`view`/`setindex!` laws: for every strict weak order, pivot rule choosing an index in the current
window and algorithm that sorts on its own, a valid `dims` sorts every slice along `dims` in place
(directly when `dims == 1` or `size(A, dims) < 30`, otherwise through a temporary vector, provided
`A` has at least one slice; the case with no slices is `sort-dimension-mutation-empty-slices`):
the result has the same axes and each slice is a sorted permutation of the original slice under
the effective order, stable when the algorithm after `InitialOptimizations` is stable. With an
explicit `scratch`, an out-of-range `dims` throws `ArgumentError("dimension out of range")`. -/
def MultidimensionalMutationCorrect : Prop :=
  ∀ (A α Axes Index K : Type) [Inhabited α] (layout : SliceArrayLayout A α Axes Index K)
      (pivot : Int → Int → Int) (lt : α → α → SortResult Bool) (array : A) (dimension : Int)
      (algorithm : Algorithm (BracketSortTarget Int) Int) (reverse : Option Bool)
      (scratch : Option (Array α)),
    SliceLayoutLaws layout → EffectNegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    let ops := sliceArrayOps layout pivot
    let valid := 1 ≤ dimension ∧ dimension ≤ Int.ofNat (layout.ndims array)
    (valid →
      (dimension = 1 ∨ layout.axisLength array dimension.toNat < 30 ∨
        layout.slices array dimension.toNat ≠ []) →
      ∃ result, sortBangDimensions ops array dimension algorithm lt () reverse lt scratch false =
          .ok result ∧
        layout.axes result = layout.axes array ∧
        EffectSlicesOutcome (if reverse = some true then fun a b => lt b a else lt)
          (genericStable (sourceApplyInitialOptimizations algorithm))
          (layout.slices array dimension.toNat) (layout.slices result dimension.toNat)) ∧
    (¬ valid →
      sortBangDimensions ops array dimension algorithm lt () reverse lt scratch false =
        .error (.jl (.argumentError "dimension out of range")))


/-- `sort!(A; dims)` when `size(A, dims) >= 30`, `dims != 1` and `A` has no slices along `dims`
(another dimension has length zero): `A` is empty, so it should be returned with its axes. -/
def DimensionMutationEmptySlices : Prop :=
  ∀ (A α Axes Index K : Type) [Inhabited α] (layout : SliceArrayLayout A α Axes Index K)
      (pivot : Int → Int → Int) (lt : α → α → SortResult Bool) (array : A) (dimension : Int)
      (algorithm : Algorithm (BracketSortTarget Int) Int) (reverse : Option Bool)
      (scratch : Option (Array α)),
    SliceLayoutLaws layout → EffectNegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    1 ≤ dimension → dimension ≤ Int.ofNat (layout.ndims array) →
    layout.slices array dimension.toNat = [] →
    ∃ result, sortBangDimensions (sliceArrayOps layout pivot) array dimension algorithm lt ()
        reverse lt scratch false = .ok result ∧
      layout.axes result = layout.axes array

/-- Column-major `0 × c` matrices, identified by their column count `c`, with their slice views. -/
def emptyRowsSliceLayout (α : Type) : SliceArrayLayout Nat α Nat Nat Nat where
  ndims := fun _ => 2
  axisLength := fun c d => if d = 1 then 0 else c
  cartesianIndices := fun c d => .ok (if d = 1 then List.range c else [])
  coordinate := fun i _ => i
  view := fun _ _ => .ok #[]
  writeView := fun c _ _ => .ok c
  axes := id
  slices := fun c d => if d = 1 then List.replicate c [] else []

theorem emptyRowsSliceLayout_laws (α : Type) : SliceLayoutLaws (emptyRowsSliceLayout α) := by
  intro c dimension h1 h2
  simp only [emptyRowsSliceLayout] at h2 ⊢
  by_cases hd : dimension = 1
  · subst hd
    simp only [↓reduceIte]
    refine ⟨List.range c, rfl, by simp, fun row hrow => by simp at hrow; simp [hrow],
      fun current hc => ?_⟩
    simp only [id] at hc
    subst hc
    refine ⟨trivial, trivial, by simp, fun i index row _ hrow => ?_,
      fun i index updated _ hsz => ?_⟩
    · have : row = [] := by
        have := List.mem_of_getElem? hrow
        simp at this
        exact this.2
      subst this; rfl
    · refine ⟨current, rfl, rfl, ?_⟩
      have hu : updated.toList = [] := by
        apply List.eq_nil_of_length_eq_zero; simpa using hsz
      rw [hu]
      exact (List.set_replicate_self).symm
  · simp only [hd, ↓reduceIte]
    refine ⟨[], rfl, rfl, fun row hrow => by simp at hrow, fun current hc => ?_⟩
    simp only [id] at hc
    subst hc
    exact ⟨trivial, rfl, rfl, fun i index row hi _ => by simp at hi,
      fun i index updated hi _ => by simp at hi⟩

theorem dimensionMutationEmptySlices_refuted : ¬ DimensionMutationEmptySlices := by
  intro h
  obtain ⟨result, hrun, _⟩ := h Nat Int Nat Nat Nat (emptyRowsSliceLayout Int) juliaPivot intCompare
    30 2 .defaultStable none none (emptyRowsSliceLayout_laws Int) intCompare_order
    juliaPivot_bounds rfl (by decide) (by decide) rfl
  have herr : sortBangDimensions (sliceArrayOps (emptyRowsSliceLayout Int) juliaPivot) 30 2
      .defaultStable intCompare () none intCompare none false = .error (.jl .boundsError) := rfl
  rw [herr] at hrun
  cases hrun


/-! ## `move!` and `bracket_kernel!` on any storage -/

section MoveKernel

variable {V α : Type} {S : VectorStorage V α} {E : V → List α}

theorem range_int_succ (m : Nat) (a : Int) :
    (List.range (m + 1)).map (fun i => a + Int.ofNat i) =
      a :: (List.range m).map (fun i => (a + 1) + Int.ofNat i) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, Int.ofNat_eq_natCast]
    omega

theorem length_filter_split (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter fun x => !p x).length = l.length := by
  have := (List.filter_append_perm p l).length_eq
  simpa using this

theorem getElem?_mid {P M Q : List α} {n : Nat} (h1 : P.length ≤ n)
    (h2 : n < P.length + M.length) : (P ++ M ++ Q)[n]? = M[n - P.length]? := by
  rw [List.append_assoc, List.getElem?_append_right h1, List.getElem?_append_left (by omega)]

theorem getElem?_outside_mid {P M M' Q : List α} (hM : M.length = M'.length) {n : Nat}
    (h : n < P.length ∨ P.length + M.length ≤ n) : (P ++ M ++ Q)[n]? = (P ++ M' ++ Q)[n]? := by
  rcases h with h | h
  · rw [List.append_assoc, List.append_assoc, List.getElem?_append_left h,
      List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
    simp [hM]

/-- `v[i], v[j] = v[j], v[i]` with `i ≤ j` written as `swap(v, j, i)`. -/
theorem storageSwap_rev (L : StorageLaws S E) (v : V) (P M Q : List α) (a b : α)
    (hv : E v = P ++ a :: (M ++ b :: Q)) (j i : Int)
    (hj : j = (P.length : Int) + M.length + 2) (hi : i = (P.length : Int) + 1) :
    ∃ v', storageSwap S v j i = .ok v' ∧ E v' = P ++ b :: (M ++ a :: Q) := by
  have hrj : S.getindex v j = .ok b :=
    storage_read_mid L (P := P ++ a :: M) (B := Q) (by rw [hv]; simp) (by omega)
      (by simp only [List.length_append, List.length_cons]; omega)
  have hri : S.getindex v i = .ok a :=
    storage_read_mid L (P := P) (B := M ++ b :: Q) hv (by omega) (by omega)
  obtain ⟨v1, hw1, hv1⟩ := storage_write_mid L a (v := v) (i := j)
    (P := P ++ a :: M) (B := Q) (z := b) (by rw [hv]; simp) (by omega)
    (by simp only [List.length_append, List.length_cons]; omega)
  obtain ⟨v2, hw2, hv2⟩ := storage_write_mid L b (v := v1) (i := i)
    (P := P) (B := M ++ a :: Q) (z := a) (by rw [hv1]; simp) (by omega) hi
  refine ⟨v2, ?_, hv2⟩
  unfold storageSwap
  rw [hrj, hri]
  simp only [liftSortJl, Except.mapError, bind, Except.bind, hw1, hw2]

theorem storageSwap_self (L : StorageLaws S E) (v : V) (P Q : List α) (a : α)
    (hv : E v = P ++ a :: Q) (i : Int) (hi : i = (P.length : Int) + 1) :
    ∃ v', storageSwap S v i i = .ok v' ∧ E v' = E v := by
  have hri : S.getindex v i = .ok a := storage_read_mid L hv (by omega) (by omega)
  obtain ⟨v1, hw1, hv1⟩ := storage_write_mid L a hv (by omega) hi
  obtain ⟨v2, hw2, hv2⟩ := storage_write_mid L a hv1 (by omega) hi
  refine ⟨v2, ?_, by rw [hv2, hv]⟩
  unfold storageSwap
  rw [hri]
  simp only [liftSortJl, Except.mapError, bind, Except.bind, hw1, hw2]

/-- `swap(v, a, b)` in pointwise form, valid also when `a = b`. -/
theorem storageSwap_at (L : StorageLaws S E) (v : V) {a b : Int} (ha : 1 ≤ a)
    (ha' : a ≤ ((E v).length : Int)) (hb : 1 ≤ b) (hb' : b ≤ ((E v).length : Int)) :
    ∃ v', storageSwap S v a b = .ok v' ∧ (E v').length = (E v).length ∧ (E v').Perm (E v) ∧
      ∀ i, 1 ≤ i → posAt (E v') i =
        if i = b then posAt (E v) a else if i = a then posAt (E v) b else posAt (E v) i := by
  obtain ⟨x, hx⟩ := posAt_some ha ha'
  obtain ⟨y, hy⟩ := posAt_some hb hb'
  obtain ⟨v1, hs1, he1⟩ := L.setindex_ok v a y ha ha'
  have hb1 : b ≤ ((E v1).length : Int) := by rw [he1, List.length_set]; exact hb'
  obtain ⟨v2, hs2, he2⟩ := L.setindex_ok v1 b x hb hb1
  refine ⟨v2, ?_, ?_, ?_, ?_⟩
  · unfold storageSwap
    rw [storage_read_at L ha hx, storage_read_at L hb hy]
    simp only [liftSortJl, Except.mapError, bind, Except.bind, hs1, hs2]
  · rw [he2, he1]; simp
  · rw [he2, he1]; exact perm_swap_at hx hy
  · intro i hi
    rw [he2, posAt_set hi hb hb1, he1, posAt_set hi ha ha', hx, hy]

/-- `reverse!(v, lo, hi)` in pointwise form. -/
theorem storageReverse_at (L : StorageLaws S E) (v : V) {lo hi : Int} (h1 : 1 ≤ lo)
    (h2 : lo ≤ hi + 1) (h3 : hi ≤ ((E v).length : Int)) :
    ∃ v', storageReverse S v lo hi = .ok v' ∧ (E v').length = (E v).length ∧
      (E v').Perm (E v) ∧
      ∀ p, 1 ≤ p → posAt (E v') p =
        if lo ≤ p ∧ p ≤ hi then posAt (E v) (lo + hi - p) else posAt (E v) p := by
  have hsplit := list_split3 (E v) h1 h2 h3
  generalize hP : (E v).take (lo - 1).toNat = P at hsplit
  generalize hX : seg (E v) lo hi = X at hsplit
  generalize hQ : (E v).drop hi.toNat = Q at hsplit
  have hPlen : (P.length : Int) + 1 = lo := by rw [← hP]; simp; omega
  have hXlen : (X.length : Int) = hi - lo + 1 := by
    rw [← hX]; unfold seg; simp; omega
  obtain ⟨v', hrev, hv'⟩ := storageReverse_spec L v lo hi P X Q hsplit hPlen hXlen
  refine ⟨v', hrev, ?_, ?_, ?_⟩
  · rw [hv', hsplit]; simp
  · rw [hv', hsplit]
    exact List.Perm.append_right Q (List.Perm.append_left P (List.reverse_perm X))
  · intro p hp
    rw [hv', hsplit]
    unfold posAt
    split
    · rename_i hin
      have e1 : (P ++ X.reverse ++ Q)[(p - 1).toNat]? = X.reverse[(p - 1).toNat - P.length]? :=
        getElem?_mid (by omega) (by simp; omega)
      have e2 : (P ++ X ++ Q)[(lo + hi - p - 1).toNat]? =
          X[(lo + hi - p - 1).toNat - P.length]? :=
        getElem?_mid (by omega) (by omega)
      rw [e1, e2, List.getElem?_reverse (by omega)]
      congr 1
      omega
    · rename_i hout
      exact getElem?_outside_mid (P := P) (M := X.reverse) (M' := X) (Q := Q) (by simp)
        (n := (p - 1).toNat) (by simp; omega)

/-! ### `move!` -/

theorem foldl_min_spec (l : List Int) (a : Int) :
    l.foldl min a ∈ a :: l ∧ ∀ x ∈ a :: l, l.foldl min a ≤ x := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (min a b)
    constructor
    · rcases List.mem_cons.1 h1 with h | h
      · rw [h]
        by_cases hab : a ≤ b
        · rw [Int.min_eq_left hab]; exact List.mem_cons_self
        · rw [Int.min_eq_right (by omega)]; simp
      · simp [h]
    · intro x hx
      have hm := h2 (min a b) List.mem_cons_self
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · exact h2 x (List.mem_cons_of_mem _ hx)

theorem foldl_max_spec (l : List Int) (a : Int) :
    l.foldl max a ∈ a :: l ∧ ∀ x ∈ a :: l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (max a b)
    constructor
    · rcases List.mem_cons.1 h1 with h | h
      · rw [h]
        by_cases hab : b ≤ a
        · rw [Int.max_eq_left hab]; exact List.mem_cons_self
        · rw [Int.max_eq_right (by omega)]; simp
      · simp [h]
    · intro x hx
      have hm := h2 (max a b) List.mem_cons_self
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · exact h2 x (List.mem_cons_of_mem _ hx)

theorem minimumIntList_spec {l : List Int} (h : l ≠ []) :
    ∃ m, minimumIntList l = some m ∧ m ∈ l ∧ ∀ x ∈ l, m ≤ x := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => exact ⟨_, rfl, foldl_min_spec l a⟩

theorem maximumIntList_spec {l : List Int} (h : l ≠ []) :
    ∃ m, maximumIntList l = some m ∧ m ∈ l ∧ ∀ x ∈ l, x ≤ m := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => exact ⟨_, rfl, foldl_max_spec l a⟩

theorem bracketTargetIndices_shift (t : BracketSortTarget Int) (c : Nat) :
    bracketTargetIndices (shiftBracketTarget t c) =
      (bracketTargetIndices t).map (· - (c : Int)) := by
  cases t with
  | index x => simp [shiftBracketTarget, bracketTargetIndices]
  | range a b =>
    simp only [shiftBracketTarget, bracketTargetIndices, arrayIndexRange, List.map_map,
      Int.ofNat_eq_natCast]
    rw [show b - (c : Int) - (a - (c : Int)) + 1 = b - a + 1 by omega]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    omega
  | ordinal a st b n =>
    simp only [shiftBracketTarget, bracketTargetIndices, List.map_map, Int.ofNat_eq_natCast]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    omega

/-- The loop body of the disjoint branch of `move!`. -/
def moveSwapBody (S : VectorStorage V α) : Int × Int → V → SortResult (ForInStep V) :=
  fun x r => match x with
    | (t, s) => do
      let r ← storageSwap S r t s
      pure (ForInStep.yield r)

theorem moveVector_eq (S : VectorStorage V α) (v : V) (target source : BracketSortTarget Int) :
    moveVector (storageMoveOps S) v target source =
      if ((storageMoveOps S).length target != (storageMoveOps S).length source) = true then
        .error (.assertionError "length mismatch")
      else if ((storageMoveOps S).length target == 1 ||
          (storageMoveOps S).disjoint target source) = true then
        (forIn ((bracketTargetIndices target).zip (bracketTargetIndices source)) v
            (moveSwapBody S) >>= fun r => pure r)
      else (do
        let sourceMinimum ← liftSortJl (match minimumIntList (bracketTargetIndices source) with
          | some value => .ok value
          | none => .error (.argumentError "reducing over an empty collection"))
        let targetMinimum ← liftSortJl (match minimumIntList (bracketTargetIndices target) with
          | some value => .ok value
          | none => .error (.argumentError "reducing over an empty collection"))
        if !decide (sourceMinimum ≤ targetMinimum) then
          throw (.assertionError "range mismatch")
        let sourceMinimum ← liftSortJl (match minimumIntList (bracketTargetIndices source) with
          | some value => .ok value
          | none => .error (.argumentError "reducing over an empty collection"))
        let targetMaximum ← liftSortJl (match maximumIntList (bracketTargetIndices target) with
          | some value => .ok value
          | none => .error (.argumentError "reducing over an empty collection"))
        let w ← storageReverse S v sourceMinimum targetMaximum
        let targetMinimum ← liftSortJl (match minimumIntList (bracketTargetIndices target) with
          | some value => .ok value
          | none => .error (.argumentError "reducing over an empty collection"))
        let targetMaximum ← liftSortJl (match maximumIntList (bracketTargetIndices target) with
          | some value => .ok value
          | none => .error (.argumentError "reducing over an empty collection"))
        storageReverse S w targetMinimum targetMaximum) := by
  unfold moveVector
  rfl

theorem forIn_swaps (L : StorageLaws S E) :
    ∀ (T Sx : List Int) (v : V), T.length = Sx.length → (T ++ Sx).Nodup →
      (∀ i ∈ T ++ Sx, 1 ≤ i ∧ i ≤ ((E v).length : Int)) →
      ∃ v', forIn (T.zip Sx) v (moveSwapBody S) = .ok v' ∧ (E v').length = (E v).length ∧
        (E v').Perm (E v) ∧
        (∀ t s, (t, s) ∈ T.zip Sx → posAt (E v') t = posAt (E v) s) ∧
        (∀ i, 1 ≤ i → i ∉ T → i ∉ Sx → posAt (E v') i = posAt (E v) i)
  | [], Sx, v, _, _, _ => ⟨v, rfl, rfl, List.Perm.refl _, by simp, fun _ _ _ _ => rfl⟩
  | _ :: _, [], _, hlen, _, _ => by simp at hlen
  | t :: T, s :: Sx, v, hlen, hnd, hb => by
    have ht := hb t (by simp)
    have hs := hb s (by simp)
    obtain ⟨v1, hsw, hl1, hp1, hpos1⟩ := storageSwap_at L v ht.1 ht.2 hs.1 hs.2
    have hnd' : (t :: (T ++ s :: Sx)).Nodup := by simpa using hnd
    rw [List.nodup_cons, List.nodup_append, List.nodup_cons] at hnd'
    obtain ⟨htn, hTn, ⟨hsn, hSxn⟩, hdisj⟩ := hnd'
    have hts : t ≠ s := fun h => htn (by simp [h])
    have htT : t ∉ T := fun h => htn (List.mem_append_left _ h)
    have htSx : t ∉ Sx := fun h => htn (List.mem_append_right _ (List.mem_cons_of_mem _ h))
    obtain ⟨v', hloop, hl', hp', hpair', hout'⟩ := forIn_swaps L T Sx v1
      (by simp at hlen; exact hlen)
      (List.nodup_append.2 ⟨hTn, hSxn, fun a ha b hb => hdisj a ha b (List.mem_cons_of_mem _ hb)⟩)
      (fun i hi => by
        rw [hl1]
        apply hb i
        simp only [List.mem_append, List.mem_cons] at hi ⊢
        rcases hi with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h))
    refine ⟨v', ?_, hl'.trans hl1, hp'.trans hp1, ?_, ?_⟩
    · rw [List.zip_cons_cons, List.forIn_cons]
      simp only [moveSwapBody, hsw, bind, Except.bind, pure, Except.pure]
      exact hloop
    · intro a b hab
      rw [List.zip_cons_cons, List.mem_cons] at hab
      rcases hab with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [hout' a ht.1 htT htSx, hpos1 a ht.1, if_neg hts, if_pos rfl]
      · have hm := List.of_mem_zip h
        have hbs : b ≠ s := fun e => hsn (e ▸ hm.2)
        have hbt : b ≠ t := fun e => htSx (e ▸ hm.2)
        rw [hpair' a b h, hpos1 b (hb b (by simp [hm.2])).1, if_neg hbs, if_neg hbt]
    · intro i hi hiT hiS
      simp only [List.mem_cons, not_or] at hiT hiS
      rw [hout' i hi hiT.2 hiS.2, hpos1 i hi, if_neg hiS.1, if_neg hiT.1]

theorem mem_zip_map_self (f : Int → Int) : ∀ {T : List Int} {i : Int}, i ∈ T →
    (i, f i) ∈ T.zip (T.map f)
  | t :: T, i, h => by
    rw [List.map_cons, List.zip_cons_cons, List.mem_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (mem_zip_map_self f h)

/-- `move!(v, target, target .- c)`, the only call (from `BracketedSort`, where `c` is the
`count_below` of `bracket_kernel!`): every target position receives the value at the matching
source position, the vector is permuted, and nothing outside `minimum(source):maximum(target)`
changes. -/
theorem moveVector_spec (L : StorageLaws S E) (v : V) (target : BracketSortTarget Int) (c : Nat)
    (hnd : (bracketTargetIndices target).Nodup)
    (hb : ∀ i ∈ bracketTargetIndices target, 1 ≤ i - (c : Int) ∧ i ≤ ((E v).length : Int)) :
    ∃ v', moveVector (storageMoveOps S) v target (shiftBracketTarget target c) = .ok v' ∧
      (E v').Perm (E v) ∧
      (∀ i ∈ bracketTargetIndices target, posAt (E v') i = posAt (E v) (i - c)) ∧
      (∀ i, 1 ≤ i → ((∀ t ∈ bracketTargetIndices target, i < t - c) ∨
          (∀ t ∈ bracketTargetIndices target, t < i)) → posAt (E v') i = posAt (E v) i) := by
  have hsrc := bracketTargetIndices_shift target c
  have hdisjDef : (storageMoveOps S).disjoint target (shiftBracketTarget target c) =
      !(bracketTargetIndices target).any (fun x =>
        ((bracketTargetIndices target).map (· - (c : Int))).contains x) := by
    simp only [storageMoveOps, hsrc]
  have hlenDef : (storageMoveOps S).length target = (bracketTargetIndices target).length := rfl
  rw [moveVector_eq, if_neg (by simp [storageMoveOps, hsrc]), hsrc]
  rw [hdisjDef, hlenDef]
  generalize bracketTargetIndices target = T at hnd hb ⊢
  have hndS : (T.map (· - (c : Int))).Nodup :=
    List.Pairwise.map _ (fun a b (h : a ≠ b) (e : a - (c : Int) = b - c) => h (by omega)) hnd
  by_cases hd : (!T.any (fun x => (T.map (· - (c : Int))).contains x)) = true
  · -- disjoint target and source: pairwise swaps
    rw [if_pos (by rw [hd]; simp)]
    have hdisj : ∀ a ∈ T, ∀ b ∈ T.map (· - (c : Int)), a ≠ b := by
      intro a ha b hbm hab
      subst hab
      have hany : (T.any fun x => (T.map (· - (c : Int))).contains x) = true :=
        List.any_eq_true.2 ⟨a, ha, by simpa using hbm⟩
      rw [hany] at hd
      cases hd
    obtain ⟨v', hloop, _, hp', hpair, hout⟩ := forIn_swaps L T (T.map (· - (c : Int))) v
      (by simp) (List.nodup_append.2 ⟨hnd, hndS, hdisj⟩)
      (fun i hi => by
        rcases List.mem_append.1 hi with h | h
        · have := hb i h; omega
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
          have := hb t ht; omega)
    refine ⟨v', by rw [hloop]; rfl, hp', fun i hi => hpair i _ (mem_zip_map_self _ hi), ?_⟩
    intro i hi hout'
    apply hout i hi
    · intro hiT
      rcases hout' with h | h
      · have := h i hiT; omega
      · have := h i hiT; omega
    · intro hiS
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hiS
      rcases hout' with h | h
      · have := h t ht; omega
      · have := h t ht; omega
  · by_cases h1 : T.length = 1
    · -- one target index: a single swap
      obtain ⟨t, rfl⟩ : ∃ t, T = [t] := by
        match T, h1 with
        | [t], _ => exact ⟨t, rfl⟩
      rw [if_pos (by simp)]
      have ht := hb t (by simp)
      obtain ⟨v1, hsw, _, hp1, hpos1⟩ := storageSwap_at L v (a := t) (b := t - c)
        (by omega) ht.2 ht.1 (by omega)
      refine ⟨v1, ?_, hp1, ?_, ?_⟩
      · simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left,
          List.forIn_cons, List.forIn_nil, moveSwapBody, hsw, bind, Except.bind, pure,
          Except.pure]
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        subst hi
        rw [hpos1 i (by omega)]
        by_cases htc : i = i - (c : Int)
        · rw [if_pos htc, ← htc]
        · rw [if_neg htc, if_pos rfl]
      · intro i hi hout
        have hne : i ≠ i - (c : Int) ∨ True := Or.inr trivial
        rw [hpos1 i hi]
        rcases hout with h | h
        · have := h t (by simp)
          rw [if_neg (by omega), if_neg (by omega)]
        · have := h t (by simp)
          rw [if_neg (by omega), if_neg (by omega)]
    · -- overlapping ranges: two reversals rotate the block
      rw [if_neg (fun h => by
        rw [Bool.or_eq_true] at h
        rcases h with h | h
        · exact h1 (by simpa using h)
        · exact hd h)]
      have hne : T ≠ [] := by
        rintro rfl
        simp at hd
      obtain ⟨mT, hmT, hmTmem, hmTle⟩ := minimumIntList_spec hne
      obtain ⟨MT, hMT, hMTmem, hMTle⟩ := maximumIntList_spec hne
      obtain ⟨mS, hmS, hmSmem, hmSle⟩ :=
        minimumIntList_spec (l := T.map (· - (c : Int))) (by simpa using hne)
      have hmS_eq : mS = mT - c := by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hmSmem
        have h1' := hmSle (mT - c) (List.mem_map_of_mem hmTmem)
        have h2' := hmTle a ha
        omega
      rw [hmS, hmT, hMT]
      simp only [liftSortJl, Except.mapError, bind, Except.bind]
      rw [hmS_eq, if_neg (by simp; omega)]
      have hbm := hb mT hmTmem
      have hbM := hb MT hMTmem
      have hmM := hmTle MT hMTmem
      obtain ⟨w, hrev1, hl1, hp1, hpos1⟩ :=
        storageReverse_at L v (lo := mT - c) (hi := MT) (by omega) (by omega) hbM.2
      obtain ⟨w', hrev2, _, hp2, hpos2⟩ :=
        storageReverse_at L w (lo := mT) (hi := MT) (by omega) (by omega) (by rw [hl1]; exact hbM.2)
      refine ⟨w', by rw [hrev1]; exact hrev2, hp2.trans hp1, ?_, ?_⟩
      · intro i hi
        have hlo := hmTle i hi
        have hhi := hMTle i hi
        have := hb i hi
        rw [hpos2 i (by omega), if_pos ⟨hlo, hhi⟩, hpos1 _ (by omega), if_pos (by omega)]
        congr 1
        omega
      · intro i hi hout
        rcases hout with h | h
        · have := h mT hmTmem
          rw [hpos2 i hi, if_neg (by omega), hpos1 i hi, if_neg (by omega)]
        · have := h MT hMTmem
          rw [hpos2 i hi, if_neg (by omega), hpos1 i hi, if_neg (by omega)]

/-! ### `bracket_kernel!` -/

/-- `lt(o, x, lo_signpost)` in `bracket_kernel!`. -/
def kBelow (lt : α → α → Bool) (lower : Option α) (z : α) : Bool := lower.any fun b => lt z b

/-- `!lt(o, hi_signpost, x)` in `bracket_kernel!`. -/
def kNotAbove (lt : α → α → Bool) (upper : Option α) (z : α) : Bool :=
  upper.all fun b => !lt b z

/-- `c = a != b` in `bracket_kernel!`: the element lies between the signposts. -/
def kSwap (lt : α → α → Bool) (lower upper : Option α) (z : α) : Bool :=
  kBelow lt lower z != kNotAbove lt upper z

/-- The loop body of `bracket_kernel!` on storage. -/
def kernelBody (S : VectorStorage V α) (lt : α → α → Bool) (lower upper : Option α) :
    Int → V × Int × Nat → SortResult (ForInStep (V × Int × Nat)) :=
  fun index s => do
    let value ← liftSortJl (S.getindex s.1 index)
    let below ← match lower with
      | none => pure false
      | some signpost => pureCompare lt value signpost
    let notAbove ← match upper with
      | none => pure true
      | some signpost => do pure (!(← pureCompare lt signpost value))
    let swapNeeded := below != notAbove
    let w ← storageSwap S s.1 index
      (index + (if swapNeeded then s.2.1 else 0))
    pure (ForInStep.yield (w, s.2.1 + (if swapNeeded then 0 else -1),
      s.2.2 + if below then 1 else 0))

theorem bracketKernel_eq (S : VectorStorage V α) (lt : α → α → Bool) (v : V) (lo hi : Int)
    (lower upper : Option α) :
    bracketKernel (storageBracketKernelOps S (pureCompare lt)) v lo hi lower upper () =
      (liftSortJl (storageCheckBounds S v lo hi) >>= fun _ =>
        forIn (arrayIndexRange lo hi) (v, (0 : Int), (0 : Nat)) (kernelBody S lt lower upper) >>=
          fun s => pure (s.1, s.2.2, hi + s.2.1)) := by
  unfold bracketKernel
  rfl

theorem kernelBody_pure (S : VectorStorage V α) (lt : α → α → Bool)
    (lower upper : Option α) (index : Int) (s : V × Int × Nat) :
    kernelBody S lt lower upper index s =
      (liftSortJl (S.getindex s.1 index) >>= fun value =>
        storageSwap S s.1 index
          (index + (if kSwap lt lower upper value = true then s.2.1 else 0)) >>= fun w =>
        pure (ForInStep.yield (w, s.2.1 + (if kSwap lt lower upper value = true then 0 else -1),
          s.2.2 + if kBelow lt lower value = true then 1 else 0))) := by
  cases lower <;> cases upper <;> rfl

theorem kernel_loop (L : StorageLaws S E) (lt : α → α → Bool) (lower upper : Option α) :
    ∀ (R : List α) (a : Int) (v : V) (off : Int) (cnt : Nat) (P D N Q Wk : List α),
      E v = P ++ D ++ N ++ R ++ Q → a = ((P.length + Wk.length : Nat) : Int) + 1 →
      D = Wk.filter (kSwap lt lower upper) →
      N.Perm (Wk.filter fun z => !kSwap lt lower upper z) →
      off = -(N.length : Int) → cnt = (Wk.filter (kBelow lt lower)).length →
      ∃ v' D' N',
        forIn ((List.range R.length).map (fun i => a + Int.ofNat i)) (v, off, cnt)
            (kernelBody S lt lower upper) =
          .ok (v', -(N'.length : Int), ((Wk ++ R).filter (kBelow lt lower)).length) ∧
        E v' = P ++ D' ++ N' ++ Q ∧ D' = (Wk ++ R).filter (kSwap lt lower upper) ∧
        N'.Perm ((Wk ++ R).filter fun z => !kSwap lt lower upper z)
  | [], a, v, off, cnt, P, D, N, Q, Wk, hv, _, hD, hN, hoff, hcnt => by
    refine ⟨v, D, N, ?_, by simpa using hv, by simpa using hD, by simpa using hN⟩
    simp only [List.length_nil, List.range_zero, List.map_nil, List.forIn_nil, List.append_nil]
    rw [hoff, hcnt]
    rfl
  | z :: R, a, v, off, cnt, P, D, N, Q, Wk, hv, ha, hD, hN, hoff, hcnt => by
    have hlenDN : D.length + N.length = Wk.length := by
      rw [hD, hN.length_eq]; exact length_filter_split _ Wk
    have hread : S.getindex v a = .ok z :=
      storage_read_mid L (P := P ++ D ++ N) (B := R ++ Q) (by rw [hv]; simp)
        (by omega) (by simp only [List.length_append]; omega)
    have ha' : a + 1 = (((P.length + (Wk ++ [z]).length : Nat) : Int)) + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    have hcnt' : cnt + (if kBelow lt lower z = true then 1 else 0) =
        ((Wk ++ [z]).filter (kBelow lt lower)).length := by
      rw [hcnt, List.filter_append, List.length_append]
      by_cases hb : kBelow lt lower z = true <;> simp [hb]
    have happ : Wk ++ [z] ++ R = Wk ++ z :: R := by simp
    -- the step: one swap, then the rest of the loop
    have finish : ∀ (v1 : V) (D1 N1 : List α),
        kernelBody S lt lower upper a (v, off, cnt) =
          .ok (.yield (v1, off + (if kSwap lt lower upper z = true then 0 else -1),
            cnt + if kBelow lt lower z = true then 1 else 0)) →
        E v1 = P ++ D1 ++ N1 ++ R ++ Q →
        D1 = (Wk ++ [z]).filter (kSwap lt lower upper) →
        N1.Perm ((Wk ++ [z]).filter fun z => !kSwap lt lower upper z) →
        off + (if kSwap lt lower upper z = true then 0 else -1) = -(N1.length : Int) →
        ∃ v' D' N',
          forIn ((List.range (z :: R).length).map (fun i => a + Int.ofNat i)) (v, off, cnt)
              (kernelBody S lt lower upper) =
            .ok (v', -(N'.length : Int), ((Wk ++ z :: R).filter (kBelow lt lower)).length) ∧
          E v' = P ++ D' ++ N' ++ Q ∧ D' = (Wk ++ z :: R).filter (kSwap lt lower upper) ∧
          N'.Perm ((Wk ++ z :: R).filter fun z => !kSwap lt lower upper z) := by
      intro v1 D1 N1 hstep hv1 hD1 hN1 hoff1
      obtain ⟨v', D', N', hloop, hv', hD', hN'⟩ := kernel_loop L lt lower upper R (a + 1) v1
        _ _ P D1 N1 Q (Wk ++ [z]) hv1 ha' hD1 hN1 hoff1 hcnt'
      rw [happ] at hloop hD' hN'
      refine ⟨v', D', N', ?_, hv', hD', hN'⟩
      rw [List.length_cons, range_int_succ, List.forIn_cons, hstep]
      simp only [bind, Except.bind]
      exact hloop
    by_cases hz : kSwap lt lower upper z = true
    · cases N with
      | nil =>
        obtain ⟨v1, hsw, hv1⟩ := storageSwap_self L v (P ++ D) (R ++ Q) z (by rw [hv]; simp) a
          (by simp only [List.length_append, List.length_nil] at hlenDN ⊢; omega)
        have hidx : a + (if kSwap lt lower upper z = true then off else 0) = a := by
          rw [if_pos hz, hoff]; simp
        apply finish v1 (D ++ [z]) []
        · rw [kernelBody_pure, hread]
          simp only [liftSortJl, Except.mapError, bind, Except.bind]
          rw [hidx, hsw]
          rfl
        · rw [hv1, hv]; simp
        · rw [hD, List.filter_append]; simp [hz]
        · rw [List.filter_append]; simpa [hz] using hN
        · rw [if_pos hz, hoff]; simp
      | cons n0 N1 =>
        obtain ⟨v1, hsw, hv1⟩ := storageSwap_rev L v (P ++ D) N1 (R ++ Q) n0 z
          (by rw [hv]; simp) a (((P ++ D).length : Int) + 1)
          (by simp only [List.length_append, List.length_cons] at hlenDN ⊢; omega) rfl
        have hidx : a + (if kSwap lt lower upper z = true then off else 0) =
            ((P ++ D).length : Int) + 1 := by
          rw [if_pos hz, hoff]
          simp only [List.length_append, List.length_cons] at hlenDN ⊢
          omega
        apply finish v1 (D ++ [z]) (N1 ++ [n0])
        · rw [kernelBody_pure, hread]
          simp only [liftSortJl, Except.mapError, bind, Except.bind]
          rw [hidx, hsw]
          rfl
        · rw [hv1]; simp
        · rw [hD, List.filter_append]; simp [hz]
        · rw [List.filter_append]
          simp only [hz, List.filter_cons, List.filter_nil, Bool.not_true, Bool.false_eq_true,
            if_false, List.append_nil]
          exact List.perm_append_comm.trans hN
        · rw [if_pos hz, hoff]
          simp only [List.length_cons, List.length_append, List.length_nil]
          omega
    · have hz' : kSwap lt lower upper z = false := by simpa using hz
      obtain ⟨v1, hsw, hv1⟩ := storageSwap_self L v (P ++ D ++ N) (R ++ Q) z (by rw [hv]; simp) a
        (by simp only [List.length_append] at ⊢; omega)
      have hidx : a + (if kSwap lt lower upper z = true then off else 0) = a := by
        rw [hz']; simp
      apply finish v1 D (N ++ [z])
      · rw [kernelBody_pure, hread]
        simp only [liftSortJl, Except.mapError, bind, Except.bind]
        rw [hidx, hsw]
        rfl
      · rw [hv1, hv]; simp
      · rw [hD, List.filter_append]; simp [hz']
      · rw [List.filter_append]
        simp only [hz', List.filter_cons, List.filter_nil, Bool.not_false, if_true]
        exact List.Perm.append_right [z] hN
      · rw [hz', hoff]; simp; omega

/-- `bracket_kernel!(v, lo, hi, lo_signpost, hi_signpost, o)` on any storage obeying the
`AbstractVector` laws, with `lo_signpost ≤ hi_signpost` (as `BracketedSort` guarantees): it
permutes only `lo:hi`, counts the elements below `lo_signpost`, and gathers the elements between
the signposts, in their original order, at `lo:i+hi`. -/
theorem bracketKernel_spec (L : StorageLaws S E) {lt : α → α → Bool} (hnt : NegTransOrder lt)
    (v : V) {lo hi : Int} (lower upper : Option α) (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1)
    (h3 : hi ≤ ((E v).length : Int))
    (hord : ∀ a b, lower = some a → upper = some b → lt b a = false) :
    ∃ v' count last,
      bracketKernel (storageBracketKernelOps S (pureCompare lt)) v lo hi lower upper () =
        .ok (v', count, last) ∧
      (E v').Perm (E v) ∧
      count = ((seg (E v) lo hi).filter fun z => lower.any fun b => lt z b).length ∧
      last = lo + Int.ofNat ((seg (E v) lo hi).filter fun z =>
        !(lower.any fun b => lt z b) && upper.all fun b => !lt b z).length - 1 ∧
      seg (E v') lo last = (seg (E v) lo hi).filter (fun z =>
        !(lower.any fun b => lt z b) && upper.all fun b => !lt b z) ∧
      Frame (E v) (E v') lo hi := by
  have hsplit := list_split3 (E v) h1 h2 h3
  generalize hP : (E v).take (lo - 1).toNat = P at hsplit
  generalize hW : seg (E v) lo hi = W at hsplit ⊢
  generalize hQ : (E v).drop hi.toNat = Q at hsplit
  have hPlen : (P.length : Int) + 1 = lo := by rw [← hP]; simp; omega
  have hWlen : (W.length : Int) = hi - lo + 1 := by
    rw [← hW]; unfold seg; simp; omega
  have hsel : ∀ z, kSwap lt lower upper z = (!kBelow lt lower z && kNotAbove lt upper z) := by
    intro z
    unfold kSwap
    cases hb : kBelow lt lower z
    · simp
    · have hna : kNotAbove lt upper z = true := by
        unfold kBelow at hb
        cases hl : lower with
        | none => rw [hl] at hb; cases hb
        | some a =>
          rw [hl] at hb
          have hza : lt z a = true := hb
          unfold kNotAbove
          cases hu : upper with
          | none => rfl
          | some b =>
            show (!lt b z) = true
            cases hbz : lt b z
            · rfl
            · have := hnt.2.1 b z a hbz hza
              rw [hord a b hl hu] at this
              cases this
      simp [hna]
  obtain ⟨v', D', N', hloop, hv', hD', hN'⟩ := kernel_loop L lt lower upper W lo v 0 0 P [] [] Q []
    (by rw [hsplit]; simp) (by simp; omega) rfl List.Perm.nil (by simp) rfl
  simp only [List.nil_append] at hloop hD' hN'
  have hlenDN : D'.length + N'.length = W.length := by
    rw [hD', hN'.length_eq]; exact length_filter_split _ W
  have hDsel : D' = W.filter (fun z => !(lower.any fun b => lt z b) &&
      upper.all fun b => !lt b z) := by
    rw [hD']; exact List.filter_congr (fun z _ => hsel z)
  have hreassoc : P ++ D' ++ N' ++ Q = P ++ (D' ++ N') ++ Q := by simp
  refine ⟨v', (W.filter (kBelow lt lower)).length, hi + -(N'.length : Int), ?_, ?_, rfl, ?_, ?_, ?_⟩
  · rw [bracketKernel_eq, storageCheckBounds_ok L (v := v) (lo := lo) (hi := hi)
      (by omega : 1 ≤ lo ∧ hi ≤ ((E v).length : Int) ∨ hi < lo)]
    simp only [liftSortJl, Except.mapError, bind, Except.bind]
    rw [show arrayIndexRange lo hi = (List.range W.length).map (fun i => lo + Int.ofNat i) by
      unfold arrayIndexRange; congr 2; omega, hloop]
    rfl
  · rw [hv', hsplit, hreassoc]
    have hDN : (D' ++ N').Perm W := by
      rw [hD']; exact (List.Perm.append_left _ hN').trans (List.filter_append_perm _ W)
    exact List.Perm.append_right Q (List.Perm.append_left P hDN)
  · rw [← hDsel]; simp only [Int.ofNat_eq_natCast]; omega
  · rw [hv', ← hDsel, show P ++ D' ++ N' ++ Q = P ++ D' ++ (N' ++ Q) by simp]
    exact seg_decomp hPlen (by omega)
  · rw [hsplit, hv', hreassoc]
    exact frame_of_decomp hPlen (by simp; omega) hWlen

end MoveKernel

/-- `move!(v, target, source)` as `BracketedSort` calls it, with `source = target .- c` for the
`count_below` `c ≥ 0` of `bracket_kernel!`, on any one-based storage obeying the `AbstractVector`
laws: for a target of distinct indices whose source and target lie inside the vector, it
succeeds, permutes the vector, moves every source value to its target position, and changes
nothing outside `minimum(source):maximum(target)`. -/
def MoveVectorCorrect : Prop :=
  ∀ (V α : Type) (S : VectorStorage V α) (E : V → List α), StorageLaws S E →
  ∀ (v : V) (target : BracketSortTarget Int) (c : Nat),
    (bracketTargetIndices target).Nodup →
    (∀ i ∈ bracketTargetIndices target, 1 ≤ i - (c : Int) ∧ i ≤ ((E v).length : Int)) →
    ∃ v', moveVector (storageMoveOps S) v target (shiftBracketTarget target c) = .ok v' ∧
      (E v').Perm (E v) ∧
      (∀ i ∈ bracketTargetIndices target, posAt (E v') i = posAt (E v) (i - c)) ∧
      (∀ i, 1 ≤ i → ((∀ t ∈ bracketTargetIndices target, i < t - c) ∨
          (∀ t ∈ bracketTargetIndices target, t < i)) → posAt (E v') i = posAt (E v) i)


/-- `bracket_kernel!(v, lo, hi, lo_signpost, hi_signpost, o)` on any one-based storage obeying
the `AbstractVector` laws, for a strict weak order and signposts with `lo_signpost ≤
hi_signpost` (either may be absent): on a window inside the vector it succeeds, permutes the
vector without touching anything outside `lo:hi`, returns the number of window elements below
`lo_signpost`, and places exactly the window elements between the signposts, in their original
order, at `lo:last` where `last` is its second result. -/
def BracketKernelCorrect : Prop :=
  ∀ (V α : Type) (S : VectorStorage V α) (E : V → List α), StorageLaws S E →
  ∀ (lt : α → α → SortResult Bool) (v : V) (lo hi : Int) (lower upper : Option α),
    EffectNegTransOrder lt → 1 ≤ lo → lo ≤ hi + 1 → hi ≤ ((E v).length : Int) →
    (∀ a b, lower = some a → upper = some b → lt b a = .ok false) →
    ∃ v' count last,
      bracketKernel (storageBracketKernelOps S lt) v lo hi lower upper () =
        .ok (v', count, last) ∧
      (E v').Perm (E v) ∧
      count = ((seg (E v) lo hi).filter fun z => lower.any fun b => comparisonTrue lt z b).length ∧
      last = lo + Int.ofNat ((seg (E v) lo hi).filter fun z =>
        !(lower.any fun b => comparisonTrue lt z b) && upper.all fun b => comparisonFalse lt b z).length - 1 ∧
      seg (E v') lo last = (seg (E v) lo hi).filter (fun z =>
        !(lower.any fun b => comparisonTrue lt z b) && upper.all fun b => comparisonFalse lt b z) ∧
      Frame (E v) (E v') lo hi


/-! ## `CountingSort` on any storage -/

section CountingArith

theorem promote_self (t : IntTy) : IntTy.promote t t = t := by
  cases t <;> rfl

/-- Wrapping into a type of the same width absorbs an inner wrap. -/
theorem wrapInt_add_wrap {T T' : IntTy} (h : T.bits = T'.bits) (a b : Int) :
    wrapInt T (a + wrapInt T' b) = wrapInt T (a + b) := by
  cases T <;> cases T' <;> simp [IntTy.bits] at h <;>
    simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_sub_wrap {T T' : IntTy} (h : T.bits = T'.bits) (a b : Int) :
    wrapInt T (a - wrapInt T' b) = wrapInt T (a - b) := by
  cases T <;> cases T' <;> simp [IntTy.bits] at h <;>
    simp [wrapInt, IntTy.signed, IntTy.bits] <;> omega

theorem wrapInt_i64_one : wrapInt .i64 1 = 1 := by decide

/-- The types `+%` and `-%` produce in `CountingSort` hold every value in `1:typemax(Int)`. -/
theorem cs_offset_range (t : IntTy) (y : Int) (h1 : 0 ≤ y) (h2 : y ≤ IntTy.max .i64) :
    (IntTy.promote t (IntTy.promote .i64 t)).min ≤ y ∧
      y ≤ (IntTy.promote t (IntTy.promote .i64 t)).max := by
  cases t <;> simp [IntTy.promote, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits] at * <;> omega

theorem cs_last_range (t : IntTy) (y : Int) (h1 : 0 ≤ y) (h2 : y ≤ IntTy.max .i64) :
    (IntTy.promote (unsignedIntegerType t) .i64).min ≤ y ∧
      y ≤ (IntTy.promote (unsignedIntegerType t) .i64).max := by
  cases t <;> simp [IntTy.promote, IntTy.min, IntTy.max, IntTy.signed, IntTy.bits,
    unsignedIntegerType] at * <;> omega

/-- `v[i] +% offs` with `offs = 1 -% low` is the one-based bucket `v[i] - low + 1`. -/
theorem cs_bucket (t : IntTy) (low x : JInt t) (hle : low.val ≤ x.val)
    (hd : x.val - low.val < IntTy.max .i64) :
    (indexAdd ⟨t, x⟩ (indexSub (searchIndex .i64 1) ⟨t, low⟩)).val = x.val - low.val + 1 := by
  simp only [indexAdd, indexSub, searchIndex, SearchIndex.val, JInt.wrap]
  rw [wrapInt_add_wrap (by cases t <;> rfl), wrapInt_i64_one,
    wrapInt_of_inRange _ _ (cs_offset_range t _ (by omega) (by omega))]
  omega

theorem searchIndex_val (T : IntTy) (x : Int) : (searchIndex T x).val = wrapInt T x := rfl
theorem searchIndex_ty (T : IntTy) (x : Int) : (searchIndex T x).ty = T := rfl
theorem indexSub_val (x y : SearchIndex) :
    (indexSub x y).val = wrapInt (IntTy.promote x.ty y.ty) (x.val - y.val) := rfl
theorem indexSub_ty (x y : SearchIndex) : (indexSub x y).ty = IntTy.promote x.ty y.ty := rfl

/-- The value `CountingSort` writes for a bucket: `i -% offs`, made signed when the element type
is signed and `i -% offs` is not. -/
def csWritten (t : IntTy) (bucket offset : SearchIndex) : SearchIndex :=
  if (!(indexSub bucket offset).ty.signed && t.signed) = true then
    searchIndex (signedIntegerType (indexSub bucket offset).ty) (indexSub bucket offset).val
  else indexSub bucket offset

/-- `val = i -% offs`, made signed when needed, is `low + i - 1` for bucket `i`. -/
theorem cs_value (t : IntTy) (low : JInt t) (k : Nat) (hk : low.val + k ≤ t.max)
    (hk64 : (k : Int) < IntTy.max .i64) :
    (csWritten t (searchIndex (IntTy.promote (unsignedIntegerType t) .i64) ((k : Int) + 1))
      (indexSub (searchIndex .i64 1) ⟨t, low⟩)).val = low.val + k := by
  have hl := low.property
  have hw : (indexSub (searchIndex (IntTy.promote (unsignedIntegerType t) .i64) ((k : Int) + 1))
      (indexSub (searchIndex .i64 1) ⟨t, low⟩)).val =
      wrapInt (IntTy.promote (IntTy.promote (unsignedIntegerType t) .i64) (IntTy.promote .i64 t))
        (low.val + k) := by
    simp only [indexSub_val, indexSub_ty, searchIndex_val, searchIndex_ty]
    rw [wrapInt_of_inRange (IntTy.promote (unsignedIntegerType t) .i64) ((k : Int) + 1)
        (cs_last_range t _ (by omega) (by omega)), wrapInt_i64_one,
      wrapInt_sub_wrap (by cases t <;> rfl)]
    congr 1
    show (k : Int) + 1 - (1 - low.val) = low.val + k
    omega
  have hty : (indexSub (searchIndex (IntTy.promote (unsignedIntegerType t) .i64) ((k : Int) + 1))
      (indexSub (searchIndex .i64 1) ⟨t, low⟩)).ty =
      IntTy.promote (IntTy.promote (unsignedIntegerType t) .i64) (IntTy.promote .i64 t) := rfl
  unfold csWritten
  simp only [hty]
  split
  · rw [searchIndex_val, hw]
    generalize low.val = y at *
    cases t <;> simp [IntTy.promote, unsignedIntegerType, signedIntegerType, IntTy.signed,
      IntTy.bits, wrapInt, IntTy.min, IntTy.max] at * <;> omega
  · rw [hw]
    generalize low.val = y at *
    cases t <;> simp [IntTy.promote, unsignedIntegerType, signedIntegerType, IntTy.signed,
      IntTy.bits, wrapInt, IntTy.min, IntTy.max] at * <;> omega

theorem cs_bucketIndex (t : IntTy) (k : Nat) (hk64 : (k : Int) < IntTy.max .i64) :
    (searchIndex (IntTy.promote (unsignedIntegerType t) .i64) ((k : Int) + 1)).val = k + 1 := by
  simp only [searchIndex, SearchIndex.val, JInt.wrap]
  exact wrapInt_of_inRange _ _ (cs_last_range t _ (by omega) (by omega))

theorem searchIndex_wrap {T T' : IntTy} (h : T.bits = T'.bits) (x : Int) :
    searchIndex T (wrapInt T' x) = searchIndex T x := by
  have e : wrapInt T (wrapInt T' x) = wrapInt T x := by simpa using wrapInt_add_wrap h 0 x
  simp only [searchIndex, JInt.wrap, e]

theorem cs_range (t : IntTy) (low high : JInt t) (hd : 0 ≤ high.val - low.val)
    (hd' : high.val - low.val < IntTy.max .i64) :
    (arrayCountingOps t).countLength
        ((arrayCountingOps t).maybeUnsigned (indexSub ⟨t, high⟩ ⟨t, low⟩)) =
      (high.val - low.val + 1).toNat ∧
    (arrayCountingOps t).bucketValues
        ((arrayCountingOps t).maybeUnsigned (indexSub ⟨t, high⟩ ⟨t, low⟩)) =
      (List.range (high.val - low.val + 1).toNat).map
        (fun (i : Nat) =>
          searchIndex (IntTy.promote (unsignedIntegerType t) .i64) ((i : Int) + 1)) := by
  have hh := high.property
  have hl := low.property
  have hr : ((arrayCountingOps t).maybeUnsigned (indexSub ⟨t, high⟩ ⟨t, low⟩)) =
      searchIndex (unsignedIntegerType t) (high.val - low.val) := by
    show searchIndex (unsignedIntegerType (indexSub ⟨t, high⟩ ⟨t, low⟩).ty)
      (indexSub ⟨t, high⟩ ⟨t, low⟩).val = _
    rw [indexSub_ty, indexSub_val]
    show searchIndex (unsignedIntegerType (IntTy.promote t t))
      (wrapInt (IntTy.promote t t) (high.val - low.val)) = _
    rw [promote_self, searchIndex_wrap (by cases t <;> rfl)]
  have hin : (unsignedIntegerType t).min ≤ high.val - low.val ∧
      high.val - low.val ≤ (unsignedIntegerType t).max := by
    generalize high.val = a at *
    generalize low.val = b at *
    cases t <;> simp [unsignedIntegerType, IntTy.signed, IntTy.bits, IntTy.min,
      IntTy.max] at * <;> omega
  have hlast : indexAdd (searchIndex (unsignedIntegerType t) (high.val - low.val))
      (searchIndex .i64 1) =
      searchIndex (IntTy.promote (unsignedIntegerType t) .i64) (high.val - low.val + 1) := by
    show searchIndex (IntTy.promote (unsignedIntegerType t) .i64)
      (wrapInt (unsignedIntegerType t) (high.val - low.val) + wrapInt .i64 1) = _
    rw [wrapInt_i64_one, wrapInt_of_inRange _ _ hin]
  have hval : (searchIndex (IntTy.promote (unsignedIntegerType t) .i64)
      (high.val - low.val + 1)).val = high.val - low.val + 1 := by
    rw [searchIndex_val]
    exact wrapInt_of_inRange _ _ (cs_last_range t _ (by omega) (by omega))
  rw [hr]
  constructor
  · show (indexAdd _ _).val.toNat = _
    rw [hlast, hval]
  · show (List.range (indexAdd _ _).val.toNat).map _ = _
    rw [hlast, hval, searchIndex_ty]
    simp only [Int.ofNat_eq_natCast]

end CountingArith

section CountingSort

variable {V : Type} {t : IntTy} {S : VectorStorage V (JInt t)} {E : V → List (JInt t)}

/-- `arrayCountingOps` with the element reads and writes of any `AbstractVector` storage
(`storageCountingOps t arrayStorage` is `arrayCountingOps t`). -/
def storageCountingOps (t : IntTy) (S : VectorStorage V (JInt t)) :
    CountingSortOps V Int SearchIndex SearchIndex (Array Nat) Bool (CountingKeywords t) Unit
      SortException where
  rangeAndScratch := (arrayCountingOps t).rangeAndScratch
  isReverse := (arrayCountingOps t).isReverse
  wrapSubtract := (arrayCountingOps t).wrapSubtract
  one := (arrayCountingOps t).one
  maybeUnsigned := (arrayCountingOps t).maybeUnsigned
  countLength := (arrayCountingOps t).countLength
  allocateCounts := (arrayCountingOps t).allocateCounts
  range := (arrayCountingOps t).range
  read := fun values index => do
    let value ← liftSortJl (S.getindex values index)
    pure ⟨t, value⟩
  write := fun values index value => do
    let converted ← liftSortJl (JInt.convert (t.name) t value.val)
    liftSortJl (S.setindex values index converted)
  bucketForValue := (arrayCountingOps t).bucketForValue
  countRead := (arrayCountingOps t).countRead
  countWrite := (arrayCountingOps t).countWrite
  bucketValues := (arrayCountingOps t).bucketValues
  bucketIndex := (arrayCountingOps t).bucketIndex
  bucketValue := (arrayCountingOps t).bucketValue
  lastBucketIndex := (arrayCountingOps t).lastBucketIndex
  nextAfterBucket := (arrayCountingOps t).nextAfterBucket
  valueNeedsSignedConversion := fun _ value => !value.ty.signed && t.signed
  toSigned := (arrayCountingOps t).toSigned

theorem storageCountingOps_array (t : IntTy) :
    storageCountingOps t (arrayStorage (α := JInt t)) = arrayCountingOps t := rfl

/-- The counting loop body of `CountingSort`. -/
def csCountBody (t : IntTy) (S : VectorStorage V (JInt t)) (values : V) (offset : SearchIndex) :
    Int → Array Nat → SortResult (ForInStep (Array Nat)) :=
  fun index counts => do
    let value ← (storageCountingOps t S).read values index
    let count ← (arrayCountingOps t).countRead counts
      ((arrayCountingOps t).bucketForValue value offset)
    let counts ← (arrayCountingOps t).countWrite counts
      ((arrayCountingOps t).bucketForValue value offset) (count + 1)
    pure (ForInStep.yield counts)

/-- The innermost loop of `CountingSort`: write one bucket value. -/
def csWriteBody (t : IntTy) (S : VectorStorage V (JInt t)) (value : SearchIndex) :
    Int → V → SortResult (ForInStep V) :=
  fun target w => do
    let w ← (storageCountingOps t S).write w target value
    pure (ForInStep.yield w)

/-- The bucket loop body of `CountingSort`. -/
def csFillBody (t : IntTy) (S : VectorStorage V (JInt t)) (counts : Array Nat)
    (offset : SearchIndex) : SearchIndex → Int × V → SortResult (ForInStep (Int × V)) :=
  fun bucket s => do
    let count ← (arrayCountingOps t).countRead counts bucket.val.toNat
    let v ← forIn (arrayIndexRange s.1 (s.1 + Int.ofNat count - 1)) s.2
      (csWriteBody t S (csWritten t bucket offset))
    pure (ForInStep.yield (s.1 + Int.ofNat count - 1 + 1, v))

theorem sortCounting_eq (t : IntTy) (S : VectorStorage V (JInt t)) (v : V) (rev : Bool)
    (lo hi : Int) (mn mx : JInt t) :
    sortCounting (storageCountingOps t S) v rev { lo, hi, minimum := mn, maximum := mx } =
      (forIn (arrayIndexRange lo hi)
          (Array.replicate ((arrayCountingOps t).countLength ((arrayCountingOps t).maybeUnsigned
            (if rev = true then indexSub ⟨t, mn⟩ ⟨t, mx⟩ else indexSub ⟨t, mx⟩ ⟨t, mn⟩))) 0)
          (csCountBody t S v (indexSub (searchIndex .i64 1)
            (if rev = true then ⟨t, mx⟩ else ⟨t, mn⟩))) >>= fun counts =>
        forIn (if rev = true then ((arrayCountingOps t).bucketValues
              ((arrayCountingOps t).maybeUnsigned
                (if rev = true then indexSub ⟨t, mn⟩ ⟨t, mx⟩ else indexSub ⟨t, mx⟩ ⟨t, mn⟩))).reverse
            else (arrayCountingOps t).bucketValues ((arrayCountingOps t).maybeUnsigned
              (if rev = true then indexSub ⟨t, mn⟩ ⟨t, mx⟩ else indexSub ⟨t, mx⟩ ⟨t, mn⟩)))
          (lo, v) (csFillBody t S counts (indexSub (searchIndex .i64 1)
            (if rev = true then ⟨t, mx⟩ else ⟨t, mn⟩))) >>= fun s =>
        pure (s.2, ())) := by
  unfold sortCounting
  rfl

theorem cs_count_loop (L : StorageLaws S E) (v : V) (offset : SearchIndex) (bk : JInt t → Nat)
    (m : Nat) :
    ∀ (R : List (JInt t)) (a : Int) (counts : Array Nat) (P Q : List (JInt t)),
      E v = P ++ R ++ Q → a = (P.length : Int) + 1 → counts.size = m →
      (∀ x ∈ R, (arrayCountingOps t).bucketForValue ⟨t, x⟩ offset = bk x ∧ 1 ≤ bk x ∧
        bk x ≤ m) →
      ∃ counts', forIn ((List.range R.length).map fun i => a + Int.ofNat i) counts
          (csCountBody t S v offset) = .ok counts' ∧ counts'.size = m ∧
        ∀ k, k < m → counts'[k]? = counts[k]?.map (· + R.countP (fun x => bk x == k + 1))
  | [], a, counts, P, Q, _, _, hm, _ => ⟨counts, rfl, hm, fun k _ => by simp⟩
  | x :: R, a, counts, P, Q, hv, ha, hm, hb => by
    obtain ⟨hbx, hb1, hb2⟩ := hb x (by simp)
    have hread : S.getindex v a = .ok x :=
      storage_read_mid L (P := P) (B := R ++ Q) (by rw [hv]; simp) (by omega) (by omega)
    have hlt : bk x - 1 < counts.size := by omega
    obtain ⟨c, hc⟩ : ∃ c, counts[bk x - 1]? = some c := ⟨counts[bk x - 1], by simp [hlt]⟩
    have hcr : (arrayCountingOps t).countRead counts (bk x) = .ok c := by
      simp only [arrayCountingOps, hc]
      rw [if_neg (by omega)]
    have hcw : (arrayCountingOps t).countWrite counts (bk x) (c + 1) =
        .ok (counts.set! (bk x - 1) (c + 1)) := by
      simp only [arrayCountingOps]
      rw [if_pos ⟨hb1, by omega⟩]
    obtain ⟨counts', hloop, hsz, hcnt⟩ := cs_count_loop L v offset bk m R (a + 1)
      (counts.set! (bk x - 1) (c + 1)) (P ++ [x]) Q (by rw [hv]; simp) (by simp; omega)
      (by simp [hm]) (fun y hy => hb y (by simp [hy]))
    refine ⟨counts', ?_, hsz, ?_⟩
    · have hstep : csCountBody t S v offset a counts =
          .ok (.yield (counts.set! (bk x - 1) (c + 1))) := by
        simp only [csCountBody, storageCountingOps, hread, liftSortJl, Except.mapError,
          bind, Except.bind, pure, Except.pure, hbx, hcr, hcw]
      rw [List.length_cons, range_int_succ, List.forIn_cons, hstep]
      simp only [bind, Except.bind]
      exact hloop
    · intro k hk
      rw [hcnt k hk, List.countP_cons, Array.set!_eq_setIfInBounds]
      by_cases hkb : bk x - 1 = k
      · subst hkb
        have hp : (bk x == bk x - 1 + 1) = true := by simp; omega
        rw [Array.getElem?_setIfInBounds_self_of_lt hlt, hc, if_pos hp]
        simp only [Option.map_some]
        congr 1
        omega
      · have hp : ¬ (bk x == k + 1) = true := by simp; omega
        rw [Array.getElem?_setIfInBounds_ne hkb]
        simp [hp]

theorem cs_write_loop (L : StorageLaws S E) (sv : SearchIndex) (y : JInt t)
    (hconv : JInt.convert (t.name) t sv.val = .ok y) :
    ∀ (c : Nat) (a : Int) (w : V) (P B Q : List (JInt t)), E w = P ++ B ++ Q →
      a = (P.length : Int) + 1 → B.length = c →
      ∃ w', forIn ((List.range c).map fun i => a + Int.ofNat i) w (csWriteBody t S sv) =
          .ok w' ∧ E w' = P ++ List.replicate c y ++ Q
  | 0, a, w, P, B, Q, hv, _, hB => ⟨w, rfl, by rw [hv, List.eq_nil_of_length_eq_zero hB]; simp⟩
  | c + 1, a, w, P, B, Q, hv, ha, hB => by
    obtain ⟨b, B', rfl⟩ : ∃ b B', B = b :: B' := by
      cases B with
      | nil => simp at hB
      | cons b B' => exact ⟨b, B', rfl⟩
    obtain ⟨w1, hw1, hv1⟩ := storage_write_mid L y (v := w) (i := a) (P := P) (B := B' ++ Q)
      (z := b) (by rw [hv]; simp) (by omega) ha
    obtain ⟨w', hloop, hv'⟩ := cs_write_loop L sv y hconv c (a + 1) w1 (P ++ [y]) B' Q
      (by rw [hv1]; simp) (by simp; omega) (by simp at hB; omega)
    refine ⟨w', ?_, by rw [hv']; simp [List.replicate_succ]⟩
    have hstep : csWriteBody t S sv a w = .ok (.yield w1) := by
      simp only [csWriteBody, storageCountingOps, hconv, hw1, liftSortJl, Except.mapError,
        bind, Except.bind, pure, Except.pure]
    rw [range_int_succ, List.forIn_cons, hstep]
    simp only [bind, Except.bind]
    exact hloop

theorem cs_fill_loop (L : StorageLaws S E) (counts : Array Nat) (offset : SearchIndex)
    (F : Nat → List (JInt t)) (LT : IntTy) :
    ∀ (K : List Nat) (a : Int) (w : V) (P Rest Q : List (JInt t)),
      E w = P ++ Rest ++ Q → a = (P.length : Int) + 1 → (K.flatMap F).length = Rest.length →
      (∀ k ∈ K, (searchIndex LT ((k : Int) + 1)).val.toNat = k + 1 ∧
        counts[k]? = some (F k).length ∧
        ∃ y, JInt.convert (t.name) t (csWritten t (searchIndex LT ((k : Int) + 1)) offset).val = .ok y ∧
          F k = List.replicate (F k).length y) →
      ∃ a' w', forIn (K.map fun (i : Nat) => searchIndex LT ((i : Int) + 1)) (a, w)
          (csFillBody t S counts offset) = .ok (a', w') ∧ E w' = P ++ K.flatMap F ++ Q
  | [], a, w, P, Rest, Q, hv, _, hlen, _ => by
    have : Rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst this
    exact ⟨a, w, rfl, by simpa using hv⟩
  | k :: K, a, w, P, Rest, Q, hv, ha, hlen, hk => by
    obtain ⟨hidx, hcount, y, hconv, hF⟩ := hk k (by simp)
    have hlenB : (Rest.take (F k).length).length = (F k).length := by
      rw [List.length_take]; simp at hlen; omega
    obtain ⟨w1, hw, hv1⟩ := cs_write_loop L (csWritten t (searchIndex LT ((k : Int) + 1)) offset)
      y hconv (F k).length a w P (Rest.take (F k).length) (Rest.drop (F k).length ++ Q)
      (by rw [← List.take_append_drop (F k).length Rest] at hv; rw [hv]; simp only [List.append_assoc]) ha hlenB
    have hcr : (arrayCountingOps t).countRead counts (k + 1) = .ok (F k).length := by
      simp only [arrayCountingOps, Nat.add_sub_cancel, hcount]
      rw [if_neg (by omega)]
    have hstep : csFillBody t S counts offset (searchIndex LT ((k : Int) + 1)) (a, w) =
        .ok (.yield (a + Int.ofNat (F k).length - 1 + 1, w1)) := by
      simp only [csFillBody]
      rw [hidx, hcr]
      simp only [bind, Except.bind]
      rw [show arrayIndexRange a (a + Int.ofNat (F k).length - 1) =
          (List.range (F k).length).map (fun i => a + Int.ofNat i) by
        unfold arrayIndexRange; congr 2; simp only [Int.ofNat_eq_natCast]; omega, hw]
      rfl
    obtain ⟨a', w', hloop, hv'⟩ := cs_fill_loop L counts offset F LT K
      (a + Int.ofNat (F k).length - 1 + 1) w1 (P ++ F k) (Rest.drop (F k).length) Q
      (by rw [hv1, ← hF]; simp) (by simp only [List.length_append, Int.ofNat_eq_natCast]; omega)
      (by simp at hlen ⊢; omega) (fun k' hk' => hk k' (by simp [hk']))
    refine ⟨a', w', ?_, by rw [hv']; simp⟩
    rw [List.map_cons, List.forIn_cons, hstep]
    simp only [bind, Except.bind]
    exact hloop

/-- Grouping a list by a key over a duplicate-free list of keys covering every key permutes it. -/
theorem flatMap_filter_perm {β : Type} (g : β → Nat) :
    ∀ (K : List Nat) (xs : List β), K.Nodup → (∀ x ∈ xs, g x ∈ K) →
      (K.flatMap fun k => xs.filter fun x => g x = k).Perm xs
  | [], xs, _, h => by
    cases xs with
    | nil => simp
    | cons x xs => exact absurd (h x (by simp)) (by simp)
  | k :: K, xs, hnd, h => by
    rw [List.nodup_cons] at hnd
    have hrest : (K.flatMap fun k' => xs.filter fun x => g x = k') =
        K.flatMap fun k' => (xs.filter fun x => !decide (g x = k)).filter fun x => g x = k' := by
      rw [List.flatMap_def, List.flatMap_def]
      congr 1
      apply List.map_congr_left
      intro k' hk'
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      by_cases hx : g x = k'
      · have hk'k : k' ≠ k := fun e => hnd.1 (e ▸ hk')
        simp [hx, hk'k]
      · simp [hx]
    rw [List.flatMap_cons, hrest]
    have ih := flatMap_filter_perm g K (xs.filter fun x => !decide (g x = k)) hnd.2 (by
      intro x hx
      rw [List.mem_filter] at hx
      rcases List.mem_cons.1 (h x hx.1) with e | e
      · simp [e] at hx
      · exact e)
    exact (List.Perm.append_left _ ih).trans (List.filter_append_perm _ xs)

/-- `CountingSort` on a window whose values lie in `low:high`: the window becomes its values
grouped by value in the order of `K`. -/
theorem counting_core (L : StorageLaws S E) (v : V) {lo hi : Int} (lowJ highJ : JInt t)
    (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1) (h3 : hi ≤ ((E v).length : Int))
    (hxs : ∀ x ∈ seg (E v) lo hi, lowJ.val ≤ x.val ∧ x.val ≤ highJ.val)
    (hd : 0 ≤ highJ.val - lowJ.val) (hd' : highJ.val - lowJ.val < IntTy.max .i64)
    (K : List Nat) (hK : K.Perm (List.range (highJ.val - lowJ.val + 1).toNat)) :
    ∃ v', (forIn (arrayIndexRange lo hi)
          (Array.replicate ((arrayCountingOps t).countLength
            ((arrayCountingOps t).maybeUnsigned (indexSub ⟨t, highJ⟩ ⟨t, lowJ⟩))) 0)
          (csCountBody t S v (indexSub (searchIndex .i64 1) ⟨t, lowJ⟩)) >>= fun counts =>
        forIn (K.map fun (i : Nat) =>
            searchIndex (IntTy.promote (unsignedIntegerType t) .i64) ((i : Int) + 1))
          (lo, v) (csFillBody t S counts (indexSub (searchIndex .i64 1) ⟨t, lowJ⟩)) >>= fun s =>
        pure (s.2, ())) = .ok (v', ()) ∧
      E v' = (E v).take (lo - 1).toNat ++
        K.flatMap (fun (k : Nat) => (seg (E v) lo hi).filter (fun x => x.val = lowJ.val + k)) ++
        (E v).drop hi.toNat := by
  have hsplit := list_split3 (E v) h1 h2 h3
  generalize hP : (E v).take (lo - 1).toNat = P at hsplit ⊢
  generalize hW : seg (E v) lo hi = W at hsplit hxs ⊢
  generalize hQ : (E v).drop hi.toNat = Q at hsplit ⊢
  have hPlen : (P.length : Int) + 1 = lo := by rw [← hP]; simp; omega
  have hWlen : (W.length : Int) = hi - lo + 1 := by
    rw [← hW]; unfold seg; simp; omega
  generalize hm : (highJ.val - lowJ.val + 1).toNat = m at hK
  have hm' : (m : Int) = highJ.val - lowJ.val + 1 := by omega
  obtain ⟨hcl, _⟩ := cs_range t lowJ highJ hd hd'
  rw [hcl, hm]
  let F : Nat → List (JInt t) := fun k => W.filter (fun x => x.val = lowJ.val + k)
  let bk : JInt t → Nat := fun x => (x.val - lowJ.val + 1).toNat
  obtain ⟨counts, hcloop, hcsz, hcnt⟩ := cs_count_loop L v
    (indexSub (searchIndex .i64 1) ⟨t, lowJ⟩) bk m W lo (Array.replicate m 0) P Q hsplit
    hPlen.symm (by simp) (by
      intro x hx
      have hb := hxs x hx
      refine ⟨?_, by simp only [bk]; omega, by simp only [bk]; omega⟩
      show (indexAdd ⟨t, x⟩ (indexSub (searchIndex .i64 1) ⟨t, lowJ⟩)).val.toNat = bk x
      rw [cs_bucket t lowJ x hb.1 (by omega)])
  have hcountF : ∀ k, k < m → counts[k]? = some (F k).length := by
    intro k hk
    rw [hcnt k hk]
    simp only [Array.getElem?_replicate, if_pos hk, Option.map_some, Nat.zero_add]
    congr 1
    rw [List.countP_eq_length_filter]
    congr 1
    apply List.filter_congr
    intro x hx
    have hb := hxs x hx
    have e : ((x.val - lowJ.val + 1).toNat = k + 1) ↔ (x.val = lowJ.val + k) := by
      constructor <;> intro h <;> omega
    rw [Bool.eq_iff_iff]
    simp only [bk, beq_iff_eq, decide_eq_true_eq]
    exact e
  have hperm : (K.flatMap F).Perm W := by
    have hgr : ∀ k ∈ K, F k = W.filter (fun x => (x.val - lowJ.val).toNat = k) := by
      intro k _
      apply List.filter_congr
      intro x hx
      have hb := hxs x hx
      rw [decide_eq_decide]
      constructor <;> intro h <;> omega
    have hflat : K.flatMap F = K.flatMap (fun (k : Nat) => W.filter (fun x => (x.val - lowJ.val).toNat = k)) := by
      rw [List.flatMap_def, List.flatMap_def]
      congr 1
      exact List.map_congr_left hgr
    rw [hflat]
    exact flatMap_filter_perm _ K W (hK.nodup_iff.2 List.nodup_range) (by
      intro x hx
      have hb := hxs x hx
      rw [hK.mem_iff, List.mem_range]
      omega)
  obtain ⟨a', v', hfloop, hv'⟩ := cs_fill_loop L counts (indexSub (searchIndex .i64 1) ⟨t, lowJ⟩)
    F (IntTy.promote (unsignedIntegerType t) .i64) K lo v P W Q hsplit hPlen.symm
    hperm.length_eq (by
      intro k hk
      have hkm : k < m := by rw [hK.mem_iff, List.mem_range] at hk; exact hk
      have hk64 : (k : Int) < IntTy.max .i64 := by omega
      have hkmax : lowJ.val + k ≤ t.max := by have := highJ.property; omega
      refine ⟨by rw [cs_bucketIndex t k hk64]; omega, hcountF k hkm, ?_⟩
      have hval := cs_value t lowJ k hkmax hk64
      have hin : t.min ≤ lowJ.val + k ∧ lowJ.val + k ≤ t.max := by
        have := lowJ.property; omega
      refine ⟨⟨lowJ.val + k, hin⟩, ?_, ?_⟩
      · rw [hval]
        unfold JInt.convert
        rw [dif_pos hin]
      · rw [List.eq_replicate_iff]
        refine ⟨rfl, fun z hz => ?_⟩
        apply Subtype.ext
        have := (List.mem_filter.1 hz).2
        simpa using this)
  refine ⟨v', ?_, hv'⟩
  rw [show arrayIndexRange lo hi = (List.range W.length).map (fun i => lo + Int.ofNat i) by
    unfold arrayIndexRange; congr 2; omega, hcloop]
  simp only [bind, Except.bind]
  rw [hfloop]
  rfl

theorem countingOrder_negTrans (rev : Bool) :
    NegTransOrder (fun a b : JInt t =>
      if rev then decide (b.val < a.val) else decide (a.val < b.val)) := by
  refine ⟨fun a => by cases rev <;> simp, fun a b c hab hbc => ?_, fun a b c hac => ?_⟩
  · cases rev <;> simp at hab hbc ⊢ <;> omega
  · cases rev <;> simp at hac ⊢ <;> omega

/-- `CountingSort` on any storage: for a window whose values lie between the extrema it sorts
the window by value (ascending, or descending for `Reverse`) and leaves the rest unchanged. -/
theorem sortCounting_spec (L : StorageLaws S E) (v : V) {lo hi : Int} (mn mx : JInt t)
    (rev : Bool) (h1 : 1 ≤ lo) (h2 : lo ≤ hi + 1) (h3 : hi ≤ ((E v).length : Int))
    (hxs : ∀ x ∈ seg (E v) lo hi, (if rev then mx.val else mn.val) ≤ x.val ∧
      x.val ≤ (if rev then mn.val else mx.val))
    (hd : 0 ≤ (if rev then mn.val else mx.val) - (if rev then mx.val else mn.val))
    (hd' : (if rev then mn.val else mx.val) - (if rev then mx.val else mn.val) <
      IntTy.max .i64) :
    ∃ v', sortCounting (storageCountingOps t S) v rev { lo, hi, minimum := mn, maximum := mx } =
        .ok (v', ()) ∧
      WindowOutcome (fun a b : JInt t =>
        if rev then decide (b.val < a.val) else decide (a.val < b.val)) false (E v) (E v') lo hi := by
  have hsplit := list_split3 (E v) h1 h2 h3
  have hPlen : (((E v).take (lo - 1).toNat).length : Int) + 1 = lo := by simp; omega
  have hWlen : ((seg (E v) lo hi).length : Int) = hi - lo + 1 := by unfold seg; simp; omega
  -- the two orders differ only in the extrema roles and the bucket order
  have key : ∀ (lowJ highJ : JInt t) (K : List Nat),
      (∀ x ∈ seg (E v) lo hi, lowJ.val ≤ x.val ∧ x.val ≤ highJ.val) →
      0 ≤ highJ.val - lowJ.val → highJ.val - lowJ.val < IntTy.max .i64 →
      K.Perm (List.range (highJ.val - lowJ.val + 1).toNat) →
      K.Pairwise (fun k k' => if rev then k' < k else k < k') →
      ∀ v', E v' = (E v).take (lo - 1).toNat ++
          K.flatMap (fun (k : Nat) => (seg (E v) lo hi).filter (fun x => x.val = lowJ.val + k)) ++
          (E v).drop hi.toNat →
        WindowOutcome (fun a b : JInt t =>
          if rev then decide (b.val < a.val) else decide (a.val < b.val)) false
          (E v) (E v') lo hi := by
    intro lowJ highJ K hb _ _ hK hord v' hv'
    refine ⟨_, _, _, _, hsplit, hPlen, hWlen, hv', ?_, ?_, fun h => by cases h⟩
    · have hgr : K.flatMap (fun (k : Nat) => (seg (E v) lo hi).filter (fun x => x.val = lowJ.val + k)) =
          K.flatMap (fun (k : Nat) => (seg (E v) lo hi).filter
            (fun x => (x.val - lowJ.val).toNat = k)) := by
        rw [List.flatMap_def, List.flatMap_def]
        congr 1
        apply List.map_congr_left
        intro k _
        apply List.filter_congr
        intro x hx
        have := hb x hx
        rw [decide_eq_decide]
        constructor <;> intro h <;> omega
      rw [hgr]
      exact flatMap_filter_perm _ K _ (hK.nodup_iff.2 List.nodup_range) (by
        intro x hx
        have := hb x hx
        rw [hK.mem_iff, List.mem_range]
        omega)
    · show List.Pairwise _ _
      rw [List.pairwise_flatMap]
      refine ⟨fun k _ => ?_, hord.imp (fun {k k'} hkk => ?_)⟩
      · apply List.pairwise_of_forall_mem_list
        intro a ha b hb'
        have ha' := (List.mem_filter.1 ha).2
        have hb'' := (List.mem_filter.1 hb').2
        simp only [decide_eq_true_eq] at ha' hb''
        cases rev <;> simp <;> omega
      · intro a ha b hb'
        have ha' := (List.mem_filter.1 ha).2
        have hb'' := (List.mem_filter.1 hb').2
        simp only [decide_eq_true_eq] at ha' hb''
        cases rev <;> simp at hkk ⊢ <;> omega
  cases rev
  · simp only [Bool.false_eq_true, ↓reduceIte] at hxs hd hd' key ⊢
    obtain ⟨_, hbv⟩ := cs_range t mn mx hd hd'
    obtain ⟨v', hrun, hv'⟩ := counting_core L v mn mx h1 h2 h3 hxs hd hd'
      (List.range (mx.val - mn.val + 1).toNat) (List.Perm.refl _)
    refine ⟨v', ?_, key mn mx _ hxs hd hd' (List.Perm.refl _) List.pairwise_lt_range v' hv'⟩
    rw [sortCounting_eq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hbv]
    exact hrun
  · simp only [↓reduceIte] at hxs hd hd' key ⊢
    obtain ⟨_, hbv⟩ := cs_range t mx mn hd hd'
    obtain ⟨v', hrun, hv'⟩ := counting_core L v mx mn h1 h2 h3 hxs hd hd'
      (List.range (mn.val - mx.val + 1).toNat).reverse (List.reverse_perm _)
    refine ⟨v', ?_, key mx mn _ hxs hd hd' (List.reverse_perm _)
      (List.pairwise_reverse.2 List.pairwise_lt_range) v' hv'⟩
    rw [sortCounting_eq]
    simp only [↓reduceIte]
    rw [hbv, ← List.map_reverse]
    exact hrun

end CountingSort

/-! ### `ComputeExtrema` in front of `CountingSort` -/

section Extrema

variable {V : Type} {t : IntTy} {S : VectorStorage V (JInt t)} {E : V → List (JInt t)}

/-- `arrayExtremaCountingOps` with the reads of any `AbstractVector` storage (`initial` is the
`scratch` that `ComputeExtrema` returns when every element is equal). -/
def storageExtremaCountingOps (t : IntTy) (S : VectorStorage V (JInt t)) (initial : V) :
    ComputeExtremaOps V Unit Int Int Int Int (JInt t) (ExtremaKeywords t) V SortException Bool where
  rangeAndScratch := fun _ _ kw => .ok (kw, kw.lo, kw.hi, initial)
  nextIndex := fun index => index + 1
  range := arrayIndexRange
  readFirst := fun values index => liftSortJl (S.getindex values index)
  read := fun values index => liftSortJl (S.getindex values index)
  less := fun reverse a b => .ok (if reverse then decide (b.val < a.val) else decide (a.val < b.val))
  appendExtrema := fun kw minimum maximum =>
    { kw with minimum := some minimum, maximum := some maximum }
  nextAlgorithm := id
  sort := fun values _ reverse kw => do
    match kw.minimum, kw.maximum with
    | some minimum, some maximum =>
      let (result, _) ← sortCounting (storageCountingOps t S) values reverse
        { lo := kw.lo, hi := kw.hi, minimum, maximum }
      pure result
    | _, _ => .error (.jl (.argumentError "extrema have not been computed"))

theorem storageExtremaCountingOps_array (t : IntTy) (initial : Array (JInt t)) :
    storageExtremaCountingOps t (arrayStorage (α := JInt t)) initial =
      arrayExtremaCountingOps t initial := rfl

/-- The running extrema of `ComputeExtrema` after the elements `R`. -/
def extremaStep (less : JInt t → JInt t → Bool) (s : JInt t × JInt t) (x : JInt t) :
    JInt t × JInt t :=
  (if less x s.1 = true then x else s.1, if less s.2 x = true then x else s.2)

theorem ce_loop (L : StorageLaws S E) (v : V) (less : JInt t → JInt t → Bool)
    (f : Int → JInt t × JInt t → SortResult (ForInStep (JInt t × JInt t)))
    (hf : ∀ index (mn mx value : JInt t), S.getindex v index = .ok value →
      f index (mn, mx) = .ok (.yield (extremaStep less (mn, mx) value))) :
    ∀ (R : List (JInt t)) (a : Int) (P Q : List (JInt t)) (s : JInt t × JInt t),
      E v = P ++ R ++ Q → a = (P.length : Int) + 1 →
      forIn ((List.range R.length).map fun i => a + Int.ofNat i) s f =
        .ok (R.foldl (extremaStep less) s)
  | [], _, _, _, _, _, _ => rfl
  | x :: R, a, P, Q, s, hv, ha => by
    have hread : S.getindex v a = .ok x :=
      storage_read_mid L (P := P) (B := R ++ Q) (by rw [hv]; simp) (by omega) (by omega)
    rw [List.length_cons, range_int_succ, List.forIn_cons, hf a s.1 s.2 x hread]
    simp only [bind, Except.bind, List.foldl_cons]
    exact ce_loop L v less f hf R (a + 1) (P ++ [x]) Q _ (by rw [hv]; simp) (by simp; omega)

theorem extrema_fold (key : JInt t → Int) (less : JInt t → JInt t → Bool)
    (hless : ∀ a b, less a b = decide (key a < key b)) :
    ∀ (R : List (JInt t)) (s : JInt t × JInt t),
      ((R.foldl (extremaStep less) s).1 ∈ s.1 :: R ∧
        ∀ y ∈ s.1 :: R, key (R.foldl (extremaStep less) s).1 ≤ key y) ∧
      ((R.foldl (extremaStep less) s).2 ∈ s.2 :: R ∧
        ∀ y ∈ s.2 :: R, key y ≤ key (R.foldl (extremaStep less) s).2)
  | [], s => by simp
  | x :: R, s => by
    rw [List.foldl_cons]
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := extrema_fold key less hless R (extremaStep less s x)
    have hs1 : key (extremaStep less s x).1 ≤ key s.1 ∧ key (extremaStep less s x).1 ≤ key x ∧
        ((extremaStep less s x).1 = s.1 ∨ (extremaStep less s x).1 = x) := by
      simp only [extremaStep, hless, decide_eq_true_eq]
      by_cases h : key x < key s.1
      · rw [if_pos h]; exact ⟨by omega, Int.le_refl _, Or.inr rfl⟩
      · rw [if_neg h]; exact ⟨Int.le_refl _, by omega, Or.inl rfl⟩
    have hs2 : key s.2 ≤ key (extremaStep less s x).2 ∧ key x ≤ key (extremaStep less s x).2 ∧
        ((extremaStep less s x).2 = s.2 ∨ (extremaStep less s x).2 = x) := by
      simp only [extremaStep, hless, decide_eq_true_eq]
      by_cases h : key s.2 < key x
      · rw [if_pos h]; exact ⟨by omega, Int.le_refl _, Or.inr rfl⟩
      · rw [if_neg h]; exact ⟨Int.le_refl _, by omega, Or.inl rfl⟩
    generalize extremaStep less s x = s1 at h1 h2 h3 h4 hs1 hs2
    generalize R.foldl (extremaStep less) s1 = r at h1 h2 h3 h4
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rcases List.mem_cons.1 h1 with e | e
      · rcases hs1.2.2 with e' | e' <;> rw [e, e'] <;> simp
      · simp [e]
    · intro y hy
      have hr := h2 s1.1 List.mem_cons_self
      rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · rcases List.mem_cons.1 hy with rfl | hy
        · omega
        · exact h2 y (List.mem_cons_of_mem _ hy)
    · rcases List.mem_cons.1 h3 with e | e
      · rcases hs2.2.2 with e' | e' <;> rw [e, e'] <;> simp
      · simp [e]
    · intro y hy
      have hr := h4 s1.2 List.mem_cons_self
      rcases List.mem_cons.1 hy with rfl | hy
      · omega
      · rcases List.mem_cons.1 hy with rfl | hy
        · omega
        · exact h4 y (List.mem_cons_of_mem _ hy)

/-- `ComputeExtrema(ConsiderCountingSort(CountingSort))` as `sort!` reaches it, on any storage:
for a nonempty window whose span fits in `Int` it sorts the window by value. -/
theorem computeExtrema_spec (L : StorageLaws S E) (v : V) {lo hi : Int} (rev : Bool)
    (h1 : 1 ≤ lo) (h2 : lo ≤ hi) (h3 : hi ≤ ((E v).length : Int))
    (hspan : ∀ x ∈ seg (E v) lo hi, ∀ y ∈ seg (E v) lo hi, y.val - x.val < IntTy.max .i64) :
    ∃ result, sortComputeExtrema (storageExtremaCountingOps t S v) v () rev { lo, hi } =
        .ok result ∧
      WindowOutcome (fun a b : JInt t =>
        if rev then decide (b.val < a.val) else decide (a.val < b.val)) false
        (E v) (E result) lo hi := by
  have hsplit := list_split3 (E v) h1 (by omega) h3
  generalize hP : (E v).take (lo - 1).toNat = P at hsplit
  generalize hQ : (E v).drop hi.toNat = Q at hsplit
  have hPlen : (P.length : Int) + 1 = lo := by rw [← hP]; simp; omega
  have hWlen : ((seg (E v) lo hi).length : Int) = hi - lo + 1 := by unfold seg; simp; omega
  generalize hW : seg (E v) lo hi = W at hsplit hspan hWlen
  obtain ⟨first, R, rfl⟩ : ∃ first R, W = first :: R := by
    cases W with
    | nil => simp at hWlen; omega
    | cons first R => exact ⟨first, R, rfl⟩
  have hread : S.getindex v lo = .ok first :=
    storage_read_mid L (P := P) (B := R ++ Q) (by rw [hsplit]; simp) h1 (by omega)
  let less : JInt t → JInt t → Bool := fun a b =>
    if rev = true then decide (b.val < a.val) else decide (a.val < b.val)
  let key : JInt t → Int := fun x => if rev then -x.val else x.val
  have hless : ∀ a b, less a b = decide (key a < key b) := by
    intro a b
    simp only [less, key]
    cases rev <;> simp <;> omega
  obtain ⟨⟨hm1, hm2⟩, ⟨hM1, hM2⟩⟩ := extrema_fold key less hless R (first, first)
  unfold sortComputeExtrema
  simp only [storageExtremaCountingOps, hread, liftSortJl, Except.mapError, bind, Except.bind]
  rw [show arrayIndexRange (lo + 1) hi = (List.range R.length).map
      (fun i => (lo + 1) + Int.ofNat i) by
    unfold arrayIndexRange; congr 2; simp at hWlen; omega]
  rw [ce_loop L v less _ ?hf R (lo + 1) (P ++ [first]) Q (first, first)
    (by rw [hsplit]; simp) (by simp; omega)]
  case hf =>
    intro index mn mx value hr
    simp only [hr, liftSortJl, Except.mapError, bind, Except.bind, extremaStep, less]
    by_cases c1 : (if rev = true then decide (mn.val < value.val) else
        decide (value.val < mn.val)) = true <;>
      by_cases c2 : (if rev = true then decide (value.val < mx.val) else
        decide (mx.val < value.val)) = true <;>
      simp only [c1, c2, if_true, if_false, Bool.false_eq_true] <;> rfl
  simp only [bind, Except.bind]
  generalize hmn : (R.foldl (extremaStep less) (first, first)).1 = mn at hm1 hm2
  generalize hmx : (R.foldl (extremaStep less) (first, first)).2 = mx at hM1 hM2
  simp only [key] at hm2 hM2
  by_cases hc : (if rev = true then decide (mx.val < mn.val) else decide (mn.val < mx.val)) = true
  · have hc' : (!(if rev = true then decide (mx.val < mn.val) else
        decide (mn.val < mx.val))) = false := by simp [hc]
    simp only [hc', Bool.false_eq_true, ↓reduceIte]
    have hxs : ∀ x ∈ seg (E v) lo hi, (if rev then mx.val else mn.val) ≤ x.val ∧
        x.val ≤ (if rev then mn.val else mx.val) := by
      rw [hW]
      intro x hx
      have a1 := hm2 x hx
      have a2 := hM2 x hx
      cases rev <;> simp at a1 a2 ⊢ <;> omega
    have a1 := hm2 mx hM1
    have hd : 0 ≤ (if rev then mn.val else mx.val) - (if rev then mx.val else mn.val) := by
      cases rev <;> simp at a1 ⊢ <;> omega
    have hd' : (if rev then mn.val else mx.val) - (if rev then mx.val else mn.val) <
        IntTy.max .i64 := by
      cases rev
      · simpa using hspan mn hm1 mx hM1
      · simpa using hspan mx hM1 mn hm1
    obtain ⟨v', hrun, hout⟩ := sortCounting_spec L v mn mx rev h1 (by omega) h3 hxs hd hd'
    refine ⟨v', ?_, hout⟩
    rw [hrun]
    rfl
  · have hc' : (!(if rev = true then decide (mx.val < mn.val) else
        decide (mn.val < mx.val))) = true := by
      cases rev <;> simp at hc ⊢ <;> omega
    simp only [hc', ↓reduceIte]
    refine ⟨v, rfl, P, first :: R, Q, first :: R, hsplit, hPlen, hWlen, hsplit,
      List.Perm.refl _, ?_, fun h => by cases h⟩
    have a1 := hm2 mx hM1
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    have b1 := hm2 a ha
    have b2 := hM2 a ha
    have b3 := hm2 b hb
    have b4 := hM2 b hb
    cases rev <;> simp at hc a1 b1 b2 b3 b4 ⊢ <;> omega


end Extrema


/-- `_sort!(v, CountingSort(), o, (; lo, hi, mn, mx))` on any one-based storage obeying the
`AbstractVector` laws, for `Forward` (`reverse = false`) and `Reverse` integer orderings: when
every window value lies between the extrema that `ComputeExtrema` supplies (`mn ≤ x ≤ mx` in
the ordering) and the extrema's span fits in `Int` (as `ConsiderCountingSort` guarantees), it
replaces the window by a sorted permutation of it and leaves the rest of the vector unchanged. -/
def CountingSortCorrect : Prop :=
  ∀ (V : Type) (t : IntTy) (S : VectorStorage V (JInt t)) (E : V → List (JInt t)),
    StorageLaws S E →
  ∀ (v : V) (lo hi : Int) (minimum maximum : JInt t) (reverse : Bool),
    1 ≤ lo → lo ≤ hi + 1 → hi ≤ ((E v).length : Int) →
    (∀ x ∈ seg (E v) lo hi, (if reverse then maximum.val else minimum.val) ≤ x.val ∧
      x.val ≤ (if reverse then minimum.val else maximum.val)) →
    0 ≤ (if reverse then minimum.val else maximum.val) -
      (if reverse then maximum.val else minimum.val) →
    (if reverse then minimum.val else maximum.val) -
      (if reverse then maximum.val else minimum.val) < IntTy.max .i64 →
    ∃ v', sortCounting (storageCountingOps t S) v reverse { lo, hi, minimum, maximum } =
        .ok (v', ()) ∧
      WindowOutcome (fun a b : JInt t =>
        if reverse then decide (b.val < a.val) else decide (a.val < b.val)) false
        (E v) (E v') lo hi


/-- Under the same preconditions every bucket index `v[i] +% offs` that `CountingSort` reads or
writes is inside `counts`, so the call never throws a `BoundsError` (it returns normally). -/
def CountBucketsInBounds : Prop :=
  ∀ (V : Type) (t : IntTy) (S : VectorStorage V (JInt t)) (E : V → List (JInt t)),
    StorageLaws S E →
  ∀ (v : V) (lo hi : Int) (minimum maximum : JInt t) (reverse : Bool),
    1 ≤ lo → lo ≤ hi + 1 → hi ≤ ((E v).length : Int) →
    (∀ x ∈ seg (E v) lo hi, (if reverse then maximum.val else minimum.val) ≤ x.val ∧
      x.val ≤ (if reverse then minimum.val else maximum.val)) →
    0 ≤ (if reverse then minimum.val else maximum.val) -
      (if reverse then maximum.val else minimum.val) →
    (if reverse then minimum.val else maximum.val) -
      (if reverse then maximum.val else minimum.val) < IntTy.max .i64 →
    sortCounting (storageCountingOps t S) v reverse { lo, hi, minimum, maximum } ≠
      .error (.jl .boundsError)


/-- `_sort!(v, ComputeExtrema(ConsiderCountingSort(CountingSort())), o, (; lo, hi, scratch))`
(the counting route, `scratch` being the input) on any one-based storage obeying the
`AbstractVector` laws, for `Forward` and `Reverse` integer orderings: on a nonempty window inside
the vector whose values span less than `typemax(Int)` it returns a vector whose window is a
sorted permutation of the old window and which agrees elsewhere. -/
def ComputeExtremaCountingCorrect : Prop :=
  ∀ (V : Type) (t : IntTy) (S : VectorStorage V (JInt t)) (E : V → List (JInt t)),
    StorageLaws S E →
  ∀ (v : V) (lo hi : Int) (reverse : Bool),
    1 ≤ lo → lo ≤ hi → hi ≤ ((E v).length : Int) →
    (∀ x ∈ seg (E v) lo hi, ∀ y ∈ seg (E v) lo hi, y.val - x.val < IntTy.max .i64) →
    ∃ result, sortComputeExtrema (storageExtremaCountingOps t S v) v () reverse { lo, hi } =
        .ok result ∧
      WindowOutcome (fun a b : JInt t =>
        if reverse then decide (b.val < a.val) else decide (a.val < b.val)) false
        (E v) (E result) lo hi


/-- Laws under which `SortpermRangeOps` behaves like `sortperm_int_range` on a
`Vector{<:Integer}` holding `input`: one-based reads of `input`, wrapping offsets that give
each value its rank, rank comparisons, and `Vector{Int}` counts and permutation storage. -/
def SortpermIntRangeOpsFaithful {V : Type}
    (ops : SortpermRangeOps (StateT (Array Int × Array Int) Jl) V Unit Unit)
    (values : V) (input : List I) (minimum : I) (rank : I → Int) : Prop :=
  (∀ s, (ops.length values).run s = .ok (JuliaLean.base.int.lit .i64 input.length, s)) ∧
  (∀ index value s, 1 ≤ index.val → index.val ≤ Int.ofNat input.length →
    ((ops.read values index).run s = .ok (value, s) ↔
      input[(index.val - 1).toNat]? = some value)) ∧
  (∀ value, value ∈ input →
    (JuliaLean.base.int.addWrap value
      (JuliaLean.base.int.subWrap (JuliaLean.base.int.lit .i64 1) minimum)).val = rank value ∧
    (JuliaLean.base.int.addWrap
      (JuliaLean.base.int.addWrap value
        (JuliaLean.base.int.subWrap (JuliaLean.base.int.lit .i64 1) minimum))
      (JuliaLean.base.int.lit .i64 1)).val = rank value + 1) ∧
  (∀ length c p, (ops.allocateCounts length).run (c, p) =
    if 0 ≤ length.val then .ok ((), (Array.replicate length.val.toNat 0, p))
    else .error .boundsError) ∧
  (∀ c p, (ops.countLength ()).run (c, p) = .ok (JuliaLean.base.int.lit .i64 c.size, (c, p))) ∧
  (∀ index c p, (ops.getCount () index).run (c, p) =
    (arrayRead c index.val).map (fun v => (JuliaLean.base.int.lit .i64 v, (c, p)))) ∧
  (∀ index value c p, (ops.setCount () index value).run (c, p) =
    (arrayWrite c index.val value.val).map (fun c' => ((), (c', p)))) ∧
  (∀ length c p, (ops.allocatePermutation length).run (c, p) =
    if 0 ≤ length.val then .ok ((), (c, Array.replicate length.val.toNat 0))
    else .error .boundsError) ∧
  (∀ index value c p, (ops.setPermutation () index value).run (c, p) =
    (arrayWrite p index.val value.val).map (fun p' => ((), (c, p')))) ∧
  (∀ lo hi s, (ops.range lo hi).run s = .ok (
    (if lo.val ≤ hi.val then
      (List.range ((hi.val - lo.val + 1).toNat)).map fun offset =>
        JuliaLean.base.int.lit .i64 (lo.val + Int.ofNat offset)
    else []), s))


section SortpermRange

variable {V T : Type}

/-- Zero-based slot that the stable counting order by `rank` gives to `xs[j]`: the number of
elements of smaller rank plus the number of earlier elements of equal rank. -/
def sp_pos (rank : T → Int) (xs : List T) (j : Nat) : Nat :=
  match xs[j]? with
  | some x => xs.countP (fun y => decide (rank y < rank x)) +
      (xs.take j).countP (fun y => decide (rank y = rank x))
  | none => 0

theorem sp_countP_add_le (p q s : T → Bool) :
    ∀ (l : List T), (∀ y ∈ l, p y = true → s y = true) → (∀ y ∈ l, q y = true → s y = true) →
      (∀ y ∈ l, ¬ (p y = true ∧ q y = true)) → l.countP p + l.countP q ≤ l.countP s
  | [], _, _, _ => by simp
  | a :: l, hp, hq, hd => by
    have ih := sp_countP_add_le p q s l (fun y hy => hp y (by simp [hy]))
      (fun y hy => hq y (by simp [hy])) (fun y hy => hd y (by simp [hy]))
    have hpa := hp a (by simp)
    have hqa := hq a (by simp)
    have hda := hd a (by simp)
    simp only [List.countP_cons]
    cases hpv : p a <;> cases hqv : q a <;> cases hsv : s a <;> simp_all <;> omega

theorem sp_countP_take_lt (rank : T → Int) (xs : List T) (j : Nat) (x : T)
    (hx : xs[j]? = some x) :
    (xs.take j).countP (fun y => decide (rank y = rank x)) + 1 ≤
      xs.countP (fun y => decide (rank y = rank x)) := by
  have hj : j < xs.length := by
    apply Classical.byContradiction
    intro h
    rw [List.getElem?_eq_none (by omega)] at hx
    cases hx
  have hxj : xs[j] = x := by
    rw [List.getElem?_eq_getElem hj] at hx
    exact Option.some.inj hx
  conv => rhs; rw [← List.take_append_drop j xs]
  rw [List.countP_append, List.drop_eq_getElem_cons hj, List.countP_cons, hxj]
  simp

theorem sp_pos_lt (rank : T → Int) (xs : List T) (j : Nat) (hj : j < xs.length) :
    sp_pos rank xs j < xs.length := by
  obtain ⟨x, hx⟩ : ∃ x, xs[j]? = some x := ⟨xs[j], List.getElem?_eq_getElem hj⟩
  unfold sp_pos
  rw [hx]
  have h1 := sp_countP_take_lt rank xs j x hx
  have h2 := sp_countP_add_le (fun y => decide (rank y < rank x))
    (fun y => decide (rank y = rank x)) (fun _ => true) xs (by simp) (by simp)
    (by intro y _ h; simp at h; omega)
  have h3 : xs.countP (fun _ => true) = xs.length := by simp
  simp only
  omega

theorem sp_pos_lt_of_rank (rank : T → Int) (xs : List T) (j1 j2 : Nat) (x1 x2 : T)
    (h1 : xs[j1]? = some x1) (h2 : xs[j2]? = some x2)
    (h : rank x1 < rank x2 ∨ (rank x1 = rank x2 ∧ j1 < j2)) :
    sp_pos rank xs j1 < sp_pos rank xs j2 := by
  unfold sp_pos
  rw [h1, h2]
  simp only
  rcases h with h | ⟨h, hj⟩
  · have ht := sp_countP_take_lt rank xs j1 x1 h1
    have hs := sp_countP_add_le (fun y => decide (rank y < rank x1))
      (fun y => decide (rank y = rank x1)) (fun y => decide (rank y < rank x2)) xs
      (by intro y _ hy; simp at hy ⊢; omega) (by intro y _ hy; simp at hy ⊢; omega)
      (by intro y _ hy; simp at hy; omega)
    omega
  · rw [show (fun y => decide (rank y < rank x2)) = (fun y => decide (rank y < rank x1)) by
        rw [h]]
    rw [show (fun y => decide (rank y = rank x2)) = (fun y => decide (rank y = rank x1)) by
        rw [h]]
    have hj1 : j1 < xs.length := by
      apply Classical.byContradiction
      intro hc
      rw [List.getElem?_eq_none (by omega)] at h1
      cases h1
    have hx1 : xs[j1] = x1 := by
      rw [List.getElem?_eq_getElem hj1] at h1
      exact Option.some.inj h1
    have htake : xs.take j2 = xs.take j1 ++ (xs.drop j1).take (j2 - j1) := by
      rw [← List.take_add]; congr 1; omega
    obtain ⟨d, hd⟩ : ∃ d, j2 - j1 = d + 1 := ⟨j2 - j1 - 1, by omega⟩
    have hdrop : (xs.drop j1).take (j2 - j1) = x1 :: (xs.drop (j1 + 1)).take d := by
      rw [List.drop_eq_getElem_cons hj1, hx1, hd, List.take_succ_cons]
    rw [htake, hdrop, List.countP_append, List.countP_cons]
    simp

theorem sp_pos_ne (rank : T → Int) (xs : List T) (j1 j2 : Nat)
    (h1 : j1 < xs.length) (h2 : j2 < xs.length) (hne : j1 ≠ j2) :
    sp_pos rank xs j1 ≠ sp_pos rank xs j2 := by
  have e1 : xs[j1]? = some xs[j1] := List.getElem?_eq_getElem h1
  have e2 : xs[j2]? = some xs[j2] := List.getElem?_eq_getElem h2
  intro heq
  rcases Int.lt_trichotomy (rank xs[j1]) (rank xs[j2]) with h | h | h
  · have := sp_pos_lt_of_rank rank xs j1 j2 _ _ e1 e2 (Or.inl h); omega
  · rcases Nat.lt_or_gt_of_ne hne with hj | hj
    · have := sp_pos_lt_of_rank rank xs j1 j2 _ _ e1 e2 (Or.inr ⟨h, hj⟩); omega
    · have := sp_pos_lt_of_rank rank xs j2 j1 _ _ e2 e1 (Or.inr ⟨h.symm, hj⟩); omega
  · have := sp_pos_lt_of_rank rank xs j2 j1 _ _ e2 e1 (Or.inl h); omega

/-- A duplicate-free list of naturals below `n` has at most `n` elements. -/
theorem sp_nodup_length_le : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < n) →
    l.length ≤ n
  | 0, l, _, h => by
    cases l with
    | nil => simp
    | cons x _ => exact absurd (h x (by simp)) (by omega)
  | n + 1, l, hnd, h => by
    have ih := sp_nodup_length_le n (l.erase n) (hnd.erase n) (by
      intro x hx
      rw [hnd.mem_erase_iff] at hx
      have := h x hx.2
      omega)
    have hl := List.length_erase (a := n) (l := l)
    split at hl <;> omega

/-- A duplicate-free list of `n` naturals below `n` contains every natural below `n`. -/
theorem sp_mem_of_nodup (n : Nat) (l : List Nat) (hnd : l.Nodup) (h : ∀ x ∈ l, x < n)
    (hlen : l.length = n) (y : Nat) (hy : y < n) : y ∈ l := by
  apply Classical.byContradiction
  intro hy'
  have hnd' : (l.map fun x => if x < y then x else x - 1).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hnd
    intro a b ha hb hab
    have hay : a ≠ y := fun e => hy' (e ▸ ha)
    have hby : b ≠ y := fun e => hy' (e ▸ hb)
    split <;> split <;> omega
  have hle := sp_nodup_length_le (n - 1) _ hnd' (by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    have := h x hx
    have hxy : x ≠ y := fun e => hy' (e ▸ hx)
    split <;> omega)
  simp only [List.length_map] at hle
  omega

/-- Every slot below `xs.length` is the slot of exactly one element. -/
theorem sp_pos_surj (rank : T → Int) (xs : List T) (p : Nat) (hp : p < xs.length) :
    ∃ j, j < xs.length ∧ sp_pos rank xs j = p := by
  have hmem := sp_mem_of_nodup xs.length ((List.range xs.length).map (sp_pos rank xs))
    (by
      unfold List.Nodup
      rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ (List.nodup_range)
      intro a b ha hb hab
      exact sp_pos_ne rank xs a b (List.mem_range.1 ha) (List.mem_range.1 hb) hab)
    (by
      intro z hz
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
      exact sp_pos_lt rank xs j (List.mem_range.1 hj))
    (by simp) p hp
  obtain ⟨j, hj, hjp⟩ := List.mem_map.1 hmem
  exact ⟨j, List.mem_range.1 hj, hjp⟩

theorem sp_countP_le_split (rank : T → Int) (k : Int) (l : List T) :
    l.countP (fun y => decide (rank y ≤ k)) =
      l.countP (fun y => decide (rank y ≤ k - 1)) + l.countP (fun y => decide (rank y = k)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons, ih]
    by_cases h1 : rank a ≤ k - 1
    · have h2 : rank a ≤ k := by omega
      have h3 : rank a ≠ k := by omega
      simp [h1, h2, h3]
      omega
    · by_cases h3 : rank a = k
      · have h4 : ¬ (k ≤ k - 1) := by omega
        simp [h3, h4]
        omega
      · have h2 : ¬ rank a ≤ k := by omega
        simp [h1, h2, h3]

/-- The first `for` loop of `sortperm_int_range`. -/
def sp_body1 [Monad m] (ops : SortpermRangeOps m V C P) (values : V)
    (offsets : I) (counts : C) (i : I) (_ : PUnit) : m (ForInStep PUnit) := do
  let value ← ops.read values i
  let bucket := JuliaLean.base.int.addWrap (JuliaLean.base.int.addWrap value offsets)
    (JuliaLean.base.int.lit .i64 1)
  let count ← ops.getCount counts bucket
  ops.setCount counts bucket (JuliaLean.base.int.add count (JuliaLean.base.int.lit .i64 1))
  pure (ForInStep.yield ⟨⟩)

/-- The cumulative-sum loop of `sortperm_int_range`. -/
def sp_body2 [Monad m] (ops : SortpermRangeOps m V C P) (counts : C) (i : I)
    (_ : PUnit) : m (ForInStep PUnit) := do
  let count ← ops.getCount counts i
  let previous ← ops.getCount counts (JuliaLean.base.int.sub i (JuliaLean.base.int.lit .i64 1))
  ops.setCount counts i (JuliaLean.base.int.add count previous)
  pure (ForInStep.yield ⟨⟩)

/-- The placement loop of `sortperm_int_range`. -/
def sp_body3 [Monad m] (ops : SortpermRangeOps m V C P) (values : V)
    (offsets : I) (counts : C) (permutation : P) (i : I) (_ : PUnit) : m (ForInStep PUnit) := do
  let value ← ops.read values i
  let label := JuliaLean.base.int.addWrap value offsets
  let target ← ops.getCount counts label
  ops.setPermutation permutation target i
  let count ← ops.getCount counts label
  ops.setCount counts label (JuliaLean.base.int.add count (JuliaLean.base.int.lit .i64 1))
  pure (ForInStep.yield ⟨⟩)

theorem sp_unfold [Monad m] (ops : SortpermRangeOps m V C P) (values : V)
    (R minValue : I) :
    sortpermIntRange ops values R minValue = (do
      let offsets := JuliaLean.base.int.subWrap (JuliaLean.base.int.lit .i64 1) minValue
      let n ← ops.length values
      let counts ← ops.allocateCounts (JuliaLean.base.int.add R (JuliaLean.base.int.lit .i64 1))
      ops.setCount counts (JuliaLean.base.int.lit .i64 1) (JuliaLean.base.int.lit .i64 1)
      let _ ← forIn (← ops.range (JuliaLean.base.int.lit .i64 1) n) ⟨⟩
        (sp_body1 ops values offsets counts)
      let _ ← forIn (← ops.range (JuliaLean.base.int.lit .i64 2) (← ops.countLength counts)) ⟨⟩
        (sp_body2 ops counts)
      let permutation ← ops.allocatePermutation n
      let _ ← forIn (← ops.range (JuliaLean.base.int.lit .i64 1) n) ⟨⟩
        (sp_body3 ops values offsets counts permutation)
      pure permutation) := rfl

theorem sp_arrayRead_of (c : Array Int) (i : Int) (k : Nat) (x : Int) (hi : 1 ≤ i)
    (hk : (i - 1).toNat = k) (hc : c[k]? = some x) : arrayRead c i = .ok x := by
  unfold arrayRead
  rw [if_pos hi, hk, hc]

theorem sp_arrayWrite_of (c : Array Int) (i : Int) (k : Nat) (x : Int) (hi : 1 ≤ i)
    (hk : (i - 1).toNat = k) (hs : i ≤ (c.size : Int)) :
    arrayWrite c i x = .ok (c.set! k x) := by
  unfold arrayWrite
  rw [if_pos ⟨hi, hs⟩, hk]

end SortpermRange

/-- `sortperm_int_range(x, rangelen, minval)`, the integer fast path of `sortperm`, on any
storage obeying the `Vector{<:Integer}` laws and with `rangelen ≥ 0` (its caller `_sortperm`
passes `rangelen = maximum - minimum + 1`): when every rank `x - minval + 1` lies in
`1:rangelen`, it returns a permutation of `1:length(x)` whose values ascend and whose equal
values keep ascending source indices. -/
def SortpermIntRangeCorrect : Prop :=
  ∀ (V : Type)
      (ops : SortpermRangeOps (StateT (Array Int × Array Int) Jl) V Unit Unit)
      (values : V) (input : List I) (rangeLength minValue : I) (rank : I → Int),
    SortpermIntRangeOpsFaithful ops values input minValue rank →
    0 ≤ rangeLength.val →
    (∀ value, value ∈ input → 1 ≤ rank value ∧ rank value ≤ rangeLength.val) →
    ∃ counts permutation,
      (sortpermIntRange ops values rangeLength minValue).run (#[], #[]) =
        .ok ((), (counts, permutation)) ∧
      permutation.size = input.length ∧
      (∀ i, 1 ≤ i → i ≤ Int.ofNat input.length →
        ∃ value, arrayRead permutation i = .ok value ∧
          1 ≤ value ∧ value ≤ Int.ofNat input.length) ∧
      (∀ i j first second, 1 ≤ i → i < j → j ≤ Int.ofNat input.length →
        arrayRead permutation i = .ok first →
        arrayRead permutation j = .ok second →
        first ≠ second) ∧
      (∀ i j first second x y, 1 ≤ i → i < j → j ≤ Int.ofNat input.length →
        arrayRead permutation i = .ok first →
        arrayRead permutation j = .ok second →
        (ops.read values (JuliaLean.base.int.lit .i64 first)).run (#[], #[]) =
          .ok (x, (#[], #[])) →
        (ops.read values (JuliaLean.base.int.lit .i64 second)).run (#[], #[]) =
          .ok (y, (#[], #[])) →
        decide (rank x ≤ rank y) = true ∧
        (decide (rank x = rank y) = true → first < second))
/-- Reading a slot of the `sortperm_int_range` result gives the index placed there. -/
theorem sp_read_slot {T : Type} (rank : T → Int) (xs : List T) (P : Array Int)
    (hP : ∀ j, j < xs.length → P[sp_pos rank xs j]? = some ((j : Int) + 1))
    (i value : Int) (h1 : 1 ≤ i) (h2 : i ≤ (xs.length : Int))
    (hv : arrayRead P i = .ok value) :
    ∃ j, j < xs.length ∧ sp_pos rank xs j = (i - 1).toNat ∧ value = (j : Int) + 1 := by
  obtain ⟨j, hj, hjp⟩ := sp_pos_surj rank xs (i - 1).toNat (by omega)
  refine ⟨j, hj, hjp, ?_⟩
  have := hP j hj
  rw [hjp] at this
  unfold arrayRead at hv
  rw [if_pos h1, this] at hv
  exact (Except.ok.inj hv).symm


/-! ## `sortperm` and `sortperm!` -/

section SortpermStableSec

def permutationOrderRef {α : Type} [Inhabited α] (lt : α → α → Bool)
    (values : Array α) (left right : Int) : Bool :=
  let a := values[(left - 1).toNat]?.getD default
  let b := values[(right - 1).toNat]?.getD default
  lt a b || (!lt b a && decide (left < right))

/-- `Perm(order, v)` is a strict weak order on indices whenever `order` is one: it compares the
values and breaks ties by index. -/
theorem sp_permOrder_negTrans {α : Type} [Inhabited α] {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (values : Array α) :
    NegTransOrder (permutationOrderRef lt values) := by
  obtain ⟨hirr, htr, hneg⟩ := hnt
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simp [permutationOrderRef, hirr]
  · intro a b c hab hbc
    unfold permutationOrderRef at hab hbc ⊢
    generalize values[(a - 1).toNat]?.getD default = x at hab hbc ⊢
    generalize values[(b - 1).toNat]?.getD default = y at hab hbc ⊢
    generalize values[(c - 1).toNat]?.getD default = z at hab hbc ⊢
    have t1 := htr x y z
    have n1 := hneg x z y
    have n2 := hneg y x z
    have n3 := hneg z y x
    cases hxy : lt x y <;> cases hyx : lt y x <;> cases hyz : lt y z <;> cases hzy : lt z y <;>
      cases hxz : lt x z <;> cases hzx : lt z x <;> simp_all <;> omega
  · intro a b c hac
    unfold permutationOrderRef at hac ⊢
    generalize values[(a - 1).toNat]?.getD default = x at hac ⊢
    generalize values[(b - 1).toNat]?.getD default = y at hac ⊢
    generalize values[(c - 1).toNat]?.getD default = z at hac ⊢
    have n1 := hneg x y z
    have n2 := hneg y z x
    have n3 := hneg z x y
    cases hxy : lt x y <;> cases hyx : lt y x <;> cases hyz : lt y z <;> cases hzy : lt z y <;>
      cases hxz : lt x z <;> cases hzx : lt z x <;> simp_all <;> omega

theorem sp_indices_toNat (n : Nat) :
    (arrayIndexRange 1 n).map Int.toNat = oneBasedIndices n := by
  unfold arrayIndexRange oneBasedIndices
  rw [List.map_map, show ((n : Int) - 1 + 1).toNat = n by omega]
  apply List.map_congr_left
  intro o _
  simp only [Function.comp_apply, Int.ofNat_eq_natCast]
  omega

theorem sp_oneBased_nodup (n : Nat) : (oneBasedIndices n).Nodup := by
  unfold oneBasedIndices List.Nodup
  rw [List.pairwise_map]
  exact List.Pairwise.imp (fun h => by omega) List.nodup_range

theorem sp_mem_oneBased (n a : Nat) : a ∈ oneBasedIndices n ↔ 1 ≤ a ∧ a ≤ n := by
  unfold oneBasedIndices
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨o, ho, rfl⟩; omega
  · intro h; exact ⟨a - 1, by omega, by omega⟩

/-- A sorted index vector of `Perm(order, v)` is what `sortperm` promises. -/
theorem sp_ordered_of_sorted {α : Type} [Inhabited α] {lt : α → α → Bool}
    (values : Array α) (G : List Int)
    (hperm : List.Perm G (arrayIndexRange 1 values.size))
    (hsorted : SortedPairwise (permutationOrderRef lt values) G) :
    List.Perm (oneBasedIndices values.size) (G.map Int.toNat) ∧
      SortpermOrdered lt values.toList (G.map Int.toNat) := by
  have hpm : List.Perm (oneBasedIndices values.size) (G.map Int.toNat) := by
    rw [← sp_indices_toNat]; exact (hperm.map _).symm
  refine ⟨hpm, ?_⟩
  have hnd : (G.map Int.toNat).Nodup := hpm.nodup_iff.1 (sp_oneBased_nodup _)
  have hmem : ∀ l ∈ G, 1 ≤ l ∧ l ≤ (values.size : Int) := by
    intro l hl
    have := hperm.mem_iff.1 hl
    unfold arrayIndexRange at this
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 this
    simp at ho ⊢
    omega
  intro i j li ri lv rv hij hli hri hlv hrv
  rw [List.getElem?_map] at hli hri
  obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 hli
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hri
  have hi : i < G.length := by
    apply Classical.byContradiction; intro h; rw [List.getElem?_eq_none (by omega)] at hl; cases hl
  have hj : j < G.length := by
    apply Classical.byContradiction; intro h; rw [List.getElem?_eq_none (by omega)] at hr; cases hr
  have hGi : G[i] = l := by rw [List.getElem?_eq_getElem hi] at hl; exact Option.some.inj hl
  have hGj : G[j] = r := by rw [List.getElem?_eq_getElem hj] at hr; exact Option.some.inj hr
  have hlm := hmem l (hGi ▸ List.getElem_mem hi)
  have hrm := hmem r (hGj ▸ List.getElem_mem hj)
  have hrl : permutationOrderRef lt values r l = false := by
    have := List.pairwise_iff_getElem.1 hsorted i j hi hj hij
    rwa [hGi, hGj] at this
  have hne : l.toNat ≠ r.toNat := by
    have := List.pairwise_iff_getElem.1 hnd i j (by simpa using hi) (by simpa using hj) hij
    simpa [hGi, hGj] using this
  have hvl : values[(l - 1).toNat]?.getD default = lv := by
    rw [← Array.getElem?_toList, show (l - 1).toNat = l.toNat - 1 by omega, hlv]; rfl
  have hvr : values[(r - 1).toNat]?.getD default = rv := by
    rw [← Array.getElem?_toList, show (r - 1).toNat = r.toNat - 1 by omega, hrv]; rfl
  unfold permutationOrderRef at hrl
  rw [hvl, hvr] at hrl
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
    decide_eq_false_iff_not] at hrl
  refine ⟨hrl.1, fun heq => ?_⟩
  rcases hrl.2 with h | h
  · rw [heq.1] at h; cases h
  · omega

/-- Open obligation of the generic `_sortperm` path. Sorting `1:n` with the checked
`Perm(order, v)` comparator runs exactly like sorting with its total reference order, because the
source dispatch only compares indices it holds in the vector being sorted. -/
def SortpermGenericRunsAgree : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool) (pivot : Int → Int → Int)
      (alg : Algorithm (BracketSortTarget Int) Int) (values : Array α) (scratch : Option (Array Int)),
    NegTransOrder lt → (∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b) →
    isFullSortAlgorithm alg = true →
    sortVectorBang (sourceVectorSortOps arrayStorage defaultBracketNumerics pivot)
        (arrayIndexRange 1 values.size).toArray alg
        (arrayPermutationOrder (pureCompare lt) values) () none
        (arrayPermutationOrder (pureCompare lt) values) scratch =
      sortVectorBang (sourceVectorSortOps arrayStorage defaultBracketNumerics pivot)
        (arrayIndexRange 1 values.size).toArray alg
        (pureCompare (permutationOrderRef lt values)) () none
        (pureCompare (permutationOrderRef lt values)) scratch

/-- The generic path of `_sortperm` and `sortperm!`: sorting `1:n` by `Perm(order, v)` through
the source `_sort!` dispatch. -/
theorem sp_generic (hagree : SortpermGenericRunsAgree) {α : Type} [Inhabited α]
    (pivot : Int → Int → Int) {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (hpivot : ∀ a b, a ≤ b → a ≤ pivot a b ∧ pivot a b ≤ b)
    (alg : Algorithm (BracketSortTarget Int) Int) (hfull : isFullSortAlgorithm alg = true)
    (values : Array α) (scratch : Option (Array Int)) :
    ∃ G, sortVectorBang (sourceVectorSortOps arrayStorage defaultBracketNumerics pivot)
        (arrayIndexRange 1 values.size).toArray alg
        (arrayPermutationOrder (pureCompare lt) values) () none
        (arrayPermutationOrder (pureCompare lt) values) scratch = .ok G ∧
      List.Perm (oneBasedIndices values.size) (G.toList.map Int.toNat) ∧
      SortpermOrdered lt values.toList (G.toList.map Int.toNat) := by
  obtain ⟨G, hrun, hout⟩ := sortVectorBang_sorts (S := arrayStorage) (E := Array.toList)
    arrayStorage_laws defaultBracketNumerics pivot (sp_permOrder_negTrans hnt values) hpivot
    alg hfull (arrayIndexRange 1 values.size).toArray none scratch
  refine ⟨G, (hagree α lt pivot alg values scratch hnt hpivot hfull).trans hrun, ?_⟩
  have hout' : SortOutcome (permutationOrderRef lt values)
      (genericStable (sourceApplyInitialOptimizations alg))
      (arrayIndexRange 1 values.size).toArray.toList G.toList := hout
  exact sp_ordered_of_sorted values G.toList hout'.1 hout'.2.1

theorem sp_ite_cases {β : Type} {p : Prop} [Decidable p] {a b c : β}
    (h : (if p then a else b) = c) : (p ∧ a = c) ∨ (¬ p ∧ b = c) := by
  by_cases hp : p
  · exact Or.inl ⟨hp, by rw [if_pos hp] at h; exact h⟩
  · exact Or.inr ⟨hp, by rw [if_neg hp] at h; exact h⟩

theorem sp_foldl_min : ∀ (l : List Int) (a : Int),
    l.foldl min a ≤ a ∧ ∀ x ∈ l, l.foldl min a ≤ x
  | [], a => by simp
  | b :: l, a => by
    have ih := sp_foldl_min l (min a b)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨by omega, ?_⟩
    rintro x (rfl | hx)
    · omega
    · exact ih.2 x hx

theorem sp_foldl_max : ∀ (l : List Int) (a : Int),
    a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], a => by simp
  | b :: l, a => by
    have ih := sp_foldl_max l (max a b)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨by omega, ?_⟩
    rintro x (rfl | hx)
    · omega
    · exact ih.2 x hx


end SortpermStableSec

/-- `sortperm(v; alg, lt, rev)` and `sortperm!(ix, v; alg, lt, rev)` on a vector of length at
most `typemax(Int)`, for every algorithm that sorts on its own and every strict weak order
`lt` (when the integer fast path of `_sortperm` applies, `lt` must order the integer values
numerically, as `isless` does): both return a permutation of `1:length(v)` that lists the
values in sorted order and lists equal values by ascending index. -/
def SortpermStable : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → SortResult Bool)
      (pivot : Int → Int → Int) (integerView : Array α → SortResult (Array Int))
      (hasIntegerElements : Array α → Bool) (integerValue : α → Int)
      (values : Array α) (initial : Array Int)
      (algorithm : Algorithm (BracketSortTarget Int) Int) (scratch : Option (Array Int))
      (reverse : Option Bool),
    EffectNegTransOrder lt → initial.size = values.size → values.size ≤ IntTy.max .i64 →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    (∀ input, hasIntegerElements input = true →
      integerView input = .ok (input.map integerValue) ∧
      (∀ a b, a ∈ input.toList → b ∈ input.toList →
        lt a b = .ok (decide (integerValue a < integerValue b)))) →
    let effective := if reverse = some true then fun a b => lt b a else lt
    let topOps := arraySortpermTopOps pivot integerView hasIntegerElements
      (fun _ => reverse != some true)
    let bangOps := arraySortpermBangOps pivot
    ∃ topIndices bangIndices,
      sortpermTop topOps values algorithm lt () reverse lt scratch () = .ok topIndices ∧
      sortpermBang bangOps initial values algorithm lt () reverse lt scratch none = .ok bangIndices ∧
      List.Perm (oneBasedIndices values.size) (topIndices.toList.map Int.toNat) ∧
      EffectSortpermOrdered effective values.toList (topIndices.toList.map Int.toNat) ∧
      List.Perm (oneBasedIndices values.size) (bangIndices.toList.map Int.toNat) ∧
      EffectSortpermOrdered effective values.toList (bangIndices.toList.map Int.toNat)


section SortApprovedOpenProofs

open JuliaLean.Promotion hiding FV FTy FTy.fmt FTy.bytes FTy.f16 FTy.f32 FTy.f64
open JuliaLean.base.float JuliaLean.base.range

inductive sortEnumFrom {I α St : Type} (iter : FiniteIterator I α St) (itr : I) :
    St → List α → Prop
  | done (s : St) : iter.next itr s = none → sortEnumFrom iter itr s []
  | step (s : St) (a : α) (s' : St) (xs : List α) :
      iter.next itr s = some (a, s') → sortEnumFrom iter itr s' xs →
      sortEnumFrom iter itr s (a :: xs)

theorem sortIterYieldsFrom {I α St : Type} {iter : FiniteIterator I α St} {itr : I}
    {s : St} {xs : List α}
    (h : IterYields iter itr (iter.next itr s) xs) : sortEnumFrom iter itr s xs := by
  cases hn : iter.next itr s with
  | none =>
    cases xs with
    | nil => exact .done s hn
    | cons a rest => simp [IterYields, hn] at h
  | some p =>
    rcases p with ⟨a, s'⟩
    cases xs with
    | nil => simp [IterYields, hn] at h
    | cons x rest =>
      simp only [IterYields, hn] at h
      rcases h with ⟨heq, hrest⟩
      subst x
      exact .step s a s' rest hn (sortIterYieldsFrom hrest)

theorem sortIssortedLoopEnum {I α St : Type} (iter : FiniteIterator I α St)
    (lt : α → α → Jl Bool) (itr : I) {s : St} {xs : List α}
    (h : sortEnumFrom iter itr s xs) :
    ∀ prev, issortedLoop iter.toIteratorOps (fun (_ : Unit) => lt) () itr
      prev (iter.next itr s) = some (.ok true) ↔ AdjacentSorted lt (prev :: xs) := by
  induction h with
  | done s hnone =>
    intro prev
    simp [issortedLoop, FiniteIterator.toIteratorOps, hnone, AdjacentSorted]
  | step s a s' xs hnext htail ih =>
    intro prev
    simp only [issortedLoop, FiniteIterator.toIteratorOps, hnext]
    cases hc : lt a prev with
    | error error => simp [hc, AdjacentSorted]
    | ok result =>
      cases result with
      | false =>
        simpa [hc, AdjacentSorted, FiniteIterator.toIteratorOps] using ih a
      | true => simp [hc, AdjacentSorted]

theorem issortedAdjacent_proven : IssortedAdjacent := by
  intro I α St iter lt itr xs hyields
  unfold issorted
  cases hf : iter.first itr with
  | none =>
    cases xs with
    | nil => simp [hf, FiniteIterator.toIteratorOps, AdjacentSorted]
    | cons a rest => simp [IterYields, hf] at hyields
  | some p =>
    rcases p with ⟨a, s⟩
    have hyields' : IterYields iter itr (some (a, s)) xs := by simpa [hf] using hyields
    cases xs with
    | nil => simp [IterYields] at hyields'
    | cons first rest =>
      simp only [IterYields] at hyields'
      rcases hyields' with ⟨hfirst, hrest⟩
      subst first
      have henum := sortIterYieldsFrom hrest
      simp only [hf, FiniteIterator.toIteratorOps]
      exact sortIssortedLoopEnum iter lt itr henum a

theorem algorithmDisplayWellFormed_proven : AlgorithmDisplayWellFormed := by
  intro IO Alg Name Arg E ops text nameText smallThreshold? argumentText hlaws io hio
  refine ⟨?_, ?_⟩
  · intro algorithm columns result h
    obtain ⟨suffix, htext, hbal⟩ :=
      printAlgorithmTree_balanced_depth ops text nameText smallThreshold? argumentText hlaws
        (ops.algorithmDepth algorithm) algorithm (Nat.le_refl _) io columns result h
    rw [hio, String.empty_append] at htext
    rw [htext]
    exact hbal
  · intro algorithm result h
    unfold showAlgorithm at h
    obtain ⟨suffix, htext, hbal⟩ :=
      printAlgorithmTree_balanced_depth ops text nameText smallThreshold? argumentText hlaws
        (ops.algorithmDepth algorithm) algorithm (Nat.le_refl _) io 0 result h
    rw [hio, String.empty_append] at htext
    rw [htext]
    exact hbal

theorem sortDimsChecked_refuted : ¬ SortDimsChecked := by
  intro h
  have h0 := h Nat Int Nat Nat Nat (emptyRowsSliceLayout Int) juliaPivot intCompare 3 0
    .defaultStable none (emptyRowsSliceLayout_laws Int) intCompare_order
    juliaPivot_bounds rfl
  have hbad : ¬ (1 ≤ (0 : Int) ∧ (0 : Int) ≤ Int.ofNat 2) := by decide
  have herr := h0.2 hbad
  change Except.error (JuliaLean.base.sort.SortException.jl JlError.boundsError) =
    Except.error (JuliaLean.base.sort.SortException.jl (JlError.argumentError "dimension out of range")) at herr
  cases herr

def sentinelVectorOps : VectorOps Unit Int where
  read := fun _ i =>
    if 1 ≤ i ∧ i ≤ 255 then
      match (List.replicate 255 (0 : Int))[(i - 1).toNat]? with
      | some value => .ok value
      | none => .error (.invalidAccess i)
    else .error (.invalidAccess i)

def sentinelFirstIndex : Unit → JInt .i64 := fun _ => ⟨1, by decide⟩
def sentinelLastIndex : Unit → JInt .i64 := fun _ => ⟨255, by decide⟩
def sentinelValues : Unit → List Int := fun _ => List.replicate 255 0

def sentinelLo : JInt .u8 := ⟨1, by decide⟩
def sentinelHi : JInt .u8 := ⟨255, by decide⟩

theorem intLt_sorted_replicate (n : Nat) :
    EffectSortedValues intCompare (List.replicate n (0 : Int)) := by
  induction n with
  | zero => simp [EffectSortedValues]
  | succ n ih =>
    cases n with
    | zero => simp [EffectSortedValues]
    | succ n =>
      simp only [List.replicate_succ, EffectSortedValues]
      constructor
      · simp [intCompare, intLt]
      · exact ih

theorem sentinelVectorLaws :
    VectorReadLaws sentinelVectorOps sentinelFirstIndex sentinelLastIndex sentinelValues := by
  intro v
  cases v
  constructor
  · decide +kernel
  · intro i
    by_cases hi : (1 : Int) ≤ i ∧ i ≤ 255
    · simp only [sentinelVectorOps, sentinelFirstIndex, sentinelLastIndex, sentinelValues,
        hi, ↓reduceIte]
      cases hget : (List.replicate 255 (0 : Int))[(i - 1).toNat]? <;> rfl
    · simp only [sentinelVectorOps, sentinelFirstIndex, sentinelLastIndex, sentinelValues,
        hi, ↓reduceIte]

theorem sentinelU8SearchlastInvalid :
    searchsortedlastBounds sentinelVectorOps (fun _ a b => intCompare a b) () () 0
      sentinelLo sentinelHi = .invalidAccess 0 := by
  decide +kernel

theorem windowSearchCorrect_refuted : ¬ WindowSearchCorrect := by
  intro h
  have hsorted : EffectSortedValues intCompare (seg (sentinelValues ()) 1 255) := by
    change EffectSortedValues intCompare (seg (List.replicate 255 (0 : Int)) 1 255)
    rw [show seg (List.replicate 255 (0 : Int)) 1 255 = List.replicate 255 0 by decide +kernel]
    exact intLt_sorted_replicate 255
  have hresults := h Unit Int Unit sentinelVectorOps sentinelFirstIndex sentinelLastIndex
    sentinelValues sentinelVectorLaws (fun _ a b => intCompare a b) () () 0 .u8
    sentinelLo sentinelHi intCompare_order
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hsorted
  rcases hresults with ⟨_, ⟨last, hlast, _⟩, _⟩
  rw [sentinelU8SearchlastInvalid] at hlast
  cases hlast

theorem windowSearchInBounds_refuted : ¬ WindowSearchInBounds := by
  intro h
  have hresults := h Unit Int sentinelVectorOps sentinelFirstIndex sentinelLastIndex
    sentinelValues sentinelVectorLaws (fun a b => intCompare a b) () 0 .u8 sentinelLo sentinelHi
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  exact hresults.1.1 0 sentinelU8SearchlastInvalid

def insortedPosZero : FV .f64 := Fl.zero false
def insortedNegZero : FV .f64 := Fl.zero true
def insortedOne : FV .f64 := Fl.ofBits 0x3ff0000000000000

def insortedZeroRange : LinRange (FV .f64) JInt64 :=
  { start := insortedPosZero, stop := insortedOne,
    len := ⟨2, by decide⟩, lendiv := ⟨1, by decide⟩ }

def insortedZeroValues : List (FV .f64) := [insortedPosZero, insortedOne]

theorem insortedZeroRangeLength :
    JLength.length insortedZeroRange = .ok (jint (2 : Int)) := by
  change Except.ok (⟨2, by decide⟩ : JInt64) = Except.ok (jint (2 : Int))
  congr 1

theorem insortedZeroRangeGetindex :
    ∀ (i : Nat) (h : i < insortedZeroValues.length),
      JGetindex.getindex insortedZeroRange (jint (i + 1)) = .ok insortedZeroValues[i] := by
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by simp [insortedZeroValues] at hi; omega
  rcases hi' with h0 | h1
  · subst i
    simpa [insortedZeroValues] using
      (show JGetindex.getindex insortedZeroRange (jint (1 : Int)) = .ok insortedPosZero by
        decide +kernel)
  · subst i
    simpa [insortedZeroValues] using
      (show JGetindex.getindex insortedZeroRange (jint (2 : Int)) = .ok insortedOne by
        decide +kernel)

theorem insortedZeroRangeSorted :
    SortedValues isless_IEEEFloat insortedZeroValues := by
  change isless_IEEEFloat insortedOne insortedPosZero = false ∧
    SortedValues isless_IEEEFloat [insortedOne]
  constructor
  · decide +kernel
  · simp [SortedValues]

theorem insortedZeroRangeMembership :
    in_Real_AbstractRange insortedNegZero insortedZeroRange = .ok true := by
  decide +kernel

theorem insortedZeroVectorFalse :
    insortedVector arrayVectorOps arrayFirstIndex arrayLastIndex
      (fun (_ : Unit) (_ : Unit) (_ : Option Bool) (_ : Unit) => ())
      (fun (_ : Unit) a b => .ok (isless_IEEEFloat a b)) insortedZeroValues.toArray insortedNegZero
      () () none () = .returned false := by
  decide +kernel

theorem insortedZeroRangeContains :
    insortedRange linRangeContains insortedNegZero insortedZeroRange = .ok true := by
  decide +kernel

theorem insortedRangeAgrees_refuted : ¬ InsortedRangeAgrees := by
  intro h
  have hprop := h insortedZeroRange insortedZeroValues insortedNegZero
    insortedZeroRangeLength insortedZeroRangeGetindex insortedZeroRangeSorted
  rcases hprop with ⟨found, hvector, ⟨inRange, _⟩, hrange⟩
  rw [insortedZeroVectorFalse] at hvector
  cases hvector
  rw [insortedZeroRangeContains] at hrange
  cases hrange

def maxAxisSearchIndex : JInt .i64 := ⟨IntTy.max .i64, by decide⟩

def maxAxisSearchOps : VectorOps Unit Int where
  read := fun _ i => if i = IntTy.max .i64 then .ok 0 else .error (.invalidAccess i)

def maxAxisSearchFirst : Unit → JInt .i64 := fun _ => maxAxisSearchIndex
def maxAxisSearchLast : Unit → JInt .i64 := fun _ => maxAxisSearchIndex
def maxAxisSearchValues : Unit → List Int := fun _ => [0]

theorem maxAxisSearchReadLaws :
    VectorReadLaws maxAxisSearchOps maxAxisSearchFirst maxAxisSearchLast maxAxisSearchValues := by
  intro v
  cases v
  constructor
  · change IntTy.max .i64 = IntTy.max .i64 + 1 - 1
    omega
  · intro i
    by_cases hi : i = IntTy.max .i64
    · subst i
      simp [maxAxisSearchOps, maxAxisSearchFirst, maxAxisSearchLast,
        maxAxisSearchIndex, maxAxisSearchValues]
    · have hout : ¬ (IntTy.max .i64 ≤ i ∧ i ≤ IntTy.max .i64) := by omega
      simp [maxAxisSearchOps, maxAxisSearchFirst, maxAxisSearchLast,
        maxAxisSearchIndex, maxAxisSearchValues, hi, hout]

theorem maxAxisSearchResult :
    searchsortedKeywords maxAxisSearchOps maxAxisSearchFirst maxAxisSearchLast
      (fun (_ : Unit) (_ : Unit) (_ : Option Bool) (_ : Unit) => ())
      (fun (_ : Unit) a b => intCompare a b) () 1 () () none () =
      .returned (IntTy.min .i64, IntTy.max .i64) := by
  decide +kernel

theorem searchsortedEquivalentRange_refuted : ¬ SearchsortedEquivalentRange := by
  intro h
  have hresults := h Unit Int Unit Unit Unit maxAxisSearchOps
    maxAxisSearchFirst maxAxisSearchLast maxAxisSearchValues maxAxisSearchReadLaws
    (fun (_ : Unit) (_ : Unit) (_ : Option Bool) (_ : Unit) => ())
    (fun (_ : Unit) a b => intCompare a b) () 1 () () none ()
    intCompare_order (by simp [maxAxisSearchValues, EffectSortedValues])
  rcases hresults with ⟨first, last, hsearch, hbefore, _, _, _⟩
  rw [maxAxisSearchResult] at hsearch
  cases hsearch
  have hbad := hbefore.1
  change IntTy.max .i64 ≤ IntTy.min .i64 at hbad
  exact (by decide : ¬ IntTy.max .i64 ≤ IntTy.min .i64) hbad

theorem maxAxisFirstOrderingResult :
    searchsortedfirstOrdering maxAxisSearchOps maxAxisSearchFirst maxAxisSearchLast
      (fun (_ : Unit) a b => intCompare a b) () 1 () =
      .returned (IntTy.min .i64) := by
  decide +kernel

theorem vectorSearchCorrect_refuted : ¬ VectorSearchCorrect := by
  intro h
  have hblocks := h Unit Int maxAxisSearchOps maxAxisSearchFirst maxAxisSearchLast
    maxAxisSearchValues maxAxisSearchReadLaws
  rcases (hblocks.1 Unit (fun (_ : Unit) a b => intCompare a b) () () 1
      intCompare_order (by simp [maxAxisSearchValues, EffectSortedValues])).1 with
    ⟨first, hsearch, hpartition⟩
  rw [maxAxisFirstOrderingResult] at hsearch
  cases hsearch
  have hbad := hpartition.1
  change IntTy.max .i64 ≤ IntTy.min .i64 at hbad
  exact (by decide : ¬ IntTy.max .i64 ≤ IntTy.min .i64) hbad

theorem maxAxisInsortedResult :
    insortedVector maxAxisSearchOps maxAxisSearchFirst maxAxisSearchLast
      (fun (_ : Unit) (_ : Unit) (_ : Option Bool) (_ : Unit) => ())
      (fun (_ : Unit) a b => intCompare a b) () 1 () () none () = .returned true := by
  decide +kernel

theorem insortedVectorCorrect_refuted : ¬ InsortedVectorCorrect := by
  intro h
  have hresults := h Unit Int Unit Unit Unit maxAxisSearchOps
    maxAxisSearchFirst maxAxisSearchLast maxAxisSearchValues maxAxisSearchReadLaws
    (fun (_ : Unit) (_ : Unit) (_ : Option Bool) (_ : Unit) => ())
    (fun (_ : Unit) a b => intCompare a b) () 1 () () none ()
    intCompare_order (by simp [maxAxisSearchValues, EffectSortedValues])
  rcases hresults with ⟨found, hsearch, hequiv⟩
  rw [maxAxisInsortedResult] at hsearch
  cases hsearch
  have hbad : ∃ y, y ∈ maxAxisSearchValues () ∧
      intCompare 1 y = .ok false ∧ intCompare y 1 = .ok false := hequiv.mp rfl
  have hnot : ¬ (∃ y, y ∈ maxAxisSearchValues () ∧
      intCompare 1 y = .ok false ∧ intCompare y 1 = .ok false) := by
    simp [maxAxisSearchValues, intCompare, intLt]
  exact hnot hbad

end SortApprovedOpenProofs

namespace opusIssorted

open JuliaLean.base.sort JuliaLean.base.ordering

def goodVal {E A St : Type} : Except E (Option (A × St)) → Except (Sum E OrderingError) Bool
  | .ok _ => .ok true
  | .error e => .error (.inl e)

def badVal {E : Type} : Except OrderingError Bool → Except (Sum E OrderingError) Bool
  | .ok _ => .ok false
  | .error e => .error (.inr e)

local notation "LT" => (fun o a b => Except.mapError Sum.inr (JuliaLean.base.ordering.ordCompare o a b))

section
variable {I A K St E : Type} (iter : IteratorOps I A St E) (itr : I) (order : OrdResult A K)

theorem oiFirst : (iteratorWithOrderingErrors iter).first itr =
    (iter.first itr).mapError (Sum.inl (β := OrderingError)) := rfl

theorem oiNext (st : St) : (iteratorWithOrderingErrors iter).next itr st =
    (iter.next itr st).mapError (Sum.inl (β := OrderingError)) := rfl

def LWit (prev : A) (cur : Option (A × St)) : Except (Sum E OrderingError) Bool → Prop
  | .ok true => ∃ ys, IterPrefix iter itr (.ok cur) ys (.ok none) ∧
      OrderedPrefix order (prev :: ys)
  | .ok false => ∃ ys xs a b next, IterPrefix iter itr (.ok cur) ys next ∧
      prev :: ys = xs ++ [a, b] ∧ OrderedPrefix order (xs ++ [a]) ∧ ordCompare order b a = .ok true
  | .error (.inr e) => ∃ ys xs a b next, IterPrefix iter itr (.ok cur) ys next ∧
      prev :: ys = xs ++ [a, b] ∧ OrderedPrefix order (xs ++ [a]) ∧ ordCompare order b a = .error e
  | .error (.inl e) => ∃ ys, IterPrefix iter itr (.ok cur) ys (.error e) ∧
      OrderedPrefix order (prev :: ys)

def TWit : Except (Sum E OrderingError) Bool → Prop
  | .ok true => ∃ xs, IterPrefix iter itr (iter.first itr) xs (.ok none) ∧ OrderedPrefix order xs
  | .ok false => ∃ xs a b next, IterPrefix iter itr (iter.first itr) (xs ++ [a, b]) next ∧
      OrderedPrefix order (xs ++ [a]) ∧ ordCompare order b a = .ok true
  | .error (.inr e) => ∃ xs a b next, IterPrefix iter itr (iter.first itr) (xs ++ [a, b]) next ∧
      OrderedPrefix order (xs ++ [a]) ∧ ordCompare order b a = .error e
  | .error (.inl e) => ∃ xs, IterPrefix iter itr (iter.first itr) xs (.error e) ∧
      OrderedPrefix order xs

theorem oiNil : OrderedPrefix order ([] : List A) := by simp [OrderedPrefix, AdjacentPairs]

theorem oiSingle (a : A) : OrderedPrefix order [a] := by simp [OrderedPrefix, AdjacentPairs]

theorem oiCons (a : A) (m : List A) :
    OrderedPrefix order (a :: m) ↔
      (∀ b ∈ m.head?, ordCompare order b a = .ok false) ∧ OrderedPrefix order m := by
  cases m with
  | nil => simp [OrderedPrefix, AdjacentPairs]
  | cons b r => simp [OrderedPrefix, AdjacentPairs]

theorem oiHead2 (xs : List A) (a b : A) : (xs ++ [a, b]).head? = (xs ++ [a]).head? := by
  cases xs <;> simp

theorem oiLast2 (l : List A) (a b : A) (h : OrderedPrefix order (l ++ [a, b])) :
    ordCompare order b a = .ok false := by
  induction l with
  | nil => exact ((oiCons order a [b]).1 h).1 b (by simp)
  | cons c l ih =>
    simp only [List.cons_append] at h
    exact ih ((oiCons order c _).1 h).2

theorem oiSnoc (l : List A) (x y : A) (h : OrderedPrefix order (l ++ [x]))
    (hc : ordCompare order y x = .ok false) : OrderedPrefix order (l ++ [x, y]) := by
  induction l with
  | nil =>
    exact (oiCons order x [y]).2 ⟨fun b hb => by simp at hb; subst hb; exact hc, oiSingle order y⟩
  | cons c l ih =>
    simp only [List.cons_append] at h ⊢
    have h' := (oiCons order c _).1 h
    refine (oiCons order c _).2 ⟨?_, ih h'.2⟩
    rw [oiHead2]
    exact h'.1

theorem oiIpError {e : E} {xs : List A} {n : Except E (Option (A × St))}
    (h : IterPrefix iter itr (.error e) xs n) : xs = [] ∧ n = .error e := by
  cases h
  exact ⟨rfl, rfl⟩

theorem oiIpNone {xs : List A} {n : Except E (Option (A × St))}
    (h : IterPrefix iter itr (.ok none) xs n) : xs = [] ∧ n = .ok none := by
  cases h
  exact ⟨rfl, rfl⟩

theorem oiIpDet {s n1 n2 : Except E (Option (A × St))} {xs ys : List A}
    (h1 : IterPrefix iter itr s xs n1) (h2 : IterPrefix iter itr s ys n2)
    (hl : xs.length = ys.length) : xs = ys ∧ n1 = n2 := by
  induction h1 generalizing ys with
  | empty current =>
    cases ys with
    | nil => cases h2; exact ⟨rfl, rfl⟩
    | cons _ _ => simp at hl
  | step x st xs next h ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      cases h2 with
      | step _ _ _ _ h2' =>
        obtain ⟨h3, h4⟩ := ih h2' (by simpa using hl)
        exact ⟨by rw [h3], h4⟩

theorem oiIpAppend {s n : Except E (Option (A × St))} {xs ys : List A} {x : A} {st : St}
    (h1 : IterPrefix iter itr s xs (.ok (some (x, st))))
    (h2 : IterPrefix iter itr (iter.next itr st) ys n) :
    IterPrefix iter itr s (xs ++ x :: ys) n := by
  generalize hm : (Except.ok (some (x, st)) : Except E (Option (A × St))) = m at h1
  induction h1 with
  | empty current => subst hm; exact .step x st ys n h2
  | step y st' zs next _ ih => exact .step y st' (zs ++ x :: ys) n (ih hm)

theorem oiIpSplit {s n : Except E (Option (A × St))} (l1 l2 : List A)
    (h : IterPrefix iter itr s (l1 ++ l2) n) :
    ∃ m, IterPrefix iter itr s l1 m ∧ IterPrefix iter itr m l2 n := by
  induction l1 generalizing s with
  | nil => exact ⟨s, .empty s, h⟩
  | cons x l1 ih =>
    rw [List.cons_append] at h
    cases h with
    | step _ st _ _ h' =>
      obtain ⟨m, hm1, hm2⟩ := ih h'
      exact ⟨m, .step x st l1 m hm1, hm2⟩

theorem oiLift (prev y : A) (st : St) (nx : Option (A × St))
    (v : Except (Sum E OrderingError) Bool)
    (hc : ordCompare order y prev = .ok false) (hn : iter.next itr st = .ok nx)
    (hw : LWit iter itr order y nx v) : LWit iter itr order prev (some (y, st)) v := by
  have hstep : ∀ {ys : List A} {n : Except E (Option (A × St))},
      IterPrefix iter itr (.ok nx) ys n → IterPrefix iter itr (.ok (some (y, st))) (y :: ys) n :=
    fun h => .step y st _ _ (by rw [hn]; exact h)
  have hord : ∀ {ys : List A}, OrderedPrefix order (y :: ys) →
      OrderedPrefix order (prev :: y :: ys) :=
    fun h => (oiCons order prev _).2 ⟨fun b hb => by simp at hb; subst hb; exact hc, h⟩
  have hbad : ∀ {xs : List A} {a b : A} {ys : List A}, y :: ys = xs ++ [a, b] →
      OrderedPrefix order (xs ++ [a]) → OrderedPrefix order ((prev :: xs) ++ [a]) := by
    intro xs a b ys h2 h3
    have hh : (xs ++ [a]).head? = some y := by rw [← oiHead2, ← h2]; rfl
    rw [List.cons_append]
    exact (oiCons order prev _).2 ⟨fun b' hb => by rw [hh] at hb; simp at hb; subst hb; exact hc, h3⟩
  rcases v with ((e | e) | (_ | _)) <;> simp only [LWit] at hw ⊢
  · obtain ⟨ys, h1, h2⟩ := hw
    exact ⟨y :: ys, hstep h1, hord h2⟩
  · obtain ⟨ys, xs, a, b, nxt, h1, h2, h3, h4⟩ := hw
    exact ⟨y :: ys, prev :: xs, a, b, nxt, hstep h1, by rw [h2]; rfl, hbad h2 h3, h4⟩
  · obtain ⟨ys, xs, a, b, nxt, h1, h2, h3, h4⟩ := hw
    exact ⟨y :: ys, prev :: xs, a, b, nxt, hstep h1, by rw [h2]; rfl, hbad h2 h3, h4⟩
  · obtain ⟨ys, h1, h2⟩ := hw
    exact ⟨y :: ys, hstep h1, hord h2⟩

theorem oiComplete :
    ∀ (prev : A) (cur : Option (A × St)) (v : Except (Sum E OrderingError) Bool),
      issortedLoop (iteratorWithOrderingErrors iter) LT order itr prev cur = some v →
      LWit iter itr order prev cur v := by
  refine issortedLoop.fixpoint_induct (iteratorWithOrderingErrors iter) LT order itr
    (fun f => ∀ prev cur v, f prev cur = some v → LWit iter itr order prev cur v) ?_ ?_
  · exact Lean.Order.admissible_pi_apply
      (P := fun (prev : A) (g : Option (A × St) → Option (Except (Sum E OrderingError) Bool)) =>
        ∀ cur v, g cur = some v → LWit iter itr order prev cur v)
      (fun prev => Lean.Order.admissible_pi_apply
        (P := fun cur o => ∀ v, o = some v → LWit iter itr order prev cur v)
        (fun cur => Lean.Order.admissible_pi
          (P := fun o v => o = some v → LWit iter itr order prev cur v)
          (fun v => Lean.Order.Option.admissible_eq_some _ v)))
  · intro f ih prev cur v h
    cases cur with
    | none =>
      dsimp only at h
      cases h
      simp only [LWit]
      exact ⟨[], .empty _, oiSingle order prev⟩
    | some p =>
      obtain ⟨y, st⟩ := p
      dsimp only at h
      cases hc : ordCompare order y prev with
      | error e =>
        simp only [hc, Except.mapError] at h
        cases h
        simp only [LWit]
        exact ⟨[y], [], prev, y, iter.next itr st, .step y st [] _ (.empty _), rfl,
          oiSingle order prev, hc⟩
      | ok b =>
        cases b with
        | true =>
          simp only [hc, Except.mapError] at h
          cases h
          simp only [LWit]
          exact ⟨[y], [], prev, y, iter.next itr st, .step y st [] _ (.empty _), rfl,
            oiSingle order prev, hc⟩
        | false =>
          simp only [hc, Except.mapError, oiNext] at h
          cases hn : iter.next itr st with
          | error e =>
            simp only [hn, Except.mapError] at h
            cases h
            simp only [LWit]
            exact ⟨[y], .step y st [] _ (by rw [hn]; exact .empty _),
              (oiCons order prev [y]).2
                ⟨fun b hb => by simp at hb; subst hb; exact hc, oiSingle order y⟩⟩
          | ok nx =>
            simp only [hn, Except.mapError] at h
            exact oiLift iter itr order prev y st nx v hc hn (ih y nx v h)

theorem oiGood (ys : List A) : ∀ (prev : A) (cur : Option (A × St))
    (n : Except E (Option (A × St))),
    IterPrefix iter itr (.ok cur) ys n → OrderedPrefix order (prev :: ys) →
    (∀ p, n ≠ .ok (some p)) →
    issortedLoop (iteratorWithOrderingErrors iter) LT order itr prev cur = some (goodVal n) := by
  induction ys with
  | nil =>
    intro prev cur n h _ hn
    cases h
    cases cur with
    | none => simp [issortedLoop, goodVal]
    | some p => exact (hn p rfl).elim
  | cons y ys ih =>
    intro prev cur n h ho hn
    cases h with
    | step _ st _ _ h' =>
      have ho' := (oiCons order prev (y :: ys)).1 ho
      have hc : ordCompare order y prev = .ok false := ho'.1 y (by simp)
      cases hn2 : iter.next itr st with
      | error e =>
        rw [hn2] at h'
        obtain ⟨rfl, rfl⟩ := oiIpError iter itr h'
        simp [issortedLoop, hc, hn2, Except.mapError, oiNext, goodVal]
      | ok c =>
        rw [hn2] at h'
        simp only [issortedLoop, hc, hn2, Except.mapError, oiNext]
        exact ih y c n h' ho'.2 hn

theorem oiBad (xs : List A) (a b : A) (r : Except OrderingError Bool) (hr : r ≠ .ok false)
    (hab : ordCompare order b a = r) :
    ∀ (prev : A) (cur : Option (A × St)) (ys : List A) (nx : Except E (Option (A × St))),
      prev :: ys = xs ++ [a, b] → IterPrefix iter itr (.ok cur) ys nx →
      OrderedPrefix order (xs ++ [a]) →
      issortedLoop (iteratorWithOrderingErrors iter) LT order itr prev cur = some (badVal r) := by
  induction xs with
  | nil =>
    intro prev cur ys nx he h _
    simp only [List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    cases h with
    | step _ st _ _ _ =>
      cases r with
      | error e => simp [issortedLoop, hab, Except.mapError, badVal]
      | ok bb =>
        cases bb with
        | false => exact (hr rfl).elim
        | true => simp [issortedLoop, hab, Except.mapError, badVal]
  | cons x xs ih =>
    intro prev cur ys nx he h ho
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨y, t, hyt⟩ : ∃ y t, xs ++ [a] = y :: t := by
      cases xs with
      | nil => exact ⟨a, [], rfl⟩
      | cons z zs => exact ⟨z, zs ++ [a], rfl⟩
    have hys : xs ++ [a, b] = y :: (t ++ [b]) := by
      simpa using congrArg (· ++ [b]) hyt
    rw [hys] at h
    cases h with
    | step _ st _ _ h' =>
      rw [List.cons_append, hyt] at ho
      have ho' := (oiCons order _ _).1 ho
      have hc := ho'.1 y (by simp)
      cases hn2 : iter.next itr st with
      | error e =>
        rw [hn2] at h'
        have := (oiIpError iter itr h').1
        simp at this
      | ok c =>
        rw [hn2] at h'
        simp only [issortedLoop, hc, hn2, Except.mapError, oiNext]
        exact ih y c (t ++ [b]) nx hys.symm h' (by rw [hyt]; exact ho'.2)

theorem oiTopGood (xs : List A) (n : Except E (Option (A × St)))
    (h1 : IterPrefix iter itr (iter.first itr) xs n) (h2 : OrderedPrefix order xs)
    (hn : ∀ p, n ≠ .ok (some p)) :
    issorted (iteratorWithOrderingErrors iter) LT order itr = some (goodVal n) := by
  cases hf : iter.first itr with
  | error e =>
    rw [hf] at h1
    obtain ⟨rfl, rfl⟩ := oiIpError iter itr h1
    simp [issorted, oiFirst, hf, Except.mapError, goodVal]
  | ok o =>
    rw [hf] at h1
    cases o with
    | none =>
      obtain ⟨rfl, rfl⟩ := oiIpNone iter itr h1
      simp [issorted, oiFirst, hf, Except.mapError, goodVal]
    | some p =>
      obtain ⟨x, st⟩ := p
      cases h1 with
      | empty => exact (hn _ rfl).elim
      | step _ _ ys _ h' =>
        cases hn2 : iter.next itr st with
        | error e =>
          rw [hn2] at h'
          obtain ⟨rfl, rfl⟩ := oiIpError iter itr h'
          simp [issorted, oiFirst, oiNext, hf, hn2, Except.mapError, goodVal]
        | ok c =>
          rw [hn2] at h'
          simp only [issorted, oiFirst, oiNext, hf, hn2, Except.mapError]
          exact oiGood iter itr order ys x c n h' h2 hn

theorem oiTopBad (xs : List A) (a b : A) (nx : Except E (Option (A × St)))
    (r : Except OrderingError Bool) (hr : r ≠ .ok false) (hab : ordCompare order b a = r)
    (h1 : IterPrefix iter itr (iter.first itr) (xs ++ [a, b]) nx)
    (h2 : OrderedPrefix order (xs ++ [a])) :
    issorted (iteratorWithOrderingErrors iter) LT order itr = some (badVal r) := by
  cases hf : iter.first itr with
  | error e =>
    rw [hf] at h1
    have := (oiIpError iter itr h1).1
    simp at this
  | ok o =>
    rw [hf] at h1
    cases o with
    | none =>
      have := (oiIpNone iter itr h1).1
      simp at this
    | some p =>
      obtain ⟨x, st⟩ := p
      generalize hL : xs ++ [a, b] = L at h1
      cases h1 with
      | empty => simp at hL
      | step _ _ ys _ h' =>
        cases hn2 : iter.next itr st with
        | error e =>
          rw [hn2] at h'
          have := congrArg List.length hL
          rw [(oiIpError iter itr h').1] at this
          simp at this <;> omega
        | ok c =>
          rw [hn2] at h'
          simp only [issorted, oiFirst, oiNext, hf, hn2, Except.mapError]
          exact oiBad iter itr order xs a b r hr hab x c ys nx hL.symm h' h2

theorem oiTopComplete (v : Except (Sum E OrderingError) Bool)
    (h : issorted (iteratorWithOrderingErrors iter) LT order itr = some v) :
    TWit iter itr order v := by
  simp only [issorted, oiFirst] at h
  cases hf : iter.first itr with
  | error e =>
    simp only [hf, Except.mapError] at h
    cases h
    simp only [TWit]
    exact ⟨[], by rw [hf]; exact .empty _, oiNil order⟩
  | ok o =>
    cases o with
    | none =>
      simp only [hf, Except.mapError] at h
      cases h
      simp only [TWit]
      exact ⟨[], by rw [hf]; exact .empty _, oiNil order⟩
    | some p =>
      obtain ⟨x, st⟩ := p
      simp only [hf, Except.mapError, oiNext] at h
      cases hn : iter.next itr st with
      | error e =>
        simp only [hn, Except.mapError] at h
        cases h
        simp only [TWit]
        exact ⟨[x], by rw [hf]; exact .step x st [] _ (by rw [hn]; exact .empty _),
          oiSingle order x⟩
      | ok c =>
        simp only [hn, Except.mapError] at h
        have hw := oiComplete iter itr order x c v h
        have hfx : ∀ {ys : List A} {n : Except E (Option (A × St))},
            IterPrefix iter itr (.ok c) ys n →
            IterPrefix iter itr (iter.first itr) (x :: ys) n := fun h' => by
          rw [hf]; exact .step x st _ _ (by rw [hn]; exact h')
        rcases v with ((e | e) | (_ | _)) <;> simp only [LWit] at hw <;> simp only [TWit]
        · obtain ⟨ys, h1, h2⟩ := hw
          exact ⟨x :: ys, hfx h1, h2⟩
        · obtain ⟨ys, xs, a, b, nxt, h1, h2, h3, h4⟩ := hw
          exact ⟨xs, a, b, nxt, by rw [← h2]; exact hfx h1, h3, h4⟩
        · obtain ⟨ys, xs, a, b, nxt, h1, h2, h3, h4⟩ := hw
          exact ⟨xs, a, b, nxt, by rw [← h2]; exact hfx h1, h3, h4⟩
        · obtain ⟨ys, h1, h2⟩ := hw
          exact ⟨x :: ys, hfx h1, h2⟩

theorem oiBadNotInf (xs : List A) (a b : A) (nx : Except E (Option (A × St)))
    (h1 : IterPrefix iter itr (iter.first itr) (xs ++ [a, b]) nx)
    (hinf : ∀ n : Nat, ∃ xs x state, xs.length = n ∧
      IterPrefix iter itr (iter.first itr) xs (.ok (some (x, state))) ∧
      OrderedPrefix order (xs ++ [x])) :
    ordCompare order b a = .ok false := by
  obtain ⟨ys, x, st, hl, hp, ho⟩ := hinf (xs.length + 1)
  obtain ⟨m, hm1, hm2⟩ := oiIpSplit iter itr (xs ++ [a]) [b]
    (by rw [List.append_assoc]; exact h1)
  cases hm2 with
  | step _ st2 _ _ _ =>
    obtain ⟨hd1, hd2⟩ := oiIpDet iter itr hm1 hp (by simp [hl])
    cases hd2
    subst hd1
    simp only [List.append_assoc, List.singleton_append] at ho
    exact oiLast2 order xs a _ ho

theorem oiOutcome : IteratorOutcome iter itr order
    (issorted (iteratorWithOrderingErrors iter) LT order itr) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, fun e => ⟨?_, ?_⟩, fun e => ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    simpa only [TWit] using oiTopComplete iter itr order _ h
  · rintro ⟨xs, h1, h2⟩
    exact oiTopGood iter itr order xs _ h1 h2 (by intro p hq; cases hq)
  · intro h
    simpa only [TWit] using oiTopComplete iter itr order _ h
  · rintro ⟨xs, a, b, nx, h1, h2, h3⟩
    exact oiTopBad iter itr order xs a b nx (.ok true) (by intro hq; cases hq) h3 h1 h2
  · intro h
    simpa only [TWit] using oiTopComplete iter itr order _ h
  · rintro ⟨xs, a, b, nx, h1, h2, h3⟩
    exact oiTopBad iter itr order xs a b nx (.error e) (by intro hq; cases hq) h3 h1 h2
  · intro h
    simpa only [TWit] using oiTopComplete iter itr order _ h
  · rintro ⟨xs, h1, h2⟩
    exact oiTopGood iter itr order xs _ h1 h2 (by intro p hq; cases hq)
  · intro h n
    induction n with
    | zero =>
      cases hf : iter.first itr with
      | error e =>
        have := oiTopGood iter itr order [] (.error e) (by rw [hf]; exact .empty _)
          (oiNil order) (by intro p hq; cases hq)
        rw [h] at this
        cases this
      | ok o =>
        cases o with
        | none =>
          have := oiTopGood iter itr order [] (.ok none) (by rw [hf]; exact .empty _)
            (oiNil order) (by intro p hq; cases hq)
          rw [h] at this
          cases this
        | some p =>
          obtain ⟨x, st⟩ := p
          exact ⟨[], x, st, rfl, .empty _, oiSingle order x⟩
    | succ n ih =>
      obtain ⟨xs, x, st, hl, hp, ho⟩ := ih
      cases hn : iter.next itr st with
      | error e =>
        have := oiTopGood iter itr order (xs ++ [x]) (.error e)
          (oiIpAppend iter itr hp (by rw [hn]; exact .empty _)) ho (by intro p hq; cases hq)
        rw [h] at this
        cases this
      | ok o =>
        cases o with
        | none =>
          have := oiTopGood iter itr order (xs ++ [x]) (.ok none)
            (oiIpAppend iter itr hp (by rw [hn]; exact .empty _)) ho (by intro p hq; cases hq)
          rw [h] at this
          cases this
        | some q =>
          obtain ⟨y, st'⟩ := q
          have hp2 : IterPrefix iter itr (iter.first itr) (xs ++ [x, y]) (iter.next itr st') :=
            oiIpAppend iter itr hp (by rw [hn]; exact .step y st' [] _ (.empty _))
          cases hc : ordCompare order y x with
          | error e =>
            have := oiTopBad iter itr order xs x y _ (.error e) (by intro hq; cases hq) hc hp2 ho
            rw [h] at this
            cases this
          | ok bb =>
            cases bb with
            | true =>
              have := oiTopBad iter itr order xs x y _ (.ok true) (by intro hq; cases hq) hc hp2 ho
              rw [h] at this
              cases this
            | false =>
              exact ⟨xs ++ [x], y, st', by simp [hl],
                oiIpAppend iter itr hp (by rw [hn]; exact .empty _),
                by rw [List.append_assoc]; exact oiSnoc order xs x y ho hc⟩
  · intro hinf
    cases hr : issorted (iteratorWithOrderingErrors iter) LT order itr with
    | none => rfl
    | some v =>
      exfalso
      have hw := oiTopComplete iter itr order v hr
      rcases v with ((e | e) | (_ | _)) <;> simp only [TWit] at hw
      · obtain ⟨xs, h1, _⟩ := hw
        obtain ⟨ys, x, st, hl, hp, _⟩ := hinf xs.length
        cases (oiIpDet iter itr h1 hp hl.symm).2
      · obtain ⟨xs, a, b, nx, h1, _, h3⟩ := hw
        have := oiBadNotInf iter itr order xs a b nx h1 hinf
        rw [h3] at this
        cases this
      · obtain ⟨xs, a, b, nx, h1, _, h3⟩ := hw
        have := oiBadNotInf iter itr order xs a b nx h1 hinf
        rw [h3] at this
        cases this
      · obtain ⟨xs, h1, _⟩ := hw
        obtain ⟨ys, x, st, hl, hp, _⟩ := hinf xs.length
        cases (oiIpDet iter itr h1 hp hl.symm).2

end

theorem issortedKeywordsCorrect_proven : IssortedKeywordsCorrect := by
  intro I A K St E iter itr less byArg rev order
  unfold issortedKeywords
  cases hR : (if rev = some true then JuliaLean.base.ordering.ordBool less byArg true order
      else JuliaLean.base.ordering.ordNothing less byArg () order) with
  | error e => exact rfl
  | ok resolved => exact oiOutcome iter itr resolved

end opusIssorted
namespace Round17

open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort
open JuliaLean.base.abstractdict

/-- Empty ranges return the insertion bounds described by the public search contract.
Julia source: base/sort.jl:243-302 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/sort.jl:314-321,351-360,390-398 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
-/
def RangeSearchEmptyCorrect : Prop :=
  (∀ (t : IntTy) (f h l : JInt t) (len : JInt64) (x : RealRangeQuery) (rev : Bool),
    RangeValid f h l len → RealQueryValid x → len.val = 0 →
    RangeAnswersReal f h l len x rev) ∧
  (∀ (A R X Q O : Type) (ops : RealRangeOps A R X Q Int O JlError)
      (lt : O → X → R → Jl Bool) (ltRange : O → R → X → Jl Bool)
      (order : O) (a : A) (x : X) (rangeValue : R → R → Nat → R)
      (emptyLast : R → R → R) (isZeroValue : R → Bool)
      (finiteValue : R → Bool) (finiteQuery : X → Bool)
      (finiteQuotient : Q → Bool),
    RealRangeOpsFaithful ops a x [] rangeValue emptyLast isZeroValue
      finiteValue finiteQuery finiteQuotient →
    RealRangeSearchPredicatesSorted [] lt ltRange order x →
    ∃ first last,
      searchsortedfirstRealRange ops ltRange order a x = .ok first ∧
      searchsortedlastRealRange ops lt order a x = .ok last ∧
      searchsortedRealRange ops lt ltRange order a x (fun f l => (f, l)) =
        .ok (first, last) ∧
      FirstContract 0
        (fun i => comparisonTrue (fun value query => ltRange order value query)
          (rangeValue (ops.first a) (ops.step a) ((i - 1).toNat)) x) first ∧
      LastContract 0
        (fun i => comparisonFalse (lt order) x
          (rangeValue (ops.first a) (ops.step a) ((i - 1).toNat)) ) last)

/-- The public legacy QuickSort overload with a vector scratch sorts every valid one-based window
as a sorted permutation and leaves its exterior unchanged.
Julia source: base/sort.jl:2409-2478,2570-2582 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: doc/src/base/sort.md:141-146
-/
def LegacyQuickSortScratchCorrect : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → SortResult Bool) (values : Array α)
      (lo hi : Int) (scratch : Array α),
    EffectNegTransOrder lt → 1 ≤ lo → lo ≤ hi + 1 → hi ≤ (values.size : Int) →
    ∃ result,
      legacySortWithScratch (storageLegacyOps arrayStorage lt)
        values lo hi .quick () scratch = .ok result ∧
      EffectWindowOutcome lt false values.toList result.toList lo hi

def keySetCollectedSortOps {T D K V : Type} [Inhabited K]
    (dictOps : DictOps T D K V) (numeric : BracketNumerics)
    (pivot : Int → Int → Int) (algorithm : Algorithm (BracketSortTarget Int) Int)
    (lt : K → K → SortResult Bool) (reverse : Option Bool) :
    SortCollectOps (KeySet K D) (Array K) JuliaLean.base.sort.SortException (Option (Array K)) where
  collect := fun collection =>
    .ok ((iterPartAll dictOps .keys collection.dict).toArray)
  sortBang := fun values selectedScratch =>
    sortVectorBang (sourceVectorSortOps arrayStorage numeric pivot)
      values algorithm lt () reverse lt selectedScratch

def valueIteratorCollectedSortOps {T D K V : Type} [Inhabited V]
    (dictOps : DictOps T D K V) (numeric : BracketNumerics)
    (pivot : Int → Int → Int) (algorithm : Algorithm (BracketSortTarget Int) Int)
    (lt : V → V → SortResult Bool) (reverse : Option Bool) :
    SortCollectOps (ValueIterator D) (Array V) JuliaLean.base.sort.SortException (Option (Array V)) where
  collect := fun collection =>
    .ok ((iterPartAll dictOps .vals collection.dict).toArray)
  sortBang := fun values selectedScratch =>
    sortVectorBang (sourceVectorSortOps arrayStorage numeric pivot)
      values algorithm lt () reverse lt selectedScratch

/-- Sorting a key set or value iterator collects its source iteration sequence and applies the
installed vector sorter, preserving the selected algorithm's stability promise.
Julia source: base/sort.jl:1782-1783 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia source: base/abstractdict.jl:65-69, base/array.jl:777-786
-/
def CollectedSortCorrect : Prop :=
  (∀ (T D K V : Type) [Inhabited K] (dictOps : DictOps T D K V) (dict : D)
      (numeric : BracketNumerics) (pivot : Int → Int → Int)
      (lt : K → K → SortResult Bool) (algorithm : Algorithm (BracketSortTarget Int) Int)
      (reverse : Option Bool) (scratch : Option (Array K)),
    EffectNegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    let values := iterPartAll dictOps .keys dict
    let effective := if reverse = some true then fun a b => lt b a else lt
    ∃ result,
      sortCollected
        (keySetCollectedSortOps dictOps numeric pivot algorithm lt reverse)
        (keysAD dict) scratch = .ok result ∧
      List.Perm values result.toList ∧
      EffectSortedValues effective result.toList ∧
      (genericStable (sourceApplyInitialOptimizations algorithm) = true →
        EffectStableWrt effective values result.toList)) ∧
  (∀ (T D K V : Type) [Inhabited V] (dictOps : DictOps T D K V) (dict : D)
      (numeric : BracketNumerics) (pivot : Int → Int → Int)
      (lt : V → V → SortResult Bool) (algorithm : Algorithm (BracketSortTarget Int) Int)
      (reverse : Option Bool) (scratch : Option (Array V)),
    EffectNegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    let values := iterPartAll dictOps .vals dict
    let effective := if reverse = some true then fun a b => lt b a else lt
    ∃ result,
      sortCollected
        (valueIteratorCollectedSortOps dictOps numeric pivot algorithm lt reverse)
        (valuesAD dict) scratch = .ok result ∧
      List.Perm values result.toList ∧
      EffectSortedValues effective result.toList ∧
      (genericStable (sourceApplyInitialOptimizations algorithm) = true →
        EffectStableWrt effective values result.toList))

end Round17

namespace JuliaLean.ChatGPT.Batch2.Group4

open JuliaLean JuliaLean.base.sort JuliaLean.base.abstractdict
open JuliaLean.Proofs.base.sort JuliaLean.Proofs.base.sort.Round17

/-- The installed collected-sort contract. The target manifest names a different,
absent declaration; this helper proves the actual statement in `Round17`. -/
theorem round17CollectedSortCorrect :
    JuliaLean.Proofs.base.sort.Round17.CollectedSortCorrect := by
  constructor
  · intro T D K V _ dictOps dict numeric pivot lt algorithm reverse scratch hnt hpivot hfull
    obtain ⟨p, hp, rfl⟩ := effect_pure_cases hnt
    obtain ⟨result, hrun, hout⟩ := sortVectorBang_sorts
      (α := K) arrayStorage_laws numeric pivot hp hpivot algorithm hfull
      (iterPartAll dictOps .keys dict).toArray reverse scratch
    have hnte := negTransOrder_effective hp reverse
    have heffective :
        (if reverse = some true then
            fun a b => pureCompare (ε := SortException) p b a
          else pureCompare (ε := SortException) p) =
          pureCompare (ε := SortException)
            (if reverse = some true then fun a b => p b a else p) := by
      rw [pureCompare_swap, pureCompare_ite]
    refine ⟨result, ?_, ?_, ?_, ?_⟩
    · simpa only [sortCollected, keySetCollectedSortOps, keysAD, bind,
        Except.bind, pure, Except.pure, heffective] using hrun
    · simpa only [List.toList_toArray, Part.Elem] using hout.1.symm
    · rw [heffective]
      exact (effectSortedValues_pure _ _).2 ((sortedValues_iff_pairwise hnte _).2 hout.2.1)
    · rw [heffective]
      intro hstable
      exact (effectStableWrt_pure _ _ _).2 (hout.2.2 hstable)
  · intro T D K V _ dictOps dict numeric pivot lt algorithm reverse scratch hnt hpivot hfull
    obtain ⟨p, hp, rfl⟩ := effect_pure_cases hnt
    obtain ⟨result, hrun, hout⟩ := sortVectorBang_sorts
      (α := V) arrayStorage_laws numeric pivot hp hpivot algorithm hfull
      (iterPartAll dictOps .vals dict).toArray reverse scratch
    have hnte := negTransOrder_effective hp reverse
    have heffective :
        (if reverse = some true then
            fun a b => pureCompare (ε := SortException) p b a
          else pureCompare (ε := SortException) p) =
          pureCompare (ε := SortException)
            (if reverse = some true then fun a b => p b a else p) := by
      rw [pureCompare_swap, pureCompare_ite]
    refine ⟨result, ?_, ?_, ?_, ?_⟩
    · simpa only [sortCollected, valueIteratorCollectedSortOps, valuesAD, bind,
        Except.bind, pure, Except.pure, heffective] using hrun
    · simpa only [List.toList_toArray, Part.Elem] using hout.1.symm
    · rw [heffective]
      exact (effectSortedValues_pure _ _).2 ((sortedValues_iff_pairwise hnte _).2 hout.2.1)
    · rw [heffective]
      intro hstable
      exact (effectStableWrt_pure _ _ _).2 (hout.2.2 hstable)

end JuliaLean.ChatGPT.Batch2.Group4


namespace JuliaLean.ChatGPT.Batch2.Group4

open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

theorem emptyReverseRangeFirst :
    searchsortedfirstIntegerRange (bitIntegerRealRangeOps .i64) (fun o a b => .ok (realQueryLtRange o a b)) true
      (JInt.wrap .i64 1, JInt.wrap .i64 1, JInt.wrap .i64 0, JInt.wrap .i64 0)
      { floor := 0, ceil := 0 } = .ok (JInt.wrap .i64 0) := by
  decide

theorem round17RangeSearchEmptyRefuted :
    ¬ JuliaLean.Proofs.base.sort.Round17.RangeSearchEmptyCorrect := by
  intro h
  have hv : RangeValid (JInt.wrap .i64 1) (JInt.wrap .i64 1)
      (JInt.wrap .i64 0) (JInt.wrap .i64 0) := by
    unfold RangeValid
    decide
  have hq : RealQueryValid { floor := 0, ceil := 0 } := by
    unfold RealQueryValid
    decide
  obtain ⟨first, last, hf, _, _, hc, _⟩ :=
    h.1 .i64 (JInt.wrap .i64 1) (JInt.wrap .i64 1)
      (JInt.wrap .i64 0) (JInt.wrap .i64 0) { floor := 0, ceil := 0 } true
      hv hq (by decide)
  rw [emptyReverseRangeFirst] at hf
  have he : first = JInt.wrap .i64 0 := (Except.ok.inj hf).symm
  have hb := hc.1
  rw [he] at hb
  exact (by decide : ¬ ((1 : Int) ≤ (JInt.wrap .i64 0).val)) hb

theorem legacyScratchSingleError :
    legacySortWithScratch (storageLegacyOps arrayStorage (fun a b : Int => .ok (decide (a < b))))
      #[1] 1 1 .quick () #[] =
      .error (.jl (.argumentError "Base.Sort._sort! is not defined for this algorithm")) := by
  rfl

theorem round17LegacyQuickSortScratchRefuted :
    ¬ JuliaLean.Proofs.base.sort.Round17.LegacyQuickSortScratchCorrect := by
  intro h
  obtain ⟨result, hr, _⟩ := h Int intCompare #[1]
    1 1 #[] intCompare_order (by decide) (by decide) (by decide)
  have herr : legacySortWithScratch (storageLegacyOps arrayStorage intCompare)
      #[1] 1 1 .quick () #[] =
      .error (.jl (.argumentError "Base.Sort._sort! is not defined for this algorithm")) := rfl
  rw [herr] at hr
  cases hr

end JuliaLean.ChatGPT.Batch2.Group4
end JuliaLean.Proofs.base.sort


namespace JuliaLean.ChatGPT.Batch4.Group20

open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort


theorem group20ArrayReadSet (α : Type) (values : Array α) (index : Int) (value : α)
    (h1 : 1 ≤ index) (h2 : index ≤ values.size) :
    arrayRead (values.set! (index - 1).toNat value) index = .ok value := by
  have hi : (index - 1).toNat < values.size := by omega
  simp only [arrayRead, h1, ↓reduceIte]
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hi]

theorem group20ArrayReadSetOther (α : Type) (values : Array α) (index other : Int)
    (value : α) (hne : other ≠ index) (h1 : 1 ≤ index) :
    arrayRead (values.set! (index - 1).toNat value) other = arrayRead values other := by
  unfold arrayRead
  by_cases ho : 1 ≤ other
  · rw [if_pos ho, if_pos ho]
    have hnat : (other - 1).toNat ≠ (index - 1).toNat := by omega
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne hnat.symm]
  · rw [if_neg ho, if_neg ho]

theorem SorttuplescovWithoutMissing_proven : JuliaLean.Proofs.base.sort.WithoutMissingVectorCorrect := by
  intro α values
  constructor
  · intro wrapped hwrap
    have hn : values.any Option.isNone = false := by
      cases h : values.any Option.isNone with
      | false => rfl
      | true =>
        simp only [withoutMissingVector, Bool.not_false, ↓reduceIte, h,
          bind, Except.bind, pure, Except.pure, reduceCtorEq] at hwrap
    have hw : wrapped = ⟨values⟩ := by
      simpa only [withoutMissingVector, Bool.not_false, ↓reduceIte, hn,
        Bool.false_eq_true, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] using hwrap.symm
    subst wrapped
    refine ⟨hn, rfl, rfl, ?_⟩
    intro index h1 h2
    have hi : (index - 1).toNat < values.size := by omega
    have hsome : ∃ a, values[(index - 1).toNat] = some a := by
      have hno := (Array.any_eq_false.mp hn) (index - 1).toNat hi
      cases he : values[(index - 1).toNat] with
      | none => exact False.elim (hno (by rw [he]; rfl))
      | some a => exact ⟨a, rfl⟩
    obtain ⟨a, ha⟩ := hsome
    have hr : arrayRead values index = .ok (some a) := by
      simp only [arrayRead, h1, ↓reduceIte, Array.getElem?_eq_getElem hi, ha]
    refine ⟨a, ?_, hr⟩
    simp only [withoutMissingGet, hr, bind, Except.bind, pure, Except.pure]
  · intro wrapped index value h1 h2
    refine ⟨⟨wrapped.data.set! (index - 1).toNat value⟩, ?_, ?_, ?_, ?_⟩
    · simp only [withoutMissingSet, arrayWrite, h1, h2, and_self, ↓reduceIte,
        bind, Except.bind, pure, Except.pure]
    · exact Array.size_set! _ _ _
    · exact group20ArrayReadSet _ _ _ _ h1 h2
    · intro other hne
      exact group20ArrayReadSetOther _ _ _ _ _ hne h1

theorem SortAlgorithmPolicyDispatch_proven : JuliaLean.Proofs.base.sort.AlgorithmPolicyDispatchCorrect := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α _ lt threshold values hnt
    obtain ⟨p, hporder, rfl⟩ := effect_pure_cases hnt
    obtain ⟨result, hr, hp, hs⟩ := arrayInsertion_whole hporder values
    have hse : EffectSortedValues (pureCompare (ε := SortException) p) result.toList :=
      (effectSortedValues_pure p result.toList).2 hs
    refine ⟨result, result, ?_, ?_, hp, hse, hp, hse⟩ <;>
      simpa only [sortSmall, bind, Except.bind, pure, Except.pure, ite_self] using hr
  · intro α _ lt t minimum maximum reverse elemSz values hnt
    obtain ⟨p, hporder, rfl⟩ := effect_pure_cases hnt
    obtain ⟨result, hr, hp, hs⟩ := arrayInsertion_whole hporder values
    have hse : EffectSortedValues (pureCompare (ε := SortException) p) result.toList :=
      (effectSortedValues_pure p result.toList).2 hs
    refine ⟨rfl, rfl, result, result, ?_, ?_, hp, hse, hp, hse⟩
    · simpa only [sortConsiderCountingInteger, bind, Except.bind, pure, Except.pure,
        ite_self] using hr
    · exact hr
  · intro α _ lt t minimum maximum reverse elemSz logSpan values hnt
    obtain ⟨p, hporder, rfl⟩ := effect_pure_cases hnt
    obtain ⟨result, hr, hp, hs⟩ := arrayInsertion_whole hporder values
    refine ⟨result, ?_, hp,
      (effectSortedValues_pure (ε := SortException) p result.toList).2 hs⟩
    simpa only [sortConsiderRadix, bind, Except.bind, pure, Except.pure, ite_self] using hr
  · intro α _ lt values target lo hi hnt
    obtain ⟨p, hporder, rfl⟩ := effect_pure_cases hnt
    obtain ⟨result, hr, hp, hs⟩ := arrayInsertion_whole hporder values
    have hse : EffectSortedValues (pureCompare (ε := SortException) p) result.toList :=
      (effectSortedValues_pure p result.toList).2 hs
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, ?_, result, result, result, hr, hr, hr, hp, hse, hp, hse, hp, hse⟩
    exact ⟨rfl, rfl⟩

theorem SorttuplescovSortNtupleAlg_refuted : ¬ JuliaLean.Proofs.base.sort.TupleSortExplicitAlgCorrect := by
  intro h
  obtain ⟨result, hresult, _, _⟩ :=
    h 2 Int intCompare juliaPivot ⟨[2, 1], rfl⟩ .insertion none
      intCompare_order juliaPivot_bounds rfl
  change (Except.error (JuliaLean.base.sort.SortException.jl (JlError.methodError "Base.Sort._sort")) : SortResult (NTuple 2 Int)) =
    .ok result at hresult
  cases hresult

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.ChatGPT.Batch4.Group20

open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

/-- sort-legacy-quicksort-correct. -/
theorem SortLegacyQuicksortCorrect_proven : JuliaLean.Proofs.base.sort.QuickSortCorrect := by
  intro V α S E laws lt values lo hi horder hlo hwindow hhi
  obtain ⟨p, hp, rfl⟩ := effect_pure_cases horder
  obtain ⟨result, hrun, hout⟩ := legacyQuick_window laws hp values lo hi hlo hwindow hhi
  exact ⟨result, hrun, (effectWindowOutcome_pure p false _ _ lo hi).2 hout⟩

/-- sort-legacy-mergesort-stable. -/
theorem SortLegacyMergesortStable_proven : JuliaLean.Proofs.base.sort.MergeSortStable := by
  intro V α _ S E laws lt values lo hi horder hlo hwindow hhi
  obtain ⟨p, hp, rfl⟩ := effect_pure_cases horder
  obtain ⟨result, hrun, hout⟩ := legacyMerge_window laws hp values lo hi hlo hwindow hhi
  exact ⟨result, hrun, (effectWindowOutcome_pure p true _ _ lo hi).2 hout⟩

/-- sort-vector-sorted-permutation. -/
theorem SortVectorSortedPermutation_proven : JuliaLean.Proofs.base.sort.SortVectorSortedPermutation := by
  intro V α _ S E laws numeric lt pivot values algorithm reverse scratch horder hpivot hfull
  obtain ⟨p, hp, rfl⟩ := effect_pure_cases horder
  obtain ⟨result, hrun, hout⟩ :=
    sortVectorBang_sorts laws numeric pivot hp hpivot algorithm hfull values reverse scratch
  have heffective :
      (if reverse = some true then
          fun a b => pureCompare (ε := SortException) p b a
        else pureCompare (ε := SortException) p) =
        pureCompare (ε := SortException)
          (if reverse = some true then fun a b => p b a else p) := by
    rw [pureCompare_swap, pureCompare_ite]
  refine ⟨result, ?_, hout.1.symm, ?_, ?_⟩
  · simpa only [sortVector, bind, Except.bind, heffective] using hrun
  · rw [heffective]
    exact (effectSortedValues_pure _ _).2
      ((sortedValues_iff_pairwise (negTransOrder_effective hp reverse) _).2 hout.2.1)
  · rw [heffective]
    intro hstable
    exact (effectStableWrt_pure _ _ _).2 (hout.2.2 hstable)

/-- sort-default-stable. -/
theorem SortDefaultStable_proven : JuliaLean.Proofs.base.sort.SortDefaultStable := by
  intro V α _ S E laws numeric lt pivot values reverse horder hpivot
  obtain ⟨p, hp, rfl⟩ := effect_pure_cases horder
  obtain ⟨result, hrun, hout⟩ :=
    sortVectorBang_sorts laws numeric pivot hp hpivot .defaultStable rfl values reverse none
  have heffective :
      (if reverse = some true then
          fun a b => pureCompare (ε := SortException) p b a
        else pureCompare (ε := SortException) p) =
        pureCompare (ε := SortException)
          (if reverse = some true then fun a b => p b a else p) := by
    rw [pureCompare_swap, pureCompare_ite]
  refine ⟨result, ?_, ?_, hout.1.symm, ?_, ?_⟩
  · simpa only [defalgArray, heffective] using hrun
  · simpa only [sortVector, bind, Except.bind, defalgArray, heffective] using hrun
  · rw [heffective]
    exact (effectSortedValues_pure _ _).2
      ((sortedValues_iff_pairwise (negTransOrder_effective hp reverse) _).2 hout.2.1)
  · rw [heffective]
    exact (effectStableWrt_pure _ _ _).2 (hout.2.2 rfl)

/-- The checked five-argument insertion entry point forwards to insertion sorting. -/
theorem legacyInsertionBoundsRun {V α : Type} [Inhabited α]
    (S : VectorStorage V α) (lt : α → α → SortResult Bool) (values : V) (lo hi : Int)
    (hcheck : storageCheckBounds S values lo hi = .ok ()) :
    legacySortBounds (storageLegacyOps S lt) values lo hi .insertion () =
      storageInsertion S lt values lo hi := by
  simp only [legacySortBounds, storageLegacyOps, storageLegacyRun, hcheck, liftSortJl, Except.mapError,
    except_bind_ok, except_pure_ok] <;>
    cases storageInsertion S lt values lo hi <;> rfl

/-- An insertion scratch argument is passed through without changing the selected sort. -/
theorem legacyInsertionScratchRun {V α : Type} [Inhabited α]
    (S : VectorStorage V α) (lt : α → α → SortResult Bool) (values : V) (scratch : Array α)
    (lo hi : Int) (hcheck : storageCheckBounds S values lo hi = .ok ()) :
    legacySortWithScratch (storageLegacyOps S lt) values lo hi .insertion () scratch =
      storageInsertion S lt values lo hi := by
  simp only [legacySortWithScratch, storageLegacyOps, storageLegacyRun, hcheck, liftSortJl, Except.mapError,
    except_bind_ok, except_pure_ok] <;>
    cases storageInsertion S lt values lo hi <;> rfl

/-- sort-legacy-invalid-window-rejected. -/
theorem SortLegacyInvalidWindowRejected_proven : JuliaLean.Proofs.base.sort.LegacyInvalidWindowRejected := by
  constructor
  · intro V α _ S E lt values scratch lo hi laws horder hlo hwindow hhi
    obtain ⟨p, hp, rfl⟩ := effect_pure_cases horder
    have hcheck := storageCheckBounds_ok laws (v := values) (Or.inl ⟨hlo, hhi⟩)
    obtain ⟨result, hrun, hout⟩ := insertion_window laws hp values hlo hwindow hhi
    constructor
    · refine ⟨result, ?_, ?_, ?_, (effectWindowOutcome_pure p true _ _ lo hi).2 hout⟩
      · rw [legacyInsertionBoundsRun S (pureCompare p) values lo hi hcheck]
        exact hrun
      · change legacySortBounds (storageLegacyOps S (pureCompare p)) values lo hi .insertion () = _
        rw [legacyInsertionBoundsRun S (pureCompare p) values lo hi hcheck]
        exact hrun
      · rw [legacyInsertionScratchRun S (pureCompare p) values scratch lo hi hcheck]
        exact hrun
    · obtain ⟨whole, hwhole, houtwhole⟩ := insertion_window laws hp values
        (lo := 1) (hi := ((E values).length : Int)) (Int.le_refl 1) (by omega) (Int.le_refl _)
      refine ⟨whole, ?_, (effectSortOutcome_pure p true _ _).2
        (windowOutcome_whole houtwhole)⟩
      change legacySortBounds (storageLegacyOps S (pureCompare p)) values (S.firstindex values)
        (S.lastindex values) .insertion () = _
      rw [laws.firstindex_eq values, storage_lastindex laws values]
      rw [legacyInsertionBoundsRun S (pureCompare p) values 1 ((E values).length : Int)
        (storageCheckBounds_ok laws (Or.inl ⟨Int.le_refl 1, Int.le_refl _⟩))]
      exact hwhole
  · intro V α _ S E lt values scratch algorithm lo hi laws hnonempty houtside
    have hcheck : storageCheckBounds S values lo hi = .error .boundsError := by
      rw [storageCheckBounds_eq, laws.firstindex_eq values, storage_lastindex laws values,
        if_neg (by omega)]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [legacySortBounds, legacySortIgnoredScratch, legacySortWithScratch,
        storageLegacyOps, hcheck, liftSortJl, Except.mapError, bind, Except.bind]

/-- An empty insertion window performs no accesses. -/
theorem insertionEmptyRun {V α : Type} (S : VectorStorage V α)
    (lt : α → α → SortResult Bool) (values : V) (lo hi : Int) (hempty : hi < lo) :
    storageInsertion S lt values lo hi = .ok values := by
  have hrange : arrayIndexRange (lo + 1) hi = [] := by
    have hlen : (hi - (lo + 1) + 1).toNat = 0 := by omega
    simp only [arrayIndexRange, hlen, List.range_zero, List.map_nil]
  simp only [storageInsertion, insertionSort, storageMutationOps, arrayIndices,
    hrange, List.forIn_nil] <;> rfl

/-- An accepted empty legacy quicksort window performs no accesses. -/
theorem quickEmptyRun {V α : Type} (S : VectorStorage V α)
    (lt : α → α → SortResult Bool) (values : V) (lo hi : Int) (hempty : hi < lo)
    (hcheck : storageCheckBounds S values lo hi = .ok ()) :
    legacyQuickSortBang (storageQuickOps S lt) values lo hi () = .ok values := by
  unfold legacyQuickSortBang
  simp only [storageQuickOps, hcheck, liftSortJl, Except.mapError, except_bind_ok]
  unfold quickSortRange
  have hdistance : (hi - lo).toNat = 0 := by omega
  have hless : decide (lo < hi) = false := by simp only [decide_eq_false_iff_not]; omega
  simp only [storageQuickOps, hdistance, Nat.zero_add, quickSortRangeLoop,
    hless, Bool.false_eq_true, ↓reduceIte, except_pure_ok]

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.ChatGPT.Batch4.Group20
open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

/-- The descending target used by both range counterexamples is small and in bounds. -/
theorem group20_descendingIndices :
    bracketTargetIndices (.ordinal (5 : Int) (-1) 3 3) = [5, 4, 3] := by
  decide

/-- A constructible 260-element input reaches the bracketed path and its empty-target check. -/
def group20_emptyPartialInput : Array Int := Array.replicate 260 1

/-- The algorithm `partialsort!` runs on an integer target (sort.jl:113-122). -/
def group20_emptyPartialAlgorithm : Algorithm (BracketSortTarget Int) Int :=
  .boolOptimization (smallDefault 12 (bracketedSort bracketTargetEndpoints (.ordinal 1 1 0 0)))

/-- Once the bracketed path is committed (nonempty window of at least 260 elements), an empty
target throws whatever the rounding of the sample count returns. -/
theorem sortBracketed_emptyTarget_error {V α K Alg Next O Kws Scratch E Result : Type}
    (ops : BracketedSortOps V α K Alg Next O Kws Scratch E Result) (vector : V) (algorithm : Alg)
    (order : O) (keywords : Kws) (lo hi : K) (scratch : Scratch) (missing : E)
    (hrange : ops.rangeAndScratch keywords = .ok (lo, hi, scratch))
    (hless : ops.lessIndex lo hi = true)
    (hlong : ¬ ops.rangeLength lo hi < 260)
    (hmin : ops.targetMinimum (ops.target algorithm) = .error missing) :
    ∃ error, sortBracketed ops vector algorithm order keywords = .error error := by
  unfold sortBracketed
  simp only [hrange, hless, hlong, hmin, bind, Except.bind, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  cases ops.roundInt (ops.square (ops.cbrt (ops.rangeLength lo hi))) <;> exact ⟨_, rfl⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem group20_emptyPartialLoop (numeric : BracketNumerics) (pivot : Int → Int → Int)
    (fuel : Nat) :
    ∃ error, sourceSortLoop arrayStorage numeric pivot (fuel + 1 + 1 + 1) group20_emptyPartialInput
      group20_emptyPartialAlgorithm intCompare
      { lo := arrayStorage.firstindex group20_emptyPartialInput,
        hi := arrayStorage.lastindex group20_emptyPartialInput, scratch := none } = .error error := by
  show ∃ error, sortBracketed (storageBracketOps arrayStorage numeric
      (sourceSortLoop arrayStorage numeric pivot fuel)) group20_emptyPartialInput
      (BracketSortTarget.ordinal 1 1 0 0, _) intCompare
      { lo := arrayStorage.firstindex group20_emptyPartialInput,
        hi := arrayStorage.lastindex group20_emptyPartialInput, scratch := none } = .error error
  refine sortBracketed_emptyTarget_error _ _ _ _ _ 1 260 none
    (.jl (.argumentError "reducing over an empty collection")) ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · exact (by decide : ¬ ((260 : Int) - 1 + 1).toNat < 260)
  · rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem group20_emptyPartialOutcome (numeric : BracketNumerics) (pivot : Int → Int → Int) :
    ∃ error, partialSortBang (storagePartialSortOps arrayStorage numeric pivot)
      group20_emptyPartialInput (.ordinal 1 1 0 0) intCompare none = .error error := by
  obtain ⟨error, herror⟩ :=
    group20_emptyPartialLoop numeric pivot (group20_emptyPartialAlgorithm.depth + 13)
  refine ⟨error, ?_⟩
  have hfuel : group20_emptyPartialAlgorithm.depth + 16 =
      group20_emptyPartialAlgorithm.depth + 13 + 1 + 1 + 1 := by omega
  show Except.bind (Except.bind (sourceSortLoop arrayStorage numeric pivot
      (group20_emptyPartialAlgorithm.depth + 16) group20_emptyPartialInput
      group20_emptyPartialAlgorithm intCompare
      { lo := arrayStorage.firstindex group20_emptyPartialInput,
        hi := arrayStorage.lastindex group20_emptyPartialInput, scratch := none }) _) _ = _
  rw [hfuel, herror]
  rfl

theorem SortPartialsortEmptyRange_refuted :
    ¬ JuliaLean.Proofs.base.sort.PartialSortEmptyRange := by
  intro h
  have hrun := h (Array Int) Int arrayStorage Array.toList intCompare juliaPivot
    group20_emptyPartialInput 1 1 0 arrayStorage_laws intCompare_order
  obtain ⟨error, herror⟩ := group20_emptyPartialOutcome defaultBracketNumerics juliaPivot
  rw [herror] at hrun
  cases hrun

/-- This input has exactly 128 ordinary integer elements. -/
def group20_indexOverflowInput : Array Int :=
  ((List.range 128).map (fun index => 128 - (Int.ofNat index))).toArray

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem group20_indexOverflowOutcome :
    partialSortperm (storagePartialSortpermOps arrayStorage .i8 juliaPivot)
      group20_indexOverflowInput (.index 1) intCompare () none intCompare false =
        .error (.jl (.inexactError "Int8")) := by
  decide +kernel

end JuliaLean.ChatGPT.Batch4.Group20

/-! Usable partial results for the sortperm target. -/
namespace JuliaLean.ChatGPT.Batch4.Group20
open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

/-- The complete in-place half of the requested stable-permutation contract. -/
theorem group20_sortpermBang_stable (hagree : SortpermGenericRunsAgree) {α : Type} [Inhabited α]
    (lt : α → α → Bool) (pivot : Int → Int → Int)
    (values : Array α) (initial : Array Int)
    (algorithm : Algorithm (BracketSortTarget Int) Int) (scratch : Option (Array Int))
    (reverse : Option Bool)
    (hnt : NegTransOrder lt) (hsize : initial.size = values.size)
    (hpivot : ∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi)
    (hfull : isFullSortAlgorithm algorithm = true) :
    let effective := if reverse = some true then fun a b => lt b a else lt
    ∃ result,
      sortpermBang (arraySortpermBangOps pivot) initial values algorithm
        (pureCompare lt) () reverse (pureCompare lt) scratch none = .ok result ∧
      List.Perm (oneBasedIndices values.size) (result.toList.map Int.toNat) ∧
      SortpermOrdered effective values.toList (result.toList.map Int.toNat) := by
  let effective := if reverse = some true then fun a b => lt b a else lt
  obtain ⟨result, hrun, hperm, hsorted⟩ := sp_generic hagree pivot
    (negTransOrder_effective hnt reverse) hpivot algorithm hfull values scratch
  refine ⟨result, ?_, hperm, hsorted⟩
  have heffective :
      (if reverse = some true then
          fun a b => pureCompare (ε := SortException) lt b a
        else pureCompare (ε := SortException) lt) =
        pureCompare (ε := SortException) effective := by
    dsimp only [effective]
    rw [pureCompare_swap, pureCompare_ite]
  simpa only [sortpermBang, arraySortpermBangOps, Option.isSome_none,
    show (true == false) = false from rfl,
    hsize, decide_true, Bool.not_true, Bool.false_eq_true,
    ite_true, ite_false, reduceCtorEq, bind, Except.bind, id_eq, heffective] using hrun

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.ChatGPT.Batch4.Group20

open JuliaLean.Proofs.base.sort

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.ChatGPT.Batch4.Group20
open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

/-- The bounded integer-array kernel contract needed by the public dispatch. -/
def Group20SortpermArrayContract : Prop :=
  ∀ (values : Array Int) (minimum : Int) (m : Nat),
    (values.size : Int) ≤ IntTy.max .i64 →
    ((m + 1 : Nat) : Int) ≤ IntTy.max .i64 →
    (∀ x, x ∈ values.toList → minimum ≤ x ∧ x < minimum + (m : Int)) →
    ∃ counts permutation,
      (sortpermIntRange arraySortpermRangeOps values
        (JuliaLean.base.int.lit .i64 (m : Int))
        (JuliaLean.base.int.lit .i64 minimum)).run (#[], #[]) =
          .ok ((), (counts, permutation)) ∧
      List.Perm (oneBasedIndices values.size) (permutation.toList.map Int.toNat) ∧
      SortpermOrdered (fun a b : Int => decide (a < b)) values.toList
        (permutation.toList.map Int.toNat)

def group20_sortpermFastCondition (n : Nat) (minimum maximum : Int) : Bool :=
  let difference := wrapInt .i64 (maximum - minimum)
  let rangeLength := wrapInt .i64 (difference + 1)
  !(decide (maximum - minimum < IntTy.min .i64 ∨
      IntTy.max .i64 < maximum - minimum) ||
    decide (difference + 1 < IntTy.min .i64 ∨ IntTy.max .i64 < difference + 1)) &&
    decide (rangeLength < Int.ofNat (n / 2))

end JuliaLean.ChatGPT.Batch4.Group20

/-! Counting-path helper lemmas for the stable sort permutation target. -/
namespace JuliaLean.ChatGPT.Batch4.Group20
open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort
open JuliaLean.Proofs.base.int

/-- Integer storage increments agree with wrapped integer addition. -/
theorem group20_sp_increment_val (z : Int) :
    (JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 z)
      (JuliaLean.base.int.lit .i64 1)).val = wrapInt .i64 (z + 1) := by
  simp only [JuliaLean.base.int.add, add_int_val, lit_val,
    wrapInt_add_left, wrapInt_add_right]

/-- Integer storage prefix sums agree with wrapped integer addition. -/
theorem group20_sp_add_val (a b : Int) :
    (JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 a)
      (JuliaLean.base.int.lit .i64 b)).val = wrapInt .i64 (a + b) := by
  simp only [JuliaLean.base.int.add, add_int_val, lit_val,
    wrapInt_add_left, wrapInt_add_right]

/-- Offsets can wrap without changing the mathematical rank modulo the word size. -/
theorem group20_sp_label_val (value minimum : Int) :
    (JuliaLean.base.int.addWrap (JuliaLean.base.int.lit .i64 value)
      (JuliaLean.base.int.subWrap (JuliaLean.base.int.lit .i64 1)
        (JuliaLean.base.int.lit .i64 minimum))).val =
    wrapInt .i64 (value - minimum + 1) := by
  simp only [JuliaLean.base.int.addWrap, add_int_val,
    JuliaLean.base.int.subWrap, sub_int_val, lit_val,
    wrapInt_add_left, wrapInt_add_right, wrapInt_sub_left, wrapInt_sub_right]
  congr 1 <;> omega

/-- An extra unit in the histogram bucket has the expected modular rank. -/
theorem group20_sp_bucket_val (value minimum : Int) :
    (JuliaLean.base.int.addWrap
      (JuliaLean.base.int.addWrap (JuliaLean.base.int.lit .i64 value)
        (JuliaLean.base.int.subWrap (JuliaLean.base.int.lit .i64 1)
          (JuliaLean.base.int.lit .i64 minimum)))
      (JuliaLean.base.int.lit .i64 1)).val =
    wrapInt .i64 (value - minimum + 2) := by
  rw [JuliaLean.base.int.addWrap, add_int_val, group20_sp_label_val,
    lit_val, wrapInt_add_left, wrapInt_add_right]
  congr 1 <;> omega

/-- Reading a known zero-based array slot through the one-based interface. -/
theorem group20_sp_read (a : Array Int) (k : Nat) (v : Int)
    (h : a[k]? = some v) : arrayRead a ((k : Int) + 1) = .ok v := by
  unfold arrayRead
  rw [if_pos (by omega), show (((k : Int) + 1) - 1).toNat = k by omega, h]

/-- Writing a known zero-based array slot through the one-based interface. -/
theorem group20_sp_write (a : Array Int) (k : Nat) (v : Int)
    (h : k < a.size) :
    arrayWrite a ((k : Int) + 1) v = .ok (a.set! k v) := by
  unfold arrayWrite
  rw [if_pos (by omega), show (((k : Int) + 1) - 1).toNat = k by omega]

/-- Expose one stateful bind without unfolding its operand. -/
theorem group20_sp_bind_run {ε S α β : Type}
    (action : StateT S (Except ε) α) (next : α → StateT S (Except ε) β) (state : S) :
    (action >>= next).run state =
      (action.run state >>= fun pair => (next pair.1).run pair.2) := rfl

theorem group20_sp_pure_run {ε S α : Type} (value : α) (state : S) :
    (pure value : StateT S (Except ε) α).run state = .ok (value, state) := rfl

theorem group20_sp_input_read_run (values : Array Int) (i : I) (value : Int)
    (hread : arrayRead values i.val = .ok value) (counts permutation : Array Int) :
    (arraySortpermRangeOps.read values i).run (counts, permutation) =
      .ok (JuliaLean.base.int.lit .i64 value, (counts, permutation)) := by
  dsimp [arraySortpermRangeOps, StateT.run]
  rw [hread] <;> rfl

/-- A successful stateful loop iteration exposes exactly the next loop state. -/
theorem group20_sp_forIn_cons {ε S α β : Type}
    (f : α → β → StateT S (Except ε) (ForInStep β))
    (a : α) (as : List α) (b b' : β) (s s' : S)
    (hstep : (f a b).run s = .ok (.yield b', s')) :
    (forIn (a :: as) b f).run s = (forIn as b' f).run s' := by
  rw [List.forIn_cons, group20_sp_bind_run, hstep] <;> rfl

/-- Source index lists, written with their zero-based starting offset. -/
def group20_sp_indexList (start length : Nat) : List I :=
  (List.range length).map fun offset =>
    JuliaLean.base.int.lit .i64 (Int.ofNat (start + offset + 1))

/-- Finite-list membership can be exposed without any additional library imports. -/
theorem group20_sp_mem_split {α : Type} (a : α) :
    ∀ (xs : List α), a ∈ xs → ∃ before after, xs = before ++ a :: after
  | [], h => by cases h
  | x :: xs, h => by
      rcases List.mem_cons.1 h with heq | htail
      · subst x
        exact ⟨[], xs, rfl⟩
      · obtain ⟨before, after, hsplit⟩ := group20_sp_mem_split a xs htail
        exact ⟨x :: before, after, by rw [hsplit]; rfl⟩

/-- Equal membership characterizes a permutation of two duplicate-free lists. -/
theorem group20_sp_perm_of_nodup {α : Type} :
    ∀ (xs ys : List α), xs.Nodup → ys.Nodup →
      (∀ a, a ∈ xs ↔ a ∈ ys) → xs.Perm ys
  | [], [], _, _, _ => .nil
  | [], y :: ys, _, _, hmem => by
      have h : y ∈ ([] : List α) := (hmem y).2 List.mem_cons_self
      cases h
  | x :: xs, ys, hxs, hys, hmem => by
      obtain ⟨before, after, hsplit⟩ :=
        group20_sp_mem_split x ys ((hmem x).1 List.mem_cons_self)
      have hfront : ys.Perm (x :: (before ++ after)) := by
        rw [hsplit]
        exact List.perm_middle
      have hfrontnd := hfront.nodup_iff.1 hys
      rw [List.nodup_cons] at hxs hfrontnd
      have htailmem : ∀ a, a ∈ xs ↔ a ∈ before ++ after := by
        intro a
        constructor
        · intro ha
          have h : a ∈ x :: (before ++ after) :=
            hfront.mem_iff.1 ((hmem a).1 (List.mem_cons_of_mem x ha))
          rcases List.mem_cons.1 h with heq | hrest
          · subst a
            exact False.elim (hxs.1 ha)
          · exact hrest
        · intro ha
          have h : a ∈ x :: xs := (hmem a).2
            (hfront.mem_iff.2 (List.mem_cons_of_mem x ha))
          rcases List.mem_cons.1 h with heq | hrest
          · subst a
            exact False.elim (hfrontnd.1 ha)
          · exact hrest
      exact (List.Perm.cons x
        (group20_sp_perm_of_nodup xs (before ++ after) hxs.2 hfrontnd.2 htailmem)).trans
          hfront.symm

/-- Values paired with their one-based source indices. -/
def group20_sp_items (start : Nat) : List Int → List (I × Int)
  | [] => []
  | x :: xs => (JuliaLean.base.int.lit .i64 (Int.ofNat (start + 1)), x) ::
      group20_sp_items (start + 1) xs

theorem group20_sp_items_values (xs : List Int) : ∀ start,
    (group20_sp_items start xs).map Prod.snd = xs := by
  induction xs with
  | nil => intro start; rfl
  | cons x xs ih => intro start; simp only [group20_sp_items, List.map_cons, ih]

/-- Predicate counts may be compared using only values that occur in the list. -/
theorem group20_sp_count_congr (p q : Int → Bool) :
    ∀ xs : List Int, (∀ x, x ∈ xs → p x = q x) → xs.countP p = xs.countP q
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.countP_cons, h x List.mem_cons_self,
        group20_sp_count_congr p q xs (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem group20_sp_count_zero (p : Int → Bool) :
    ∀ xs : List Int, (∀ x, x ∈ xs → p x = false) → xs.countP p = 0
  | [], _ => rfl
  | x :: xs, h => by
      simp only [List.countP_cons, h x List.mem_cons_self, Bool.false_eq_true, ite_false,
        group20_sp_count_zero p xs (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- Integer ranks partition a cumulative count into its previous count and one bucket. -/
theorem group20_sp_count_lt_step (xs : List Int) (z : Int) :
    xs.countP (fun x => decide (x < z + 1)) =
      xs.countP (fun x => decide (x < z)) + xs.countP (fun x => decide (x = z)) := by
  have h := sp_countP_le_split (fun x : Int => x) z xs
  have hleft : (fun x : Int => decide (x ≤ z)) = (fun x => decide (x < z + 1)) := by
    funext x
    rw [decide_eq_decide]
    omega
  have hright : (fun x : Int => decide (x ≤ z - 1)) = (fun x => decide (x < z)) := by
    funext x
    rw [decide_eq_decide]
    omega
  simpa only [hleft, hright] using h

/-- Raw and cumulative histogram descriptions for integer-valued input. -/
def group20_sp_raw (xs : List Int) (minimum : Int) (k : Nat) : Int :=
  xs.countP (fun x => decide (x = minimum + (k : Int) - 1))

def group20_sp_start (xs : List Int) (minimum : Int) (k : Nat) : Int :=
  1 + (xs.countP (fun x => decide (x < minimum + (k : Int))) : Int)

theorem group20_sp_start_rec (xs : List Int) (minimum : Int) (k : Nat) (hk : 0 < k) :
    group20_sp_start xs minimum k = group20_sp_raw xs minimum k +
      group20_sp_start xs minimum (k - 1) := by
  have h := group20_sp_count_lt_step xs (minimum + (k : Int) - 1)
  have heq : minimum + (k : Int) - 1 + 1 = minimum + (k : Int) := by omega
  have hprev : minimum + ((k - 1 : Nat) : Int) = minimum + (k : Int) - 1 := by omega
  simp only [heq] at h
  unfold group20_sp_start group20_sp_raw
  rw [hprev, h]
  simp only [Int.natCast_add]
  omega

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.ChatGPT.Batch4.Group20
open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.ChatGPT.Batch4.Group20
open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

/-- One public partial-permutation scratch-initialization step. -/
def group20_initializeInt8Step (index : Int) (indices : Array (JInt .i8)) :
    Jl (ForInStep (Array (JInt .i8))) := do
  let updated ← (do
    let converted ← JInt.convert "Int8" .i8 index
    arrayWrite indices index converted)
  pure (.yield updated)

end JuliaLean.ChatGPT.Batch4.Group20

namespace JuliaLean.Proofs.base.sort
open JuliaLean.Registry
end JuliaLean.Proofs.base.sort

section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace JuliaLean.ChatGPT.Batch8.Group11

open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

/-- One iteration of the checked partial-permutation index initialization. -/
def initializeIndexStep (t : IntTy) (index : Int) (indices : Array (JInt t)) :
    SortResult (ForInStep (Array (JInt t))) := do
  let updated ← (do
    let converted ← liftSortJl (JInt.convert t.name t index)
    liftSortJl (arrayWrite indices index converted))
  pure (.yield updated)

/-- If the initialization loop succeeds, every visited index fits its element type. -/
theorem initializeIndexLoop_success_bounds (t : IntTy) :
    ∀ (indices : List Int) (initial result : Array (JInt t)),
      forIn indices initial (initializeIndexStep t) = .ok result →
      ∀ index ∈ indices, t.min ≤ index ∧ index ≤ t.max := by
  intro indices
  induction indices with
  | nil =>
    intro initial result h index hi
    cases hi
  | cons i rest ih =>
    intro initial result h index hi
    rw [List.forIn_cons] at h
    by_cases hb : t.min ≤ i ∧ i ≤ t.max
    · simp only [initializeIndexStep, JInt.convert, dite_eq_left hb, liftSortJl_ok,
        bind, Except.bind] at h
      cases hw : arrayWrite initial i ⟨i, hb⟩ with
      | error error =>
        simp only [hw, liftSortJl, Except.mapError] at h
        cases h
      | ok updated =>
        simp only [hw, liftSortJl_ok, pure, Except.pure] at h
        rcases List.mem_cons.mp hi with rfl | hrest
        · exact hb
        · exact ih updated result h index hrest
    · simp only [initializeIndexStep, JInt.convert, dite_eq_right hb,
        liftSortJl, Except.mapError, bind, Except.bind] at h
      cases h

/-- An exception-valued bind can succeed only after a successful first action. -/
theorem except_bind_success_input {E A B : Type} (action : Except E A)
    (next : A → Except E B) (result : B)
    (h : (action >>= next) = .ok result) :
    ∃ value, action = .ok value := by
  cases action with
  | error error => cases h
  | ok value => exact ⟨value, rfl⟩

/-- Successful completion of the public wrapper requires successful initialization. -/
theorem partialSortpermBang_initialization_succeeds
    {IX V K Axis Idx Alg L B O PO Kws R E : Type}
    (ops : PartialSortpermOps IX V K Axis Idx Alg L B O PO Kws R E)
    (ix : IX) (v : V) (k : K) (less : L) (byFn : B) (rev : Option Bool)
    (order : O) (initialized : Bool) (result : R)
    (h : partialSortpermBang ops ix v k less byFn rev order initialized = .ok result) :
    ∃ ready,
      forIn (ops.eachIndex ix) ix (fun index current => do
        let updated ← ops.writeIndex current index index
        pure (.yield updated)) = .ok ready := by
  unfold partialSortpermBang at h
  dsimp only at h
  split at h
  · cases h
  · change ((forIn (ops.eachIndex ix) ix (fun index current => do
        let updated ← ops.writeIndex current index index
        pure (.yield updated))) >>= fun ready => do
          let sorted ← ops.sort ready (ops.initialOptimizations (ops.scratchQuickSort k))
            (ops.permutationOrder (ops.ordering less byFn rev order) v) ops.emptyKeywords
          ops.maybeView sorted k) = .ok result at h
    exact except_bind_success_input _ _ result h

/-- Allocation followed by successful initialization requires every source index
to fit the chosen permutation element type. This argument is symbolic in the
source storage and does not evaluate a concrete initialization loop. -/
theorem partialSortperm_success_index_bounds {V α : Type} [Inhabited α]
    (S : VectorStorage V α) (t : IntTy) (pivot : Int → Int → Int)
    (values : V) (target : BracketSortTarget Int)
    (less order : α → α → SortResult Bool) (reverse : Option Bool) (initialized : Bool)
    (result : List (JInt t))
    (h : partialSortperm (storagePartialSortpermOps S t pivot)
      values target less () reverse order initialized = .ok result) :
    ∀ index ∈ arrayIndexRange 1 (S.length values),
      t.min ≤ index ∧ index ≤ t.max := by
  let initial := Array.replicate (S.length values) (JInt.wrap t 0)
  change partialSortpermBang (storagePartialSortpermOps S t pivot)
    initial values target less () reverse order initialized = .ok result at h
  obtain ⟨ready, hloop⟩ := partialSortpermBang_initialization_succeeds
    (storagePartialSortpermOps S t pivot)
    initial values target less () reverse order initialized result h
  change forIn (arrayIndexRange 1 initial.size) initial (initializeIndexStep t) =
    .ok ready at hloop
  have hb := initializeIndexLoop_success_bounds t _ initial ready hloop
  simpa only [initial, Array.size_replicate] using hb

/-- A fully constructible input with 128 ordinary machine-integer values. -/
def indexOverflowInput : Array Int :=
  ((List.range 128).map (fun index => 128 - (Int.ofNat index))).toArray

theorem indexOverflowInput_size : indexOverflowInput.size = 128 := by
  simp only [indexOverflowInput, List.size_toArray, List.length_map, List.length_range]

/-- The allocating wrapper cannot succeed when its index element type is Int8. -/
theorem indexOverflow_no_success (result : List (JInt .i8)) :
    partialSortperm (storagePartialSortpermOps arrayStorage .i8 juliaPivot)
      indexOverflowInput (.index 1) intCompare () none intCompare false ≠ .ok result := by
  have herr : partialSortperm (storagePartialSortpermOps arrayStorage .i8 juliaPivot)
      indexOverflowInput (.index 1) intCompare () none intCompare false =
      .error (.jl (.inexactError "Int8")) := by
    decide +kernel
  rw [herr]
  intro h
  cases h

/-- The exact frozen partial-permutation contract fails on a 128-element vector. -/
theorem SortPartialsortpermIndexType_refuted :
    ¬ JuliaLean.Proofs.base.sort.PartialSortpermIndexTypeCorrect := by
  intro h
  have hbound : ∀ index, index ∈ bracketTargetIndices (.index (1 : Int)) →
      1 ≤ index ∧ index ≤ (indexOverflowInput.toList.length : Int) ∧
      IntTy.min .i8 ≤ index ∧ index ≤ IntTy.max .i8 := by
    intro index hindex
    have hi : index = 1 := by
      simpa only [bracketTargetIndices, List.mem_singleton] using hindex
    subst index
    rw [Array.length_toList, indexOverflowInput_size]
    decide
  obtain ⟨result, hrun, _, _⟩ := h .i8 (Array Int) Int arrayStorage Array.toList
    intCompare indexOverflowInput (.index 1) juliaPivot none arrayStorage_laws
    intCompare_order (by decide)
    (by rw [Array.length_toList, indexOverflowInput_size]; decide) hbound juliaPivot_bounds
  exact indexOverflow_no_success result hrun

end JuliaLean.ChatGPT.Batch8.Group11

namespace JuliaLean.ChatGPT.Batch8.Group11
open JuliaLean.ChatGPT.Batch4.Group20
open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

/-- The top-level core follows the generic path when the forward/integer gate is false. -/
theorem g11_sortpermCore_generic {α : Type} [Inhabited α]
    (pivot : Int → Int → Int) (integerView : Array α → SortResult (Array Int))
    (hasIntegerElements : Array α → Bool)
    (isForward : (α → α → SortResult Bool) → Bool)
    (values : Array α) (algorithm : Algorithm (BracketSortTarget Int) Int)
    (order : α → α → SortResult Bool) (scratch : Option (Array Int))
    (hgate : (isForward order && hasIntegerElements values) = false) :
    sortpermCore (arraySortpermCoreOps pivot integerView hasIntegerElements isForward)
      values algorithm order scratch () =
    sortVectorBang (sourceVectorSortOps arrayStorage defaultBracketNumerics pivot)
      (arrayIndexRange 1 values.size).toArray algorithm (arrayPermutationOrder order values)
      () none (arrayPermutationOrder order values) scratch := by
  simp only [sortpermCore, arraySortpermCoreOps, Bool.and_true, hgate,
    Bool.false_eq_true, ite_false, bind, Except.bind, id_eq]

/-- The top-level path is also stable whenever integer counting is bypassed. -/
theorem g11_sortpermTop_stable_generic (hagree : SortpermGenericRunsAgree) {α : Type} [Inhabited α]
    (lt : α → α → Bool) (pivot : Int → Int → Int)
    (integerView : Array α → SortResult (Array Int))
    (hasIntegerElements : Array α → Bool)
    (values : Array α) (algorithm : Algorithm (BracketSortTarget Int) Int)
    (scratch : Option (Array Int)) (reverse : Option Bool)
    (hnt : NegTransOrder lt)
    (hpivot : ∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi)
    (hfull : isFullSortAlgorithm algorithm = true)
    (hbypass : reverse = some true ∨ hasIntegerElements values = false) :
    let effective := if reverse = some true then fun a b => lt b a else lt
    ∃ result,
      sortpermTop (arraySortpermTopOps pivot integerView hasIntegerElements
        (fun _ => reverse != some true)) values algorithm (pureCompare lt) () reverse
          (pureCompare lt) scratch () =
          .ok result ∧
      List.Perm (oneBasedIndices values.size) (result.toList.map Int.toNat) ∧
      SortpermOrdered effective values.toList (result.toList.map Int.toNat) := by
  let effective := if reverse = some true then fun a b => lt b a else lt
  obtain ⟨result, hrun, hperm, hsorted⟩ := sp_generic hagree pivot
    (negTransOrder_effective hnt reverse) hpivot algorithm hfull values scratch
  refine ⟨result, ?_, hperm, hsorted⟩
  have hgate : ((reverse != some true) && hasIntegerElements values) = false := by
    rcases hbypass with hreverse | hinteger
    · simp only [hreverse, bne_self_eq_false, Bool.false_and]
    · simp only [hinteger, Bool.and_false]
  have hcore := g11_sortpermCore_generic pivot integerView hasIntegerElements
    (fun _ => reverse != some true) values algorithm (pureCompare effective) scratch hgate
  have htop : sortpermTop (arraySortpermTopOps pivot integerView hasIntegerElements
      (fun _ => reverse != some true)) values algorithm (pureCompare lt) () reverse
        (pureCompare lt) scratch () =
      sortpermCore (arraySortpermCoreOps pivot integerView hasIntegerElements
        (fun _ => reverse != some true)) values algorithm (pureCompare effective) scratch () := by
    by_cases hreverse : reverse = some true
    · simp only [sortpermTop, arraySortpermTopOps, hreverse, ite_true, effective,
        pureCompare_swap]
    · simp only [sortpermTop, arraySortpermTopOps, hreverse, ite_false,
        reduceCtorEq, effective]
  rw [htop, hcore]
  exact hrun

end JuliaLean.ChatGPT.Batch8.Group11

namespace JuliaLean.ChatGPT.Batch8.Group11
open JuliaLean.ChatGPT.Batch4.Group20

open JuliaLean.Proofs.base.sort

/-- Numeric key order transfers sortedness and stable index tie-breaking to the original values. -/
theorem sortpermOrderedIntegerTransfer {α : Type} (values : List α) (key : α → Int)
    (lt : α → α → Bool) (indices : List Nat)
    (hkey : ∀ a ∈ values, ∀ b ∈ values,
      lt a b = decide (key a < key b))
    (hordered : SortpermOrdered (fun a b : Int => decide (a < b)) (values.map key) indices) :
    SortpermOrdered lt values indices := by
  intro i j leftIndex rightIndex leftValue rightValue hij hleft hright hleftValue hrightValue
  have hleftMem : leftValue ∈ values := List.mem_of_getElem? hleftValue
  have hrightMem : rightValue ∈ values := List.mem_of_getElem? hrightValue
  have hleftKey : (values.map key)[leftIndex - 1]? = some (key leftValue) := by
    rw [List.getElem?_map, hleftValue] <;> rfl
  have hrightKey : (values.map key)[rightIndex - 1]? = some (key rightValue) := by
    rw [List.getElem?_map, hrightValue] <;> rfl
  have hsorted := hordered i j leftIndex rightIndex (key leftValue) (key rightValue)
    hij hleft hright hleftKey hrightKey
  have hlr := hkey leftValue hleftMem rightValue hrightMem
  have hrl := hkey rightValue hrightMem leftValue hleftMem
  constructor
  · exact hrl.trans hsorted.1
  · intro hequal
    exact hsorted.2 ⟨hlr.symm.trans hequal.1, hrl.symm.trans hequal.2⟩

end JuliaLean.ChatGPT.Batch8.Group11

namespace JuliaLean.ChatGPT.Batch8.Group11
open JuliaLean.ChatGPT.Batch4.Group20
open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

theorem g11_integerExtrema_bounds (values : Array Int) (hne : 0 < values.size) :
    ∃ minimum maximum,
      arrayIntegerExtrema values = .ok (minimum, maximum) ∧ minimum ≤ maximum ∧
      ∀ x, x ∈ values.toList → minimum ≤ x ∧ x ≤ maximum := by
  cases hlist : values.toList with
  | nil =>
    have hz : values.size = 0 := by
      have h := congrArg List.length hlist
      simpa only [Array.length_toList, List.length_nil] using h
    omega
  | cons first rest =>
    have hminimum := sp_foldl_min rest first
    have hmaximum := sp_foldl_max rest first
    refine ⟨rest.foldl min first, rest.foldl max first, ?_, by omega, ?_⟩
    · simp only [arrayIntegerExtrema, hlist]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hrest
      · exact ⟨hminimum.1, hmaximum.1⟩
      · exact ⟨hminimum.2 x hrest, hmaximum.2 x hrest⟩

theorem g11_sortpermFastFacts (n : Nat) (minimum maximum : Int)
    (hn : (n : Int) ≤ IntTy.max .i64) (horder : minimum ≤ maximum)
    (hfast : group20_sortpermFastCondition n minimum maximum = true) :
    wrapInt .i64 (wrapInt .i64 (maximum - minimum) + 1) = maximum - minimum + 1 ∧
    0 < maximum - minimum + 1 ∧ maximum - minimum + 1 + 1 ≤ IntTy.max .i64 := by
  simp only [group20_sortpermFastCondition, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq] at hfast
  have hd : wrapInt .i64 (maximum - minimum) = maximum - minimum :=
    wrapInt_of_inRange .i64 _ (by omega)
  simp only [hd] at hfast
  have hr : wrapInt .i64 (maximum - minimum + 1) = maximum - minimum + 1 :=
    wrapInt_of_inRange .i64 _ (by omega)
  simp only [hr, Int.ofNat_eq_natCast] at hfast
  have hhalf : n / 2 ≤ n := Nat.div_le_self n 2
  have hhalfInt : Int.ofNat (n / 2) ≤ (n : Int) := Int.ofNat_le.mpr hhalf
  exact ⟨by rw [hd, hr], by omega, by omega⟩

/-- A nonempty numeric fast branch is stable; all rejected guards use the generic path. -/
theorem g11_sortpermCore_forward (hkernel : Group20SortpermArrayContract)
    (hagree : SortpermGenericRunsAgree)
    {α : Type} [Inhabited α] (lt : α → α → Bool) (pivot : Int → Int → Int)
    (integerView : Array α → SortResult (Array Int)) (hasIntegerElements : Array α → Bool)
    (integerValue : α → Int) (values : Array α)
    (algorithm : Algorithm (BracketSortTarget Int) Int) (scratch : Option (Array Int))
    (hnt : NegTransOrder lt) (hsize : (values.size : Int) ≤ IntTy.max .i64)
    (hpivot : ∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi)
    (hfull : isFullSortAlgorithm algorithm = true)
    (hinteger : hasIntegerElements values = true)
    (hview : integerView values = .ok (values.map integerValue))
    (horder : ∀ a ∈ values.toList, ∀ b ∈ values.toList,
      lt a b = decide (integerValue a < integerValue b)) :
    ∃ result,
      sortpermCore (arraySortpermCoreOps pivot integerView hasIntegerElements (fun _ => true))
        values algorithm (pureCompare lt) scratch () = .ok result ∧
      List.Perm (oneBasedIndices values.size) (result.toList.map Int.toNat) ∧
      SortpermOrdered lt values.toList (result.toList.map Int.toNat) := by
  let integers := values.map integerValue
  let generic := sortVectorBang
    (sourceVectorSortOps arrayStorage defaultBracketNumerics pivot)
    (arrayIndexRange 1 values.size).toArray algorithm
    (arrayPermutationOrder (pureCompare lt) values) () none
    (arrayPermutationOrder (pureCompare lt) values) scratch
  have hcore :
      sortpermCore (arraySortpermCoreOps pivot integerView hasIntegerElements (fun _ => true))
        values algorithm (pureCompare lt) scratch () =
      if 1 < values.size then
        (do
          let (minimum, maximum) ← liftSortJl (arrayIntegerExtrema integers)
          if group20_sortpermFastCondition values.size minimum maximum then
            let (_, (_, permutation)) ←
              liftSortJl ((sortpermIntRange arraySortpermRangeOps integers
                (JuliaLean.base.int.lit .i64
                  (wrapInt .i64 (wrapInt .i64 (maximum - minimum) + 1)))
                (JuliaLean.base.int.lit .i64 minimum)).run (#[], #[]))
            pure permutation
          else generic)
      else generic := by
    simp only [sortpermCore, arraySortpermCoreOps, hinteger, hview, Bool.true_and,
      ↓reduceIte, bind, Except.bind, integers, generic, group20_sortpermFastCondition,
      JInt.wrap, id_eq]
    rfl
  obtain ⟨genericResult, hgeneric, hgenericPerm, hgenericOrder⟩ :=
    sp_generic hagree pivot hnt hpivot algorithm hfull values scratch
  by_cases hlong : 1 < values.size
  · obtain ⟨minimum, maximum, hextrema, hminmax, hbounds⟩ :=
      g11_integerExtrema_bounds integers (by simp only [integers, Array.size_map]; omega)
    rw [if_pos hlong, hextrema] at hcore
    simp only [liftSortJl_ok, bind, Except.bind] at hcore
    by_cases hfast : group20_sortpermFastCondition values.size minimum maximum = true
    · obtain ⟨hrange, hpositive, hcountBound⟩ :=
        g11_sortpermFastFacts values.size minimum maximum hsize hminmax hfast
      let m := (maximum - minimum + 1).toNat
      have hm : (m : Int) = maximum - minimum + 1 := by dsimp only [m]; omega
      obtain ⟨counts, result, hrun, hperm, hsorted⟩ :=
        hkernel integers minimum m (by simpa only [integers, Array.size_map] using hsize)
          (by simp only [Int.natCast_add, Int.natCast_one, hm]; omega)
          (by
            intro x hx
            have h := hbounds x hx
            rw [hm]
            omega)
      refine ⟨result, ?_, ?_, ?_⟩
      · rw [if_pos hfast, hrange, ← hm, hrun] at hcore
        simp only [liftSortJl_ok, pure, Except.pure, bind, Except.bind] at hcore
        exact hcore
      · simpa only [integers, Array.size_map] using hperm
      · apply sortpermOrderedIntegerTransfer values.toList integerValue lt _ horder
        simpa only [integers, Array.toList_map] using hsorted
    · refine ⟨genericResult, ?_, hgenericPerm, hgenericOrder⟩
      rw [if_neg hfast] at hcore
      exact hcore.trans hgeneric
  · refine ⟨genericResult, ?_, hgenericPerm, hgenericOrder⟩
    rw [if_neg hlong] at hcore
    exact hcore.trans hgeneric

theorem g11_sortpermStable_of_array_contract
    (hkernel : Group20SortpermArrayContract) (hagree : SortpermGenericRunsAgree) :
    JuliaLean.Proofs.base.sort.SortpermStable := by
  intro α _ lt pivot integerView hasIntegerElements integerValue values initial algorithm
    scratch reverse hnt hinitSize hsize hpivot hfull hfaithful
  obtain ⟨p, hp, rfl⟩ := effect_pure_cases hnt
  obtain ⟨bangResult, hbang, hbangPerm, hbangOrder⟩ :=
    group20_sortpermBang_stable hagree p pivot values initial algorithm scratch reverse
      hp hinitSize hpivot hfull
  have heffective :
      (if reverse = some true then
          fun a b => pureCompare (ε := SortException) p b a
        else pureCompare (ε := SortException) p) =
        pureCompare (ε := SortException)
          (if reverse = some true then fun a b => p b a else p) := by
    rw [pureCompare_swap, pureCompare_ite]
  have htop :
      ∃ result,
        sortpermTop (arraySortpermTopOps pivot integerView hasIntegerElements
          (fun _ => reverse != some true)) values algorithm (pureCompare p) () reverse
            (pureCompare p) scratch () =
            .ok result ∧
        List.Perm (oneBasedIndices values.size) (result.toList.map Int.toNat) ∧
        SortpermOrdered (if reverse = some true then fun a b => p b a else p)
          values.toList (result.toList.map Int.toNat) := by
    by_cases hreverse : reverse = some true
    · exact g11_sortpermTop_stable_generic hagree p pivot integerView hasIntegerElements
        values algorithm scratch reverse hp hpivot hfull (Or.inl hreverse)
    · by_cases hinteger : hasIntegerElements values = true
      · obtain ⟨hview, horderEffect⟩ := hfaithful values hinteger
        have horder : ∀ a ∈ values.toList, ∀ b ∈ values.toList,
            p a b = decide (integerValue a < integerValue b) := by
          intro a ha b hb
          exact Except.ok.inj (horderEffect a b ha hb)
        obtain ⟨result, hrun, hperm, hsorted⟩ :=
          g11_sortpermCore_forward hkernel hagree p pivot integerView hasIntegerElements
            integerValue values algorithm scratch hp hsize hpivot hfull hinteger hview horder
        have hforward : (reverse != some true) = true := by
          simpa only [bne_iff_ne] using hreverse
        refine ⟨result, ?_, hperm, ?_⟩
        · simpa only [sortpermTop, arraySortpermTopOps, hreverse, ↓reduceIte,
            reduceCtorEq, hforward] using hrun
        · simpa only [hreverse, ↓reduceIte] using hsorted
      · have hfalse : hasIntegerElements values = false := by
          cases h : hasIntegerElements values with
          | false => rfl
          | true => exact False.elim (hinteger h)
        exact g11_sortpermTop_stable_generic hagree p pivot integerView hasIntegerElements
          values algorithm scratch reverse hp hpivot hfull (Or.inr hfalse)
  obtain ⟨topResult, htopRun, htopPerm, htopOrder⟩ := htop
  refine ⟨topResult, bangResult, htopRun, hbang, htopPerm, ?_, hbangPerm, ?_⟩
  · rw [heffective]
    exact (effectSortpermOrdered_pure _ _ _).2 htopOrder
  · rw [heffective]
    exact (effectSortpermOrdered_pure _ _ _).2 hbangOrder

end JuliaLean.ChatGPT.Batch8.Group11

/-! Counting-path helper lemmas for the stable sort permutation target. -/
namespace JuliaLean.ChatGPT.Batch8.Group11
open JuliaLean.ChatGPT.Batch4.Group20
open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort
open JuliaLean.Proofs.base.int

/-- Reduce a successful exception bind without unfolding stateful binds. -/
theorem g11_sp_except_ok_bind {ε α β : Type}
    (value : α) (next : α → Except ε β) :
    ((.ok value : Except ε α) >>= next) = next value := rfl

/-- One histogram iteration increments exactly its selected bucket. -/
theorem g11_sp_histogram_step (values counts permutation : Array Int)
    (offsets i : I) (value counter : Int) (k : Nat)
    (hread : arrayRead values i.val = .ok value)
    (hbucket : (JuliaLean.base.int.addWrap
      (JuliaLean.base.int.addWrap (JuliaLean.base.int.lit .i64 value) offsets)
      (JuliaLean.base.int.lit .i64 1)).val = (k : Int) + 1)
    (hcount : counts[k]? = some counter) (hk : k < counts.size) :
    (sp_body1 arraySortpermRangeOps values offsets () i ⟨⟩).run
      (counts, permutation) =
    .ok (.yield ⟨⟩, (counts.set! k (wrapInt .i64 (counter + 1)), permutation)) := by
  let bucket := JuliaLean.base.int.addWrap
    (JuliaLean.base.int.addWrap (JuliaLean.base.int.lit .i64 value) offsets)
    (JuliaLean.base.int.lit .i64 1)
  have hget : (arraySortpermRangeOps.getCount () bucket).run (counts, permutation) =
      .ok (JuliaLean.base.int.lit .i64 counter, (counts, permutation)) := by
    change (arrayRead counts bucket.val >>= fun v =>
      .ok (JuliaLean.base.int.lit .i64 v, (counts, permutation))) = _
    dsimp only [bucket]
    rw [hbucket, group20_sp_read counts k counter hcount] <;> rfl
  have hset : (arraySortpermRangeOps.setCount () bucket
      (JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 counter)
        (JuliaLean.base.int.lit .i64 1))).run (counts, permutation) =
      .ok ((), (counts.set! k (wrapInt .i64 (counter + 1)), permutation)) := by
    change (arrayWrite counts bucket.val
      (JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 counter)
        (JuliaLean.base.int.lit .i64 1)).val >>= fun c => .ok ((), (c, permutation))) = _
    dsimp only [bucket]
    rw [hbucket, group20_sp_increment_val, group20_sp_write counts k _ hk] <;> rfl
  dsimp only [bucket] at hget hset
  simp only [sp_body1, group20_sp_bind_run,
    group20_sp_input_read_run values i value hread counts permutation,
    hget, hset, group20_sp_pure_run, g11_sp_except_ok_bind]

/-- One cumulative-sum iteration changes only its current bucket. -/
theorem g11_sp_prefix_step (counts permutation : Array Int)
    (i : I) (k : Nat) (current previous : Int)
    (hi : i.val = (k : Int) + 1) (hkpos : 0 < k) (hk : k < counts.size)
    (hsub : (JuliaLean.base.int.sub i (JuliaLean.base.int.lit .i64 1)).val = (k : Int))
    (hcurrent : counts[k]? = some current)
    (hprevious : counts[k - 1]? = some previous) :
    (sp_body2 arraySortpermRangeOps () i ⟨⟩).run (counts, permutation) =
    .ok (.yield ⟨⟩, (counts.set! k (wrapInt .i64 (current + previous)), permutation)) := by
  have hgetCurrent : (arraySortpermRangeOps.getCount () i).run (counts, permutation) =
      .ok (JuliaLean.base.int.lit .i64 current, (counts, permutation)) := by
    change (arrayRead counts i.val >>= fun v =>
      .ok (JuliaLean.base.int.lit .i64 v, (counts, permutation))) = _
    rw [hi, group20_sp_read counts k current hcurrent] <;> rfl
  have hpreviousRead : arrayRead counts (k : Int) = .ok previous := by
    simpa only [show ((k - 1 : Nat) : Int) + 1 = (k : Int) by omega] using
      group20_sp_read counts (k - 1) previous hprevious
  have hgetPrevious : (arraySortpermRangeOps.getCount ()
      (JuliaLean.base.int.sub i (JuliaLean.base.int.lit .i64 1))).run
        (counts, permutation) =
      .ok (JuliaLean.base.int.lit .i64 previous, (counts, permutation)) := by
    change (arrayRead counts (JuliaLean.base.int.sub i (JuliaLean.base.int.lit .i64 1)).val
      >>= fun v => .ok (JuliaLean.base.int.lit .i64 v, (counts, permutation))) = _
    rw [hsub, hpreviousRead] <;> rfl
  have hset : (arraySortpermRangeOps.setCount () i
      (JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 current)
        (JuliaLean.base.int.lit .i64 previous))).run (counts, permutation) =
      .ok ((), (counts.set! k (wrapInt .i64 (current + previous)), permutation)) := by
    change (arrayWrite counts i.val
      (JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 current)
        (JuliaLean.base.int.lit .i64 previous)).val >>= fun c =>
      .ok ((), (c, permutation))) = _
    rw [hi, group20_sp_add_val, group20_sp_write counts k _ hk] <;> rfl
  simp only [sp_body2, group20_sp_bind_run, hgetCurrent, hgetPrevious,
    hset, group20_sp_pure_run, g11_sp_except_ok_bind]

/-- Histogram loop invariant, including arbitrary wrapped initial bucket counts. -/
theorem g11_sp_histogram_loop (values : Array Int) (offsets : I)
    (bucket : Int → Nat) (m : Nat) :
    ∀ (items : List (I × Int)) (counts permutation : Array Int) (seed : Nat → Int),
      counts.size = m →
      (∀ k, k < m → counts[k]? = some (wrapInt .i64 (seed k))) →
      (∀ item, item ∈ items → arrayRead values item.1.val = .ok item.2 ∧
        (JuliaLean.base.int.addWrap
          (JuliaLean.base.int.addWrap (JuliaLean.base.int.lit .i64 item.2) offsets)
          (JuliaLean.base.int.lit .i64 1)).val = (bucket item.2 : Int) + 1 ∧
        bucket item.2 < m) →
      ∃ finalCounts,
        (forIn (items.map Prod.fst) ⟨⟩
          (sp_body1 arraySortpermRangeOps values offsets ())).run
            (counts, permutation) = .ok (⟨⟩, (finalCounts, permutation)) ∧
        finalCounts.size = m ∧
        ∀ k, k < m → finalCounts[k]? = some (wrapInt .i64
          (seed k + (items.countP (fun item => bucket item.2 == k) : Int)))
  | [], counts, permutation, seed, hsize, hcounts, _ => by
      refine ⟨counts, rfl, hsize, ?_⟩
      intro k hk
      simpa only [List.countP_nil, Int.natCast_zero, Int.add_zero] using hcounts k hk
  | item :: items, counts, permutation, seed, hsize, hcounts, hitems => by
      obtain ⟨hread, hbucket, hk⟩ := hitems item List.mem_cons_self
      let k := bucket item.2
      let nextCounts := counts.set! k (wrapInt .i64 (seed k + 1))
      let nextSeed := fun j => seed j + if k = j then 1 else 0
      have hstep : (sp_body1 arraySortpermRangeOps values offsets () item.1 ⟨⟩).run
          (counts, permutation) = .ok (.yield ⟨⟩, (nextCounts, permutation)) := by
        have h := g11_sp_histogram_step values counts permutation offsets item.1
          item.2 (wrapInt .i64 (seed k)) k hread hbucket (hcounts k hk) (by omega)
        simpa only [wrapInt_add_left, nextCounts] using h
      have hnextsize : nextCounts.size = m := by
        simpa [nextCounts] using hsize
      have hnext : ∀ j, j < m → nextCounts[j]? = some (wrapInt .i64 (nextSeed j)) := by
        intro j hj
        simp only [nextCounts, Array.set!_eq_setIfInBounds]
        by_cases hkj : k = j
        · subst j
          rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)]
          simp only [nextSeed, ite_true]
        · rw [Array.getElem?_setIfInBounds_ne hkj, hcounts j hj]
          simp only [nextSeed, hkj, ite_false, Int.add_zero]
      obtain ⟨finalCounts, hloop, hfinalsize, hfinal⟩ :=
        g11_sp_histogram_loop values offsets bucket m items nextCounts permutation
          nextSeed hnextsize hnext (fun i hi => hitems i (List.mem_cons_of_mem _ hi))
      refine ⟨finalCounts, ?_, hfinalsize, ?_⟩
      · rw [List.map_cons, group20_sp_forIn_cons _ _ _ _ _ _ _ hstep]
        exact hloop
      · intro j hj
        rw [hfinal j hj]
        congr 2
        simp only [nextSeed, List.countP_cons]
        by_cases hkj : k = j
        · have heq : (bucket item.2 == j) = true := by
            simp only [beq_iff_eq]
            exact hkj
          simp only [hkj, heq, ite_true, Int.natCast_add, Int.natCast_one]
          omega
        · have hne : (bucket item.2 == j) = false := by
            simp only [beq_eq_false_iff_ne]
            exact hkj
          simp only [hkj, hne, ite_false, Bool.false_eq_true, Int.add_zero, Nat.add_zero]


theorem g11_sp_indexList_succ (start length : Nat) :
    group20_sp_indexList start (length + 1) =
      JuliaLean.base.int.lit .i64 (Int.ofNat (start + 1)) ::
        group20_sp_indexList (start + 1) length := by
  unfold group20_sp_indexList
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero]
  apply congrArg (List.cons (JuliaLean.base.int.lit .i64 (Int.ofNat (start + 1))))
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  apply congrArg (JuliaLean.base.int.lit .i64)
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Cumulative-sum loop invariant. Wrapped values are retained even for the
final sentinel counter, which can be one greater than the input length. -/
theorem g11_sp_prefix_loop (raw total : Nat → Int)
    (hrec : ∀ k, 0 < k → total k = raw k + total (k - 1)) :
    ∀ (remaining start : Nat) (counts permutation : Array Int),
      0 < start → counts.size = start + remaining →
      (counts.size : Int) ≤ IntTy.max .i64 →
      (∀ j, j < counts.size → counts[j]? = some (wrapInt .i64
        (if j < start then total j else raw j))) →
      ∃ finalCounts,
        (forIn (group20_sp_indexList start remaining) ⟨⟩
          (sp_body2 arraySortpermRangeOps ())).run (counts, permutation) =
          .ok (⟨⟩, (finalCounts, permutation)) ∧
        finalCounts.size = counts.size ∧
        ∀ j, j < counts.size → finalCounts[j]? = some (wrapInt .i64 (total j))
  | 0, start, counts, permutation, hstart, hsize, hbound, hcounts => by
      refine ⟨counts, rfl, rfl, ?_⟩
      intro j hj
      simpa only [if_pos (by omega : j < start)] using hcounts j hj
  | remaining + 1, start, counts, permutation, hstart, hsize, hbound, hcounts => by
      let index := JuliaLean.base.int.lit .i64 (Int.ofNat (start + 1))
      have hindex : index.val = (start : Int) + 1 := by
        dsimp only [index]
        rw [lit_val, Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_one]
        apply wrapInt_of_inRange
        have hmin : IntTy.min .i64 < 0 := by decide
        constructor <;> omega
      have hsub : (JuliaLean.base.int.sub index (JuliaLean.base.int.lit .i64 1)).val =
          (start : Int) := by
        rw [JuliaLean.base.int.sub, sub_int_val, hindex]
        have h1 : (JuliaLean.base.int.lit .i64 1).val = 1 := by decide
        rw [h1, show (start : Int) + 1 - 1 = (start : Int) by omega]
        apply wrapInt_of_inRange
        have hmin : IntTy.min .i64 < 0 := by decide
        constructor <;> omega
      have hcurrent : counts[start]? = some (wrapInt .i64 (raw start)) := by
        simpa only [Nat.lt_irrefl, ite_false] using hcounts start (by omega)
      have hprevious : counts[start - 1]? = some (wrapInt .i64 (total (start - 1))) := by
        simpa only [if_pos (by omega : start - 1 < start)] using
          hcounts (start - 1) (by omega)
      let nextCounts := counts.set! start (wrapInt .i64 (total start))
      have hstep : (sp_body2 arraySortpermRangeOps () index ⟨⟩).run
          (counts, permutation) = .ok (.yield ⟨⟩, (nextCounts, permutation)) := by
        have h := g11_sp_prefix_step counts permutation index start
          (wrapInt .i64 (raw start)) (wrapInt .i64 (total (start - 1)))
          hindex hstart (by omega) hsub hcurrent hprevious
        simpa only [wrapInt_add_left, wrapInt_add_right, ← hrec start hstart,
          nextCounts] using h
      have hnextsize : nextCounts.size = counts.size := by simp [nextCounts]
      have hnext : ∀ j, j < nextCounts.size → nextCounts[j]? = some (wrapInt .i64
          (if j < start + 1 then total j else raw j)) := by
        intro j hj
        rw [hnextsize] at hj
        simp only [nextCounts, Array.set!_eq_setIfInBounds]
        by_cases hs : start = j
        · subst j
          rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)]
          simp only [if_pos (by omega : start < start + 1)]
        · rw [Array.getElem?_setIfInBounds_ne hs, hcounts j hj]
          by_cases hjs : j < start
          · simp only [hjs, if_pos (by omega : j < start + 1), ite_true]
          · simp only [hjs, if_neg (by omega : ¬ j < start + 1), ite_false]
      obtain ⟨finalCounts, hloop, hfinalsize, hfinal⟩ :=
        g11_sp_prefix_loop raw total hrec remaining (start + 1)
          nextCounts permutation (by omega) (by omega) (by omega) hnext
      refine ⟨finalCounts, ?_, hfinalsize.trans hnextsize, ?_⟩
      · rw [g11_sp_indexList_succ, group20_sp_forIn_cons _ _ _ _ _ _ _ hstep]
        exact hloop
      · intro j hj
        exact hfinal j (by omega)

/-- One placement iteration writes its source index to the current bucket cursor. -/
theorem g11_sp_placement_step (values counts permutation : Array Int)
    (offsets i : I) (value : Int) (bucket slot : Nat)
    (hread : arrayRead values i.val = .ok value)
    (hlabel : (JuliaLean.base.int.addWrap
      (JuliaLean.base.int.lit .i64 value) offsets).val = (bucket : Int) + 1)
    (hcount : counts[bucket]? = some (wrapInt .i64 ((slot : Int) + 1)))
    (hbucket : bucket < counts.size) (hslot : slot < permutation.size)
    (hbound : (permutation.size : Int) ≤ IntTy.max .i64) :
    (sp_body3 arraySortpermRangeOps values offsets () () i ⟨⟩).run
      (counts, permutation) = .ok (.yield ⟨⟩,
        (counts.set! bucket (wrapInt .i64 ((slot : Int) + 2)),
          permutation.set! slot i.val)) := by
  have hfits : IntTy.min .i64 ≤ (slot : Int) + 1 ∧
      (slot : Int) + 1 ≤ IntTy.max .i64 := by
    have hmin : IntTy.min .i64 < 0 := by decide
    constructor <;> omega
  have htarget : (JuliaLean.base.int.lit .i64
      (wrapInt .i64 ((slot : Int) + 1))).val = (slot : Int) + 1 := by
    rw [lit_val, wrapInt_wrapInt, wrapInt_of_inRange .i64 _ hfits]
  let label := JuliaLean.base.int.addWrap (JuliaLean.base.int.lit .i64 value) offsets
  let counter := wrapInt .i64 ((slot : Int) + 1)
  let nextPermutation := permutation.set! slot i.val
  have hget : ∀ p : Array Int, (arraySortpermRangeOps.getCount () label).run (counts, p) =
      .ok (JuliaLean.base.int.lit .i64 counter, (counts, p)) := by
    intro p
    change (arrayRead counts label.val >>= fun v =>
      .ok (JuliaLean.base.int.lit .i64 v, (counts, p))) = _
    dsimp only [label]
    rw [hlabel, group20_sp_read counts bucket _ hcount] <;> rfl
  have hsetPermutation : (arraySortpermRangeOps.setPermutation ()
      (JuliaLean.base.int.lit .i64 counter) i).run (counts, permutation) =
      .ok ((), (counts, nextPermutation)) := by
    change (arrayWrite permutation (JuliaLean.base.int.lit .i64 counter).val i.val >>= fun p =>
      .ok ((), (counts, p))) = _
    dsimp only [counter]
    rw [htarget, group20_sp_write permutation slot i.val hslot] <;> rfl
  have hsetCount : (arraySortpermRangeOps.setCount () label
      (JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 counter)
        (JuliaLean.base.int.lit .i64 1))).run (counts, nextPermutation) =
      .ok ((), (counts.set! bucket (wrapInt .i64 ((slot : Int) + 2)), nextPermutation)) := by
    change (arrayWrite counts label.val
      (JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 counter)
        (JuliaLean.base.int.lit .i64 1)).val >>= fun c =>
      .ok ((), (c, nextPermutation))) = _
    dsimp only [label]
    rw [hlabel, group20_sp_increment_val]
    dsimp only [counter]
    rw [wrapInt_add_left,
      show ((slot : Int) + 1) + 1 = (slot : Int) + 2 by omega,
      group20_sp_write counts bucket _ hbucket] <;> rfl
  unfold sp_body3
  rw [group20_sp_bind_run,
    group20_sp_input_read_run values i value hread counts permutation,
    g11_sp_except_ok_bind]
  change ((arraySortpermRangeOps.getCount () label >>= fun target => do
      arraySortpermRangeOps.setPermutation () target i
      let count ← arraySortpermRangeOps.getCount () label
      arraySortpermRangeOps.setCount () label
        (JuliaLean.base.int.add count (JuliaLean.base.int.lit .i64 1))
      pure (ForInStep.yield (⟨⟩ : PUnit))).run (counts, permutation)) = _
  rw [group20_sp_bind_run, hget permutation, g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hsetPermutation, g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hget nextPermutation, g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hsetCount, g11_sp_except_ok_bind, group20_sp_pure_run] <;> rfl

/-- Stable counting slots themselves form a permutation of all available slots. -/
theorem g11_sp_slots_perm {T : Type} (rank : T → Int) (xs : List T) :
    ((List.range xs.length).map (sp_pos rank xs)).Perm (List.range xs.length) := by
  have hnd : ((List.range xs.length).map (sp_pos rank xs)).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.nodup_range
    intro a b ha hb hab
    exact sp_pos_ne rank xs a b (List.mem_range.1 ha) (List.mem_range.1 hb) hab
  apply group20_sp_perm_of_nodup _ _ hnd List.nodup_range
  intro p
  constructor
  · intro hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
    exact List.mem_range.2 (sp_pos_lt rank xs j (List.mem_range.1 hj))
  · intro hp
    obtain ⟨j, hj, heq⟩ := sp_pos_surj rank xs p (List.mem_range.1 hp)
    exact List.mem_map.2 ⟨j, List.mem_range.2 hj, heq⟩

/-- A placement at every stable counting slot yields a permutation of source indices. -/
theorem g11_sp_placement_permutation {T : Type} (rank : T → Int) (xs : List T)
    (permutation : Array Int) (hsize : permutation.size = xs.length)
    (hslots : ∀ j, j < xs.length →
      permutation[sp_pos rank xs j]? = some ((j : Int) + 1)) :
    List.Perm (oneBasedIndices xs.length) (permutation.toList.map Int.toNat) := by
  let read : Nat → Int := fun k => (permutation[k]?).getD (0 : Int)
  have hperm := (g11_sp_slots_perm rank xs).map read
  have hleft : (((List.range xs.length).map (sp_pos rank xs)).map read) =
      (List.range xs.length).map (fun j : Nat => (j : Int) + 1) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply, read, hslots j (List.mem_range.1 hj), Option.getD_some]
  have hright : (List.range xs.length).map read = permutation.toList := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, Array.length_toList, hsize]
    · intro j hj hj'
      simp only [List.getElem_map, List.getElem_range, read]
      have hlt : j < permutation.size := by
        simpa only [Array.length_toList] using hj'
      simp only [Array.getElem?_eq_getElem hlt, Option.getD_some, Array.getElem_toList]
  rw [hleft, hright] at hperm
  have hnat := hperm.map Int.toNat
  have hindices : ((List.range xs.length).map (fun j : Nat => (j : Int) + 1)).map
      Int.toNat = oneBasedIndices xs.length := by
    rw [List.map_map]
    unfold oneBasedIndices
    apply List.map_congr_left
    intro j hj
    change ((j : Int) + 1).toNat = j + 1
    omega
  rw [hindices] at hnat
  exact hnat

/-- Stable slot placement also proves the documented order and tie-breaking rule. -/
theorem g11_sp_placement_ordered {T : Type} (rank : T → Int) (xs : List T)
    (permutation : Array Int) (hsize : permutation.size = xs.length)
    (hslots : ∀ j, j < xs.length →
      permutation[sp_pos rank xs j]? = some ((j : Int) + 1)) :
    SortpermOrdered (fun a b => decide (rank a < rank b)) xs
      (permutation.toList.map Int.toNat) := by
  intro i j leftIndex rightIndex leftValue rightValue hij hleft hright hleftValue hrightValue
  rw [List.getElem?_map] at hleft hright
  obtain ⟨left, hleftRaw, hleftNat⟩ := Option.map_eq_some_iff.1 hleft
  obtain ⟨right, hrightRaw, hrightNat⟩ := Option.map_eq_some_iff.1 hright
  subst leftIndex
  subst rightIndex
  have hleftArray : permutation[i]? = some left := by
    simpa only [Array.getElem?_toList] using hleftRaw
  have hrightArray : permutation[j]? = some right := by
    simpa only [Array.getElem?_toList] using hrightRaw
  have hi : i < xs.length := by
    apply Classical.byContradiction
    intro h
    rw [List.getElem?_eq_none (by simp only [Array.length_toList]; omega)] at hleftRaw
    cases hleftRaw
  have hj : j < xs.length := by
    apply Classical.byContradiction
    intro h
    rw [List.getElem?_eq_none (by simp only [Array.length_toList]; omega)] at hrightRaw
    cases hrightRaw
  obtain ⟨sourceLeft, hsourceLeft, hposLeft⟩ := sp_pos_surj rank xs i hi
  obtain ⟨sourceRight, hsourceRight, hposRight⟩ := sp_pos_surj rank xs j hj
  have hleftInt : left = (sourceLeft : Int) + 1 := by
    have h := hslots sourceLeft hsourceLeft
    rw [hposLeft, hleftArray] at h
    exact Option.some.inj h
  have hrightInt : right = (sourceRight : Int) + 1 := by
    have h := hslots sourceRight hsourceRight
    rw [hposRight, hrightArray] at h
    exact Option.some.inj h
  have hleftSource : xs[sourceLeft]? = some leftValue := by
    simpa only [hleftInt,
      show ((sourceLeft : Int) + 1).toNat - 1 = sourceLeft by omega] using hleftValue
  have hrightSource : xs[sourceRight]? = some rightValue := by
    simpa only [hrightInt,
      show ((sourceRight : Int) + 1).toNat - 1 = sourceRight by omega] using hrightValue
  have hnot : ¬ rank rightValue < rank leftValue := by
    intro h
    have hpos := sp_pos_lt_of_rank rank xs sourceRight sourceLeft rightValue leftValue
      hrightSource hleftSource (Or.inl h)
    rw [hposLeft, hposRight] at hpos
    omega
  refine ⟨by simpa only [decide_eq_false_iff_not] using hnot, ?_⟩
  intro htie
  have hnotOther : ¬ rank leftValue < rank rightValue := by
    simpa only [decide_eq_false_iff_not] using htie.1
  have hequal : rank leftValue = rank rightValue := by omega
  have hsourceNe : sourceLeft ≠ sourceRight := by
    intro h
    rw [h] at hposLeft
    omega
  have hsourceLt : sourceLeft < sourceRight := by
    apply Classical.byContradiction
    intro h
    have hlt : sourceRight < sourceLeft := by omega
    have hpos := sp_pos_lt_of_rank rank xs sourceRight sourceLeft rightValue leftValue
      hrightSource hleftSource (Or.inr ⟨hequal.symm, hlt⟩)
    rw [hposLeft, hposRight] at hpos
    omega
  rw [hleftInt, hrightInt]
  omega

theorem g11_sp_items_indices (xs : List Int) : ∀ start,
    (group20_sp_items start xs).map Prod.fst = group20_sp_indexList start xs.length := by
  induction xs with
  | nil => intro start; rfl
  | cons x xs ih =>
      intro start
      rw [group20_sp_items, List.map_cons, List.length_cons, g11_sp_indexList_succ,
        ih]

theorem g11_sp_items_count (xs : List Int) (start : Nat) (p : Int → Bool) :
    (group20_sp_items start xs).countP (fun item => p item.2) = xs.countP p := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
      simp only [group20_sp_items, List.countP_cons, ih]

theorem g11_sp_lit_nat_val (n : Nat) (h : (n : Int) ≤ IntTy.max .i64) :
    (JuliaLean.base.int.lit .i64 (Int.ofNat n)).val = (n : Int) := by
  rw [lit_val, Int.ofNat_eq_natCast]
  apply wrapInt_of_inRange
  constructor
  · have : IntTy.min .i64 < 0 := by decide
    omega
  · exact h

/-- Enumerated input reads are all valid, including near the representable bound. -/
theorem g11_sp_items_read (values : Array Int)
    (hbound : (values.size : Int) ≤ IntTy.max .i64) :
    ∀ (xs before : List Int), values.toList = before ++ xs →
      ∀ item, item ∈ group20_sp_items before.length xs →
        arrayRead values item.1.val = .ok item.2
  | [], before, _, item, hitem => by cases hitem
  | x :: xs, before, hvalues, item, hitem => by
      rw [group20_sp_items] at hitem
      rcases List.mem_cons.1 hitem with heq | htail
      · subst item
        have hlen : before.length + 1 ≤ values.size := by
          have := congrArg List.length hvalues
          simp only [Array.length_toList, List.length_append, List.length_cons] at this
          omega
        rw [g11_sp_lit_nat_val (before.length + 1) (by omega)]
        exact storage_read_mid arrayStorage_laws hvalues (by omega) (by omega)
      · have hnext : values.toList = (before ++ [x]) ++ xs := by
          rw [hvalues]
          simp only [List.append_assoc, List.singleton_append]
        apply g11_sp_items_read values hbound xs (before ++ [x]) hnext item
        simpa only [List.length_append, List.length_singleton] using htail

/-- Histogram phase instantiated for the source's actual integer array reads. -/
theorem g11_sp_histogram_values (values : Array Int) (minimum : Int) (m : Nat)
    (hsize : (values.size : Int) ≤ IntTy.max .i64)
    (hcounts : ((m + 1 : Nat) : Int) ≤ IntTy.max .i64)
    (hvalues : ∀ x, x ∈ values.toList → minimum ≤ x ∧ x < minimum + (m : Int)) :
    let offsets := JuliaLean.base.int.subWrap (JuliaLean.base.int.lit .i64 1)
      (JuliaLean.base.int.lit .i64 minimum)
    let initial := (Array.replicate (m + 1) (0 : Int)).set! 0 1
    ∃ counts,
      (forIn (group20_sp_indexList 0 values.size) ⟨⟩
        (sp_body1 arraySortpermRangeOps values offsets ())).run (initial, #[]) =
        .ok (⟨⟩, (counts, #[])) ∧ counts.size = m + 1 ∧
      ∀ k, k < m + 1 → counts[k]? = some (wrapInt .i64
        (if k < 1 then group20_sp_start values.toList minimum k
          else group20_sp_raw values.toList minimum k)) := by
  let offsets := JuliaLean.base.int.subWrap (JuliaLean.base.int.lit .i64 1)
    (JuliaLean.base.int.lit .i64 minimum)
  let initial := (Array.replicate (m + 1) (0 : Int)).set! 0 1
  let bucket := fun x : Int => (x - minimum + 1).toNat
  let seed := fun k : Nat => if k = 0 then (1 : Int) else 0
  have hinitialSize : initial.size = m + 1 := by simp [initial]
  have hinitial : ∀ k, k < m + 1 → initial[k]? = some (wrapInt .i64 (seed k)) := by
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp [initial, seed, wrapInt, IntTy.signed, IntTy.bits]
    · have h0k : 0 ≠ k := Ne.symm hk0
      simp only [initial, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne h0k]
      simp [seed, hk0, hk, wrapInt, IntTy.signed, IntTy.bits]
  have hitems : ∀ item, item ∈ group20_sp_items 0 values.toList →
      arrayRead values item.1.val = .ok item.2 ∧
      (JuliaLean.base.int.addWrap
        (JuliaLean.base.int.addWrap (JuliaLean.base.int.lit .i64 item.2) offsets)
        (JuliaLean.base.int.lit .i64 1)).val = (bucket item.2 : Int) + 1 ∧
      bucket item.2 < m + 1 := by
    intro item hitem
    have hmem : item.2 ∈ values.toList := by
      have h : item.2 ∈ (group20_sp_items 0 values.toList).map Prod.snd :=
        List.mem_map.2 ⟨item, hitem, rfl⟩
      rw [group20_sp_items_values values.toList 0] at h
      exact h
    obtain ⟨hmin, hmax⟩ := hvalues item.2 hmem
    refine ⟨g11_sp_items_read values hsize values.toList []
      (by simp only [List.nil_append]) item hitem, ?_, ?_⟩
    · dsimp only [offsets]
      rw [group20_sp_bucket_val, wrapInt_of_inRange]
      · dsimp only [bucket]
        omega
      · constructor
        · have : IntTy.min .i64 < 0 := by decide
          omega
        · omega
    · dsimp only [bucket]
      omega
  obtain ⟨counts, hrun, hcountSize, hcountValues⟩ :=
    g11_sp_histogram_loop values offsets bucket (m + 1)
      (group20_sp_items 0 values.toList) initial #[] seed hinitialSize hinitial hitems
  refine ⟨counts, ?_, hcountSize, ?_⟩
  · simpa only [g11_sp_items_indices, Array.length_toList] using hrun
  · intro k hk
    rw [hcountValues k hk,
      g11_sp_items_count values.toList 0 (fun x => bucket x == k)]
    by_cases hk0 : k = 0
    · subst k
      have hzero : values.toList.countP (fun x => bucket x == 0) = 0 := by
        apply group20_sp_count_zero
        intro x hx
        have hmin := (hvalues x hx).1
        simp only [beq_eq_false_iff_ne, bucket]
        omega
      have hminzero : values.toList.countP (fun x => decide (x < minimum)) = 0 := by
        apply group20_sp_count_zero
        intro x hx
        simp only [decide_eq_false_iff_not]
        exact Int.not_lt.mpr (hvalues x hx).1
      simp only [seed, ite_true, hzero, Int.natCast_zero, Int.add_zero,
        group20_sp_start, Nat.zero_lt_succ, hminzero]
    · have hcountEq : values.toList.countP (fun x => bucket x == k) =
          values.toList.countP (fun x => decide (x = minimum + (k : Int) - 1)) := by
        apply group20_sp_count_congr
        intro x hx
        have hmin := (hvalues x hx).1
        rw [Bool.eq_iff_iff]
        simp only [beq_iff_eq, decide_eq_true_eq, bucket]
        omega
      simp only [seed, hk0, ite_false, Int.zero_add, hcountEq,
        if_neg (by omega : ¬ k < 1), group20_sp_raw]

/-- Placement phase instantiated with the documented stable counting slots. -/
theorem g11_sp_placement_values (values : Array Int) (minimum : Int) (m : Nat)
    (hsize : (values.size : Int) ≤ IntTy.max .i64)
    (hcountsBound : ((m + 1 : Nat) : Int) ≤ IntTy.max .i64)
    (hvalues : ∀ x, x ∈ values.toList → minimum ≤ x ∧ x < minimum + (m : Int)) :
    ∀ (remaining processed : List Int) (counts permutation : Array Int),
      values.toList = processed ++ remaining → counts.size = m + 1 →
      permutation.size = values.size →
      (∀ k, k < m + 1 → counts[k]? = some (wrapInt .i64
        (group20_sp_start values.toList minimum k +
          (processed.countP (fun x => decide (x = minimum + (k : Int))) : Int)))) →
      (∀ j, j < processed.length → permutation[sp_pos id values.toList j]? =
        some ((j : Int) + 1)) →
      ∃ finalCounts finalPermutation,
        (forIn (group20_sp_indexList processed.length remaining.length) ⟨⟩
          (sp_body3 arraySortpermRangeOps values
            (JuliaLean.base.int.subWrap (JuliaLean.base.int.lit .i64 1)
              (JuliaLean.base.int.lit .i64 minimum)) () ())).run
            (counts, permutation) = .ok (⟨⟩, (finalCounts, finalPermutation)) ∧
        finalPermutation.size = values.size ∧
        ∀ j, j < values.size → finalPermutation[sp_pos id values.toList j]? =
          some ((j : Int) + 1)
  | [], processed, counts, permutation, hall, hcs, hps, hc, hp => by
      have hlen : processed.length = values.size := by
        have h := congrArg List.length hall
        simp only [Array.length_toList, List.append_nil] at h
        exact h.symm
      exact ⟨counts, permutation, rfl, hps, fun j hj => hp j (by omega)⟩
  | x :: remaining, processed, counts, permutation, hall, hcs, hps, hc, hp => by
      let offsets := JuliaLean.base.int.subWrap (JuliaLean.base.int.lit .i64 1)
        (JuliaLean.base.int.lit .i64 minimum)
      let index := JuliaLean.base.int.lit .i64 (Int.ofNat (processed.length + 1))
      let k := (x - minimum).toNat
      let slot := sp_pos id values.toList processed.length
      have hxmem : x ∈ values.toList := by
        rw [hall]
        exact List.mem_append_right _ List.mem_cons_self
      obtain ⟨hmin, hmax⟩ := hvalues x hxmem
      have hlen : processed.length < values.size := by
        have h := congrArg List.length hall
        simp only [Array.length_toList, List.length_append, List.length_cons] at h
        omega
      have hindex : index.val = (processed.length : Int) + 1 := by
        dsimp only [index]
        simpa only [Int.natCast_add, Int.natCast_one] using
          g11_sp_lit_nat_val (processed.length + 1) (by omega)
      have hread : arrayRead values index.val = .ok x := by
        rw [hindex]
        exact storage_read_mid arrayStorage_laws hall (by omega) (by omega)
      have hxk : minimum + (k : Int) = x := by dsimp only [k]; omega
      have hk : k < m + 1 := by dsimp only [k]; omega
      have hlabel : (JuliaLean.base.int.addWrap
          (JuliaLean.base.int.lit .i64 x) offsets).val = (k : Int) + 1 := by
        dsimp only [offsets]
        rw [group20_sp_label_val, wrapInt_of_inRange]
        · omega
        · constructor
          · have : IntTy.min .i64 < 0 := by decide
            omega
          · omega
      have hxget : values.toList[processed.length]? = some x := by
        rw [hall, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero]
      have htake : values.toList.take processed.length = processed := by
        rw [hall]
        simp
      have hslot : slot < values.size := by
        exact sp_pos_lt id values.toList processed.length (by
          simpa only [Array.length_toList] using hlen)
      have hslotEq : slot = values.toList.countP (fun y => decide (y < x)) +
          processed.countP (fun y => decide (y = x)) := by
        simp only [slot, sp_pos, hxget, htake, id_eq]
      have hcursor : group20_sp_start values.toList minimum k +
          (processed.countP (fun y => decide (y = minimum + (k : Int))) : Int) =
          (slot : Int) + 1 := by
        unfold group20_sp_start
        rw [hxk, hslotEq]
        simp only [Int.natCast_add]
        omega
      have hcount : counts[k]? = some (wrapInt .i64 ((slot : Int) + 1)) := by
        rw [hc k hk, hcursor]
      let nextCounts := counts.set! k (wrapInt .i64 ((slot : Int) + 2))
      let nextPermutation := permutation.set! slot ((processed.length : Int) + 1)
      have hstep : (sp_body3 arraySortpermRangeOps values offsets () () index ⟨⟩).run
          (counts, permutation) = .ok (.yield ⟨⟩, (nextCounts, nextPermutation)) := by
        simpa only [hindex, nextCounts, nextPermutation] using
          g11_sp_placement_step values counts permutation offsets index x k slot
            hread hlabel hcount (by omega) (by omega) (by omega)
      have hncs : nextCounts.size = m + 1 := by simpa [nextCounts] using hcs
      have hnps : nextPermutation.size = values.size := by simpa [nextPermutation] using hps
      have hnc : ∀ j, j < m + 1 → nextCounts[j]? = some (wrapInt .i64
          (group20_sp_start values.toList minimum j +
            ((processed ++ [x]).countP (fun y => decide (y = minimum + (j : Int))) : Int))) := by
        intro j hj
        simp only [nextCounts, Array.set!_eq_setIfInBounds]
        by_cases hkj : k = j
        · subst j
          rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)]
          apply congrArg (fun z : Int => some (wrapInt .i64 z))
          simp only [List.countP_append, List.countP_cons, hxk, eq_self, decide_true,
            ite_true, List.countP_nil, Nat.zero_add, Int.natCast_add, Int.natCast_one]
          rw [hxk] at hcursor
          omega
        · rw [Array.getElem?_setIfInBounds_ne hkj, hc j hj]
          have hxne : x ≠ minimum + (j : Int) := by intro h; omega
          simp only [List.countP_append, List.countP_cons, hxne, decide_false,
            Bool.false_eq_true, ite_false, List.countP_nil, Nat.add_zero]
      have hnp : ∀ j, j < (processed ++ [x]).length →
          nextPermutation[sp_pos id values.toList j]? = some ((j : Int) + 1) := by
        intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        simp only [nextPermutation, Array.set!_eq_setIfInBounds]
        by_cases hjp : j = processed.length
        · subst j
          rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)]
        · have hjlt : j < processed.length := by omega
          have hne : slot ≠ sp_pos id values.toList j :=
            sp_pos_ne id values.toList processed.length j
              (by simpa only [Array.length_toList] using hlen)
              (by simp only [Array.length_toList]; omega) (by omega)
          rw [Array.getElem?_setIfInBounds_ne hne]
          exact hp j hjlt
      obtain ⟨finalCounts, finalPermutation, hloop, hfsize, hfslots⟩ :=
        g11_sp_placement_values values minimum m hsize hcountsBound hvalues remaining
          (processed ++ [x]) nextCounts nextPermutation
          (by rw [hall]; simp only [List.append_assoc, List.singleton_append]) hncs hnps hnc hnp
      refine ⟨finalCounts, finalPermutation, ?_, hfsize, hfslots⟩
      rw [List.length_cons, g11_sp_indexList_succ,
        group20_sp_forIn_cons _ _ _ _ _ _ _ hstep]
      simpa only [List.length_append, List.length_singleton] using hloop

theorem g11_sp_range_eq (start length : Nat) :
    ((arrayIndexRange (Int.ofNat (start + 1)) (Int.ofNat (start + length))).map
      (JuliaLean.base.int.lit .i64)) = group20_sp_indexList start length := by
  unfold arrayIndexRange group20_sp_indexList
  have hlength :
      (Int.ofNat (start + length) - Int.ofNat (start + 1) + 1).toNat = length := by
    simp only [Int.ofNat_eq_natCast]
    omega
  rw [hlength, List.map_map]
  apply List.map_congr_left
  intro offset _
  simp only [Function.comp_apply]
  apply congrArg (JuliaLean.base.int.lit .i64)
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Allocation equations keep the machine-integer argument symbolic. -/
theorem g11_sp_allocateCounts_run (n : I) (counts permutation : Array Int) :
    (arraySortpermRangeOps.allocateCounts n).run (counts, permutation) =
      if 0 ≤ n.val then
        .ok ((), (Array.replicate n.val.toNat (0 : Int), permutation))
      else .error JlError.boundsError := rfl

theorem g11_sp_allocatePermutation_run (n : I) (counts permutation : Array Int) :
    (arraySortpermRangeOps.allocatePermutation n).run (counts, permutation) =
      if 0 ≤ n.val then
        .ok ((), (counts, Array.replicate n.val.toNat (0 : Int)))
      else .error JlError.boundsError := rfl

theorem g11_sp_range_run (lo hi : I) (state : Array Int × Array Int) :
    (arraySortpermRangeOps.range lo hi).run state =
      .ok ((arrayIndexRange lo.val hi.val).map (JuliaLean.base.int.lit .i64), state) := rfl

theorem g11_sp_array_kernel (values : Array Int) (minimum : Int) (m : Nat)
    (hsize : (values.size : Int) ≤ IntTy.max .i64)
    (hcountsBound : ((m + 1 : Nat) : Int) ≤ IntTy.max .i64)
    (hvalues : ∀ x, x ∈ values.toList → minimum ≤ x ∧ x < minimum + (m : Int)) :
    ∃ counts permutation,
      (sortpermIntRange arraySortpermRangeOps values
        (JuliaLean.base.int.lit .i64 (m : Int))
        (JuliaLean.base.int.lit .i64 minimum)).run (#[], #[]) =
        .ok ((), (counts, permutation)) ∧
      permutation.size = values.size ∧
      ∀ j, j < values.size → permutation[sp_pos id values.toList j]? =
        some ((j : Int) + 1) := by
  let offsets := JuliaLean.base.int.subWrap (JuliaLean.base.int.lit .i64 1)
    (JuliaLean.base.int.lit .i64 minimum)
  let initial := (Array.replicate (m + 1) (0 : Int)).set! 0 1
  obtain ⟨counts1, hhist, hsize1, hcounts1⟩ :=
    g11_sp_histogram_values values minimum m hsize hcountsBound hvalues
  obtain ⟨counts2, hprefix, hsize2, hcounts2⟩ :=
    g11_sp_prefix_loop (group20_sp_raw values.toList minimum)
      (group20_sp_start values.toList minimum)
      (group20_sp_start_rec values.toList minimum) m 1 counts1 #[]
      (by omega) (by omega) (by omega)
      (fun k hk => hcounts1 k (by omega))
  let permutation0 := Array.replicate values.size (0 : Int)
  obtain ⟨counts3, permutation3, hplace, hsize3, hslots3⟩ :=
    g11_sp_placement_values values minimum m hsize hcountsBound hvalues
      values.toList [] counts2 permutation0 (by simp only [List.nil_append])
      (by omega) (by simp [permutation0])
      (by
        intro k hk
        simpa only [List.countP_nil, Int.natCast_zero, Int.add_zero] using
          hcounts2 k (by omega))
      (by intro j hj; simp only [List.length_nil] at hj; omega)
  refine ⟨counts3, permutation3, ?_, hsize3, hslots3⟩
  have hlen : (JuliaLean.base.int.lit .i64 (Int.ofNat values.size)).val =
      (values.size : Int) := g11_sp_lit_nat_val values.size hsize
  have hm : (JuliaLean.base.int.lit .i64 (m : Int)).val = (m : Int) :=
    g11_sp_lit_nat_val m (by omega)
  have hadd : (JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 (m : Int))
      (JuliaLean.base.int.lit .i64 1)).val = (m : Int) + 1 := by
    rw [group20_sp_increment_val]
    apply wrapInt_of_inRange
    have hmin : IntTy.min .i64 < 0 := by decide
    constructor <;> omega
  have hone : (JuliaLean.base.int.lit .i64 1).val = 1 := by decide
  have htwo : (JuliaLean.base.int.lit .i64 2).val = 2 := by decide
  have hwrite : arrayWrite (Array.replicate (m + 1) (0 : Int)) 1 1 = .ok initial := by
    simpa only [Int.natCast_zero, Int.zero_add] using
      group20_sp_write (Array.replicate (m + 1) (0 : Int)) 0 1 (by simp)
  have hcountLength : (JuliaLean.base.int.lit .i64 (Int.ofNat counts1.size)).val =
      Int.ofNat (1 + m) := by
    rw [hsize1, g11_sp_lit_nat_val _ hcountsBound]
    simp only [Int.ofNat_eq_natCast]
    omega
  have hrange1 : ((arrayIndexRange 1 (values.size : Int)).map
      (JuliaLean.base.int.lit .i64)) = group20_sp_indexList 0 values.size := by
    simpa only [Nat.zero_add, Int.ofNat_eq_natCast, Int.natCast_one] using
      g11_sp_range_eq 0 values.size
  have hrange2 : ((arrayIndexRange 2 (Int.ofNat (1 + m))).map
      (JuliaLean.base.int.lit .i64)) = group20_sp_indexList 1 m :=
    g11_sp_range_eq 1 m
  have hlengthRun : ∀ state : Array Int × Array Int,
      (arraySortpermRangeOps.length values).run state =
        .ok (JuliaLean.base.int.lit .i64 (Int.ofNat values.size), state) := by
    intro state
    rfl
  have hallocateCounts : (arraySortpermRangeOps.allocateCounts
      (JuliaLean.base.int.add (JuliaLean.base.int.lit .i64 (m : Int))
        (JuliaLean.base.int.lit .i64 1))).run (#[], #[]) =
      .ok ((), (Array.replicate (m + 1) (0 : Int), #[])) := by
    rw [g11_sp_allocateCounts_run, hadd]
    exact if_pos (Int.natCast_nonneg (m + 1))
  have hsetFirst : (arraySortpermRangeOps.setCount () (JuliaLean.base.int.lit .i64 1)
      (JuliaLean.base.int.lit .i64 1)).run
        (Array.replicate (m + 1) (0 : Int), #[]) = .ok ((), (initial, #[])) := by
    change (arrayWrite (Array.replicate (m + 1) (0 : Int))
      (JuliaLean.base.int.lit .i64 1).val (JuliaLean.base.int.lit .i64 1).val >>= fun c =>
      .ok ((), (c, #[]))) = _
    rw [hone, hwrite] <;> rfl
  have hrange1Run : ∀ state : Array Int × Array Int,
      (arraySortpermRangeOps.range (JuliaLean.base.int.lit .i64 1)
        (JuliaLean.base.int.lit .i64 (Int.ofNat values.size))).run state =
      .ok (group20_sp_indexList 0 values.size, state) := by
    intro state
    rw [g11_sp_range_run, hone, hlen, hrange1]
  have hcountLengthRun : (arraySortpermRangeOps.countLength ()).run (counts1, #[]) =
      .ok (JuliaLean.base.int.lit .i64 (Int.ofNat counts1.size), (counts1, #[])) := rfl
  have hrange2Run : (arraySortpermRangeOps.range (JuliaLean.base.int.lit .i64 2)
      (JuliaLean.base.int.lit .i64 (Int.ofNat counts1.size))).run (counts1, #[]) =
      .ok (group20_sp_indexList 1 m, (counts1, #[])) := by
    rw [g11_sp_range_run, htwo, hcountLength, hrange2]
  have hallocatePermutation : (arraySortpermRangeOps.allocatePermutation
      (JuliaLean.base.int.lit .i64 (Int.ofNat values.size))).run (counts2, #[]) =
      .ok ((), (counts2, permutation0)) := by
    rw [g11_sp_allocatePermutation_run, hlen]
    simp only [Int.natCast_nonneg, ite_true, Int.toNat_natCast, permutation0]
  simp only [Array.length_toList, List.length_nil] at hplace
  dsimp only [initial] at hsetFirst
  rw [sp_unfold]
  rw [group20_sp_bind_run, hlengthRun (#[], #[]), g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hallocateCounts, g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hsetFirst, g11_sp_except_ok_bind]
  rw [group20_sp_bind_run,
    hrange1Run ((Array.replicate (m + 1) (0 : Int)).set! 0 1, #[]),
    g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hhist, g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hcountLengthRun, g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hrange2Run, g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hprefix, g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hallocatePermutation, g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hrange1Run (counts2, permutation0), g11_sp_except_ok_bind]
  rw [group20_sp_bind_run, hplace, g11_sp_except_ok_bind, group20_sp_pure_run]


end JuliaLean.ChatGPT.Batch8.Group11

namespace JuliaLean.ChatGPT.Batch8.Group11
open JuliaLean.ChatGPT.Batch4.Group20
open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

theorem g11_sortpermArrayContract : Group20SortpermArrayContract := by
  intro values minimum m hsize hcounts hvalues
  obtain ⟨counts, permutation, hrun, hpermutationSize, hslots⟩ :=
    g11_sp_array_kernel values minimum m hsize hcounts hvalues
  refine ⟨counts, permutation, hrun, ?_, ?_⟩
  · simpa only [Array.length_toList] using
      g11_sp_placement_permutation id values.toList permutation
        (by simpa only [Array.length_toList] using hpermutationSize)
        (by simpa only [Array.length_toList] using hslots)
  · simpa only [id_eq] using
      g11_sp_placement_ordered id values.toList permutation
        (by simpa only [Array.length_toList] using hpermutationSize)
        (by simpa only [Array.length_toList] using hslots)

end JuliaLean.ChatGPT.Batch8.Group11

end
namespace JuliaLean.ChatGPT.Batch8.Group10

open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort


/-- A trace of `LinRange(-1e308, 1e308, 3)` searched for `9e307`.
The constructors name the values used in that public Julia execution. -/
inductive SearchFloatCase where
  | negative | zero | query | positive | infinity | notANumber
  deriving DecidableEq

/-- A separate quotient domain keeps the finite-rounding premise meaningful:
`finiteTwo` denotes the exactly representable number 2.  The reproduced execution
visits only `infinity` and then `notANumber`.  This is a trace model, rather than
an implementation of floating arithmetic on arbitrary inputs. -/
inductive SearchFloatQuotient where
  | finiteTwo | infinity | notANumber
  deriving DecidableEq

def searchFloatFinite : SearchFloatCase → Bool
  | .infinity | .notANumber => false
  | _ => true

def searchFloatQuotientFinite : SearchFloatQuotient → Bool
  | .finiteTwo => true
  | .infinity | .notANumber => false

def searchFloatRank : SearchFloatCase → Nat
  | .negative => 0
  | .zero => 1
  | .query => 2
  | .positive => 3
  | .infinity => 4
  | .notANumber => 5

def searchFloatLess (_ : Unit) (a b : SearchFloatCase) : Jl Bool :=
  .ok (decide (searchFloatRank a < searchFloatRank b))

def searchFloatValues : List SearchFloatCase := [.negative, .zero, .positive]

def searchFloatElement (_ _ : SearchFloatCase) : Nat → SearchFloatCase
  | 0 => .negative
  | 1 => .zero
  | _ => .positive

def searchFloatOperations :
    RealRangeOps Unit SearchFloatCase SearchFloatCase SearchFloatQuotient Int Unit JlError where
  requireOneBased := fun _ => .ok ()
  first := fun _ => .negative
  step := fun _ => .infinity
  last := fun _ => .positive
  length := fun _ => 3
  zeroIndex := 0
  oneIndex := 1
  increment := (· + 1)
  decrement := (· - 1)
  isZero := fun a => decide (a = .zero)
  subtract := fun a b =>
    match a, b with
    | .query, .negative => .infinity
    | .positive, .negative => .infinity
    | _, _ => .finiteTwo
  divide := fun a b =>
    if a = .infinity ∧ b = .infinity then .notANumber
    else if a = .infinity then .infinity else .finiteTwo
  addOne := id
  roundInteger := fun a =>
    match a with
    | .finiteTwo => .ok 2
    | .infinity | .notANumber => .error (.inexactError "Int64")
  get := fun _ i =>
    match searchFloatValues[(i - 1).toNat]? with
    | some v => .ok v
    | none => .error .boundsError
  finiteSearch := fun _ x =>
    searchFloatValues.all searchFloatFinite = true ∧ searchFloatFinite x = true

theorem searchFloatFaithful :
    RealRangeOpsFaithful searchFloatOperations () .query searchFloatValues
      searchFloatElement (fun _ _ => .negative) (fun a => decide (a = .zero))
      searchFloatFinite searchFloatFinite searchFloatQuotientFinite := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, ?_, Iff.rfl, ?_⟩
  · intro i
    exact ⟨rfl, rfl⟩
  · intro i hi hj
    change i ≤ 3 at hj
    have hc : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hc with rfl | rfl | rfl
    · exact ⟨.negative, rfl, rfl⟩
    · exact ⟨.zero, rfl, rfl⟩
    · exact ⟨.positive, rfl, rfl⟩
  · intro q hq
    cases q <;> first | exact ⟨2, rfl⟩ | cases hq

theorem searchFloatPredicates :
    RealRangeSearchPredicatesSorted searchFloatValues searchFloatLess searchFloatLess () .query := by
  intro i j left right hij hl hr
  have hi : i < 3 := by
    obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hl
    simpa only [searchFloatValues, List.length_cons, List.length_nil] using hbound
  have hj : j < 3 := by
    obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hr
    simpa only [searchFloatValues, List.length_cons, List.length_nil] using hbound
  have hci : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hcj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hci with rfl | rfl | rfl <;> rcases hcj with rfl | rfl | rfl <;>
    simp only [searchFloatValues, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.some.injEq] at hl hr <;>
    subst left <;> subst right <;> first | omega | decide

theorem SorttuplescovFloatRangeSearchOverflow_refuted :
    ¬ JuliaLean.Proofs.base.sort.FloatRangeSearchNoThrow := by
  intro h
  obtain ⟨first, last, hfirst, _, _⟩ :=
    h Unit SearchFloatCase SearchFloatCase SearchFloatQuotient Unit searchFloatOperations
      searchFloatLess searchFloatLess searchFloatLess () () .query searchFloatValues
      searchFloatElement (fun _ _ => .negative) (fun a => decide (a = .zero))
      searchFloatFinite searchFloatFinite searchFloatQuotientFinite searchFloatFaithful
      (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl, True.intro⟩) searchFloatPredicates
  change (Except.error (JlError.inexactError "Int64") : Jl Int) = .ok first at hfirst
  cases hfirst




open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

open JuliaLean JuliaLean.base.sort JuliaLean.Proofs.base.sort

/-- A successful base-sort computation remains successful in its option wrapper. -/
theorem windowLiftOk {E A : Type} (value : A) :
    (JuliaLean.base.sort.liftExcept (E := E) (.ok value)).run = some (.ok value) := rfl

/-- Finite index windows terminate whenever both reads at every visited index succeed. -/
theorem indexWindowLoopTerminates {V α K E : Type}
    (indices : IntegerIndexOps K) (checkBounds : V → K → K → Except E Unit)
    (get : V → K → Except E α) (values : V) (lt : α → α → Bool) (window : List K) :
    ∀ indicesLeft : List K,
      (∀ i ∈ indicesLeft, ∃ current previous,
        get values i = .ok current ∧ get values (indices.previous i) = .ok previous) →
      ∃ b, issortedWindowLoop (indexWindowOps indices checkBounds get) values window
        (JuliaLean.base.ordering.OrdResult.plain (K := α) inferInstance
          JuliaLean.base.ordering.Forward (fun _ a b => .ok (lt a b)))
        (match indicesLeft with | [] => none | i :: rest => some (i, rest)) = some (.ok b)
  | [], _ => by
    refine ⟨true, ?_⟩
    simp only [issortedWindowLoop]
  | i :: rest, hreads => by
    obtain ⟨current, previous, hcurrent, hprevious⟩ := hreads i List.mem_cons_self
    have hrest : ∀ j ∈ rest, ∃ current previous,
        get values j = .ok current ∧ get values (indices.previous j) = .ok previous :=
      fun j hj => hreads j (List.mem_cons_of_mem i hj)
    cases hlt : lt current previous with
    | false =>
      obtain ⟨b, hb⟩ := indexWindowLoopTerminates indices checkBounds get values lt window rest hrest
      refine ⟨b, ?_⟩
      rw [issortedWindowLoop]
      simp only [indexWindowOps, hcurrent, hprevious, windowLiftOk,
        JuliaLean.base.ordering.ordCompare, hlt] at hb ⊢
      exact hb
    | true =>
      refine ⟨false, ?_⟩
      simp only [issortedWindowLoop, indexWindowOps, hcurrent, hprevious,
        windowLiftOk, JuliaLean.base.ordering.ordCompare, hlt]

/-- The public sortedness model terminates on a checked window with successful reads. -/
theorem indexWindowTerminates {V α K E : Type}
    (indices : IntegerIndexOps K) (checkBounds : V → K → K → Except E Unit)
    (get : V → K → Except E α) (values : V) (lt : α → α → Bool) (lo hi : K)
    (hcheck : checkBounds values lo hi = .ok ())
    (hreads : WindowReadsSucceed indices get values lo hi) :
    ∃ b, issortedWindow (indexWindowOps indices checkBounds get) values lo hi
      (JuliaLean.base.ordering.OrdResult.plain (K := α) inferInstance
        JuliaLean.base.ordering.Forward (fun _ a b => .ok (lt a b))) = some (.ok b) := by
  obtain ⟨b, hb⟩ := indexWindowLoopTerminates indices checkBounds get values lt
    (indices.range (indices.addOne lo) hi) (indices.range (indices.addOne lo) hi) hreads
  refine ⟨b, ?_⟩
  simp only [issortedWindow, indexWindowOps, windowLiftOk, hcheck] at hb ⊢
  exact hb

/-- memsafety-sort-checked-windows. -/
theorem MemsafetySortCheckedWindows_proven : JuliaLean.Proofs.base.sort.CheckedWindowsInBounds := by
  intro V α S E laws lt values lo hi hcheck horder
  obtain ⟨p, hp, rfl⟩ := effect_pure_cases horder
  have hbounds : hi < lo ∨ (1 ≤ lo ∧ hi ≤ ((E values).length : Int)) := by
    by_cases h : hi < lo ∨ (1 ≤ lo ∧ hi ≤ ((E values).length : Int))
    · exact h
    · rw [storageCheckBounds_eq, laws.firstindex_eq values, storage_lastindex laws values,
        if_neg h] at hcheck
      cases hcheck
  have hreads : WindowReadsSucceed arrayIndices S.getindex values lo hi := by
    intro i hiMem
    have hiRange : lo + 1 ≤ i ∧ i ≤ hi := mem_arrayIndexRange.1 hiMem
    have hnempty : ¬ hi < lo := by omega
    have hvalid : 1 ≤ lo ∧ hi ≤ ((E values).length : Int) := hbounds.resolve_left hnempty
    obtain ⟨current, hcurrent⟩ := posAt_some (l := E values) (i := i) (by omega) (by omega)
    obtain ⟨previous, hprevious⟩ := posAt_some (l := E values) (i := i - 1) (by omega) (by omega)
    exact ⟨current, previous, storage_read_at laws (i := i) (by omega) hcurrent,
      storage_read_at laws (i := i - 1) (by omega) hprevious⟩
  have hreadsLift : ∀ i ∈ arrayIndices.range (arrayIndices.addOne lo) hi, ∃ current previous,
      liftSortJl (S.getindex values i) = .ok current ∧
      liftSortJl (S.getindex values (arrayIndices.previous i)) = .ok previous := by
    intro i hiMem
    obtain ⟨current, previous, hcurrent, hprevious⟩ := hreads i hiMem
    exact ⟨current, previous, by rw [hcurrent]; rfl, by rw [hprevious]; rfl⟩
  obtain ⟨b, hb⟩ := forIn_window_check_ok arrayIndices
    (fun current index => liftSortJl (S.getindex current index)) (fun _ => p) values ()
    (arrayIndices.range (arrayIndices.addOne lo) hi) hreadsLift
  refine ⟨⟨b, ?_⟩, ?_⟩
  · unfold storageIssortedWindow
    simpa only [hcheck, liftSortJl_ok, pureCompare, bind, Except.bind] using hb
  rcases hbounds with hempty | ⟨hlo, hhi⟩
  · exact ⟨⟨values, JuliaLean.ChatGPT.Batch4.Group20.insertionEmptyRun S (pureCompare p)
        values lo hi hempty⟩,
      ⟨values, JuliaLean.ChatGPT.Batch4.Group20.quickEmptyRun S (pureCompare p) values lo hi
        hempty hcheck⟩⟩
  · by_cases hempty : hi < lo
    · exact ⟨⟨values, JuliaLean.ChatGPT.Batch4.Group20.insertionEmptyRun S (pureCompare p)
          values lo hi hempty⟩,
        ⟨values, JuliaLean.ChatGPT.Batch4.Group20.quickEmptyRun S (pureCompare p) values lo hi
          hempty hcheck⟩⟩
    · obtain ⟨inserted, hinsertion, _⟩ := insertion_window laws hp values hlo (by omega) hhi
      obtain ⟨quicksorted, hquick, _⟩ := legacyQuick_window laws hp values lo hi hlo
        (by omega) hhi
      exact ⟨⟨inserted, hinsertion⟩, ⟨quicksorted, hquick⟩⟩

/-- The modern partial sorter returns the wrong value at position 3. -/
theorem SortPartialsortReversedRange_refuted :
    ¬ JuliaLean.Proofs.base.sort.PartialSortRangeCorrect := by
  intro h
  have hbound : ∀ index,
      index ∈ bracketTargetIndices (.ordinal (5 : Int) (-1) 3 3) →
      1 ≤ index ∧ index ≤ (reversedRangeInput.toList.length : Int) := by
    intro index hindex
    rw [JuliaLean.ChatGPT.Batch4.Group20.group20_descendingIndices] at hindex
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hindex
    rcases hindex with rfl | rfl | rfl <;> decide
  obtain ⟨result, hrun, _, hselected⟩ := h (Array Int) Int arrayStorage Array.toList
    (pureCompare intLt) juliaPivot reversedRangeInput (.ordinal 5 (-1) 3 3)
    arrayStorage_laws (effectNegTrans_pure intLt_negTransOrder) (by decide) juliaPivot_bounds hbound
  rw [reversedRangePartialSortOutcome] at hrun
  cases hrun
  have hexpected :
      (bracketTargetIndices (.ordinal (5 : Int) (-1) 3 3)).filterMap
        (fun index => (sortRef intLt reversedRangeInput.toList)[(index - 1).toNat]?) =
          [2, 2, 2] := by decide
  simp only [comparisonTrue_pure_fun] at hselected
  change [2, 2, 1] = _ at hselected
  rw [hexpected] at hselected
  exact (by decide : ([2, 2, 1] : List Int) ≠ [2, 2, 2]) hselected

/-- The legacy partial sorter skips a requested position of a descending range. -/
theorem SorttuplescovPartialquicksortReversedRange_refuted :
    ¬ JuliaLean.Proofs.base.sort.LegacyPartialRangeCorrect := by
  intro h
  have hindices : (List.range 3).map (fun i => (5 : Int) + Int.ofNat i * (-1)) =
      [5, 4, 3] := by decide
  have hbound : ∀ index,
      index ∈ (List.range 3).map (fun i => (5 : Int) + Int.ofNat i * (-1)) →
      1 ≤ index ∧ index ≤ (legacyPartialInput.toList.length : Int) := by
    intro index hindex
    rw [hindices] at hindex
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hindex
    rcases hindex with rfl | rfl | rfl <;> decide
  obtain ⟨result, hrun, hselected⟩ := h (Array Int) Int arrayStorage Array.toList intCompare
    legacyPartialInput 5 (-1) 3 3 arrayStorage_laws intCompare_order
    (by decide) hbound (by decide) (by decide)
  have hout := legacyPartialRangeOutcome
  change legacyPartialQuickSortBang (storagePartialQuickOps arrayStorage intCompare)
    legacyPartialInput 1 (Int.ofNat legacyPartialInput.size) (5, 3) () = .ok result at hrun
  rw [hrun] at hout
  have hwrong :
      ((List.range 3).map (fun i => (5 : Int) + Int.ofNat i * (-1))).filterMap
        (fun index => result[(index - 1).toNat]?) = [2, 1, 1] := by
    simpa only [Option.some.injEq] using hout
  have hactual :
      ((List.range 3).map (fun i => (5 : Int) + Int.ofNat i * (-1))).filterMap
        (fun index => result[(index - 1).toNat]?) = [2, 2, 1] := by
    have hcmp : comparisonTrue intCompare = intLt := comparisonTrue_pure_fun intLt
    rw [hcmp] at hselected
    simpa only [Array.getElem?_toList, legacyPartialRangeExpected] using hselected
  rw [hwrong] at hactual
  exact (by decide : ([2, 1, 1] : List Int) ≠ [2, 2, 1]) hactual



end JuliaLean.ChatGPT.Batch8.Group10

namespace JuliaLean.Proofs.base.sort
open JuliaLean.Registry
def entries : List Entry := [
{ id := "sorttuplescov-insorted-range-equivalence", juliaFile := "base/sort.jl",
    juliaFns := ["insorted(x, v::AbstractVector; kw...)", "insorted(x, r::AbstractRange)"],
    statement := "For every sorted sequence and order-compatible equality predicate, range membership and vector search report the same insorted result.",
    source := "base/sort.jl:427-433 (insorted docstring); base/sort.jl:465-466", status := .refuted,
    prop := ``InsortedRangeAgrees, thm := some ``insortedRangeAgrees_refuted,
    issue := "related #48388 (duplicate of #44102); related PR #37490; no duplicates (queries: insorted range, insorted missing, insorted -0.0; issues and PRs)",
    notes := "The vector overload tests order-equivalence while range membership uses ==. On the sorted Float64 vector [0.0, 1.0], insorted(-0.0, values) is false while insorted(-0.0, 0.0:1.0) is true. Reproducer: repro/sorttuplescov-insorted-range-equivalence.jl." },
  { id := "sort-algorithm-policy-dispatch", juliaFile := "base/sort.jl",
    juliaFns := ["Small{N}(small, big)", "Small{N}(big)", "_sort!(v, Small{N}, o, kw)", "ConsiderCountingSort(next)", "_sort!(v, ConsiderCountingSort, o::DirectOrdering, kw)", "_sort!(v, ConsiderCountingSort, o::Ordering, kw)", "maybe_reverse", "ConsiderRadixSort(next)", "_sort!(v, ConsiderRadixSort, o::DirectOrdering, kw)", "ScratchQuickSort", "BracketedSort(k)", "maybe_unsigned", "InitialOptimizations(next)", "_sort!(v, ::Union{DefaultStable, DefaultUnstable}, o, kw)", "defalg", "maybe_apply_initial_optimizations", "_sort!(v, ::SubArrayOptimization, o, kw)", "_sort!(v, ::BoolOptimization, o, kw)"],
    statement := "Policy dispatchers, algorithm constructors, default-algorithm selectors, and fallback wrappers preserve full-sort and target-selection contracts and dispatch to a sorted permutation.",
    source := "base/sort.jl:559,745,793-802,922-933,946-947,982-992,1079-1082,1224,1443-1444,1473,1592,1620-1624,2396-2399", status := .proven,
    prop := ``AlgorithmPolicyDispatchCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.SortAlgorithmPolicyDispatch_proven },
  { id := "sorttuplescov-without-missing", juliaFile := "base/sort.jl",
    juliaFns := ["WithoutMissingVector", "getindex(::WithoutMissingVector)", "setindex!(::WithoutMissingVector)", "size(::WithoutMissingVector)", "axes(::WithoutMissingVector)"],
    statement := "Validated construction permits every in-bounds read without a missing-value assertion; mutation changes only the chosen backing element, and shape metadata is preserved.",
    source := "base/sort.jl:591-608; MissingOptimization docstring", status := .proven,
    prop := ``WithoutMissingVectorCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.SorttuplescovWithoutMissing_proven },
  { id := "sort-range-search-no-overflow", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedfirst(::AbstractRange{<:Integer}, x, o)", "searchsortedlast(::AbstractRange{<:Integer}, x, o)"],
    statement := "On every nonempty sorted integer range and every real query whose floor and ceiling offsets are representable, both range searches return the documented boundary indices.",
    source := "base/sort.jl:269-299,353-357,392-396 (search docstrings)", status := .todo,
    prop := ``RangeSearchNoOverflowCorrect, thm := none, notes := "Prop additionally requires floor(x) and ceil(x) themselves to fit the range element type; prose only requires their offsets to fit." },
  { id := "sort-range-search-overflow", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedfirst(::AbstractRange{<:Integer}, x, o)", "searchsortedlast(::AbstractRange{<:Integer}, x, o)", "searchsorted(::AbstractRange{<:Real}, x, o)"],
    statement := "On every nonempty sorted integer range and every real query, range searches return the documented boundary indices.",
    source := "base/sort.jl:353-357,392-396 (search docstrings)", status := .refuted,
    prop := ``RangeSearchNonemptyCorrect, thm := some ``rangeSearchNonemptyCorrect_refuted,
    issue := "#63399 (open PR, same overflow; queries: searchsorted overflow, searchsortedfirst range, searchsorted range wrong, searchsortedlast Int8)" },
  { id := "sort-range-search-empty", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedfirst(::AbstractRange{<:Integer}, x, o)", "searchsortedlast(::AbstractRange{<:Integer}, x, o)", "searchsorted(::AbstractRange{<:Real}, x, o)"],
    statement := "For every valid empty integer range and faithful empty real-range model, searchsortedfirst, searchsortedlast, and searchsorted return the documented first and last insertion bounds.",
    source := "base/sort.jl:243-302,314-321,351-360,390-398", status := .refuted,
    prop := ``Round17.RangeSearchEmptyCorrect, thm := some ``JuliaLean.ChatGPT.Batch2.Group4.round17RangeSearchEmptyRefuted,
    issue := "none found (queries: issues: searchsorted empty range; prs: searchsorted empty; issues: searchsortedfirst empty range; issues: searchsorted rev range; issues: searchsortedfirst range)" },
  { id := "sorttuplescov-float-range-search-overflow", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedlast(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings)", "searchsortedfirst(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings)", "searchsorted(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings)"],
    statement := "Searching finite real ranges returns first, last, and matching-range indices without throwing.",
    source := "base/sort.jl:243-267,301-302", status := .refuted,
    prop := ``FloatRangeSearchNoThrow, thm := some ``JuliaLean.ChatGPT.Batch8.Group10.SorttuplescovFloatRangeSearchOverflow_refuted,
    issue := "bugs/sorttuplescov-float-range-search-overflow.yaml" },
  { id := "sort-issorted-adjacent", juliaFile := "base/sort.jl",
    juliaFns := ["issorted(itr, order)"],
    statement := "issorted returns true exactly when no element is ordered before its predecessor.",
    source := "base/sort.jl:62-66 (issorted docstring)", status := .proven,
    prop := ``IssortedAdjacent, thm := some ``issortedAdjacent_proven },
  { id := "sort-vector-search-correct", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedfirst(v, x; kws...)", "searchsortedlast(v, x; kws...)"],
    statement := "For every sorted vector and strict weak order, first and last search return the documented boundary indices.",
    source := "base/sort.jl:353-360,392-399 (search docstrings)", status := .refuted,
    prop := ``VectorSearchCorrect, thm := some ``vectorSearchCorrect_refuted,
    issue := "none found (queries: searchsorted typemax, searchsorted offset axis, searchsorted overflow; issues and PRs)",
    notes := "The generalized statement covers a one-element AbstractVector whose only index is typemax(Int). For [0] on that axis, searchsortedfirst(v, 1) wraps the insertion boundary to typemin(Int). Reproducer: repro/sort-searchsorted-equivalent-range.jl." },
  { id := "sort-vector-u8-search-sentinel", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedlast(v, x, lo::T, hi::T, o)", "searchsorted(v, x, lo::T, hi::T, o)"],
    statement := "For each valid vector window, searchsortedlast and searchsorted only read indices inside the vector.",
    source := "base/sort.jl:203-238 (inbounds search accesses)", status := .refuted,
    prop := ``WindowSearchInBounds, thm := some ``windowSearchInBounds_refuted,
    issue := "none found (related: #31618 generalized lo/hi to T<:Integer; #30388 these methods are undocumented; queries: searchsortedlast UInt8, searchsorted lo hi, searchsorted overflow; issues and PRs)",
    notes := "With valid UInt8 bounds 1:255, hi + 1 wraps to 0 and searchsortedlast reads index 0. Reproducer: repro/sort-vector-u8-search-sentinel.jl." },
  { id := "sort-partialsort-reversed-range", juliaFile := "base/sort.jl",
    juliaFns := ["partialsort!(v, k, o; scratch)", "partialsort!(v, k; kws...)", "partialsort(v, k; kws...)"],
    statement := "On any AbstractVector storage obeying the interface laws, for every valid integer-index target, including a descending range, partialsort and partialsort! return the values at those positions in a fully sorted permutation of the input.",
    source := "base/sort.jl:113-122 (partialsort! contract)", status := .refuted,
    prop := ``PartialSortRangeCorrect, thm := some ``JuliaLean.ChatGPT.Batch8.Group10.SortPartialsortReversedRange_refuted,
    issue := "bugs/sort-partialsort-reversed-range.yaml" },
  { id := "sort-partialsort-empty-range", juliaFile := "base/sort.jl",
    juliaFns := ["partialsort!(v, k, o; scratch)", "partialsort(v, k; kws...)"],
    statement := "On any AbstractVector storage and element type, an empty selection range returns an empty vector for every input length.",
    source := "base/sort.jl:113-122 (partialsort! contract)", status := .refuted,
    prop := ``PartialSortEmptyRange, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.SortPartialsortEmptyRange_refuted,
    issue := "bugs/sort-partialsort-empty-range.yaml" },
  { id := "sort-default-stable", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v; alg, lt, by, rev, order)", "sort(v; kws...)"],
    statement := "On any AbstractVector storage, sort! and sort with the default DEFAULT_STABLE algorithm return the same permutation of the input, sorted by the effective (possibly reversed) order and stable: equivalent elements keep their original relative order.",
    source := "base/sort.jl:1627-1658 (sort! contract); base/sort.jl:1550-1561 (DEFAULT_STABLE guarantee)", status := .proven,
    prop := ``SortDefaultStable, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.SortDefaultStable_proven },
  { id := "sort-vector-sorted-permutation", juliaFile := "base/sort.jl",
    juliaFns := ["sort(v::AbstractVector; alg, kws...)"],
    statement := "On any AbstractVector storage and for every algorithm that sorts on its own, sort copies the input and returns a permutation of it sorted by the effective order, stable whenever the algorithm after InitialOptimizations is stable.",
    source := "base/sort.jl:1743-1747 (sort copy contract)", status := .proven,
    prop := ``SortVectorSortedPermutation, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.SortVectorSortedPermutation_proven },
  { id := "sort-partialsortperm-index-type", juliaFile := "base/sort.jl",
    juliaFns := ["partialsortperm(v, k)", "partialsortperm!(ix, v, k)"],
    statement := "On any AbstractVector storage obeying the interface laws: when 1:length(v) fits in eltype(ix), partialsortperm! returns the stable-sorted permutation entries; when 1:length(v) fits in keytype(v) = Int64, partialsortperm(v, k) succeeds for every valid target k of any integer type.",
    source := "base/sort.jl:1853-1854,1896-1915 (partialsortperm contract)", status := .refuted,
    prop := ``PartialSortpermIndexTypeCorrect, thm := some ``JuliaLean.ChatGPT.Batch8.Group11.SortPartialsortpermIndexType_refuted,
    issue := "none found (queries: partialsortperm, partialsortperm Int8, partialsortperm InexactError, partialsortperm eltype)" },
  { id := "sortperm-stable-permutation", juliaFile := "base/sort.jl",
    juliaFns := ["sortperm", "_sortperm", "sortperm!"],
    statement := "For a vector of length at most typemax(Int), every algorithm that sorts on its own (run through the source _sort! dispatch), every strict weak order lt (ordering integer elements numerically whenever _sortperm's integer fast path applies, as isless does) and rev in {nothing, false, true}: sortperm and sortperm! both succeed and return a permutation of 1:length(v) that lists the values in sorted order and lists equal values by ascending index.",
    source := "base/sort.jl:1920-1926 (sortperm contract)", status := .todo,
    prop := ``SortpermStable, thm := none,
    notes := "Julia's Perm comparator reads p.data[a] with bounds checks, which the model now follows; the canonical proof relied on default-valued reads. JuliaLean.ChatGPT.Batch8.Group11.g11_sortpermStable_of_array_contract proves the property from g11_sortpermArrayContract and SortpermGenericRunsAgree; the open obligation is SortpermGenericRunsAgree, that the source dispatch only compares in-range indices when it sorts 1:n." },
  { id := "memsafety-sort-checked-windows", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, lo, hi, QuickSort, o)", "_issorted(v, lo, hi, o)", "_sort!(v, InsertionSort, o, kw)"],
    statement := "On any AbstractVector storage, once checkbounds accepts lo:hi, the sortedness check, insertion sort and the public legacy quicksort on that window return without throwing.",
    source := "base/sort.jl:835-852,1445-1451,2454-2478; checked-window invariant", status := .proven,
    prop := ``CheckedWindowsInBounds, thm := some ``JuliaLean.ChatGPT.Batch8.Group10.MemsafetySortCheckedWindows_proven },
  { id := "sorttuplescov-legacy-sort-scratch", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, lo, hi, a, o, scratch)", "_sort!(v, a::Algorithm, o, kw)"],
    statement := "For every Julia Vector input and valid one-based window, the public six-argument legacy QuickSort overload with a Vector scratch returns a sorted permutation of the window and leaves its exterior unchanged.",
    source := "base/sort.jl:2409-2478,2570-2582; doc/src/base/sort.md:141-146", status := .refuted,
    prop := ``Round17.LegacyQuickSortScratchCorrect, thm := some ``JuliaLean.ChatGPT.Batch2.Group4.round17LegacyQuickSortScratchRefuted,
    issue := "none found (queries: issues/prs: sort! QuickSort scratch; issues/prs: _sort! is not defined; issues/prs: sort! lo hi QuickSort; issues/prs: sort! six argument; issues/prs: legacy sort! QuickSort)" },
  { id := "sorttuplescov-partialquicksort-reversed-range", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, lo, hi, a::PartialQuickSort, o)", "_partialquicksort!(v, lo, hi, a, o)"],
    statement := "On any AbstractVector storage obeying the interface laws, every requested valid target position of the legacy PartialQuickSort, including a descending range, contains the value it would contain in a fully sorted vector.",
    source := "base/sort.jl:2533-2566; PartialQuickSort target invariant", status := .refuted,
    prop := ``LegacyPartialRangeCorrect, thm := some ``JuliaLean.ChatGPT.Batch8.Group10.SorttuplescovPartialquicksortReversedRange_refuted,
    issue := "bugs/sorttuplescov-partialquicksort-reversed-range.yaml" },
  { id := "sorttuplescov-sort-dims-exception", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(A; dims, alg, lt, by, rev, order, scratch)"],
    statement := "Every out-of-range dimension reaches the explicit dimension-out-of-range exception.",
    source := "base/sort.jl:2187-2196 (dimension validation)", status := .refuted,
    prop := ``SortDimsChecked, thm := some ``sortDimsChecked_refuted,
    issue := "none found (queries: sort! dims BoundsError, sort dims out of range; issues and PRs)",
    notes := "With default scratch, dims=0 calls size(A, dims) before the explicit check and throws BoundsError; scratch=nothing reaches ArgumentError. The sort! docs do not promise an exception type, so this is a low-priority implementation/property inconsistency. Reproducer: repro/sorttuplescov-sort-dims-exception.jl." },
  { id := "sorttuplescov-sort-ntuple-alg", juliaFile := "base/sort.jl",
    juliaFns := ["sort(x::NTuple; alg, kws...)", "_sort(x::NTuple, a, o, kw)"],
    statement := "Every full sorting algorithm accepted by the NTuple sort signature returns a sorted permutation of the input tuple.",
    source := "base/sort.jl:1785-1808", status := .refuted,
    prop := ``TupleSortExplicitAlgCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.SorttuplescovSortNtupleAlg_refuted,
    issue := "bugs/sorttuplescov-sort-ntuple-alg.yaml" },
  { id := "sorttuplescov-sort-missing-scratch", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v; scratch)", "_sort!(v, MissingOptimization(next), o::DirectOrdering, kw)", "WithoutMissingVector", "make_scratch(::Vector,T,len)"],
    statement := "Calling sort!(v; scratch) with a scratch vector of eltype(v) = Union{Missing, Int32} succeeds when MissingOptimization forwards the unwrapped vector and scratch buffer.",
    source := "base/sort.jl:511-516,651-655,1017-1046,1732-1741", status := .refuted,
    prop := ``SortMissingScratchAccepted, thm := some ``sortMissingScratchAccepted_refuted,
    issue := "bugs/sorttuplescov-sort-missing-scratch.yaml",
    notes := "The source-mirrored native default tree preserves the Union-typed scratch through MissingOptimization and WithoutMissingVector. On the reproducer's 98-element prefix it selects RadixSort; make_scratch calls the installed reinterpret constructor, which rejects the non-isbits scratch eltype before the radix chunk-size heuristic or passes run." },
  { id := "sort-issorted-keywords", juliaFile := "base/sort.jl",
    juliaFns := ["issorted(itr; lt, by, rev, order)"],
    statement := "For every iterator and keyword combination, issorted preserves order-construction, comparison, and iteration errors; returns false at the first descending pair and true exactly at ordered termination; an infinite ascending run does not return.",
    source := "base/sort.jl:62-66,86-95", status := .proven,
    prop := ``IssortedKeywordsCorrect, thm := some ``opusIssorted.issortedKeywordsCorrect_proven },
  { id := "sort-searchsorted-equivalent-range", juliaFile := "base/sort.jl",
    juliaFns := ["searchsorted(v, x, lo, hi, o)", "searchsorted(v, x; kws...)"],
    statement := "The result contains exactly the indices equivalent to the query; an absent query produces the empty range at its insertion point.",
    source := "base/sort.jl:313-322 (searchsorted contract)", status := .refuted,
    prop := ``SearchsortedEquivalentRange, thm := some ``searchsortedEquivalentRange_refuted,
    issue := "none found (queries: searchsorted typemax, searchsorted offset axis, searchsorted overflow; issues and PRs)",
    notes := "On a one-element AbstractVector indexed at typemax(Int), searchsorted(v, 1) for [0] wraps the empty insertion range into typemin(Int):typemax(Int), a nonempty range. Reproducer: repro/sort-searchsorted-equivalent-range.jl." },
  { id := "sort-legacy-quicksort-correct", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, lo, hi, QuickSort, o)", "_quicksort!", "partition!", "selectpivot!"],
    statement := "On any AbstractVector storage, legacy sort!(v, lo, hi, QuickSort, o) turns every window inside the vector into a sorted permutation of itself for every strict weak order and leaves the other elements unchanged.",
    source := "base/sort.jl:2409-2478; sorting contract", status := .proven,
    prop := ``QuickSortCorrect, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.SortLegacyQuicksortCorrect_proven },
  { id := "sort-legacy-mergesort-stable", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, lo, hi, MergeSort, o, scratch)", "_mergesort!"],
    statement := "On any AbstractVector storage, legacy sort!(v, lo, hi, MergeSort, o) turns every window inside the vector into a stable sorted permutation of itself and leaves the other elements unchanged.",
    source := "base/sort.jl:2480-2531; MergeSort stability contract", status := .proven,
    prop := ``MergeSortStable, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.SortLegacyMergesortStable_proven },
  { id := "sort-tuple-stable-permutation", juliaFile := "base/sort.jl",
    juliaFns := ["sort(x::NTuple; kws...)", "_sort(x::NTuple, a, o, kw)", "_mergesort(x::NTuple, o)"],
    statement := "sort(x::NTuple) with the default algorithm, any lt, rev and scratch, returns a permutation of the tuple sorted by the effective order and stable, both through the unrolled merge sort (at most nine elements) and through _sort! on a copied vector (longer tuples).",
    source := "base/sort.jl:1743-1747,1785-1813", status := .proven,
    prop := ``TupleSortStable, thm := some ``tupleSortStable_proven },
  { id := "sort-dimension-copy-correct", juliaFile := "base/sort.jl",
    juliaFns := ["sort(A::AbstractArray; dims)", "sort_chunks!(Av, n, alg, order, scratch)"],
    statement := "For every valid dimension of positive length (the zero-length case is sort-dimension-copy-empty-axis), on any array obeying the A[:]/reshape and permutedims/vec layout laws, sort(A; dims) returns an array with the same axes whose every slice along dims is a sorted permutation of the original slice under the effective order, stable when the algorithm after InitialOptimizations is stable.",
    source := "base/sort.jl:2084-2099,2112-2134", status := .proven,
    prop := ``MultidimensionalCopyCorrect, thm := some ``multidimensionalCopyCorrect_proven },
  { id := "sort-dimension-copy-empty-axis", juliaFile := "base/sort.jl",
    juliaFns := ["sort(A::AbstractArray; dims)", "sort_chunks!(Av, n, alg, order, scratch, fst, lst)"],
    statement := "sort(A; dims) with size(A, dims) == 0 returns an array with the same axes.",
    source := "base/sort.jl:2112-2154 (sort contract: returns a sorted copy)", status := .refuted,
    prop := ``DimensionCopyEmptyAxis, thm := some ``dimensionCopyEmptyAxis_refuted,
    issue := "none found (queries: sort dims empty, sort_chunks, step cannot be zero sort, sort empty matrix dims)",
    notes := "sort_chunks! iterates fst:n:lst with n = size(A, dims) = 0, so sort(zeros(0, 3); dims=1) throws ArgumentError(\"step cannot be zero\") while sort!(copy(A); dims=1) returns the 0x3 matrix. The Lean counterexample is the lawful layout of 0 x c matrices; reproducer repro/sort-dimension-copy-empty-axis.jl." },
  { id := "sort-dimension-mutation-correct", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(A::AbstractArray; dims)", "get_view", "get_value"],
    statement := "On any array whose slice views obey the view/setindex! laws, for every algorithm that sorts on its own, sort!(A; dims) with a valid dims returns an array with the same axes whose every slice along dims is a sorted permutation of the original slice under the effective order, stable when the algorithm after InitialOptimizations is stable, through both the direct branch (dims == 1 or size(A, dims) < 30) and the temporary-vector branch when A has at least one slice (no slices: sort-dimension-mutation-empty-slices); with explicit scratch an out-of-range dims throws ArgumentError(\"dimension out of range\").",
    source := "base/sort.jl:2156-2185,2187-2224", status := .todo,
    prop := ``MultidimensionalMutationCorrect, thm := none,
    notes := "The effectful model leaves both the direct-slice and temporary-vector branch reductions in sortBangDims_sorts unproved." },
  { id := "sort-dimension-mutation-empty-slices", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(A::AbstractArray; dims)", "get_view"],
    statement := "sort!(A; dims) on an array with no slices along a valid dims (another dimension has length 0) returns the array with its axes, also when size(A, dims) >= 30 and dims != 1.",
    source := "base/sort.jl:2187-2224 (sort! contract)", status := .refuted,
    prop := ``DimensionMutationEmptySlices, thm := some ``dimensionMutationEmptySlices_refuted,
    issue := "none found (queries: sort! dims BoundsError, sort! dims empty array, sort! dims first(idxs), sort dims BoundsError empty)",
    notes := "When size(A, dims) >= 30 and dims != 1, sort!(A; dims) calls get_view(first(idxs)) before its loop, so sort!(zeros(0, 30); dims=2) throws BoundsError while sort!(zeros(0, 29); dims=2) returns the empty matrix. The Lean counterexample is the lawful slice layout of 0 x c matrices; reproducer repro/sort-dimension-mutation-empty-slices.jl." },
  { id := "sort-algorithm-display-well-formed", juliaFile := "base/sort.jl",
    juliaFns := ["Base.show(io, alg::Algorithm)", "print_tree", "show_type(io, a)", "show_type(io, alg::Small)"],
    statement := "The recursive algorithm display balances its parentheses when leaf displays do, show_type forwards type names, and Small's display identifies its type and parameter.",
    source := "base/sort.jl:1597-1618", status := .proven,
    prop := ``AlgorithmDisplayWellFormed, thm := some ``algorithmDisplayWellFormed_proven },
  { id := "sort-collected-permutation", juliaFile := "base/sort.jl",
    juliaFns := ["sort(v::COLLECT_ON_SORT_TYPES; kws...)"],
    statement := "For every KeySet and ValueIterator, sort collects the source iteration sequence and returns a sorted permutation under the selected effective ordering, stable when the algorithm after InitialOptimizations is stable.",
    source := "base/sort.jl:1782-1783; base/abstractdict.jl:65-69; base/array.jl:777-786", status := .proven,
    prop := ``Round17.CollectedSortCorrect, thm := some ``JuliaLean.ChatGPT.Batch2.Group4.round17CollectedSortCorrect },
  { id := "sort-legacy-invalid-window-rejected", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, a, o)", "sort!(v, lo, hi, a, o)", "sort!(v, lo, hi, a, o, _)", "sort!(v, lo, hi, a, o, scratch::Vector)"],
    statement := "On any AbstractVector storage obeying the interface laws, for valid windows the legacy InsertionSort entry points (with and without scratch) all return the same vector whose window is a stable sorted permutation of the original window with the rest unchanged, and sort!(v, a, o) stably sorts the whole vector; for nonempty out-of-bounds windows every legacy algorithm rejects with BoundsError.",
    source := "base/sort.jl:2571-2582", status := .proven,
    prop := ``LegacyInvalidWindowRejected, thm := some ``JuliaLean.ChatGPT.Batch4.Group20.SortLegacyInvalidWindowRejected_proven },
  { id := "sort-insorted-vector-correct", juliaFile := "base/sort.jl",
    juliaFns := ["insorted(x, v::AbstractVector; kw...)"],
    statement := "For a vector with values sorted under its effective keyword ordering, insorted returns true exactly when an element is equivalent to the query under that ordering.",
    source := "base/sort.jl:427-433,465-466", status := .refuted,
    prop := ``InsortedVectorCorrect, thm := some ``insortedVectorCorrect_refuted,
    issue := "none found (queries: searchsorted typemax, searchsorted offset axis, searchsorted overflow; issues and PRs)",
    notes := "The one-element AbstractVector indexed at typemax(Int) stores 0, but insorted(1, v) returns true after searchsorted wraps its empty range. Reproducer: repro/sort-searchsorted-equivalent-range.jl." },
  { id := "sort-window-search-correct", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedfirst(v, x, lo::T, hi::T, o)", "searchsortedlast(v, x, lo::T, hi::T, o)", "searchsorted(v, x, lo::T, hi::T, o)"],
    statement := "For every sorted valid window of an AbstractVector, the five-argument search functions return the insertion boundaries determined by comparisons within that window for any bit-integer bound type.",
    source := "base/sort.jl:184-199,203-216,221-238", status := .refuted,
    prop := ``WindowSearchCorrect, thm := some ``windowSearchCorrect_refuted,
    issue := "none found (queries: searchsortedlast UInt8, searchsorted lo hi, searchsorted overflow; issues and PRs)",
    notes := "For the valid UInt8 window 1:255, hi + 1 wraps to 0 and searchsortedlast reads outside the vector instead of returning the boundary. Reproducer: repro/sort-window-search-correct.jl." }
]
/-!
Nothing to promise:
- `insorted@464`, `_sort!@542`, `uint_map@2251`, and `uint_unmap@2261` declare generic functions without method bodies.
- `maybeview@110-111` forwards to the external `view` or `getindex` operation.
- `getkw@470` builds internal extraction syntax. The generated getters at `$usym@483` extract typed keywords and supply defaults; their bodies are keyword plumbing.
- `get_value@2224` unwraps `Val` for local dimension selection.
Method → property table:
| Julia method | Property or coverage note |
|---|---|
| `issorted@48` | sort-issorted-adjacent |
| `issorted@86` | sort-issorted-keywords |
| `partialsort!@97` | sort-partialsort-reversed-range, sort-partialsort-empty-range |
| `maybeview@110` | nothing to promise: external view forwarding |
| `maybeview@111` | nothing to promise: external indexing forwarding |
| `partialsort!@166` | sort-partialsort-reversed-range |
| `partialsort@176` | sort-partialsort-reversed-range |
| `searchsortedfirst@184` | sort-vector-search-correct |
| `searchsortedlast@203` | sort-vector-search-correct, sort-vector-u8-search-sentinel |
| `searchsorted@221` | sort-searchsorted-equivalent-range, sort-vector-u8-search-sentinel |
| `searchsortedlast@243` | sorttuplescov-float-range-search-overflow |
| `searchsortedfirst@256` | sorttuplescov-float-range-search-overflow |
| `searchsortedlast@269` | sort-range-search-no-overflow, sort-range-search-overflow, sort-range-search-empty |
| `searchsortedfirst@285` | sort-range-search-no-overflow, sort-range-search-overflow, sort-range-search-empty |
| `searchsorted@301` | sorttuplescov-float-range-search-overflow, sort-range-search-empty |
| `$s@306` | sort-vector-search-correct, sort-searchsorted-equivalent-range |
| `$s@307` | sort-vector-search-correct, sort-searchsorted-equivalent-range |
| `insorted@464` | nothing to promise: generic declaration |
| `insorted@465` | sorttuplescov-insorted-range-equivalence |
| `insorted@466` | sorttuplescov-insorted-range-equivalence |
| `getkw@470` | nothing to promise: extraction syntax |
| `$usym@483` | nothing to promise: typed keyword plumbing |
| `make_scratch@503` | sorttuplescov-make-scratch |
| `make_scratch@507` | sorttuplescov-make-scratch |
| `make_scratch@511` | sorttuplescov-make-scratch, sorttuplescov-sort-missing-scratch |
| `_sort!@542` | nothing to promise: generic declaration |
| `_sort!@559` | sort-algorithm-policy-dispatch |
| `_sort!@560` | sort-subarray-preserves-parent |
| `WithoutMissingVector@591` | sorttuplescov-without-missing |
| `Base.getindex@598` | sorttuplescov-without-missing |
| `Base.setindex!@603` | sorttuplescov-without-missing |
| `Base.size@607` | sorttuplescov-without-missing |
| `Base.axes@608` | sorttuplescov-without-missing |
| `send_to_end!@620` | sort-send-to-end-stable-partition, memsafety-sort-send-to-end-window |
| `send_to_end!@645` | sort-send-to-end-stable-partition, sort-missing-direct-correct, sort-ieee-float-correct |
| `send_to_end!@647` | sort-send-to-end-stable-partition, sort-missing-direct-correct, sort-ieee-float-correct |
| `_sort!@651` | sort-missing-direct-correct, sort-missing-permutation-correct, sorttuplescov-sort-missing-scratch |
| `after_zero@703` | sort-ieee-float-correct, sort-ieee-permutation-correct |
| `after_zero@704` | sort-ieee-float-correct, sort-ieee-permutation-correct |
| `is_concrete_IEEEFloat@705` | sort-ieee-float-correct, sort-ieee-permutation-correct |
| `_sort!@706` | sort-ieee-float-correct, sort-ieee-permutation-correct |
| `_sort!@745` | sort-algorithm-policy-dispatch |
| `_sort!@746` | sort-bool-sorted-permutation |
| `_sort!@774` | sort-uint-mappable-dispatch |
| `Small{N}@793` | sort-algorithm-policy-dispatch |
| `Small{N}@794` | sort-algorithm-policy-dispatch |
| `_sort!@795` | sort-algorithm-policy-dispatch |
| `_sort!@835` | sort-insertionsort-stable |
| `_sort!@864` | sort-check-sorted-correct |
| `_sort!@893` | sort-compute-extrema-correct |
| `ConsiderCountingSort@922` | sort-algorithm-policy-dispatch |
| `_sort!@923` | sort-algorithm-policy-dispatch |
| `_sort!@933` | sort-algorithm-policy-dispatch |
| `maybe_reverse@946` | sort-algorithm-policy-dispatch |
| `maybe_reverse@947` | sort-algorithm-policy-dispatch |
| `_sort!@948` | sort-counting-sorted-permutation, memsafety-sort-count-buckets |
| `ConsiderRadixSort@982` | sort-algorithm-policy-dispatch |
| `_sort!@983` | sort-algorithm-policy-dispatch |
| `_sort!@1017` | sort-radix-wrapper-correct, sorttuplescov-sort-missing-scratch |
| `ScratchQuickSort@1079` | sort-algorithm-policy-dispatch |
| `ScratchQuickSort@1080` | sort-algorithm-policy-dispatch |
| `ScratchQuickSort@1081` | sort-algorithm-policy-dispatch |
| `ScratchQuickSort@1082` | sort-algorithm-policy-dispatch |
| `partition!@1088` | sort-scratchquicksort-stable |
| `_sort!@1121` | sort-scratchquicksort-stable, sort-partialsort-reversed-range |
| `BracketedSort@1224` | sort-algorithm-policy-dispatch |
| `bracket_kernel!@1226` | sort-bracket-kernel-partition |
| `move!@1248` | sort-move-preserves-selected-values |
| `_sort!@1264` | sort-partialsort-reversed-range, sort-partialsort-empty-range |
| `_sort!@1368` | sort-default-stable |
| `radix_sort!@1384` | sort-radix-sorted-permutation |
| `radix_sort_pass!@1402` | sort-radix-sorted-permutation |
| `radix_chunk_size_heuristic@1430` | sort-radix-chunk-covers-bits |
| `maybe_unsigned@1443` | sort-algorithm-policy-dispatch |
| `maybe_unsigned@1444` | sort-algorithm-policy-dispatch |
| `_issorted@1445` | sort-window-issorted-correct, memsafety-sort-checked-windows |
| `InitialOptimizations@1473` | sort-algorithm-policy-dispatch |
| `_sort!@1592` | sort-algorithm-policy-dispatch |
| `Base.show@1597` | sort-algorithm-display-well-formed |
| `print_tree@1600` | sort-algorithm-display-well-formed |
| `show_type@1617` | sort-algorithm-display-well-formed |
| `show_type@1618` | sort-algorithm-display-well-formed |
| `defalg@1620` | sort-algorithm-policy-dispatch |
| `defalg@1621` | sort-algorithm-policy-dispatch |
| `defalg@1622` | sort-algorithm-policy-dispatch |
| `defalg@1623` | sort-algorithm-policy-dispatch |
| `defalg@1624` | sort-algorithm-policy-dispatch |
| `sort!@1732` | sort-default-stable, sort-vector-sorted-permutation, sorttuplescov-sort-missing-scratch |
| `sort@1780` | sort-vector-sorted-permutation |
| `sort@1783` | sort-collected-permutation |
| `sort@1785` | sort-tuple-stable-permutation, sorttuplescov-sort-ntuple-alg |
| `_sort@1798` | sort-tuple-stable-permutation, sorttuplescov-sort-ntuple-alg |
| `_mergesort@1809` | sort-tuple-stable-permutation |
| `_mergesort@1810` | sort-tuple-stable-permutation |
| `merge@1814` | sort-tuple-merge-correct |
| `merge@1815` | sort-tuple-merge-correct |
| `merge@1816` | sort-tuple-merge-correct |
| `merge@1817` | sort-tuple-merge-correct |
| `partialsortperm@1853` | sort-partialsortperm-index-type |
| `partialsortperm!@1896` | sort-partialsortperm-index-type |
| `sortperm@1966` | sortperm-stable-permutation |
| `_sortperm@1980` | sortperm-stable-permutation |
| `sortperm!@2037` | sortperm-stable-permutation |
| `sortperm_int_range@2058` | sorttuplescov-sortperm-int-range |
| `sort@2112` | sort-dimension-copy-correct, sort-dimension-copy-empty-axis |
| `sort_chunks!@2136` | sort-chunks-correct, sort-dimension-copy-correct |
| `sort_chunks!@2141` | sort-chunks-correct |
| `sort_chunks!@2149` | sort-chunks-correct |
| `sort!@2187` | sort-dimension-mutation-correct, sort-dimension-mutation-empty-slices, sorttuplescov-sort-dims-exception |
| `get_view@2206` | sort-dimension-mutation-correct, sort-dimension-mutation-empty-slices |
| `get_value@2224` | nothing to promise: Val unwrapping |
| `UIntMappable@2237` | sort-uint-mappable-dispatch |
| `uint_map@2251` | nothing to promise: generic declaration |
| `uint_unmap@2261` | nothing to promise: generic declaration |
| `uint_map@2267` | sorttuplescov-uint-mapping |
| `uint_unmap@2268` | sorttuplescov-uint-mapping |
| `uint_map@2270` | sorttuplescov-uint-mapping |
| `uint_unmap@2272` | sorttuplescov-uint-mapping |
| `UIntMappable@2275` | sort-uint-mappable-dispatch |
| `uint_map@2282` | sorttuplescov-uint-mapping |
| `uint_unmap@2283` | sorttuplescov-uint-mapping |
| `UIntMappable@2284` | sort-uint-mappable-dispatch |
| `uint_map@2287` | sorttuplescov-uint-mapping |
| `uint_unmap@2288` | sorttuplescov-uint-mapping |
| `UIntMappable@2289` | sort-uint-mappable-dispatch |
| `uint_map!@2295` | sort-uint-vector-round-trip |
| `uint_unmap!@2303` | sort-uint-vector-round-trip |
| `maybe_apply_initial_optimizations@2396` | sort-algorithm-policy-dispatch |
| `maybe_apply_initial_optimizations@2397` | sort-algorithm-policy-dispatch |
| `maybe_apply_initial_optimizations@2398` | sort-algorithm-policy-dispatch |
| `maybe_apply_initial_optimizations@2399` | sort-algorithm-policy-dispatch |
| `selectpivot!@2409` | sort-legacy-quicksort-correct |
| `partition!@2435` | sort-legacy-quicksort-correct |
| `sort!@2454` | sort-legacy-quicksort-correct, memsafety-sort-checked-windows |
| `_quicksort!@2459` | sort-legacy-quicksort-correct |
| `sort!@2480` | sort-legacy-mergesort-stable |
| `sort!@2482` | sort-legacy-mergesort-stable |
| `_mergesort!@2488` | sort-legacy-mergesort-stable |
| `sort!@2533` | sorttuplescov-partialquicksort-reversed-range |
| `_partialquicksort!@2539` | sorttuplescov-partialquicksort-reversed-range |
| `sort!@2571` | sort-legacy-invalid-window-rejected |
| `sort!@2572` | sort-legacy-invalid-window-rejected |
| `sort!@2577` | sort-legacy-invalid-window-rejected |
| `sort!@2578` | sorttuplescov-legacy-sort-scratch, sort-legacy-invalid-window-rejected |
| `_sort!@2586` | sort-legacy-dispatch-rejects-cycles |
-/

end JuliaLean.Proofs.base.sort

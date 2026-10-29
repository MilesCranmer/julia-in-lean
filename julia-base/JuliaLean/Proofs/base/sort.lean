import JuliaLean.base.sort
import JuliaLean.Registry.Types

namespace JuliaLean.Proofs.base.sort

open JuliaLean JuliaLean.base.sort JuliaLean.Registry

@[simp] theorem arrayStorage_getindex {α : Type} :
    (arrayStorage (α := α)).getindex = arrayRead := rfl

@[simp] theorem arrayStorage_setindex {α : Type} :
    (arrayStorage (α := α)).setindex = arrayWrite := rfl

@[simp] theorem arrayStorage_length {α : Type} :
    (arrayStorage (α := α)).length = Array.size := rfl

@[simp] theorem storageCheckBounds_array {α : Type} :
    storageCheckBounds (arrayStorage (α := α)) = arrayCheckBounds := rfl

private instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error e1, .error e2 =>
    if h : e1 = e2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .ok a1, .ok a2 =>
    if h : a1 = a2 then isTrue (by rw [h]) else isFalse (by intro heq; cases heq; exact h rfl)
  | .error _, .ok _ => isFalse (by intro heq; cases heq)
  | .ok _, .error _ => isFalse (by intro heq; cases heq)

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

def AdjacentSorted {α : Type} (lt : α → α → Bool) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => lt b a = false ∧ AdjacentSorted lt (b :: rest)

def IssortedAdjacent : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (xs : List α),
    issorted listIterator (fun _ => lt) () xs = true ↔ AdjacentSorted lt xs

def NegTransOrder {α : Type} (lt : α → α → Bool) : Prop :=
  (∀ a, lt a a = false) ∧
  (∀ a b c, lt a b = true → lt b c = true → lt a c = true) ∧
  (∀ a b c, lt a c = true → lt a b = true ∨ lt b c = true)

def VecSorted {α : Type} (lt : α → α → Bool) (v : Array α) : Prop :=
  ∀ i j a b, i ≤ j → arrayVectorOps.read v i = some a →
    arrayVectorOps.read v j = some b → lt b a = false

def SearchPartition (p : Int → Bool) (lo hi result : Int) : Prop :=
  lo ≤ result ∧ result ≤ hi ∧
  (∀ i, lo ≤ i → i < result → p i = true) ∧
  (∀ i, result ≤ i → i < hi → p i = false)

def before {α : Type} (lt : α → α → Bool) (v : Array α) (x : α) (i : Int) : Bool :=
  match arrayVectorOps.read v i with
  | some value => lt value x
  | none => false

def notAfter {α : Type} (lt : α → α → Bool) (v : Array α) (x : α) (i : Int) : Bool :=
  match arrayVectorOps.read v i with
  | some value => !(lt x value)
  | none => false

def VectorSearchCorrect : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (v : Array α) (x : α),
    NegTransOrder lt → VecSorted lt v → v.size < 2 ^ 62 →
    (∃ first, searchsortedfirstKeywords arrayVectorOps arrayFirstIndex arrayLastIndex
        (fun (_ : Unit) (_ : Unit) (_ : Option Bool) (_ : Unit) => ())
        (fun _ => lt) v x () () none () = .returned first ∧
      SearchPartition (before lt v x) 1 (v.size + 1) first) ∧
    (∃ last, searchsortedlastKeywords arrayVectorOps arrayFirstIndex arrayLastIndex
        (fun (_ : Unit) (_ : Unit) (_ : Option Bool) (_ : Unit) => ())
        (fun _ => lt) v x () () none () = .returned last ∧
      SearchPartition (notAfter lt v x) 1 (v.size + 1) (last + 1))

def WindowSearchInBounds : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (v : Array α) (x : α)
      (t : IntTy) (lo hi : JInt t),
    1 ≤ lo.val → lo.val ≤ hi.val → hi.val ≤ v.size →
    (∀ i, searchsortedlastBounds arrayVectorOps (fun _ => lt) () v x lo hi ≠ .invalidAccess i) ∧
    (∀ i, searchsortedBounds arrayVectorOps (fun _ => lt) () v x lo hi ≠ .invalidAccess i)

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
    searchsortedfirstIntegerRange (bitIntegerRangeOps t) rangeLt rev (f, h, l, len) x = .ok first ∧
    searchsortedlastIntegerRange (bitIntegerRangeOps t) rangeLt rev (f, h, l, len) x = .ok last ∧
    searchsortedIntegerRange (bitIntegerRangeOps t) rangeLt rangeLt rev (f, h, l, len) x
      (fun a b => (a, b)) = .ok (first, last) ∧
    FirstContract len.val (fun i => elemLt rev (rangeElem f h i) x.val) first.val ∧
    LastContract len.val (fun i => !(elemLt rev x.val (rangeElem f h i))) last.val)

def RealQueryValid (x : RealRangeQuery) : Prop :=
  x.floor ≤ x.ceil ∧ x.ceil ≤ x.floor + 1

def RangeAnswersReal {t : IntTy} (f h l : JInt t) (len : JInt64)
    (x : RealRangeQuery) (rev : Bool) : Prop :=
  ∃ first last,
    searchsortedfirstIntegerRange (bitIntegerRealRangeOps t) realQueryLtRange rev (f, h, l, len) x = .ok first ∧
    searchsortedlastIntegerRange (bitIntegerRealRangeOps t) realQueryLt rev (f, h, l, len) x = .ok last ∧
    searchsortedIntegerRange (bitIntegerRealRangeOps t) realQueryLt realQueryLtRange rev (f, h, l, len) x
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

def IntegerRangeSearchEmptyCorrect : Prop :=
  ∀ (t : IntTy) (f h l : JInt t) (len : JInt64) (x : RealRangeQuery) (rev : Bool),
    RangeValid f h l len → RealQueryValid x → len.val = 0 →
    searchsortedfirstIntegerRange (bitIntegerRealRangeOps t) realQueryLtRange rev (f, h, l, len) x =
      .ok (JInt.lit .i64 1) ∧
    searchsortedlastIntegerRange (bitIntegerRealRangeOps t) realQueryLt rev (f, h, l, len) x =
      .ok (JInt.lit .i64 0) ∧
    searchsortedIntegerRange (bitIntegerRealRangeOps t) realQueryLt realQueryLtRange rev (f, h, l, len) x
      (fun a b => (a, b)) = .ok (JInt.lit .i64 1, JInt.lit .i64 0)
def RealRangeSearchPredicatesSorted {X α O : Type} (values : List α)
    (lt : O → X → α → Bool) (ltRange : O → α → X → Bool)
    (order : O) (x : X) : Prop :=
  ∀ (i j : Nat) (left right : α), i < j →
    values[i]? = some left → values[j]? = some right →
    (ltRange order right x = true → ltRange order left x = true) ∧
    (lt order x left = true → lt order x right = true)

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

def RealRangeSearchEmptyCorrect : Prop :=
  ∀ (A R X Q O : Type) (ops : RealRangeOps A R X Q Int O JlError)
      (lt : O → X → R → Bool) (ltRange : O → R → X → Bool)
      (order : O) (a : A) (x : X) (rangeValue : R → R → Nat → R)
      (emptyLast : R → R → R) (isZeroValue : R → Bool)
      (finiteValue : R → Bool) (finiteQuery : X → Bool)
      (finiteQuotient : Q → Bool),
    RealRangeOpsFaithful ops a x [] rangeValue emptyLast isZeroValue
      finiteValue finiteQuery finiteQuotient →
    ops.finiteSearch a x →
    lt order x (ops.first a) = true →
    ltRange order (ops.first a) x = true →
    ltRange order (ops.last a) x = true →
    searchsortedfirstRealRange ops ltRange order a x = .ok ops.oneIndex ∧
    searchsortedlastRealRange ops lt order a x = .ok ops.zeroIndex ∧
    searchsortedRealRange ops lt ltRange order a x (fun f l => (f, l)) =
      .ok (ops.oneIndex, ops.zeroIndex)

def RangeSearchEmptyCorrect : Prop :=
  IntegerRangeSearchEmptyCorrect ∧ RealRangeSearchEmptyCorrect

def FloatRangeSearchNoThrow : Prop :=
  ∀ (A R X Q O : Type) (ops : RealRangeOps A R X Q Int O JlError)
      (lt : O → X → R → Bool) (ltRange : O → R → X → Bool)
      (ltValues : O → R → R → Bool) (order : O) (a : A) (x : X)
      (values : List R) (rangeValue : R → R → Nat → R)
      (emptyLast : R → R → R) (isZeroValue : R → Bool)
      (finiteValue : R → Bool) (finiteQuery : X → Bool)
      (finiteQuotient : Q → Bool),
    RealRangeOpsFaithful ops a x values rangeValue emptyLast isZeroValue
      finiteValue finiteQuery finiteQuotient →
    ops.finiteSearch a x →
    RangeSortedBy (ltValues order) values →
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
      withoutMissingVector (fun storage => storage.any Option.isNone)
        JlError.argumentError values false = .ok wrapped →
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

def WindowIssortedCorrect : Prop :=
  ∀ (V α K O E : Type) (indices : IntegerIndexOps K)
      (checkBounds : V → K → K → Except E Unit) (get : V → K → Except E α)
      (lt : O → α → α → Bool) (v : V) (lo hi : K) (order : O),
    checkBounds v lo hi = .ok () →
    WindowReadsSucceed indices get v lo hi →
    (issortedWindow indices checkBounds get lt v lo hi order = .ok true ↔
      WindowSorted indices get lt v lo hi order)

def UIntMappingCorrect : Prop :=
  (∀ (t : IntTy) (x : JInt t) (reverse : Bool),
    integerDecode t reverse (integerCode t reverse x) = x) ∧
  (∀ (t : IntTy) (x y : JInt t) (reverse : Bool),
    (if reverse then y.val < x.val else x.val < y.val) ↔
      integerCode t reverse x < integerCode t reverse y) ∧
  (∀ (value : CharacterCode),
    uintUnmapChar CharacterCode.mk (uintMapChar CharacterCode.bits value) = value) ∧
  (∀ (left right : CharacterCode),
    left.bits.toNat < right.bits.toNat ↔
      (uintMapChar CharacterCode.bits left).toNat <
        (uintMapChar CharacterCode.bits right).toNat)
def SortedValues {α : Type} (lt : α → α → Bool) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => lt b a = false ∧ SortedValues lt (b :: rest)

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
  (∀ (α : Type) [Inhabited α] (lt : α → α → Bool)
      (mappableType : Option Type) (values : Array α),
    NegTransOrder lt →
    let ops : UIntMappableSortOps (Array α) (Algorithm (BracketSortTarget Int) Int)
        (α → α → Bool) (ArraySortKeywords α) (Array α) JlError := {
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
      SortedValues lt result.toList)

def AlgorithmPolicyDispatchCorrect : Prop :=
  (∀ (α : Type) [Inhabited α] (lt : α → α → Bool) (threshold : Nat) (values : Array α),
    NegTransOrder lt →
    let ops : SmallSortOps (Array α) (Algorithm (BracketSortTarget Int) Int)
        (α → α → Bool) Int (ArraySortKeywords α) (Array α) JlError := {
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
      List.Perm values.toList res1.toList ∧ SortedValues lt res1.toList ∧
      List.Perm values.toList res2.toList ∧ SortedValues lt res2.toList) ∧
  (∀ (α : Type) [Inhabited α] (lt : α → α → Bool) (t : IntTy)
      (minimum maximum : JInt t) (reverse : Bool) (elemSz : Nat) (values : Array α),
    NegTransOrder lt →
    let ops : ConsiderCountingOps (Array α) (JInt t) Nat Int
        (Algorithm (BracketSortTarget Int) Int) Bool (ArraySortKeywords α) (Array α) JlError := {
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
      List.Perm values.toList res1.toList ∧ SortedValues lt res1.toList ∧
      List.Perm values.toList res2.toList ∧ SortedValues lt res2.toList) ∧
  (∀ (α : Type) [Inhabited α] (lt : α → α → Bool) (t : IntTy)
      (minimum maximum : JInt t) (reverse : Bool) (elemSz : Nat) (logSpan : Float) (values : Array α),
    NegTransOrder lt →
    let ops : ConsiderRadixSortOps (Array α) (JInt t) Int Nat
        (Algorithm (BracketSortTarget Int) Int) Bool (ArraySortKeywords α) (Array α) JlError := {
      rangeAndExtrema := fun kw => .ok (kw.lo, kw.hi, minimum, maximum)
      uintMap := fun x rev => integerCode t rev x
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
      List.Perm values.toList result.toList ∧ SortedValues lt result.toList) ∧
  (∀ (α : Type) [Inhabited α] (lt : α → α → Bool) (values : Array α)
      (target : BracketSortTarget Int) (lo hi : Option Int),
    NegTransOrder lt →
    let sortLeaf := fun (v : Array α) (_ : Algorithm (BracketSortTarget Int) Int)
      (o : α → α → Bool) (kw : ArraySortKeywords α) => storageInsertion arrayStorage o v kw.lo kw.hi
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
      List.Perm values.toList r1.toList ∧ SortedValues lt r1.toList ∧
      List.Perm values.toList r2.toList ∧ SortedValues lt r2.toList ∧
      List.Perm values.toList r3.toList ∧ SortedValues lt r3.toList)
def SortpermIntRangeOpsFaithful {V T : Type}
    (ops : SortpermRangeOps V T (Array Int) (Array Int) JlError)
    (values : V) (input : List T) (minimum : T) (rank : T → Int) : Prop :=
  ops.length values = Int.ofNat input.length ∧
  (∀ index value, 1 ≤ index → index ≤ Int.ofNat input.length →
    ops.read values index = .ok value ↔
      input[(index - 1).toNat]? = some value) ∧
  (∀ value, value ∈ input →
    ops.toIndex (ops.wrapAdd value (ops.wrapSub ops.one minimum)) = rank value ∧
    ops.toIndex
      (ops.wrapAdd (ops.wrapAdd value (ops.wrapSub ops.one minimum)) ops.one) =
        rank value + 1) ∧
  (∀ left right, left ∈ input → right ∈ input →
    ops.lessEqual left right = decide (rank left ≤ rank right) ∧
    ops.equal left right = decide (rank left = rank right)) ∧
  (∀ length, ops.allocateCounts length =
    if 0 ≤ length then .ok (Array.replicate length.toNat 0)
    else .error .boundsError) ∧
  (∀ counts, ops.countLength counts = Int.ofNat counts.size) ∧
  (∀ counts index, ops.getCount counts index = arrayRead counts index) ∧
  (∀ counts index value,
    ops.setCount counts index value = arrayWrite counts index value) ∧
  (∀ length, ops.allocatePermutation length =
    if 0 ≤ length then .ok (Array.replicate length.toNat 0)
    else .error .boundsError) ∧
  (∀ permutation index,
    ops.getPermutation permutation index = arrayRead permutation index) ∧
  (∀ permutation index value,
    ops.setPermutation permutation index value = arrayWrite permutation index value) ∧
  (∀ lo hi, ops.range lo hi =
    if lo ≤ hi then
      (List.range ((hi - lo + 1).toNat)).map fun offset => lo + Int.ofNat offset
    else [])

def SortpermIntRangeCorrect : Prop :=
  ∀ (V T : Type)
      (ops : SortpermRangeOps V T (Array Int) (Array Int) JlError)
      (values : V) (input : List T) (rangeLength : Int)
      (minValue : T) (rank : T → Int),
    SortpermIntRangeOpsFaithful ops values input minValue rank →
    (∀ value, value ∈ input → 1 ≤ rank value ∧ rank value ≤ rangeLength) →
    ∃ permutation,
      sortpermIntRange ops values rangeLength minValue = .ok permutation ∧
      permutation.size = input.length ∧
      (∀ i, 1 ≤ i → i ≤ Int.ofNat input.length →
        ∃ value, ops.getPermutation permutation i = .ok value ∧
          1 ≤ value ∧ value ≤ Int.ofNat input.length) ∧
      (∀ i j first second, 1 ≤ i → i < j → j ≤ Int.ofNat input.length →
        ops.getPermutation permutation i = .ok first →
        ops.getPermutation permutation j = .ok second →
        first ≠ second) ∧
      (∀ i j first second x y, 1 ≤ i → i < j → j ≤ Int.ofNat input.length →
        ops.getPermutation permutation i = .ok first →
        ops.getPermutation permutation j = .ok second →
        ops.read values first = .ok x →
        ops.read values second = .ok y →
        ops.lessEqual x y = true ∧
        (ops.equal x y = true → first < second))

def SendToEndInBounds : Prop :=
  ∀ (α : Type) (predicate : α → Bool) (values : Array α) (lo hi : Int),
    lo ≤ hi →
    ∃ last result,
      (sendToEndBang (storageSendToEndOps arrayStorage)
        (fun value => fun state => .ok (predicate value, state))
        ⟨1, 1, values.size⟩ (some lo) (some hi)).run values = .ok (last, result)
structure TaggedSortValue (α : Type) where
  key : α
  originalIndex : Nat

private instance [Inhabited α] : Inhabited (TaggedSortValue α) where
  default := ⟨default, 0⟩

def TaggedSorted {α : Type} (lt : α → α → Bool)
    (values : List (TaggedSortValue α)) : Prop :=
  ∀ (i j : Nat) (x y : TaggedSortValue α), i < j → values[i]? = some x → values[j]? = some y →
    lt y.key x.key = false

def TaggedStable {α : Type} (lt : α → α → Bool)
    (values : List (TaggedSortValue α)) : Prop :=
  ∀ (i j : Nat) (x y : TaggedSortValue α), i < j → values[i]? = some x → values[j]? = some y →
    lt x.key y.key = false → lt y.key x.key = false →
    x.originalIndex < y.originalIndex

def InsertionSortStable : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool),
    NegTransOrder lt → ∀ keys : List α,
      let input := (keys.zipIdx.map fun (key, originalIndex) =>
        TaggedSortValue.mk key originalIndex).toArray
      let compare := fun (a b : TaggedSortValue α) => lt a.key b.key
      ∃ result,
        storageInsertion arrayStorage compare input 1 input.size = .ok result ∧
        List.Perm input.toList result.toList ∧
        TaggedSorted lt result.toList ∧
        TaggedStable lt result.toList

def InsortedRangeAgrees : Prop :=
  ∀ (α : Type) (lt eq : α → α → Bool) (values : List α) (value : α),
    NegTransOrder lt →
    (∀ a, eq a a = true) →
    (∀ a b, eq a b = eq b a) →
    (∀ a b, (lt a b = false ∧ lt b a = false) → eq a b = true) →
    AdjacentSorted lt values →
    let vector := values.toArray
    let vectorResult :=
      insortedVector arrayVectorOps arrayFirstIndex arrayLastIndex
        (fun (_ : Unit) (_ : Unit) (_ : Option Bool) (_ : Unit) => ())
        (fun (_ : Unit) => lt) vector value () () none ()
    let rangeResult := insortedRange (fun x xs => xs.any (eq x)) value values
    vectorResult = .returned rangeResult
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
    1 ≤ numeric.roundInt (root * root) ∧ numeric.roundInt (root * root) ≤ n) ∧
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

def PartialSortRangeCorrect : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool)
      (numeric : BracketNumerics) (pivot : Int → Int → Int)
      (values : Array α) (target : BracketSortTarget Int),
    BracketNumericsLaws numeric → NegTransOrder lt →
    values.size ≤ IntTy.max .i64 →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    (∀ index, index ∈ bracketTargetIndices target → 1 ≤ index ∧ index ≤ values.size) →
    let expected := sortRef lt values.toList
    let selected := (bracketTargetIndices target).filterMap fun index =>
      expected[(index - 1).toNat]?
    ∃ result,
      partialSortBang (storagePartialSortOps arrayStorage numeric pivot) values target lt none = .ok result ∧
      partialSort (storagePartialSortOps arrayStorage numeric pivot) (fun source => .ok source)
        (fun (less : α → α → Bool) (_ : Unit) (_ : Option Bool) _ => less)
        values target lt () none lt { lo := 1, hi := values.size, scratch := none } = .ok result ∧
      result = selected

def PartialSortEmptyRange : Prop :=
  ∀ (numeric : BracketNumerics) (pivot : Int → Int → Int)
      (values : Array Int) (first step last : Int),
    partialSortBang (storagePartialSortOps arrayStorage numeric pivot) values
      (.ordinal first step last 0) (fun a b : Int => decide (a < b)) none = .ok []

def SortVectorSortedPermutation : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool)
      (pivot : Int → Int → Int) (values : Array α)
      (algorithm : Algorithm (BracketSortTarget Int) Int) (reverse : Option Bool)
      (scratch : Option (Array α)),
    NegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    let effective := if reverse = some true then fun a b => lt b a else lt
    let vectorOps := sourceVectorSortOps arrayStorage defaultBracketNumerics pivot
    let copyOps : SortCopyOps (Array α) JlError (Option (Array α)) := {
      copyMutable := fun source => .ok source
      sortBang := fun source selectedScratch =>
        sortVectorBang vectorOps source algorithm lt () reverse lt selectedScratch
    }
    ∀ result, sortVector copyOps values scratch = .ok result →
      List.Perm values.toList result.toList ∧
      SortedValues effective result.toList

def SortDefaultStable : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool)
      (pivot : Int → Int → Int) (keys : List α) (reverse : Option Bool),
    NegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    let input := (keys.zipIdx.map fun (key, originalIndex) =>
      TaggedSortValue.mk key originalIndex).toArray
    let compare := fun (a b : TaggedSortValue α) => lt a.key b.key
    let effective := if reverse = some true then fun a b => lt b a else lt
    let vectorOps := sourceVectorSortOps arrayStorage defaultBracketNumerics pivot
    let copyOps : SortCopyOps (Array (TaggedSortValue α)) JlError
        (Option (Array (TaggedSortValue α))) := {
      copyMutable := fun source => .ok source
      sortBang := fun source selectedScratch =>
        sortVectorBang vectorOps source (defalgArray source)
          compare () reverse compare selectedScratch
    }
    ∃ result,
      sortVectorBang vectorOps input (defalgArray input)
        compare () reverse compare none = .ok result ∧
      sortVector copyOps input none = .ok result ∧
      List.Perm input.toList result.toList ∧
      TaggedSorted effective result.toList ∧ TaggedStable effective result.toList


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

def SortpermStable : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool)
      (pivot : Int → Int → Int) (integerView : Array α → Jl (Array Int))
      (hasIntegerElements : Array α → Bool) (integerValue : α → Int)
      (values : Array α) (initial : Array Int)
      (algorithm : Algorithm (BracketSortTarget Int) Int) (scratch : Option (Array Int))
      (reverse : Option Bool),
    NegTransOrder lt → initial.size = values.size →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    (∀ input, hasIntegerElements input = true →
      integerView input = .ok (input.map integerValue) ∧
      (∀ a b, a ∈ input.toList → b ∈ input.toList →
        lt a b = decide (integerValue a < integerValue b))) →
    let effective := if reverse = some true then fun a b => lt b a else lt
    let topOps := arraySortpermTopOps pivot integerView hasIntegerElements
      (fun _ => reverse != some true)
    let bangOps := arraySortpermBangOps pivot
    ∃ topIndices bangIndices,
      sortpermTop topOps values algorithm lt () reverse lt scratch () = .ok topIndices ∧
      sortpermBang bangOps initial values algorithm lt () reverse lt scratch none = .ok bangIndices ∧
      List.Perm (oneBasedIndices values.size) (topIndices.toList.map Int.toNat) ∧
      SortpermOrdered effective values.toList (topIndices.toList.map Int.toNat) ∧
      List.Perm (oneBasedIndices values.size) (bangIndices.toList.map Int.toNat) ∧
      SortpermOrdered effective values.toList (bangIndices.toList.map Int.toNat)

def PartialSortpermIndexTypeCorrect : Prop :=
  ∀ (t : IntTy) (α : Type) [Inhabited α] (less : α → α → Bool)
      (values : Array α) (target : BracketSortTarget Int) (pivot : Int → Int → Int)
      (reverse : Option Bool),
    NegTransOrder less →
    (bracketTargetIndices target).Nodup →
    (values.size : Int) ≤ IntTy.max .i64 →
    (∀ index, index ∈ bracketTargetIndices target →
      1 ≤ index ∧ index ≤ values.size ∧ IntTy.min t ≤ index ∧ index ≤ IntTy.max t) →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    let effective := if reverse = some true then fun a b => less b a else less
    let ops := storagePartialSortpermOps arrayStorage t pivot
    let initial := Array.replicate values.size (JInt.wrap t 0)
    ∃ result,
      partialSortperm ops values target less () reverse
        effective false = .ok result ∧
      ((values.size : Int) ≤ IntTy.max t →
        partialSortpermBang ops initial values target less () reverse
          effective false = .ok result) ∧
      let indices := oneBasedIndices values.size
      let expected := sortRef (fun a b =>
        let left := values[a - 1]?.getD default
        let right := values[b - 1]?.getD default
        effective left right || (!(effective right left) && decide (a < b))) indices
      result.map (fun value => value.val) =
        (bracketTargetIndices target).filterMap fun index =>
          (expected[(index - 1).toNat]?).map Int.ofNat
def ScratchQuickSortStable : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool)
      (pivot : Int → Int → Int) (keys : List α),
    NegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    let input := (keys.zipIdx.map fun (key, originalIndex) =>
      TaggedSortValue.mk key originalIndex).toArray
    let compare := fun (a b : TaggedSortValue α) => lt a.key b.key
    ∃ result scratch,
      sourceSortWindow arrayStorage defaultBracketNumerics pivot input
        (.scratchQuickSort none none .insertion) compare
        { lo := 1, hi := input.size } = .ok (result, scratch) ∧
      List.Perm input.toList result.toList ∧
      TaggedSorted lt result.toList ∧ TaggedStable lt result.toList

def CheckedWindowsInBounds : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (values : Array α) (lo hi : Int),
    arrayCheckBounds values lo hi = .ok () → NegTransOrder lt →
    issortedWindow arrayIndices arrayCheckBounds arrayRead
      (fun (_ : Unit) => lt) values lo hi () ≠ .error .boundsError ∧
    storageInsertion arrayStorage lt values lo hi ≠ .error .boundsError ∧
    legacyQuickSortBang (storageQuickOps arrayStorage lt) values lo hi () ≠ .error .boundsError

def CountBucketsInBounds : Prop :=
  ∀ (t : IntTy) (values : Array (JInt t)) (minimum maximum : JInt t) (reverse : Bool),
    let low := if reverse then maximum.val else minimum.val
    let high := if reverse then minimum.val else maximum.val
    0 < values.size →
    (∀ value, value ∈ values.toList → low ≤ value.val ∧ value.val ≤ high) →
    0 ≤ high - low → high - low < IntTy.max .i64 →
      sortCounting (arrayCountingOps t) values reverse
        { lo := 1, hi := values.size, minimum, maximum } ≠ .error .boundsError

def LegacySortScratch : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool)
      (values scratch : Array α) (lo hi : Int) (algorithm : LegacyArrayAlgorithm),
    arrayCheckBounds values lo hi = .ok () →
    ∀ expected, storageLegacyFive arrayStorage lt values lo hi algorithm = .ok expected →
      ∃ result, legacySortWithScratch (storageLegacyOps arrayStorage lt) values lo hi algorithm () scratch =
        .ok result ∧ result = expected

def LegacyPartialRangeCorrect : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool)
      (values : Array α) (first step last : Int) (length : Nat),
    NegTransOrder lt →
    step ≠ 0 →
    let target := (List.range length).map fun index =>
      first + Int.ofNat index * step
    (∀ index, index ∈ target → 1 ≤ index ∧ index ≤ Int.ofNat values.size) →
    0 < length →
    last = first + Int.ofNat (length - 1) * step →
    let expected := sortRef lt values.toList
    ∃ result,
      legacyPartialQuickSortBang (storagePartialQuickOps arrayStorage lt)
        values 1 (Int.ofNat values.size) (first, last) () = .ok result ∧
      target.filterMap (fun index => result[(index - 1).toNat]?) =
        target.filterMap (fun index => expected[(index - 1).toNat]?)
def IssortedKeywordsCorrect : Prop :=
  ∀ (α L B O : Type) (orderOf : L → B → Option Bool → O → O)
      (lt : O → α → α → Bool) (values : List α) (less : L) (byFn : B)
      (reverse : Option Bool) (order : O),
    let effective := orderOf less byFn (if reverse = some true then some true else none) order
    issortedKeywords listIterator orderOf lt values less byFn reverse order = true ↔
      AdjacentSorted (lt effective) values

def SearchsortedEquivalentRange : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (values : Array α) (query : α),
    NegTransOrder lt → VecSorted lt values →
    values.size < IntTy.max .i64 →
    ∃ first last,
      searchsortedKeywords arrayVectorOps arrayFirstIndex arrayLastIndex
        (fun (_ : Unit) (_ : Unit) (_ : Option Bool) (_ : Unit) => ())
        (fun _ => lt) values query () () none () = .returned (first, last) ∧
      SearchPartition (before lt values query) 1 (values.size + 1) first ∧
      SearchPartition (notAfter lt values query) 1 (values.size + 1) (last + 1) ∧
      first ≤ last + 1 ∧
      (∀ index value, arrayRead values index = .ok value →
        ((first ≤ index ∧ index ≤ last) ↔
          (lt value query = false ∧ lt query value = false)))

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
  ∀ (values : Array Bool) (lt : Bool → Bool → Bool),
    NegTransOrder lt →
    ∃ result, sortBoolVector (storageBoolSortOps arrayStorage) values lt (1, values.size) = .ok result ∧
      List.Perm values.toList result.toList ∧ SortedValues lt result.toList

def CountingSortCorrect : Prop :=
  ∀ (t : IntTy) (values : Array (JInt t)) (minimum maximum : JInt t) (reverse : Bool),
    let low := if reverse then maximum.val else minimum.val
    let high := if reverse then minimum.val else maximum.val
    0 < values.size →
    (∀ value, value ∈ values.toList → low ≤ value.val ∧ value.val ≤ high) →
    0 ≤ high - low → high - low < IntTy.max .i64 →
    ∃ result,
      sortCounting (arrayCountingOps t) values reverse
        { lo := 1, hi := values.size, minimum, maximum } = .ok (result, ()) ∧
      List.Perm values.toList result.toList ∧
      SortedValues (fun a b : JInt t =>
        if reverse then decide (b.val < a.val) else decide (a.val < b.val)) result.toList

def RadixSortCorrect : Prop :=
  ∀ (heuristic : RadixChunkHeuristicOps Int Nat Nat JlError)
      (values : Array Nat) (bits : Nat) (chunk : UInt8),
    0 < bits → bits ≤ 128 → 0 < chunk.toNat → chunk.toNat ≤ 10 →
    (∀ value, value ∈ values.toList → value < 2 ^ bits) →
    ∃ vector temporary inVector,
      radixSortBang (arrayRadixOps heuristic) values 1 values.size bits
        (Array.replicate values.size 0) 0 (some chunk) = .ok (vector, temporary, inVector) ∧
      let result := if inVector then vector else temporary
      List.Perm values.toList result.toList ∧
      SortedValues (fun a b : Nat => decide (a < b)) result.toList


def QuickSortCorrect : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (values : Array α),
    NegTransOrder lt →
    ∃ result, legacyQuickSortBang (storageQuickOps arrayStorage lt) values 1 values.size () = .ok result ∧
      List.Perm values.toList result.toList ∧ SortedValues lt result.toList

def MergeSortStable : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool) (keys : List α),
    NegTransOrder lt →
    let input := (keys.zipIdx.map fun (key, originalIndex) =>
      TaggedSortValue.mk key originalIndex).toArray
    ∃ result,
      legacyMergeSortBang (storageMergeOps arrayStorage (fun a b : TaggedSortValue α => lt a.key b.key))
        input 1 input.size () () = .ok result ∧
      List.Perm input.toList result.toList ∧
      TaggedSorted lt result.toList ∧ TaggedStable lt result.toList

def TupleSortStable : Prop :=
  ∀ (n : Nat) (α : Type) [Inhabited α] (lt : α → α → Bool)
      (pivot : Int → Int → Int) (keys : NTuple n α)
      (reverse : Option Bool),
    NegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    let taggedList := keys.val.zipIdx.map fun (key, originalIndex) =>
      TaggedSortValue.mk key originalIndex
    let input : NTuple n (TaggedSortValue α) :=
      ⟨taggedList, by simp [taggedList, keys.property]⟩
    let compare := fun (a b : TaggedSortValue α) => lt a.key b.key
    let effective := if reverse = some true then fun a b => lt b a else lt
    ∃ result,
      sortTupleTop (nTuplePublicOps n pivot) input (defalgOther input)
        compare () reverse compare none = .ok result ∧
      List.Perm input.val result.val ∧
      TaggedSorted effective result.val ∧
      TaggedStable effective result.val

def TupleSortExplicitAlgCorrect : Prop :=
  ∀ (n : Nat) (α : Type) [Inhabited α] (lt : α → α → Bool)
      (pivot : Int → Int → Int) (tuple : NTuple n α)
      (algorithm : Algorithm (BracketSortTarget Int) Int)
      (reverse : Option Bool),
    NegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    let effective := if reverse = some true then fun a b => lt b a else lt
    ∃ result,
      sortTupleTop (nTuplePublicOps n pivot) tuple algorithm
        lt () reverse lt none = .ok result ∧
      List.Perm tuple.val result.val ∧
      SortedValues effective result.val

def TupleMergeCorrect : Prop :=
  ∀ (m n : Nat) (α : Type) [Inhabited α] (lt : α → α → Bool)
      (left : NTuple m α) (right : NTuple n α),
    NegTransOrder lt → SortedValues lt left.val → SortedValues lt right.val →
    ∃ result, mergeNTuple lt left right = .ok result ∧
      List.Perm (left.val ++ right.val) result.val ∧ SortedValues lt result.val

def MissingDirectCorrect : Prop :=
  ∀ (Alg : Type) (nextAlgorithm : Alg → Alg)
      (sortWrapped : WithoutMissingVector Int (Array (Option Int)) → Alg → Bool →
        (Int × Int) → Jl (Array (Option Int)))
      (sortVector : Array (Option Int) → Alg → Bool →
        (Int × Int) → Jl (Array (Option Int)))
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
        (Int × Int) → Jl (Array Int))
      (sortVector : Array Int → Alg → Bool → (Int × Int) → Jl (Array Int))
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

def SortMissingScratchAccepted : Prop :=
  ∀ (values scratch : Array (Option (JInt .i32))),
    let scratchOps : ScratchOps (Array (Option (JInt .i32))) (Array (JInt .i32)) JlError := {
      allocate := fun len => .ok (Array.replicate len none)
      length := Array.size
      resize := fun v len => .ok (v ++ Array.replicate (len - v.size) none)
      sizeofBacking := 8
      multiply := Nat.mul
      divide := fun bytes sz => if sz = 0 then .error .divideError else .ok (bytes / sz)
      reinterpret := fun _ _ => .error (.argumentError "cannot reinterpret Union{Missing, Int32}")
      viewLength := Array.size
      allocateLength := by intro n v h; cases h; simp
      resizeLength := by intro v n v' h; cases h; simp; omega
      reinterpretBytes := by intro b v w h; cases h
      multiplyEq := fun _ _ => rfl
      divideEq := by intro a b q h; split at h <;> simp_all; omega
    }
    let missingOps : MissingSortOps (Array (Option (JInt .i32))) (Array (Option (JInt .i32)))
        (WithoutMissingVector (JInt .i32) (Array (Option (JInt .i32)))) Int Int (Option (JInt .i32))
        (Algorithm (BracketSortTarget Int) Int) Bool Empty
        (Int × Int × Option (Array (Option (JInt .i32))))
        (Array (Option (JInt .i32))) JlError := {
      range := fun (lo, hi, _) => .ok (lo, hi)
      elementType := fun _ => Option (JInt .i32)
      isDirectOrdering := fun _ => true
      hasMissingSupertype := fun _ => true
      nonMissingType := fun _ => JInt .i32
      sameType := fun _ _ => false
      sendMissingToEnd := fun v _ lo hi => .ok (v, lo, hi)
      wrapVectorWithoutMissing := fun v =>
        withoutMissingVector (fun _ => false) JlError.argumentError v true
      permutationDetails := fun _ => none
      dataElementType := fun _ => Option (JInt .i32)
      isDirectPermutationOrder := fun e => nomatch e
      isIntegerType := fun _ => false
      allIdentityIndices := fun _ _ => false
      eachDataIndex := fun _ => []
      indexRange := fun _ _ => []
      dataIndexAt := fun _ i => i
      readData := fun _ _ => .error .boundsError
      isMissing := Option.isNone
      isReversePermutationOrder := fun e => nomatch e
      writeIndex := fun v _ _ => .ok v
      nextIndex := (· + 1)
      previousIndex := (· - 1)
      reverse := fun v _ _ => .ok v
      wrapDataWithoutMissing := fun v =>
        withoutMissingVector (fun _ => false) JlError.argumentError v true
      permutationOrder := fun e _ => nomatch e
      nextAlgorithm := id
      appendBounds := fun (_, _, s) lo hi => (lo, hi, s)
      sortWrapped := fun wrapped _ _ (lo, hi, s) => do
        match s with
        | none =>
          let _ ← makeScratchNothing scratchOps (hi - lo + 1).toNat
          pure wrapped.data
        | some existing =>
          let _ ← makeScratchOther scratchOps existing 4 (hi - lo + 1).toNat
          pure wrapped.data
      sortVector := fun v _ _ _ => .ok v
    }
    let vecOps : SortVectorOps (Array (Option (JInt .i32))) (Algorithm (BracketSortTarget Int) Int)
        (Option (JInt .i32) → Option (JInt .i32) → Bool) Unit Bool
        (Option (Array (Option (JInt .i32))))
        (Int × Int × Option (Array (Option (JInt .i32)))) JlError := {
      applyInitialOptimizations := maybeApplyInitialGeneric
      ordering := fun _ _ rev o => match rev with | some r => r | none => o
      runSort := fun v a o kw => sortMissingOptimization missingOps v a o kw
      withScratch := fun s => (1, values.size, s)
    }
    ∃ sorted,
      sortVectorBang vecOps values (.missing .radix)
        (fun _ _ => false) () none false (some scratch) = .ok sorted
def IEEECodecLaws {α : Type} (codec : IEEECodec α) : Prop :=
  (∀ value, codec.decode (codec.encode value) = .ok value) ∧
  (∀ value, codec.encode value < 2 ^ 64) ∧
  (∀ a b,
    codec.less a b =
      if codec.isNaN b then !codec.isNaN a
      else if codec.isNaN a then false
      else if codec.signbit a != codec.signbit b then codec.signbit a
      else if codec.signbit a then decide (codec.encode b < codec.encode a)
      else decide (codec.encode a < codec.encode b))

def IEEEFloatOptimizationCorrect : Prop :=
  (∀ (α : Type) (signbit : α → Bool) (x : α),
    afterZeroForward signbit x = !signbit x ∧
    afterZeroReverse signbit x = signbit x) ∧
  (∀ (isIEEE isConcrete : Type → Bool) (T : Type),
    isConcreteIEEEFloat isIEEE isConcrete T = (isIEEE T && isConcrete T)) ∧
  (∀ (α Alg : Type) (codec : IEEECodec α) (nextAlgorithm : Alg → Alg)
      (sortUnsigned : Array Nat → Alg → Bool → ArraySortKeywords Nat →
        Jl (Array Nat × Option (Array Nat)))
      (sortFallback : Array α → Alg → Bool → ArraySortKeywords Nat →
        Jl (Array α × Option (Array Nat)))
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
      SortedValues (if reverse then fun a b => codec.less b a else codec.less) result.toList ∧
      result.toList.filter codec.isNaN = values.toList.filter codec.isNaN)

def CheckSortedCorrect : Prop :=
  ∀ (α Alg : Type) [Inhabited α] (lt : α → α → Bool)
      (nextAlgorithm : Alg → Alg)
      (values : Array α) (algorithm : Alg),
    NegTransOrder lt →
    let sortNext := fun (v : Array α) (_ : Alg) (o : α → α → Bool) (kw : ArraySortKeywords α) => do
      let sorted ← storageInsertion arrayStorage o v kw.lo kw.hi
      pure (sorted, kw.scratch)
    ∃ result scratch,
      sortCheckSorted (storageCheckSortedOps arrayStorage nextAlgorithm sortNext)
        values algorithm lt { lo := 1, hi := values.size } = .ok (result, scratch) ∧
      List.Perm values.toList result.toList ∧ SortedValues lt result.toList
def integerArraySpan {t : IntTy} (values : Array (JInt t)) : Int :=
  match values.toList.map (fun value => value.val) with
  | [] => 0
  | first :: rest => rest.foldl max first - rest.foldl min first

def ComputeExtremaCountingCorrect : Prop :=
  ∀ (t : IntTy) (values : Array (JInt t)) (reverse : Bool),
    0 < values.size → integerArraySpan values < IntTy.max .i64 →
    ∃ result,
      sortComputeExtrema (arrayExtremaCountingOps t values) values () reverse
        { lo := 1, hi := values.size } = .ok result ∧
      List.Perm values.toList result.toList ∧
      SortedValues (fun a b : JInt t =>
        if reverse then decide (b.val < a.val) else decide (a.val < b.val)) result.toList

def UIntVectorRoundTrip : Prop :=
  ∀ (t : IntTy) (values : Array (JInt t)) (lo hi : Int) (reverse : Bool),
    1 ≤ lo → lo ≤ hi + 1 → hi ≤ values.size →
    ∃ mapped,
      uintMapVectorBang (arrayIntegerMapOps t) values lo hi reverse = .ok mapped ∧
      mapped.size = values.size ∧
      uintUnmapVectorBang (arrayIntegerUnmapOps t) values mapped lo hi reverse = .ok values ∧
      (∀ index value, lo ≤ index → index ≤ hi → arrayRead values index = .ok value →
        arrayRead mapped index = .ok (integerCode t reverse value))

def RadixWrapperCorrect : Prop :=
  ∀ (t : IntTy) (values : Array (JInt t)) (minimum maximum : JInt t) (reverse : Bool),
    let low := if reverse then maximum.val else minimum.val
    let high := if reverse then minimum.val else maximum.val
    low ≤ high →
    (∀ value, value ∈ values.toList → low ≤ value.val ∧ value.val ≤ high) →
    ∃ result scratch,
      sortRadixAlgorithm (arrayRadixWrapperOps t arrayRadixHeuristicOps) values reverse
        { lo := 1, hi := values.size, minimum, maximum } = .ok (result, scratch) ∧
      List.Perm values.toList result.toList ∧
      SortedValues (fun a b : JInt t =>
        if reverse then decide (b.val < a.val) else decide (a.val < b.val)) result.toList

def sliceRows {α : Type} (width count : Nat) (values : List α) : List (List α) :=
  (List.range count).map fun index => (values.drop (index * width)).take width

def SortedSlices {α : Type} (lt : α → α → Bool)
    (before after : List (List α)) : Prop :=
  before.length = after.length ∧
  ∀ (index : Nat) (input result : List α),
    before[index]? = some input → after[index]? = some result →
    List.Perm input result ∧ SortedValues lt result

def arrayChunkRows {α : Type} (width : Nat) (values : Array α) : List (List α) :=
  if width = 0 then [] else
    (List.range ((values.size + width - 1) / width)).map fun index =>
      (values.toList.drop (index * width)).take width

def ChunkSortCorrect : Prop :=
  ∀ (α : Type) [Inhabited α] (pivot : Int → Int → Int)
      (values : Array α) (width : Nat)
      (algorithm : Algorithm (BracketSortTarget Int) Int)
      (order : α → α → Bool) (scratch : Option (Array α)),
    0 < width →
    NegTransOrder order →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    ∃ result,
      sortChunksDispatch (arrayChunkDispatchOps pivot)
        values width algorithm order scratch = .ok result ∧
      result.size = values.size ∧
      SortedSlices order (arrayChunkRows width values) (arrayChunkRows width result)

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

def MultidimensionalCopyCorrect : Prop :=
  ∀ (A α Axes : Type) [Inhabited α]
      (layout : DimensionArrayLayout A α Axes)
      (pivot : Int → Int → Int) (lt : α → α → Bool)
      (array : A) (dimension : Nat)
      (algorithm : Algorithm (BracketSortTarget Int) Int)
      (reverse : Option Bool) (scratch : Option (Array α)),
    DimensionLayoutLaws layout → NegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    1 ≤ dimension → dimension ≤ layout.ndims array →
    0 < layout.axisLength array dimension →
    ∃ result, sortArrayDimension (dimensionArrayOps layout pivot)
        array dimension algorithm lt () reverse lt scratch = .ok result ∧
      layout.axes result = layout.axes array ∧
      SortedSlices (if reverse = some true then fun a b => lt b a else lt)
        (layout.slices array dimension) (layout.slices result dimension)
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

def MultidimensionalMutationCorrect : Prop :=
  (∀ (A D Idx K V E : Type) (view : A → List (Option K) → Except E V)
      (dimensionValue : D → Nat) (dimensionCount : A → Nat)
      (getIndex : Idx → Nat → K) (array : A) (dimension : D) (index : Idx),
    getView view dimensionValue dimensionCount getIndex array dimension index =
      view array ((List.range (dimensionCount array)).map fun offset =>
        if offset + 1 = dimensionValue dimension then none
        else some (getIndex index (offset + 1)))) ∧
  (∀ (A α Axes Index K : Type) [Inhabited α]
      (layout : SliceArrayLayout A α Axes Index K)
      (pivot : Int → Int → Int) (lt : α → α → Bool)
      (array : A) (dimension : Int)
      (algorithm : Algorithm (BracketSortTarget Int) Int)
      (reverse : Option Bool) (scratch : Option (Array α)),
    SliceLayoutLaws layout → NegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    let ops := sliceArrayOps layout pivot
    let valid := 1 ≤ dimension ∧ dimension ≤ Int.ofNat (layout.ndims array)
    ((valid →
      ∃ result, sortBangDimensions ops array dimension algorithm lt () reverse lt scratch false =
          .ok result ∧
        layout.axes result = layout.axes array ∧
        SortedSlices (if reverse = some true then fun a b => lt b a else lt)
          (layout.slices array dimension.toNat)
          (layout.slices result dimension.toNat)) ∧
      (¬ valid →
        sortBangDimensions ops array dimension algorithm lt () reverse lt scratch false =
          .error (.argumentError "dimension out of range"))))

def SortDimsChecked : Prop :=
  ∀ (A α Axes Index K : Type) [Inhabited α]
      (layout : SliceArrayLayout A α Axes Index K)
      (pivot : Int → Int → Int) (lt : α → α → Bool)
      (array : A) (dimension : Int)
      (algorithm : Algorithm (BracketSortTarget Int) Int)
      (reverse : Option Bool) (useDefaultScratch : Bool),
    (dimension < 1 ∨ Int.ofNat (layout.ndims array) < dimension) →
    sortBangDimensions (sliceArrayOps layout pivot) array dimension
      algorithm lt () reverse lt none useDefaultScratch =
      .error (.argumentError "dimension out of range")

def BracketKernelCorrect : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (values : Array α) (lo hi : Int)
      (lower upper : Option α),
    NegTransOrder lt → 1 ≤ lo → lo ≤ hi + 1 → hi ≤ values.size →
    (∀ a b, lower = some a → upper = some b → lt b a = false) →
    let window := arraySlice values lo hi
    let selected := window.filter fun value =>
      !(lower.any fun bound => lt value bound) &&
        upper.all (fun bound => !lt bound value)
    ∃ result count last,
      bracketKernel (storageBracketKernelOps arrayStorage lt) values lo hi lower upper () =
        .ok (result, count, last) ∧
      List.Perm values.toList result.toList ∧
      count = (window.filter fun value => lower.any fun bound => lt value bound).length ∧
      last = lo + Int.ofNat selected.length - 1 ∧
      List.Perm selected (arraySlice result lo last) ∧
      result.toList.take (lo - 1).toNat = values.toList.take (lo - 1).toNat ∧
      result.toList.drop hi.toNat = values.toList.drop hi.toNat

def MoveVectorCorrect : Prop :=
  ∀ (α : Type) (values : Array α) (target source : BracketSortTarget Int),
    let targetIndices := bracketTargetIndices target
    let sourceIndices := bracketTargetIndices source
    targetIndices.length = sourceIndices.length →
    targetIndices.Nodup → sourceIndices.Nodup →
    (∀ i, i ∈ targetIndices ++ sourceIndices → 1 ≤ i ∧ i ≤ values.size) →
    ((storageMoveOps (arrayStorage (α := α))).disjoint target source = true ∨
      (storageMoveOps (arrayStorage (α := α))).minimum source ≤ (storageMoveOps (arrayStorage (α := α))).minimum target) →
    ∃ result, moveVector (storageMoveOps arrayStorage) values target source = .ok result ∧
      List.Perm values.toList result.toList ∧
      (∀ i j value, (i, j) ∈ targetIndices.zip sourceIndices →
        arrayRead values j = .ok value → arrayRead result i = .ok value) ∧
      (∀ index, index ∉ targetIndices ++ sourceIndices →
        arrayRead result index = arrayRead values index)

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
        BalancedParentheses (text result)) ∧
      (∀ threshold result, showSmallAlgorithmType ops io threshold = .ok result →
        text result = "Base.Sort.Small{" ++ toString threshold ++ "}") ∧
      (∀ algorithm result, showAlgorithmType ops io algorithm = .ok result →
        text result = nameText (ops.algorithmTypeName algorithm))

def SubArraySortCorrect : Prop :=
  ∀ (α Alg : Type) [Inhabited α] (lt : α → α → Bool)
      (nextAlgorithm : Alg → Alg)
      (view : FlatSortView α) (algorithm : Alg),
    NegTransOrder lt →
    0 ≤ view.offset → view.offset + Int.ofNat view.length ≤ view.parent.storage.size →
    let sortSlice := fun (v : Array α) (_ : Alg) (o : α → α → Bool) (kw : ArraySortKeywords α) => do
      let sorted ← storageInsertion arrayStorage o v kw.lo kw.hi
      pure (sorted, kw.scratch)
    ∃ result, sortSubArrayUnwrappable
        (flatSubArraySortOpsWithNext view nextAlgorithm sortSlice)
        view algorithm lt { lo := 1, hi := view.length } = .ok result ∧
      result.offset = view.offset ∧ result.length = view.length ∧
      result.parent.dimensions = view.parent.dimensions ∧
      List.Perm view.parent.storage.toList result.parent.storage.toList ∧
      SortedValues lt (arraySlice result.parent.storage
        (view.offset + 1) (view.offset + Int.ofNat view.length)) ∧
      result.parent.storage.toList.take view.offset.toNat =
        view.parent.storage.toList.take view.offset.toNat ∧
      result.parent.storage.toList.drop (view.offset + Int.ofNat view.length).toNat =
        view.parent.storage.toList.drop (view.offset + Int.ofNat view.length).toNat

def RadixChunkHeuristicLaws (ops : RadixChunkHeuristicOps Int Nat Nat JlError) : Prop :=
  (∀ hi lo, 0 < hi - lo → hi - lo ≤ IntTy.max .i64 →
    ops.subtract hi lo = hi - lo ∧
    ops.maybeUnsigned (hi - lo) = (hi - lo).toNat) ∧
  ops.bitsToNat = id ∧
  (∀ span : Nat, 0 < span →
    let guess := ops.min (ops.fromNat 10)
      (ops.add (ops.divide (ops.multiply (ops.log span) (ops.fromNat 3)) (ops.fromNat 4))
        (ops.fromNat 3))
    ∃ g : Nat, 3 ≤ g ∧ g ≤ 10 ∧
      ∀ bits : Nat, 0 < bits → bits ≤ 128 →
        let inner := (bits + g - 1) / g
        let outer := (bits + inner - 1) / inner
        ops.ceilingDiv bits guess = ops.fromNat inner ∧
        ops.ceilingDiv bits (ops.fromNat inner) = ops.fromNat outer ∧
        ops.toUInt8 (ops.fromNat outer) = .ok (UInt8.ofNat outer))

def RadixChunkCoversBits : Prop :=
  ∀ (ops : RadixChunkHeuristicOps Int Nat Nat JlError) (lo hi : Int) (bits : Nat),
    RadixChunkHeuristicLaws ops →
    0 < hi - lo → hi - lo ≤ IntTy.max .i64 →
    0 < bits → bits ≤ 128 →
    ∃ chunk, radixChunkSizeHeuristic ops lo hi bits = .ok chunk ∧
      0 < chunk.toNat ∧ chunk.toNat ≤ 10 ∧
      bits ≤ ((bits + chunk.toNat - 1) / chunk.toNat) * chunk.toNat

def CollectedSortCorrect : Prop :=
  ∀ (C α : Type) [Inhabited α] (enumerate : C → List α)
      (lt : α → α → Bool) (pivot : Int → Int → Int) (collection : C)
      (algorithm : Algorithm (BracketSortTarget Int) Int) (reverse : Option Bool)
      (scratch : Option (Array α)),
    NegTransOrder lt →
    (∀ lo hi, lo ≤ hi → lo ≤ pivot lo hi ∧ pivot lo hi ≤ hi) →
    isFullSortAlgorithm algorithm = true →
    let effective := if reverse = some true then fun a b => lt b a else lt
    let ops : SortCollectOps C (Array α) JlError (Option (Array α)) := {
      collect := fun source => .ok (enumerate source).toArray
      sortBang := fun source selectedScratch =>
        sortVectorBang (sourceVectorSortOps arrayStorage defaultBracketNumerics pivot)
          source algorithm lt () reverse lt selectedScratch
    }
    ∀ result, sortCollected ops collection scratch = .ok result →
      List.Perm (enumerate collection) result.toList ∧
      SortedValues effective result.toList

def IEEEFloatPermutationCorrect : Prop :=
  ∀ (α Alg : Type) [Inhabited α] (codec : IEEECodec α)
      (nextAlgorithm : Alg → Alg)
      (sortPermutation : Array Int → Alg → (Bool × Array Nat) → ArraySortKeywords Nat →
        Jl (Array Int × Option (Array Nat)))
      (sortFallback : Array Int → Alg → (Bool × Array α) → ArraySortKeywords Nat →
        Jl (Array Int × Option (Array Nat)))
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
      SortpermOrdered (if reverse then fun a b => codec.less b a else codec.less)
        data.toList (result.toList.map Int.toNat)

def LegacyInvalidWindowRejected : Prop :=
  (∀ (α : Type) [Inhabited α] (lt : α → α → Bool)
      (values scratch : Array α) (lo hi : Int),
    NegTransOrder lt →
    1 ≤ lo → lo ≤ hi + 1 → hi ≤ Int.ofNat values.size →
    (∃ result,
      legacySortBounds (storageLegacyOps arrayStorage lt) values lo hi .insertion () = .ok result ∧
      legacySortIgnoredScratch (storageLegacyOps arrayStorage lt) values lo hi .insertion () () = .ok result ∧
      legacySortWithScratch (storageLegacyOps arrayStorage lt) values lo hi .insertion () scratch = .ok result ∧
      List.Perm values.toList result.toList ∧
      SortedValues lt (arraySlice result lo hi) ∧
      result.toList.take (lo - 1).toNat = values.toList.take (lo - 1).toNat ∧
      result.toList.drop hi.toNat = values.toList.drop hi.toNat) ∧
    (∃ wholeResult,
      legacySortWhole (storageLegacyOps arrayStorage lt) values .insertion () = .ok wholeResult ∧
      List.Perm values.toList wholeResult.toList ∧
      SortedValues lt wholeResult.toList)) ∧
  (∀ (α : Type) [Inhabited α] (lt : α → α → Bool)
      (values scratch : Array α) (algorithm : LegacyArrayAlgorithm) (lo hi : Int),
    lo ≤ hi → (lo < 1 ∨ Int.ofNat values.size < hi) →
    legacySortBounds (storageLegacyOps arrayStorage lt) values lo hi algorithm () = .error .boundsError ∧
    legacySortIgnoredScratch (storageLegacyOps arrayStorage lt) values lo hi algorithm () () = .error .boundsError ∧
    legacySortWithScratch (storageLegacyOps arrayStorage lt) values lo hi algorithm () scratch = .error .boundsError)

def LegacyDispatchRejectsCycles : Prop :=
  (∀ (α : Type) [Inhabited α] (lt : α → α → Bool)
      (values : Array α) (lo hi : Int) (scratch : Option (Array α)),
    NegTransOrder lt →
    1 ≤ lo → lo ≤ hi + 1 → hi ≤ Int.ofNat values.size →
    let ops : LegacyDispatchOps (Array α) Int LegacyArrayAlgorithm Unit
        (LegacyArrayKeywords α) (Option (Array α)) JlError := {
      getKeywords := fun kw => .ok (kw.lo, kw.hi, kw.scratch, kw.entry)
      sameAlgorithm := BEq.beq
      undefinedAlgorithm := fun _ _ _ =>
        .argumentError "Base.Sort._sort! is not defined for this algorithm"
      legacySort := fun current lo' hi' alg ord =>
        legacySortBounds (storageLegacyOps arrayStorage lt) current lo' hi' alg ord
    }
    ∃ expected,
      legacySortDispatch ops values .insertion () ⟨lo, hi, scratch, none⟩ = .ok (expected, scratch) ∧
      List.Perm values.toList expected.toList ∧
      SortedValues lt (arraySlice expected lo hi) ∧
      expected.toList.take (lo - 1).toNat = values.toList.take (lo - 1).toNat ∧
      expected.toList.drop hi.toNat = values.toList.drop hi.toNat) ∧
  (∀ (V K Alg O Kws Scratch : Type)
      (ops : LegacyDispatchOps V K Alg O Kws Scratch JlError)
      (vector : V) (algorithm entry : Alg) (order : O) (keywords : Kws)
      (lo hi : K) (scratch : Scratch) (message : String),
    ops.getKeywords keywords = .ok (lo, hi, scratch, some entry) →
    ops.sameAlgorithm entry algorithm = true →
    ops.undefinedAlgorithm vector algorithm order = .argumentError message →
    legacySortDispatch ops vector algorithm order keywords =
      .error (.argumentError message))

/-! ## Proofs and Refutations (Batch 1) -/

theorem issortedLoop_list {α : Type} (lt : α → α → Bool) :
    ∀ (xs : List α) (prev : α) (itr : List α),
      issortedLoop listIterator (fun _ => lt) () itr xs.length prev xs = true ↔
        AdjacentSorted lt (prev :: xs)
  | [], prev, itr => by simp [issortedLoop, AdjacentSorted]
  | b :: rest, prev, itr => by
    unfold issortedLoop
    change (if lt b prev then false
      else issortedLoop listIterator (fun _ => lt) () itr rest.length b rest) = true ↔
      (lt b prev = false ∧ AdjacentSorted lt (b :: rest))
    cases h : lt b prev
    · simp [issortedLoop_list lt rest b itr]
    · simp

theorem issortedAdjacent_proven : IssortedAdjacent := by
  intro α lt xs
  cases xs with
  | nil => simp [issorted, listIterator, AdjacentSorted]
  | cons a rest =>
    cases rest with
    | nil => simp [issorted, listIterator, AdjacentSorted]
    | cons b tail =>
      unfold issorted
      change (if lt b a then false
        else issortedLoop listIterator (fun _ => lt) () (a :: b :: tail) tail.length b tail) = true ↔
        (lt b a = false ∧ AdjacentSorted lt (b :: tail))
      cases h : lt b a
      · simp [issortedLoop_list lt tail b (a :: b :: tail)]
      · simp

theorem issortedLoop_const_order {I α St O : Type} (iter : FiniteIterator I α St)
    (lt : O → α → α → Bool) (order : O) (itr : I) :
    ∀ (fuel : Nat) (prev : α) (state : St),
      issortedLoop iter lt order itr fuel prev state =
        issortedLoop iter (fun (_ : Unit) => lt order) () itr fuel prev state
  | 0, _, _ => rfl
  | fuel + 1, prev, state => by
    unfold issortedLoop
    cases iter.next itr state with
    | none => rfl
    | some pair =>
      dsimp only
      cases lt order pair.1 prev
      · simp [issortedLoop_const_order iter lt order itr fuel pair.1 pair.2]
      · rfl

theorem issorted_const_order {I α St O : Type} (iter : FiniteIterator I α St)
    (lt : O → α → α → Bool) (order : O) (itr : I) :
    issorted iter lt order itr = issorted iter (fun (_ : Unit) => lt order) () itr := by
  unfold issorted
  cases iter.first itr with
  | none => rfl
  | some first =>
    dsimp only
    cases iter.next itr first.2 with
    | none => rfl
    | some second =>
      dsimp only
      rw [issortedLoop_const_order iter lt order itr _ second.1 second.2]

theorem issortedKeywordsCorrect_proven : IssortedKeywordsCorrect := by
  intro α L B O orderOf lt values less byFn reverse order
  unfold issortedKeywords
  by_cases hrev : reverse = some true
  · simp only [hrev, ↓reduceIte, issorted_const_order]
    exact issortedAdjacent_proven α _ values
  · simp only [hrev, ↓reduceIte, issorted_const_order]
    exact issortedAdjacent_proven α _ values

theorem u8WindowReadsZero :
    searchsortedlastBounds arrayVectorOps (fun _ a b => decide (a < b)) ()
      (Array.replicate 255 (0 : Int)) 0 (JInt.lit .u8 1) (JInt.lit .u8 255) =
      .invalidAccess 0 := by
  decide +kernel

theorem windowSearchInBounds_refuted : ¬ WindowSearchInBounds := by
  intro h
  exact (h Int (fun a b => decide (a < b)) (Array.replicate 255 0) 0 .u8
    (JInt.lit .u8 1) (JInt.lit .u8 255) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).1 0 u8WindowReadsZero

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
  have e : searchsortedlastIntegerRange (bitIntegerRealRangeOps .i8) realQueryLt false
      (JInt.lit .i8 (-100), JInt.lit .i8 1, JInt.lit .i8 100, JInt.lit .i64 201)
      ⟨50, 50⟩ = .ok (JInt.lit .i64 (-105)) := rfl
  rw [e] at hr
  cases hr
  exact absurd hc.1 (by decide)

theorem rangeSearchEmptyCorrect_refuted : ¬ RangeSearchEmptyCorrect := by
  intro h
  have hv : RangeValid (t := .i64) (JInt.lit .i64 1) (JInt.lit .i64 1)
      (JInt.lit .i64 0) (JInt.lit .i64 0) := by
    unfold RangeValid rangeElem; decide
  have hq : RealQueryValid ⟨0, 0⟩ := by unfold RealQueryValid; decide
  have e : searchsortedfirstIntegerRange (bitIntegerRealRangeOps .i64) realQueryLtRange true
      (JInt.lit .i64 1, JInt.lit .i64 1, JInt.lit .i64 0, JInt.lit .i64 0)
      ⟨0, 0⟩ = .ok (JInt.lit .i64 0) := rfl
  have h1 := (h.1 .i64 _ _ _ _ ⟨0, 0⟩ true hv hq (by decide)).1
  rw [e] at h1
  exact absurd h1 (by decide)

private inductive F64 where
  | negHuge | zero | nearPosHuge | posHuge | posInf
  deriving DecidableEq

def F64.isFinite : F64 → Bool
  | .posInf => false
  | _ => true

def F64.lt : F64 → F64 → Bool
  | .negHuge, .negHuge => false
  | .negHuge, _ => true
  | .zero, .negHuge | .zero, .zero => false
  | .zero, _ => true
  | .nearPosHuge, .posHuge | .nearPosHuge, .posInf => true
  | .nearPosHuge, _ => false
  | .posHuge, .posInf => true
  | .posHuge, _ => false
  | .posInf, _ => false

def F64.sub : F64 → F64 → F64
  | .nearPosHuge, .negHuge => .posInf
  | a, .zero => a
  | .posHuge, .negHuge => .posInf
  | _, _ => .zero

def F64.div : F64 → F64 → F64
  | .posInf, _ => .posInf
  | _, _ => .nearPosHuge

def F64.addOne : F64 → F64
  | .posInf => .posInf
  | x => x

def F64.roundInteger : F64 → Jl Int
  | .posInf => .error (.inexactError "Int64")
  | _ => .ok 2

def f64RangeValues : List F64 := [.negHuge, .zero, .posHuge]

def f64RangeValue (_ _ : F64) : Nat → F64
  | 0 => .negHuge
  | 1 => .zero
  | _ => .posHuge

def f64RangeOps : RealRangeOps Unit F64 F64 F64 Int Unit JlError where
  requireOneBased := fun _ => .ok ()
  first := fun _ => .negHuge
  step := fun _ => .posHuge
  last := fun _ => .posHuge
  length := fun _ => 3
  zeroIndex := 0
  oneIndex := 1
  increment := (· + 1)
  decrement := (· - 1)
  isZero := fun a => decide (a = .zero)
  subtract := F64.sub
  divide := F64.div
  addOne := F64.addOne
  roundInteger := F64.roundInteger
  get := fun _ i =>
    match f64RangeValues[(i - 1).toNat]? with
    | some v => .ok v
    | none => .error .boundsError
  finiteSearch := fun _ x =>
    f64RangeValues.all F64.isFinite = true ∧ F64.isFinite x = true

theorem floatRangeSearchNoThrow_refuted : ¬ FloatRangeSearchNoThrow := by
  intro h
  have hf : RealRangeOpsFaithful f64RangeOps () .nearPosHuge f64RangeValues
      f64RangeValue (fun a _ => a) (fun a => decide (a = .zero))
      F64.isFinite F64.isFinite F64.isFinite := by
    refine ⟨rfl, rfl, rfl, rfl, fun _ => ⟨rfl, rfl⟩, rfl, rfl, by decide, by decide,
      ?_, Iff.rfl, ?_⟩
    · intro i h1 h2
      change i ≤ 3 at h2
      have : i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl | rfl <;> exact ⟨_, rfl, rfl⟩
    · intro q hq
      cases q <;> simp [f64RangeOps, F64.isFinite, F64.roundInteger] at hq ⊢
  have hfin : f64RangeOps.finiteSearch () .nearPosHuge := by
    simp [f64RangeOps, f64RangeValues, F64.isFinite]
  have hsort : RangeSortedBy F64.lt f64RangeValues := by
    simp [f64RangeValues, RangeSortedBy, F64.lt]
  have hpred : RealRangeSearchPredicatesSorted f64RangeValues
      (fun _ => F64.lt) (fun _ => F64.lt) () .nearPosHuge := by
    intro i j left right hij hi hj
    have hi3 : i < 3 := by
      have := List.getElem?_eq_some_iff.1 hi
      simpa [f64RangeValues] using this.1
    have hj3 : j < 3 := by
      have := List.getElem?_eq_some_iff.1 hj
      simpa [f64RangeValues] using this.1
    have : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [f64RangeValues] at hi hj <;> subst hi hj <;> decide
  obtain ⟨first, last, _, hlast, _⟩ :=
    h Unit F64 F64 F64 Unit f64RangeOps (fun _ => F64.lt) (fun _ => F64.lt)
      (fun _ => F64.lt) () () .nearPosHuge f64RangeValues f64RangeValue
      (fun a _ => a) (fun a => decide (a = .zero)) F64.isFinite F64.isFinite
      F64.isFinite hf hfin hsort hpred
  change Except.error (JlError.inexactError "Int64") = Except.ok last at hlast
  cases hlast

private inductive SortFloat3 where
  | negZero | posZero | one
  deriving DecidableEq

def SortFloat3.lt : SortFloat3 → SortFloat3 → Bool
  | .negZero, .posZero | .negZero, .one | .posZero, .one => true
  | _, _ => false

def SortFloat3.eq : SortFloat3 → SortFloat3 → Bool
  | .negZero, .posZero | .posZero, .negZero => true
  | a, b => decide (a = b)

theorem insortedRangeAgrees_refuted : ¬ InsortedRangeAgrees := by
  intro h
  have hnt : NegTransOrder SortFloat3.lt := by
    refine ⟨?_, ?_, ?_⟩
    · intro a; cases a <;> rfl
    · intro a b c; cases a <;> cases b <;> cases c <;> decide
    · intro a b c; cases a <;> cases b <;> cases c <;> decide
  have hrefl : ∀ a, SortFloat3.eq a a = true := by intro a; cases a <;> rfl
  have hsymm : ∀ a b, SortFloat3.eq a b = SortFloat3.eq b a := by
    intro a b; cases a <;> cases b <;> rfl
  have hcompat : ∀ a b, (SortFloat3.lt a b = false ∧ SortFloat3.lt b a = false) →
      SortFloat3.eq a b = true := by
    intro a b; cases a <;> cases b <;> decide
  have hadj : AdjacentSorted SortFloat3.lt [.posZero, .one] := by
    simp [AdjacentSorted, SortFloat3.lt]
  have heq := h SortFloat3 SortFloat3.lt SortFloat3.eq [.posZero, .one] .negZero
    hnt hrefl hsymm hcompat hadj
  revert heq
  decide +kernel

theorem sendToEndInBounds_refuted : ¬ SendToEndInBounds := by
  intro h
  obtain ⟨last, result, hrun⟩ :=
    h Int (· == 0) #[1, 2] 0 2 (by decide)
  have herr : (sendToEndBang (storageSendToEndOps (arrayStorage (α := Int)))
      (fun value => fun state => .ok ((value == 0), state))
      ⟨1, 1, (#[1, 2] : Array Int).size⟩ (some 0) (some 2)).run (#[1, 2] : Array Int) =
      .error .boundsError := by
    decide +kernel
  rw [herr] at hrun
  cases hrun

def testBracketNumerics : BracketNumerics where
  cbrt := fun n => Float.ofNat n
  roundInt := fun _ => 1
  floorInt := fun v => .ok (binary64Floor v)
  topSetBit := fun n => if n = 0 then 0 else Nat.log2 n + 1
  hashLength := id
  hashAttempt := fun a b => a + b
  sampleIndex := fun _ lo _ => .ok lo

theorem testBracketNumerics_laws : BracketNumericsLaws testBracketNumerics := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn _
    simp [testBracketNumerics]
    omega
  · intro value _ _ _
    rfl
  · intro n
    rfl
  · intro seed lo hi hle
    exact ⟨lo, rfl, Int.le_refl lo, hle⟩

theorem juliaPivot_bounds : ∀ lo hi : Int, lo ≤ hi →
    lo ≤ juliaPivot lo hi ∧ juliaPivot lo hi ≤ hi := by
  intro lo hi hle
  unfold juliaPivot
  have hpos : 0 < (hi - lo + 1).toNat := by omega
  have hmod := Nat.mod_lt ((juliaHashInt lo + 2 ^ 64 - lo.toNat) % 2 ^ 64) hpos
  omega

def intLt (a b : Int) : Bool := decide (a < b)

theorem intLt_negTransOrder : NegTransOrder intLt := by
  refine ⟨?_, ?_, ?_⟩
  · intro a; simp [intLt]
  · intro a b c; simp [intLt]; omega
  · intro a b c; simp [intLt]; omega

def reversedRangeInput : Array Int :=
  #[4, 5, 2, 1, 1, 4, 4, 4, 2, 4, 5, 5, 3, 3, 2, 2, 4, 5, 2, 2, 5, 5]

theorem reversedRangePartialSortOutcome :
    partialSortBang (storagePartialSortOps arrayStorage testBracketNumerics juliaPivot)
      reversedRangeInput (.ordinal 5 (-1) 3 3) intLt none = .ok [2, 2, 1] := by
  decide +kernel

theorem partialSortRangeCorrect_refuted : ¬ PartialSortRangeCorrect := by
  intro h
  have hb : ∀ index, index ∈ bracketTargetIndices (.ordinal 5 (-1) 3 3) →
      1 ≤ index ∧ index ≤ reversedRangeInput.size := by
    decide +kernel
  obtain ⟨result, hbang, _, hsel⟩ :=
    h Int intLt testBracketNumerics juliaPivot reversedRangeInput
      (.ordinal 5 (-1) 3 3) testBracketNumerics_laws intLt_negTransOrder
      (by decide +kernel) juliaPivot_bounds hb
  rw [reversedRangePartialSortOutcome] at hbang
  injection hbang with hres
  subst hres
  have hexp : ((bracketTargetIndices (.ordinal 5 (-1) 3 3)).filterMap fun index =>
      (sortRef intLt reversedRangeInput.toList)[(index - 1).toNat]?) =
      [2, 2, 2] := by
    decide +kernel
  rw [hexp] at hsel
  exact absurd hsel (by decide)

theorem partialSortEmptyRange_refuted : ¬ PartialSortEmptyRange := by
  intro h
  have h1 := h testBracketNumerics juliaPivot (Array.replicate 260 0) 4 1 3
  have herr : partialSortBang (storagePartialSortOps arrayStorage testBracketNumerics juliaPivot)
      (Array.replicate 260 (0 : Int)) (.ordinal 4 1 3 0)
      (fun a b : Int => decide (a < b)) none =
      .error (.argumentError "reducing over an empty collection") := by
    decide +kernel
  rw [herr] at h1
  cases h1

theorem partialSortpermIndexTypeCorrect_refuted : ¬ PartialSortpermIndexTypeCorrect := by
  intro h
  have hnd : (bracketTargetIndices (.index (3 : Int))).Nodup := by decide
  have hb : ∀ index, index ∈ bracketTargetIndices (.index (3 : Int)) →
      1 ≤ index ∧ index ≤ (Array.replicate 128 (0 : Int)).size ∧
      IntTy.min .i8 ≤ index ∧ index ≤ IntTy.max .i8 := by
    decide +kernel
  obtain ⟨result, hr, _, _⟩ :=
    h .i8 Int intLt (Array.replicate 128 0) (.index 3) juliaPivot none
      intLt_negTransOrder hnd (by decide +kernel) hb juliaPivot_bounds
  change partialSortperm (storagePartialSortpermOps arrayStorage .i8 juliaPivot)
      (Array.replicate 128 (0 : Int)) (.index 3) intLt () none intLt false = .ok result at hr
  have herr : (partialSortperm (storagePartialSortpermOps arrayStorage .i8 juliaPivot)
      (Array.replicate 128 (0 : Int)) (.index 3) intLt () none intLt false).isOk = false := by
    decide +kernel
  rw [hr] at herr
  cases herr
theorem legacySortScratch_refuted : ¬ LegacySortScratch := by
  intro h
  have hb : arrayCheckBounds (#[5, 4, 3, 2, 1] : Array Int) 2 4 = .ok () := by decide
  have hfive : storageLegacyFive arrayStorage intLt #[5, 4, 3, 2, 1] 2 4 .quick = .ok #[5, 2, 3, 4, 1] := by
    decide +kernel
  obtain ⟨result, hscr, _⟩ :=
    h Int intLt #[5, 4, 3, 2, 1] #[] 2 4 .quick hb #[5, 2, 3, 4, 1] hfive
  have herr : legacySortWithScratch (storageLegacyOps arrayStorage intLt) #[5, 4, 3, 2, 1] 2 4 .quick () #[] =
      .error (.argumentError "Base.Sort._sort! is not defined for this algorithm") := by
    decide +kernel
  rw [herr] at hscr
  cases hscr

def legacyPartialInput : Array Int :=
  #[1, 3, 4, 5, 3, 5, 5, 2, 1, 4, 5, 1, 4, 3, 5, 5, 5, 4, 3, 5, 5, 2]

theorem legacyPartialRangeOutcome :
    (match legacyPartialQuickSortBang (storagePartialQuickOps arrayStorage intLt)
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

theorem legacyPartialRangeCorrect_refuted : ¬ LegacyPartialRangeCorrect := by
  intro h
  have hb : ∀ index, index ∈ (List.range 3).map (fun i => (5 : Int) + Int.ofNat i * (-1)) →
      1 ≤ index ∧ index ≤ Int.ofNat legacyPartialInput.size := by
    decide +kernel
  obtain ⟨result, hrun, hsel⟩ :=
    h Int intLt legacyPartialInput 5 (-1) 3 3 intLt_negTransOrder
      (by decide) hb (by decide) (by decide)
  have hout := legacyPartialRangeOutcome
  rw [hrun] at hout
  injection hout with hgotSel
  rw [hgotSel, legacyPartialRangeExpected] at hsel
  exact absurd hsel (by decide)

def dummySliceLayout : SliceArrayLayout Unit Int Unit Nat Int where
  ndims := fun _ => 2
  axisLength := fun _ _ => 2
  cartesianIndices := fun _ _ => .ok [1, 2]
  coordinate := fun i _ => Int.ofNat i
  view := fun _ _ => .ok #[1, 2]
  writeView := fun _ _ _ => .ok ()
  axes := fun _ => ()
  slices := fun _ _ => [[1, 2], [1, 2]]

theorem sortDimsChecked_refuted : ¬ SortDimsChecked := by
  intro h
  have h0 := h Unit Int Unit Nat Int dummySliceLayout juliaPivot intLt () 0
    .defaultStable none true (Or.inl (by decide))
  change Except.error JlError.boundsError =
    Except.error (JlError.argumentError "dimension out of range") at h0
  cases h0

theorem tupleSortExplicitAlgCorrect_refuted : ¬ TupleSortExplicitAlgCorrect := by
  intro h
  obtain ⟨result, hrun, _, _⟩ :=
    h 3 Int intLt juliaPivot ⟨[3, 1, 2], rfl⟩ .quick none
      intLt_negTransOrder juliaPivot_bounds rfl
  change Except.error (JlError.methodError "Base.Sort._sort") = Except.ok result at hrun
  cases hrun

theorem sortMissingScratchAccepted_refuted : ¬ SortMissingScratchAccepted := by
  intro h
  obtain ⟨sorted, hrun⟩ := h #[some (JInt.lit .i32 1)] #[]
  change Except.error (JlError.argumentError "cannot reinterpret Union{Missing, Int32}") =
    Except.ok sorted at hrun
  cases hrun

theorem makeScratchCorrect_proven : MakeScratchCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro V W E ops len backing view h
    unfold makeScratchNothing at h
    cases halloc : ops.allocate len <;> simp [halloc, bind, Except.bind, pure, Except.pure] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, ops.allocateLength len _ halloc⟩
  · intro V W E ops scratch len backing view h
    unfold makeScratchSame at h
    by_cases hgt : len > ops.length scratch
    · simp only [hgt, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
      cases hres : ops.resize scratch len <;> simp [hres] at h
      rcases h with ⟨rfl, rfl⟩
      have hlen := ops.resizeLength scratch len _ hres
      exact ⟨rfl, hlen, by omega, by omega⟩
    · simp only [hgt, ↓reduceIte, bind, Except.bind, pure, Except.pure] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, by omega, by omega, Nat.le_refl _⟩
  · intro V W E ops scratch targetBytes len backing view hpos hdiv h
    unfold makeScratchOther at h
    rw [ops.multiplyEq] at h
    cases hdivEq : ops.divide (len * targetBytes) ops.sizeofBacking with
    | error e => simp [hdivEq, bind, Except.bind] at h
    | ok lenScratch =>
      simp only [hdivEq, bind, Except.bind] at h
      obtain ⟨hbs, hq⟩ := ops.divideEq (len * targetBytes) ops.sizeofBacking lenScratch hdivEq
      have hmul : lenScratch * ops.sizeofBacking = len * targetBytes := by
        rw [hq]
        exact Nat.div_mul_cancel hdiv
      by_cases hgt : lenScratch > ops.length scratch
      · simp only [hgt, ↓reduceIte] at h
        cases hres : ops.resize scratch lenScratch with
        | error e => simp [hres] at h
        | ok resized =>
          simp only [hres] at h
          cases hre : ops.reinterpret targetBytes resized with
          | error e => simp [hre] at h
          | ok v =>
            simp only [hre, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨h1, h2⟩
            subst h1 h2
            have hlen := ops.resizeLength scratch lenScratch resized hres
            have hbytes := ops.reinterpretBytes targetBytes resized v hre
            have hge : lenScratch * ops.sizeofBacking ≤ ops.length resized * ops.sizeofBacking :=
              Nat.mul_le_mul_right ops.sizeofBacking (by omega)
            rw [hmul, ← hbytes, Nat.mul_comm len targetBytes] at hge
            exact ⟨by omega, hbytes, Nat.le_of_mul_le_mul_left hge hpos⟩
      · simp only [hgt, ↓reduceIte, pure, Except.pure] at h
        cases hre : ops.reinterpret targetBytes scratch with
        | error e => simp [hre] at h
        | ok v =>
          simp only [hre, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨h1, h2⟩
          subst h1 h2
          have hbytes := ops.reinterpretBytes targetBytes scratch v hre
          have hge : lenScratch * ops.sizeofBacking ≤ ops.length scratch * ops.sizeofBacking :=
            Nat.mul_le_mul_right ops.sizeofBacking (by omega)
          rw [hmul, ← hbytes, Nat.mul_comm len targetBytes] at hge
          exact ⟨Nat.le_refl _, hbytes, Nat.le_of_mul_le_mul_left hge hpos⟩

theorem withoutMissingVectorCorrect_proven : WithoutMissingVectorCorrect := by
  intro α values
  constructor
  · intro wrapped h
    unfold withoutMissingVector at h
    cases hnone : values.any Option.isNone <;> simp [hnone] at h
    subst h
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro index h1 h2
    have hi : (index - 1).toNat < values.size := by omega
    have hmem : values[(index - 1).toNat] ∈ values.toList := by
      rw [← Array.getElem_toList]
      exact List.getElem_mem _
    have hisSome : (values[(index - 1).toNat]).isNone = false := by
      cases hopt : (values[(index - 1).toNat]).isNone
      · rfl
      · have hany : values.any Option.isNone = true := by
          rw [← Array.any_toList]
          exact List.any_eq_true.2 ⟨_, hmem, hopt⟩
        rw [hnone] at hany
        cases hany
    cases hv : values[(index - 1).toNat] with
    | none => rw [hv] at hisSome; cases hisSome
    | some val =>
      refine ⟨val, ?_, ?_⟩
      · unfold withoutMissingGet arrayRead
        simp only [h1, ↓reduceIte, Array.getElem?_eq_getElem hi, hv, bind, Except.bind, pure, Except.pure]
      · unfold arrayRead
        simp only [h1, ↓reduceIte, Array.getElem?_eq_getElem hi, hv]
  · intro wrapped index value h1 h2
    have hi : (index - 1).toNat < wrapped.data.size := by omega
    refine ⟨⟨wrapped.data.set! (index - 1).toNat value⟩, ?_, ?_, ?_, ?_⟩
    · unfold withoutMissingSet arrayWrite
      simp only [h1, h2, and_self, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    · simp
    · unfold arrayRead
      simp only [h1, ↓reduceIte, Array.set!, Array.setIfInBounds, hi, ↓reduceDIte, Array.getElem?_set]
    · intro other hne
      unfold arrayRead
      by_cases ho1 : 1 ≤ other
      · have hneNat : (index - 1).toNat ≠ (other - 1).toNat := by omega
        simp only [ho1, ↓reduceIte, Array.set!, Array.setIfInBounds, hi, ↓reduceDIte, Array.getElem?_set, hneNat]
      · simp only [ho1, ↓reduceIte]
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

theorem windowIssortedCorrect_proven : WindowIssortedCorrect := by
  intro V α K O E indices checkBounds get lt v lo hi order hchk hreads
  unfold issortedWindow WindowSorted
  rw [hchk]
  simp only [bind, Except.bind]
  exact forIn_window_check indices get lt v order (indices.range (indices.addOne lo) hi) hreads

theorem uintMappingCorrect_proven : UIntMappingCorrect := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t x reverse
    apply Subtype.ext
    have hx := x.property
    cases reverse <;> cases t <;>
      simp [integerDecode, integerCode, uintMapReverse, uintUnmapReverse,
        integerReverseMappingOps, forwardIntegerCode, forwardIntegerDecode,
        uintMapSigned, uintUnmapSigned, uintMapUnsigned, uintUnmapUnsigned,
        xorIntegerWords, JInt.wrap, wrapInt, IntTy.signed, IntTy.min, IntTy.max,
        IntTy.bits] at hx ⊢ <;> omega
  · intro t x y reverse
    have hx := x.property
    have hy := y.property
    cases reverse <;> cases t <;>
      simp [integerCode, uintMapReverse, integerReverseMappingOps, forwardIntegerCode,
        uintMapSigned, uintMapUnsigned, xorIntegerWords, JInt.wrap, wrapInt,
        IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] at hx hy ⊢ <;> omega
  · intro value
    cases value
    rfl
  · intro left right
    rfl

theorem radixChunkCoversBits_proven : RadixChunkCoversBits := by
  intro ops lo hi bits hlaws hspan1 hspan2 hbits1 hbits2
  obtain ⟨hsub, hbitsEq, hguess⟩ := hlaws
  obtain ⟨hsubEq, hunsignedEq⟩ := hsub hi lo hspan1 hspan2
  obtain ⟨g, hg1, hg2, hceil⟩ := hguess (hi - lo).toNat (by omega)
  obtain ⟨hinner, houter, htoUInt8⟩ := hceil bits hbits1 hbits2
  unfold radixChunkSizeHeuristic
  dsimp only
  rw [hsubEq, hunsignedEq, hbitsEq]
  simp only [id_eq, hinner, houter, htoUInt8]
  let inner := (bits + g - 1) / g
  let outer := (bits + inner - 1) / inner
  have hinnerPos : 0 < inner := by
    dsimp [inner]
    have : g ≤ bits + g - 1 := by omega
    exact Nat.div_pos this (by omega)
  have hbitsLeInnerG : bits ≤ g * inner := by
    dsimp [inner]
    have hmod := Nat.div_add_mod (bits + g - 1) g
    have hlt := Nat.mod_lt (bits + g - 1) (show 0 < g by omega)
    omega
  have hbitsLeInner10 : bits ≤ 10 * inner := by
    have : g * inner ≤ 10 * inner := Nat.mul_le_mul_right inner hg2
    omega
  have houterPos : 0 < outer := by
    dsimp [outer]
    have : inner ≤ bits + inner - 1 := by omega
    exact Nat.div_pos this hinnerPos
  have houterLe10 : outer ≤ 10 := by
    dsimp [outer]
    have hnum : bits + inner - 1 < 11 * inner := by omega
    have := (Nat.div_lt_iff_lt_mul hinnerPos).2 hnum
    omega
  have hchunkVal : (UInt8.ofNat outer).toNat = outer := by
    simp; omega
  refine ⟨UInt8.ofNat outer, rfl, by rw [hchunkVal]; exact houterPos,
    by rw [hchunkVal]; exact houterLe10, ?_⟩
  rw [hchunkVal, Nat.mul_comm _ outer]
  have hdiv := Nat.div_add_mod (bits + outer - 1) outer
  have hlt := Nat.mod_lt (bits + outer - 1) houterPos
  omega

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
    ∃ a, arrayVectorOps.read v i = some a := by
  unfold arrayVectorOps
  dsimp only
  have hb : 1 ≤ i ∧ i ≤ (v.size : Int) := ⟨h1, h2⟩
  rw [if_pos hb]
  exact ⟨v[i.toNat - 1]'(by omega), Array.getElem?_eq_getElem (by omega)⟩

theorem before_of_read {α : Type} {lt : α → α → Bool} {v : Array α} {x a : α} {i : Int}
    (h : arrayVectorOps.read v i = some a) : before lt v x i = lt a x := by
  unfold before; rw [h]

theorem notAfter_of_read {α : Type} {lt : α → α → Bool} {v : Array α} {x a : α} {i : Int}
    (h : arrayVectorOps.read v i = some a) : notAfter lt v x i = !(lt x a) := by
  unfold notAfter; rw [h]

theorem firstLoop_correct {α : Type} (lt : α → α → Bool) (v : Array α) (x : α)
    (hsz : v.size < IntTy.max .i64)
    (mono : ∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size → before lt v x j = true → before lt v x i = true) :
    ∀ (fuel len : Nat) (lo : Int) (hiIdx : SearchIndex),
      len < fuel → 1 ≤ lo → lo + len ≤ v.size + 1 →
      ∃ r, firstSearchLoop arrayVectorOps (fun _ => lt) () v x fuel (I64Idx lo) hiIdx (I64Idx len) = .returned r ∧
        SearchPartition (before lt v x) lo (lo + len) r := by
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
      simp only
      cases hc : lt a x
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hl2 : ((len : Int) / 2) = (((len / 2 : Nat)) : Int) := by omega
        rw [hl2]
        obtain ⟨r, hr, hp⟩ := ih (len / 2) lo (I64Idx (lo + ↑(len / 2))) (by omega) hlo (by omega)
        refine ⟨r, hr, ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := hp
        have hmb : before lt v x (lo + (len : Int) / 2) = false := by rw [before_of_read ha, hc]
        refine ⟨h1, by omega, h3, ?_⟩
        intro i hi1 hi2
        by_cases hi : i < lo + ((len / 2 : Nat) : Int)
        · exact h4 i hi1 hi
        · cases hb : before lt v x i with
          | false => rfl
          | true =>
            have := mono (lo + (len : Int) / 2) i (by omega) (by omega) (by omega) hb
            rw [hmb] at this; exact absurd this (by decide)
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
        have hmb : before lt v x (lo + (len : Int) / 2) = true := by rw [before_of_read ha, hc]
        refine ⟨by omega, by omega, ?_, fun i hi1 hi2 => h4 i hi1 (by omega)⟩
        intro i hi1 hi2
        by_cases hi : lo + (len : Int) / 2 + 1 ≤ i
        · exact h3 i hi hi2
        · exact mono i (lo + (len : Int) / 2) (by omega) (by omega) (by omega) hmb

theorem lastLoop_correct {α : Type} (lt : α → α → Bool) (v : Array α) (x : α)
    (hsz : v.size < IntTy.max .i64)
    (mono : ∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size → notAfter lt v x j = true → notAfter lt v x i = true) :
    ∀ (fuel gap : Nat) (lo : Int), gap < fuel → 0 ≤ lo → lo + gap + 1 ≤ v.size + 1 →
      ∃ r, lastSearchLoop arrayVectorOps (fun _ => lt) () v x (I64Idx 1) fuel (I64Idx lo) (I64Idx (lo + gap + 1)) = .returned r ∧
        SearchPartition (notAfter lt v x) (lo + 1) (lo + gap + 1) (r + 1) := by
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
      simp only
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
        have hmv : notAfter lt v x m = true := by rw [notAfter_of_read ha, hc]; rfl
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
        have hmv : notAfter lt v x m = false := by rw [notAfter_of_read ha, hc]; rfl
        refine ⟨h1, by omega, h3, ?_⟩
        intro i hi1 hi2
        by_cases hi : i < m
        · exact h4 i hi1 hi
        · cases hb : notAfter lt v x i with
          | false => rfl
          | true =>
            have := mono m i (by omega) (by omega) (by omega) hb
            rw [hmv] at this; exact absurd this (by decide)

theorem equalLoop_correct {α : Type} (lt : α → α → Bool) (v : Array α) (x : α)
    (hsz : v.size < IntTy.max .i64)
    (monoB : ∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size → before lt v x j = true → before lt v x i = true)
    (monoN : ∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size → notAfter lt v x j = true → notAfter lt v x i = true)
    (impBN : ∀ i : Int, 1 ≤ i → i ≤ v.size → before lt v x i = true → notAfter lt v x i = true) :
    ∀ (fuel gap : Nat) (lo : Int), gap < fuel → 0 ≤ lo → lo + gap + 1 ≤ v.size + 1 →
      ∃ first last,
        equalSearchLoop arrayVectorOps (fun _ => lt) () v x (I64Idx 1) fuel (I64Idx lo) (I64Idx (lo + gap + 1)) =
          .returned (first, last) ∧
        SearchPartition (before lt v x) (lo + 1) (lo + gap + 1) first ∧
        SearchPartition (notAfter lt v x) (lo + 1) (lo + gap + 1) (last + 1) := by
  have hmin : IntTy.min .i64 ≤ 0 := by decide
  intro fuel
  induction fuel with
  | zero => intro gap lo h; omega
  | succ fuel ih =>
    intro gap lo hfuel hlo hhi
    unfold equalSearchLoop
    have e0 : indexSub (I64Idx (lo + gap + 1)) (I64Idx 1) = I64Idx (lo + gap + 1 - 1) :=
      sub_I64Idx (by omega) (by omega) (by omega) (by omega)
    rw [e0, I64Idx_val (by omega) (by omega), I64Idx_val (by omega) (by omega)]
    by_cases hz : (gap : Int) = 0
    · rw [if_pos (by omega)]
      have e1 : (indexAdd (I64Idx lo) (I64Idx 1)).val = lo + 1 := by
        rw [add_I64Idx (by omega) (by omega) (by omega) (by omega), I64Idx_val (by omega) (by omega)]
      refine ⟨_, _, rfl, ?_, ?_⟩
      · rw [e1]; refine ⟨by omega, by omega, fun i h1 h2 => by omega, fun i h1 h2 => by omega⟩
      · refine ⟨by omega, by omega, fun i h1 h2 => by omega, fun i h1 h2 => by omega⟩
    · rw [if_neg (by omega)]
      have em : indexMidpoint (I64Idx lo) (I64Idx (lo + gap + 1)) = I64Idx (lo + (lo + gap + 1 - lo) / 2) :=
        mid_I64Idx (by omega) (by omega) (by omega)
      have emv : (I64Idx (lo + (lo + gap + 1 - lo) / 2)).val = lo + (lo + gap + 1 - lo) / 2 :=
        I64Idx_val (by omega) (by omega)
      simp only [em, emv]
      obtain ⟨a, ha⟩ := arrayVectorOps_read_some (v := v) (i := lo + (lo + gap + 1 - lo) / 2) (by omega) (by omega)
      rw [ha]
      simp only
      have hmr : lo < lo + (lo + gap + 1 - lo) / 2 ∧ lo + (lo + gap + 1 - lo) / 2 < lo + gap + 1 := by
        omega
      generalize hmd : lo + (lo + gap + 1 - lo) / 2 = m at *
      cases hc1 : lt a x
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hc2 : lt x a
        · simp only [Bool.false_eq_true, ↓reduceIte]
          have hmb : before lt v x m = false := by rw [before_of_read ha, hc1]
          have hmn : notAfter lt v x m = true := by rw [notAfter_of_read ha, hc2]; rfl
          have estart : indexAdd (I64Idx lo) (I64Idx 1) = I64Idx (lo + 1) :=
            add_I64Idx (by omega) (by omega) (by omega) (by omega)
          have efhi : indexAdd (I64Idx m) (searchIndex (I64Idx m).ty 1) = I64Idx (m + 1) :=
            add_I64Idx (by omega) (by omega) (by omega) (by omega)
          have eflen : indexSub (I64Idx (m + 1)) (I64Idx (lo + 1)) = I64Idx ((m - lo).toNat) := by
            rw [sub_I64Idx (by omega) (by omega) (by omega) (by omega)]
            congr 1; omega
          have eflenv : (I64Idx ((m - lo).toNat)).val.toNat = (m - lo).toNat := by
            rw [I64Idx_val (by omega) (by omega)]; omega
          simp only [estart, efhi, eflen, eflenv]
          obtain ⟨first, hfirst, hpB⟩ := firstLoop_correct lt v x hsz monoB
            ((m - lo).toNat + 2) (m - lo).toNat (lo + 1) (I64Idx (m + 1)) (by omega) (by omega) (by omega)
          rw [hfirst]
          simp only
          have emty : searchIndex (I64Idx m).ty 1 = I64Idx 1 := rfl
          have ello : indexSub (I64Idx m) (I64Idx 1) = I64Idx (m - 1) :=
            sub_I64Idx (by omega) (by omega) (by omega) (by omega)
          have elhi : indexAdd (I64Idx (lo + ↑gap + 1 - 1)) (I64Idx 1) =
              I64Idx ((m - 1) + (lo + gap + 1 - m).toNat + 1) := by
            have harg : lo + ↑gap + 1 - 1 + 1 = (m - 1) + ((lo + gap + 1 - m).toNat : Int) + 1 := by omega
            rw [add_I64Idx (by omega) (by omega) (by omega) (by omega), harg]
          have ellen : (indexSub (I64Idx ((m - 1) + (lo + gap + 1 - m).toNat + 1)) (I64Idx (m - 1))).val.toNat =
              (lo + gap + 1 - m).toNat + 1 := by
            rw [sub_I64Idx (by omega) (by omega) (by omega) (by omega), I64Idx_val (by omega) (by omega)]
            omega
          simp only [emty, ello, elhi, ellen]
          obtain ⟨last, hlast, hpN⟩ := lastLoop_correct lt v x hsz monoN
            ((lo + gap + 1 - m).toNat + 1 + 2) (lo + gap + 1 - m).toNat (m - 1) (by omega) (by omega) (by omega)
          rw [hlast]
          refine ⟨first, last, rfl, ?_, ?_⟩
          · obtain ⟨hb1, hb2, hb3, hb4⟩ := hpB
            refine ⟨hb1, by omega, hb3, ?_⟩
            intro i hi1 hi2
            by_cases him : i < m
            · exact hb4 i hi1 (by omega)
            · cases hbi : before lt v x i with
              | false => rfl
              | true =>
                have := monoB m i (by omega) (by omega) (by omega) hbi
                rw [hmb] at this; exact absurd this (by decide)
          · obtain ⟨hn1, hn2, hn3, hn4⟩ := hpN
            refine ⟨by omega, by omega, ?_, fun i hi1 hi2 => hn4 i hi1 (by omega)⟩
            intro i hi1 hi2
            by_cases him : m ≤ i
            · exact hn3 i (by omega) hi2
            · exact monoN i m (by omega) (by omega) (by omega) hmn
        · simp only [↓reduceIte]
          have he : m = lo + (((m - lo - 1 : Int).toNat : Nat) : Int) + 1 := by omega
          obtain ⟨first, last, hr, hpB, hpN⟩ := ih (m - lo - 1).toNat lo (by omega) hlo (by omega)
          rw [← he] at hr hpB hpN
          refine ⟨first, last, hr, ?_, ?_⟩
          · obtain ⟨h1, h2, h3, h4⟩ := hpB
            have hmb : before lt v x m = false := by rw [before_of_read ha, hc1]
            refine ⟨h1, by omega, h3, ?_⟩
            intro i hi1 hi2
            by_cases hi : i < m
            · exact h4 i hi1 hi
            · cases hb : before lt v x i with
              | false => rfl
              | true =>
                have := monoB m i (by omega) (by omega) (by omega) hb
                rw [hmb] at this; exact absurd this (by decide)
          · obtain ⟨h1, h2, h3, h4⟩ := hpN
            have hmn : notAfter lt v x m = false := by rw [notAfter_of_read ha, hc2]; rfl
            refine ⟨h1, by omega, h3, ?_⟩
            intro i hi1 hi2
            by_cases hi : i < m
            · exact h4 i hi1 hi
            · cases hb : notAfter lt v x i with
              | false => rfl
              | true =>
                have := monoN m i (by omega) (by omega) (by omega) hb
                rw [hmn] at this; exact absurd this (by decide)
      · simp only [↓reduceIte]
        have he : lo + ↑gap + 1 = m + (((lo + gap - m : Int).toNat : Nat) : Int) + 1 := by omega
        rw [he]
        obtain ⟨first, last, hr, hpB, hpN⟩ := ih (lo + gap - m).toNat m (by omega) (by omega) (by omega)
        refine ⟨first, last, hr, ?_, ?_⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hpB
          have hmb : before lt v x m = true := by rw [before_of_read ha, hc1]
          refine ⟨by omega, by omega, ?_, fun i hi1 hi2 => h4 i hi1 (by omega)⟩
          intro i hi1 hi2
          by_cases hi : m + 1 ≤ i
          · exact h3 i hi hi2
          · exact monoB i m (by omega) (by omega) (by omega) hmb
        · obtain ⟨h1, h2, h3, h4⟩ := hpN
          have hmb : before lt v x m = true := by rw [before_of_read ha, hc1]
          have hmn : notAfter lt v x m = true := impBN m (by omega) (by omega) hmb
          refine ⟨by omega, by omega, ?_, fun i hi1 hi2 => h4 i hi1 (by omega)⟩
          intro i hi1 hi2
          by_cases hi : m + 1 ≤ i
          · exact h3 i hi hi2
          · exact monoN i m (by omega) (by omega) (by omega) hmn

theorem search_monotone {α : Type} {lt : α → α → Bool} {v : Array α} {x : α}
    (hnt : NegTransOrder lt) (hs : VecSorted lt v) :
    (∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size → before lt v x j = true → before lt v x i = true) ∧
    (∀ i j : Int, 1 ≤ i → i ≤ j → j ≤ v.size → notAfter lt v x j = true → notAfter lt v x i = true) ∧
    (∀ i : Int, 1 ≤ i → i ≤ v.size → before lt v x i = true → notAfter lt v x i = true) := by
  obtain ⟨hirr, htrans, hneg⟩ := hnt
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hij hj hb
    obtain ⟨a, ha⟩ := arrayVectorOps_read_some (v := v) (i := i) hi (by omega)
    obtain ⟨b, hb'⟩ := arrayVectorOps_read_some (v := v) (i := j) (by omega) hj
    rw [before_of_read hb'] at hb
    rw [before_of_read ha]
    rcases hneg b a x hb with h | h
    · rw [hs i j a b hij ha hb'] at h; exact absurd h (by decide)
    · exact h
  · intro i j hi hij hj hb
    obtain ⟨a, ha⟩ := arrayVectorOps_read_some (v := v) (i := i) hi (by omega)
    obtain ⟨b, hb'⟩ := arrayVectorOps_read_some (v := v) (i := j) (by omega) hj
    rw [notAfter_of_read hb'] at hb
    rw [notAfter_of_read ha]
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
    cases hxa : lt x a with
    | false => rfl
    | true =>
      have hxx := htrans a x a hb hxa
      rw [hirr a] at hxx
      cases hxx

theorem vectorSearchCorrect_proven : VectorSearchCorrect := by
  have hmin : IntTy.min .i64 ≤ 0 := by decide
  have hmax2 : (2 ^ 62 : Int) < IntTy.max .i64 := by decide
  intro α lt v x hnt hs hsz
  have hsz' : v.size < IntTy.max .i64 := by omega
  obtain ⟨monoB, monoN, _⟩ := search_monotone (x := x) hnt hs
  constructor
  · unfold searchsortedfirstKeywords searchsortedfirstOrdering searchsortedfirstBounds
      arrayFirstIndex arrayLastIndex
    have e1 : (⟨.i64, JInt.wrap .i64 1⟩ : SearchIndex) = I64Idx 1 := rfl
    have e2 : indexAdd ⟨.i64, JInt.wrap .i64 v.size⟩ (searchIndex .i64 1) = I64Idx (v.size + 1) := by
      show indexAdd (I64Idx v.size) (I64Idx 1) = _
      exact add_I64Idx (by omega) (by omega) (by omega) (by omega)
    dsimp only; rw [e1, e2, sub_I64Idx (by omega) (by omega) (by omega) (by omega)]
    have e3 : (v.size : Int) + 1 - 1 = ((v.size : Nat) : Int) := by omega
    have e4 : (I64Idx ((v.size : Nat) : Int)).val.toNat = v.size := by
      rw [I64Idx_val (by omega) (by omega)]; omega
    rw [e3, e4]
    obtain ⟨r, hr, hp⟩ := firstLoop_correct lt v x hsz' monoB (v.size + 2) v.size 1
      (I64Idx (v.size + 1)) (by omega) (by omega) (by omega)
    exact ⟨r, hr, by rw [Int.add_comm]; exact hp⟩
  · unfold searchsortedlastKeywords searchsortedlastOrdering searchsortedlastBounds
      arrayFirstIndex arrayLastIndex
    have e1 : indexSub ⟨.i64, JInt.wrap .i64 1⟩ (searchIndex .i64 1) = I64Idx 0 := by
      show indexSub (I64Idx 1) (I64Idx 1) = _
      exact sub_I64Idx (by omega) (by omega) (by omega) (by omega)
    have e2 : indexAdd ⟨.i64, JInt.wrap .i64 v.size⟩ (searchIndex .i64 1) = I64Idx (0 + v.size + 1) := by
      show indexAdd (I64Idx v.size) (I64Idx 1) = _
      rw [add_I64Idx (by omega) (by omega) (by omega) (by omega)]
      congr 1; omega
    have e3 : (indexSub (I64Idx (0 + v.size + 1)) (I64Idx 0)).val.toNat = v.size + 1 := by
      rw [sub_I64Idx (by omega) (by omega) (by omega) (by omega), I64Idx_val (by omega) (by omega)]
      omega
    simp only [e1, e2, e3]
    obtain ⟨r, hr, hp⟩ := lastLoop_correct lt v x hsz' monoN (v.size + 1 + 2) v.size 0
      (by omega) (by omega) (by omega)
    refine ⟨r, hr, ?_⟩
    have e4 : (0 : Int) + ↑v.size + 1 = ↑v.size + 1 := by omega
    rw [e4] at hp
    simpa using hp

theorem searchsortedEquivalentRange_proven : SearchsortedEquivalentRange := by
  have hmin : IntTy.min .i64 ≤ 0 := by decide
  intro α lt values query hnt hs hsz
  obtain ⟨monoB, monoN, impBN⟩ := search_monotone (x := query) hnt hs
  unfold searchsortedKeywords searchsortedOrdering searchsortedBounds
    arrayFirstIndex arrayLastIndex
  have e1 : indexSub ⟨.i64, JInt.wrap .i64 1⟩ (searchIndex .i64 1) = I64Idx 0 := by
    show indexSub (I64Idx 1) (I64Idx 1) = _
    exact sub_I64Idx (by omega) (by omega) (by omega) (by omega)
  have e2 : indexAdd ⟨.i64, JInt.wrap .i64 values.size⟩ (searchIndex .i64 1) = I64Idx (0 + values.size + 1) := by
    show indexAdd (I64Idx values.size) (I64Idx 1) = _
    rw [add_I64Idx (by omega) (by omega) (by omega) (by omega)]
    congr 1; omega
  have e3 : (indexSub (I64Idx (0 + values.size + 1)) (I64Idx 0)).val.toNat = values.size + 1 := by
    rw [sub_I64Idx (by omega) (by omega) (by omega) (by omega), I64Idx_val (by omega) (by omega)]
    omega
  simp only [e1, e2, e3]
  obtain ⟨first, last, hr, hpB, hpN⟩ := equalLoop_correct lt values query hsz monoB monoN impBN
    (values.size + 1 + 2) values.size 0 (by omega) (by omega) (by omega)
  have e4 : (0 : Int) + ↑values.size + 1 = ↑values.size + 1 := by omega
  rw [e4] at hpB hpN
  simp only [Int.zero_add] at hpB hpN
  refine ⟨first, last, hr, hpB, hpN, ?_, ?_⟩
  · obtain ⟨hb1, hb2, hb3, _⟩ := hpB
    obtain ⟨hn1, hn2, _, hn4⟩ := hpN
    by_cases hle : first ≤ last + 1
    · exact hle
    · have hgt : last + 1 < first := by omega
      have hb := hb3 (last + 1) hn1 hgt
      have hn := hn4 (last + 1) (Int.le_refl _) (by omega)
      have himp := impBN (last + 1) hn1 (by omega) hb
      rw [himp] at hn
      cases hn
  · intro index value hread
    have hbounds : 1 ≤ index ∧ index ≤ (values.size : Int) ∧
        arrayVectorOps.read values index = some value := by
      unfold arrayRead at hread
      split at hread
      · rename_i h1
        cases hget : values[(index - 1).toNat]? with
        | none => rw [hget] at hread; cases hread
        | some v =>
          rw [hget] at hread
          injection hread with hveq
          subst hveq
          have hltNat : (index - 1).toNat < values.size :=
            (Array.getElem?_eq_some_iff.1 hget).1
          have h2 : index ≤ (values.size : Int) := by omega
          refine ⟨h1, h2, ?_⟩
          unfold arrayVectorOps
          dsimp only
          rw [if_pos ⟨h1, h2⟩]
          have heqIdx : index.toNat - 1 = (index - 1).toNat := by omega
          rw [heqIdx, hget]
      · cases hread
    obtain ⟨h1, h2, hvec⟩ := hbounds
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hpB
    obtain ⟨hn1, hn2, hn3, hn4⟩ := hpN
    have hbef : before lt values query index = lt value query := before_of_read hvec
    have hnot : notAfter lt values query index = !(lt query value) := notAfter_of_read hvec
    constructor
    · rintro ⟨hfi, hil⟩
      have hbF := hb4 index hfi (by omega)
      have hnT := hn3 index h1 (by omega)
      rw [hbef] at hbF
      rw [hnot, Bool.not_eq_true'] at hnT
      exact ⟨hbF, hnT⟩
    · rintro ⟨hbF, hnT⟩
      constructor
      · by_cases hfi : first ≤ index
        · exact hfi
        · have := hb3 index h1 (by omega)
          rw [hbef, hbF] at this; cases this
      · by_cases hil : index ≤ last
        · exact hil
        · have := hn4 index (by omega) (by omega)
          rw [hnot, hnT] at this; cases this

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
        searchsortedfirstIntegerRange (bitIntegerRangeOps t) rangeLt rev (f, h, l, len) x = .ok first ∧
        1 ≤ first.val ∧ first.val ≤ n + 1 ∧
        (∀ i, 1 ≤ i → i < first.val → elemLt rev (rangeElem f h i) x.val = true) ∧
        (∀ i, first.val ≤ i → i ≤ n → elemLt rev (rangeElem f h i) x.val = false)) ∧
      (∃ last,
        searchsortedlastIntegerRange (bitIntegerRangeOps t) rangeLt rev (f, h, l, len) x = .ok last ∧
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
        simp only [Bool.false_eq_true, ↓reduceIte]
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
            rw [if_neg (by simp [b2]; omega)]
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
        simp only [Bool.false_eq_true, ↓reduceIte]
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
            rw [if_neg (by simp [b2]; omega)]
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
        simp only [↓reduceIte]
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
            rw [if_neg (by simp [b2]; omega)]
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
        simp only [↓reduceIte]
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
            rw [if_neg (by simp [b2]; omega)]
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

theorem rangeSearchNoOverflowCorrect_proven : RangeSearchNoOverflowCorrect := by
  intro t f h l len x rev hv hs hqv hne hmin hmax hdloF hdloC hdhiF hdhiC
  have hfc := hqv.1
  let xf : JInt t := ⟨x.floor, ⟨hmin, by omega⟩⟩
  let xc : JInt t := ⟨x.ceil, ⟨by omega, hmax⟩⟩
  have hconvF : JInt.convert t x.floor = .ok xf := by
    unfold JInt.convert
    rw [dif_pos ⟨hmin, by omega⟩]
  have hconvC : JInt.convert t x.ceil = .ok xc := by
    unfold JInt.convert
    rw [dif_pos ⟨by omega, hmax⟩]
  obtain ⟨firstF, lastF, hffF, hflF, _, hcfF, hclF⟩ :=
    rangeSearchNoOverflowCorrect_int t f h l len xf rev hv hs hne hdloF hdhiF
  obtain ⟨firstC, lastC, hffC, hflC, _, hcfC, hclC⟩ :=
    rangeSearchNoOverflowCorrect_int t f h l len xc rev hv hs hne hdloC hdhiC
  cases rev
  · have hfirstEq : searchsortedfirstIntegerRange (bitIntegerRealRangeOps t)
        realQueryLtRange false (f, h, l, len) x =
      searchsortedfirstIntegerRange (bitIntegerRangeOps t)
        rangeLt false (f, h, l, len) xc := by
      unfold searchsortedfirstIntegerRange bitIntegerRealRangeOps bitIntegerRangeOps
        realQueryLtRange rangeLt
      dsimp only [bind, Except.bind, pure, Except.pure, id_eq]
      rw [hconvC]
      rfl
    have hlastEq : searchsortedlastIntegerRange (bitIntegerRealRangeOps t)
        realQueryLt false (f, h, l, len) x =
      searchsortedlastIntegerRange (bitIntegerRangeOps t)
        rangeLt false (f, h, l, len) xf := by
      unfold searchsortedlastIntegerRange bitIntegerRealRangeOps bitIntegerRangeOps
        realQueryLt rangeLt
      dsimp only [bind, Except.bind, pure, Except.pure, id_eq]
      rw [hconvF]
      rfl
    rw [hffC] at hfirstEq
    rw [hflF] at hlastEq
    refine ⟨firstC, lastF, hfirstEq, hlastEq, ?_, hcfC, hclF⟩
    unfold searchsortedIntegerRange
    rw [hfirstEq, hlastEq]
    rfl
  · have hfirstEq : searchsortedfirstIntegerRange (bitIntegerRealRangeOps t)
        realQueryLtRange true (f, h, l, len) x =
      searchsortedfirstIntegerRange (bitIntegerRangeOps t)
        rangeLt true (f, h, l, len) xf := by
      unfold searchsortedfirstIntegerRange bitIntegerRealRangeOps bitIntegerRangeOps
        realQueryLtRange rangeLt
      dsimp only [bind, Except.bind, pure, Except.pure, id_eq]
      rw [hconvF]
      rfl
    have hlastEq : searchsortedlastIntegerRange (bitIntegerRealRangeOps t)
        realQueryLt true (f, h, l, len) x =
      searchsortedlastIntegerRange (bitIntegerRangeOps t)
        rangeLt true (f, h, l, len) xc := by
      unfold searchsortedlastIntegerRange bitIntegerRealRangeOps bitIntegerRangeOps
        realQueryLt rangeLt
      dsimp only [bind, Except.bind, pure, Except.pure, id_eq]
      rw [hconvC]
      rfl
    rw [hffF] at hfirstEq
    rw [hflC] at hlastEq
    refine ⟨firstF, lastC, hfirstEq, hlastEq, ?_, hcfF, hclC⟩
    unfold searchsortedIntegerRange
    rw [hfirstEq, hlastEq]
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
        mergeAnyNTupleLoop lt fuel left right = .ok merged ∧
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
  obtain ⟨merged, hloop, hperm, hsort⟩ :=
    mergeAnyNTupleLoop_correct hnt (m + n + 1) ⟨m, left⟩ ⟨n, right⟩
      (by simp [left.property, right.property]) hleft hright
  have hlen : merged.2.val.length = m + n := by
    rw [← hperm.length_eq, List.length_append, left.property, right.property]
  unfold mergeNTuple
  rw [hloop]
  simp only [bind, Except.bind, pure, Except.pure, hlen, ↓reduceDIte]
  exact ⟨⟨merged.2.val, hlen⟩, rfl, hperm, hsort⟩

theorem integerCode_lt_two_pow (t : IntTy) (x : JInt t) (reverse : Bool) :
    integerCode t reverse x < 2 ^ t.bits := by
  have hx := x.property
  cases reverse <;> cases t <;>
    simp [integerCode, uintMapReverse, integerReverseMappingOps, forwardIntegerCode,
      uintMapSigned, uintMapUnsigned, xorIntegerWords, JInt.wrap, wrapInt,
      IntTy.signed, IntTy.min, IntTy.max, IntTy.bits] at hx ⊢ <;> omega

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
            let mapped ← (Except.ok (integerCode t reverse value) : Jl Nat)
            unsignedVector ← arrayWrite unsignedVector index mapped
          pure unsignedVector : Jl (Array Nat)) = .ok mapped ∧
        mapped.size = values.size ∧
        ∀ j, 1 ≤ j → j ≤ (values.size : Int) →
          (j ∈ xs → ∀ v, arrayRead values j = .ok v →
            arrayRead mapped j = .ok (integerCode t reverse v)) ∧
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
    let u' := u.set! (i - 1).toNat (integerCode t reverse (values[(i - 1).toNat]'hiNat))
    have hwrite : arrayWrite u i (integerCode t reverse (values[(i - 1).toNat]'hiNat)) = .ok u' := by
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

theorem forIn_uintUnmap_loop (t : IntTy) (values : Array (JInt t))
    (mapped : Array Nat) (reverse : Bool) :
    ∀ (xs : List Int),
      (∀ i ∈ xs, 1 ≤ i ∧ i ≤ (values.size : Int) ∧
        ∀ v, arrayRead values i = .ok v → arrayRead mapped i = .ok (integerCode t reverse v)) →
      (do
        let mut vector := values
        for index in xs do
          let unsigned ← arrayRead mapped (Int.add index 0)
          let value ← (Except.ok (integerDecode t reverse ((unsigned + 0) % 2 ^ t.bits)) : Jl (JInt t))
          vector ← arrayWrite vector index value
        pure vector : Jl (Array (JInt t))) = .ok values
  | [], _ => rfl
  | i :: rest, hprop => by
    obtain ⟨hi1, hi2, himap⟩ := hprop i List.mem_cons_self
    have hiNat : (i - 1).toNat < values.size := by omega
    have hreadV : arrayRead values i = .ok (values[(i - 1).toNat]'hiNat) := by
      unfold arrayRead
      simp only [hi1, ↓reduceIte, Array.getElem?_eq_getElem hiNat]
    let val := values[(i - 1).toNat]'hiNat
    have hreadM : arrayRead mapped (Int.add i 0) = .ok (integerCode t reverse val) := by
      change arrayRead mapped (i + 0) = _
      rw [Int.add_zero]
      exact himap val hreadV
    have hmod : (integerCode t reverse val + 0) % 2 ^ t.bits = integerCode t reverse val := by
      rw [Nat.add_zero]
      exact Nat.mod_eq_of_lt (integerCode_lt_two_pow t val reverse)
    have hdec : integerDecode t reverse ((integerCode t reverse val + 0) % 2 ^ t.bits) = val := by
      rw [hmod]
      exact uintMappingCorrect_proven.1 t val reverse
    have hwrite : arrayWrite values i val = .ok values := arrayWrite_self values i val hreadV
    have hrest : ∀ j ∈ rest, 1 ≤ j ∧ j ≤ (values.size : Int) ∧
        ∀ v, arrayRead values j = .ok v → arrayRead mapped j = .ok (integerCode t reverse v) :=
      fun j hj => hprop j (List.mem_cons_of_mem i hj)
    simp only [List.forIn_cons, hreadM, hdec, hwrite, bind, Except.bind, pure, Except.pure]
    exact forIn_uintUnmap_loop t values mapped reverse rest hrest

theorem mem_arrayIndexRange {lo hi i : Int} :
    i ∈ arrayIndexRange lo hi ↔ lo ≤ i ∧ i ≤ hi := by
  unfold arrayIndexRange
  simp only [List.mem_map, List.mem_range, Int.ofNat_eq_natCast]
  constructor
  · rintro ⟨k, hk, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨(i - lo).toNat, by omega, by omega⟩

theorem uintVectorRoundTrip_proven : UIntVectorRoundTrip := by
  intro t values lo hi reverse hlo hle hhi
  unfold uintMapVectorBang uintUnmapVectorBang
  have hcap : (if reverse = true then uintMappableReverse (integerReverseMappingOps t) (JInt t) ()
      else uintMappableBitInteger (fun _ => JInt (unsignedIntegerType t)) (JInt t)) =
      some (JInt (unsignedIntegerType t)) := by
    cases reverse <;> rfl
  dsimp only [arrayIntegerMapOps, arrayIntegerUnmapOps, Option.getD]
  rw [hcap]
  dsimp only [bind, Except.bind]
  let u0 := values.map fun value : JInt t => (value.val % 2 ^ t.bits).toNat
  have hu0 : u0.size = values.size := by simp [u0]
  have hbounds : ∀ i ∈ arrayIndexRange lo hi, 1 ≤ i ∧ i ≤ (values.size : Int) := by
    intro i hiMem
    have := mem_arrayIndexRange.1 hiMem
    omega
  obtain ⟨mapped, hmap, hmsize, hmprop⟩ :=
    forIn_uintMap_loop t values reverse (arrayIndexRange lo hi) u0 hu0 hbounds
  refine ⟨mapped, hmap, hmsize, ?_, ?_⟩
  · apply forIn_uintUnmap_loop t values mapped reverse (arrayIndexRange lo hi)
    intro i hiMem
    have hb := hbounds i hiMem
    exact ⟨hb.1, hb.2, (hmprop i hb.1 hb.2).1 hiMem⟩
  · intro index value h1 h2 hread
    have hiMem : index ∈ arrayIndexRange lo hi := mem_arrayIndexRange.2 ⟨h1, h2⟩
    exact (hmprop index (by omega) (by omega)).1 hiMem value hread

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

theorem algorithmDisplayWellFormed_proven : AlgorithmDisplayWellFormed := by
  intro IO Alg Name Arg E ops text nameText smallThreshold? argumentText hlaws io hio
  refine ⟨?_, ?_, ?_, ?_⟩
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
  · intro threshold result h
    unfold showSmallAlgorithmType at h
    have htext := hlaws.1 io ("Base.Sort.Small{" ++ toString threshold ++ "}") result h
    rw [hio, String.empty_append] at htext
    exact htext
  · intro algorithm result h
    unfold showAlgorithmType at h
    have htext := hlaws.2.2.2.1 io (ops.algorithmTypeName algorithm) result h
    rw [hio, String.empty_append] at htext
    exact htext

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
        if (← arrayRead values index) == b then
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
    simp only [List.forIn_cons, hread, List.filter_cons, hget, except_bind_ok]
    cases hcond : (values[(i - 1).toNat]'hiNat == b)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact forIn_bool_count values b rest c hrest
    · simp only [↓reduceIte, List.length_cons]
      change (forIn rest (c + 1) fun index count => do
        if (← arrayRead values index) == b then
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
            values ← arrayWrite values index val
          pure values : Jl (Array Bool)) = .ok v' ∧
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
    · simp only [List.forIn_cons, hwrite, bind, Except.bind, pure, Except.pure]
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
  · dsimp only [storageBoolSortOps, arrayStorage]
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

theorem boolSortCorrect_proven : BoolSortCorrect := by
  intro values lt hnt
  unfold sortBoolVector
  dsimp only [storageBoolSortOps, arrayStorage]
  by_cases hft : lt false true = true
  · simp only [hft, ↓reduceIte]
    exact boolSort_branch values lt hnt false (hnt.1 false) (hnt.1 true)
      (negTransOrder_asymm hnt hft)
  · have hftF : lt false true = false := Bool.eq_false_iff.2 hft
    simp only [hftF, Bool.false_eq_true, ↓reduceIte]
    by_cases htf : lt true false = true
    · simp only [htf, ↓reduceIte]
      exact boolSort_branch values lt hnt true (hnt.1 true) (hnt.1 false)
        (negTransOrder_asymm hnt htf)
    · have htfF : lt true false = false := Bool.eq_false_iff.2 htf
      simp only [htfF, Bool.false_eq_true, ↓reduceIte]
      refine ⟨values, rfl, List.Perm.refl _, ?_⟩
      rw [sortedValues_iff_pairwise hnt, List.pairwise_iff_getElem]
      intro i j hi hj _
      have h1 := hnt.1 false
      have h2 := hnt.1 true
      cases values.toList[i] <;> cases values.toList[j] <;> assumption

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
  simp only [bind, Except.bind, hwrite1, hwrite2]

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
          pure values : Jl (Array α)) = .ok v' ∧
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

theorem checkSortedCorrect_aux :
    ∀ (α Alg : Type) [Inhabited α] (lt : α → α → Bool)
      (nextAlgorithm : Alg → Alg)
      (sortNext : Array α → Alg → (α → α → Bool) → ArraySortKeywords α →
        Jl (Array α × Option (Array α)))
      (values : Array α) (algorithm : Alg),
      NegTransOrder lt →
      (∃ nextResult nextScratch,
        sortNext values (nextAlgorithm algorithm) lt { lo := 1, hi := values.size } =
          .ok (nextResult, nextScratch) ∧
        List.Perm values.toList nextResult.toList ∧
        SortedValues lt nextResult.toList) →
      ∃ result scratch,
        sortCheckSorted (storageCheckSortedOps arrayStorage nextAlgorithm sortNext)
          values algorithm lt { lo := 1, hi := values.size } = .ok (result, scratch) ∧
        List.Perm values.toList result.toList ∧ SortedValues lt result.toList := by
  intro α Alg _ lt nextAlgorithm sortNext values algorithm hnt hnext
  obtain ⟨nextResult, nextScratch, hnextRun, hnextPerm, hnextSort⟩ := hnext
  have hchk : arrayCheckBounds values 1 values.size = .ok () := by
    unfold arrayCheckBounds
    by_cases hlt : (values.size : Int) < 1
    · rw [if_pos hlt]
    · rw [if_neg hlt, if_pos ⟨Int.le_refl 1, Int.le_refl _⟩]
  have hreads : WindowReadsSucceed arrayIndices arrayRead values 1 values.size := by
    intro i hi
    have hiBounds : 1 + 1 ≤ i ∧ i ≤ (values.size : Int) := mem_arrayIndexRange.1 hi
    have hi1 : (i - 1).toNat < values.size := by omega
    have hi2 : (i - 1 - 1).toNat < values.size := by omega
    refine ⟨values[(i - 1).toNat]'hi1, values[(i - 1 - 1).toNat]'hi2, ?_, ?_⟩
    · unfold arrayRead
      have hpos : 1 ≤ i := by omega
      simp only [hpos, ↓reduceIte, Array.getElem?_eq_getElem hi1]
    · unfold arrayRead arrayIndices
      dsimp only
      have hpos : 1 ≤ i - 1 := by omega
      simp only [hpos, ↓reduceIte, Array.getElem?_eq_getElem hi2]
  obtain ⟨b1, hb1⟩ := forIn_window_check_ok arrayIndices arrayRead (fun o => o) values lt
    (arrayIndexRange (1 + 1) values.size) hreads
  have his1 : issortedWindow arrayIndices arrayCheckBounds arrayRead (fun o => o)
      values 1 values.size lt = .ok b1 := by
    unfold issortedWindow
    rw [hchk]
    exact hb1
  unfold sortCheckSorted storageCheckSortedOps
  simp only [storageCheckBounds_array, arrayStorage_getindex]
  simp only [bind, Except.bind, pure, Except.pure, his1]
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hbig : Int.sub (values.size : Int) 1 ≥ 500
    · simp only [hbig, ↓reduceIte]
      obtain ⟨b2, hb2⟩ := forIn_window_check_ok arrayIndices arrayRead (fun o => o) values
        (fun a b => lt b a) (arrayIndexRange (1 + 1) values.size) hreads
      have his2 : issortedWindow arrayIndices arrayCheckBounds arrayRead (fun o => o)
          values 1 values.size (fun a b => lt b a) = .ok b2 := by
        unfold issortedWindow
        rw [hchk]
        exact hb2
      rw [his2]
      dsimp only
      cases b2
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨nextResult, nextScratch, hnextRun, hnextPerm, hnextSort⟩
      · simp only [↓reduceIte]
        have hntRev : NegTransOrder (fun a b => lt b a) :=
          ⟨hnt.1, fun a b c h1 h2 => hnt.2.1 c b a h2 h1,
            fun a b c h1 => (hnt.2.2 c b a h1).symm⟩
        have hwRev : WindowSorted arrayIndices arrayRead (fun o => o) values 1 values.size
            (fun a b => lt b a) :=
          (windowIssortedCorrect_proven ( Array α ) α Int (α → α → Bool) JlError
            arrayIndices arrayCheckBounds arrayRead (fun o => o) values 1 values.size
            (fun a b => lt b a) hchk hreads).1 his2
        have hsortRev := windowSorted_whole_imp_sortedValues hntRev values hwRev
        have hpwRev := (sortedValues_iff_pairwise hntRev values.toList).1 hsortRev
        obtain ⟨reversed, hrev, hrevList⟩ :=
          arrayReverse_spec values 1 values.size [] values.toList []
            (by simp) rfl (by simp)
        rw [hrev]
        refine ⟨reversed, none, rfl, ?_, ?_⟩
        · rw [hrevList, List.nil_append, List.append_nil]
          exact (List.reverse_perm _).symm
        · rw [hrevList, List.nil_append, List.append_nil, sortedValues_iff_pairwise hnt]
          exact List.pairwise_reverse.2 hpwRev
    · simp only [hbig, ↓reduceIte]
      exact ⟨nextResult, nextScratch, hnextRun, hnextPerm, hnextSort⟩
  · simp only [↓reduceIte]
    have hw : WindowSorted arrayIndices arrayRead (fun o => o) values 1 values.size lt :=
      (windowIssortedCorrect_proven (Array α) α Int (α → α → Bool) JlError
        arrayIndices arrayCheckBounds arrayRead (fun o => o) values 1 values.size lt
        hchk hreads).1 his1
    exact ⟨values, none, rfl, List.Perm.refl _, windowSorted_whole_imp_sortedValues hnt values hw⟩

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
          let value ← arrayRead sorted index
          let p ← arrayWrite p (offset + index) value
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
      simp only [List.forIn_cons, hreadS, hwriteP, bind, Except.bind, pure, Except.pure]
      exact hloop
    · rw [hp'List]; simp [List.append_assoc]

theorem subArraySortCorrect_aux :
    ∀ (α Alg : Type) [Inhabited α] (lt : α → α → Bool)
      (nextAlgorithm : Alg → Alg)
      (sortSlice : Array α → Alg → (α → α → Bool) → ArraySortKeywords α →
        Jl (Array α × Option (Array α)))
      (view : FlatSortView α) (algorithm : Alg),
      NegTransOrder lt →
      0 ≤ view.offset → view.offset + Int.ofNat view.length ≤ view.parent.storage.size →
      (∀ (values : Array α) (kw : ArraySortKeywords α),
        1 ≤ kw.lo → kw.lo ≤ kw.hi + 1 → kw.hi ≤ values.size →
        ∃ sorted scratch,
          sortSlice values (nextAlgorithm algorithm) lt kw = .ok (sorted, scratch) ∧
          sorted.size = values.size ∧
          List.Perm (arraySlice values kw.lo kw.hi) (arraySlice sorted kw.lo kw.hi) ∧
          SortedValues lt (arraySlice sorted kw.lo kw.hi) ∧
          sorted.toList.take (kw.lo - 1).toNat = values.toList.take (kw.lo - 1).toNat ∧
          sorted.toList.drop kw.hi.toNat = values.toList.drop kw.hi.toNat) →
      ∃ result, sortSubArrayUnwrappable
          (flatSubArraySortOpsWithNext view nextAlgorithm sortSlice)
          view algorithm lt { lo := 1, hi := view.length } = .ok result ∧
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
      let values ← flatSortViewValues view
      let (sorted, _) ← sortSlice values (nextAlgorithm algorithm) lt { lo := 1, hi := view.length }
      let mut parent := view.parent.storage
      for index in arrayIndexRange 1 view.length do
        let value ← arrayRead sorted index
        parent ← arrayWrite parent (view.offset + index) value
      pure { view with parent := { view.parent with storage := parent } }
    else
      let (sorted, _) ← sortSlice view.parent.storage (nextAlgorithm algorithm) lt { lo := 1, hi := view.length }
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
        let (sorted, _) ← sortSlice values (nextAlgorithm algorithm) lt { lo := 1, hi := view.length }
        let mut parent := view.parent.storage
        for index in arrayIndexRange 1 view.length do
          let value ← arrayRead sorted index
          parent ← arrayWrite parent (view.offset + index) value
        pure { view with parent := { view.parent with storage := parent } }) = .ok _
      rw [hsort]
      change (do
        let mut parent := view.parent.storage
        for index in arrayIndexRange 1 view.length do
          let value ← arrayRead sorted index
          parent ← arrayWrite parent (view.offset + index) value
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

def StableRel {α : Type} (lt : α → α → Bool) (a b : TaggedSortValue α) : Prop :=
  lt b.key a.key = false ∧ (lt a.key b.key = false → a.originalIndex < b.originalIndex)

theorem stableRel_insertStable {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (x : TaggedSortValue α) :
    ∀ {S : List (TaggedSortValue α)},
      S.Pairwise (StableRel lt) →
      (∀ s ∈ S, s.originalIndex < x.originalIndex) →
      (insertStable (fun a b : TaggedSortValue α => lt a.key b.key) x S).Pairwise (StableRel lt)
  | [], _, _ => by simp [insertStable]
  | y :: ys, hS, hltIdx => by
    have ⟨hy, hys⟩ := List.pairwise_cons.1 hS
    unfold insertStable
    by_cases hxy : lt x.key y.key = true
    · simp only [hxy, ↓reduceIte]
      refine List.Pairwise.cons ?_ hS
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact ⟨negTransOrder_asymm hnt hxy, fun hF => by rw [hxy] at hF; cases hF⟩
      · have hzy := (hy z hz).1
        have hxz : lt x.key z.key = true := negTransOrder_lt_of_lt_of_nlt hnt hxy hzy
        exact ⟨negTransOrder_asymm hnt hxz, fun hF => by rw [hxz] at hF; cases hF⟩
    · have hxyF : lt x.key y.key = false := Bool.eq_false_iff.2 hxy
      simp only [hxyF, Bool.false_eq_true, ↓reduceIte]
      refine List.Pairwise.cons ?_
        (stableRel_insertStable hnt x hys (fun s hs => hltIdx s (List.mem_cons_of_mem y hs)))
      intro z hz
      rcases mem_insertStable.1 hz with rfl | hz
      · exact ⟨hxyF, fun _ => hltIdx y List.mem_cons_self⟩
      · exact hy z hz

theorem stableRel_insAll {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) :
    ∀ (L S : List (TaggedSortValue α)),
      S.Pairwise (StableRel lt) →
      L.Pairwise (fun a b => a.originalIndex < b.originalIndex) →
      (∀ s ∈ S, ∀ x ∈ L, s.originalIndex < x.originalIndex) →
      (insAll (fun a b : TaggedSortValue α => lt a.key b.key) S L).Pairwise (StableRel lt)
  | [], S, hS, _, _ => hS
  | x :: L, S, hS, hL, hSL => by
    have ⟨hxL, hLL⟩ := List.pairwise_cons.1 hL
    rw [insAll_cons]
    apply stableRel_insAll hnt L _
      (stableRel_insertStable hnt x hS (fun s hs => hSL s hs x List.mem_cons_self))
      hLL
    intro s hs z hz
    rcases mem_insertStable.1 hs with rfl | hs
    · exact hxL z hz
    · exact hSL s hs z (List.mem_cons_of_mem x hz)

theorem zipIdx_originalIndex_pairwise {α : Type} :
    ∀ (keys : List α) (start : Nat),
      (∀ x ∈ (keys.zipIdx start).map (fun (key, idx) => TaggedSortValue.mk key idx),
        start ≤ x.originalIndex) ∧
      ((keys.zipIdx start).map (fun (key, idx) => TaggedSortValue.mk key idx)).Pairwise
        (fun a b => a.originalIndex < b.originalIndex)
  | [], _ => ⟨fun _ h => by simp at h, List.Pairwise.nil⟩
  | k :: rest, start => by
    obtain ⟨hge, hpw⟩ := zipIdx_originalIndex_pairwise rest (start + 1)
    simp only [List.zipIdx_cons, List.map_cons]
    refine ⟨?_, List.Pairwise.cons ?_ hpw⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Nat.le_refl start
      · have := hge x hx; omega
    · intro x hx
      exact hge x hx

theorem sortRef_tagged_props {α : Type} {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (keys : List α) :
    let tagged := keys.zipIdx.map fun (key, originalIndex) =>
      TaggedSortValue.mk key originalIndex
    let compare := fun (a b : TaggedSortValue α) => lt a.key b.key
    List.Perm tagged (sortRef compare tagged) ∧
    TaggedSorted lt (sortRef compare tagged) ∧
    TaggedStable lt (sortRef compare tagged) := by
  intro tagged compare
  have hpw := stableRel_insAll hnt tagged [] List.Pairwise.nil
    (zipIdx_originalIndex_pairwise keys 0).2 (fun _ hs => nomatch hs)
  rw [← sortRef_eq_insAll] at hpw
  have hget := List.pairwise_iff_getElem.1 hpw
  refine ⟨perm_sortRef compare tagged, ?_, ?_⟩
  · intro i j x y hij hx hy
    have hi : i < (sortRef compare tagged).length := (List.getElem?_eq_some_iff.1 hx).1
    have hj : j < (sortRef compare tagged).length := (List.getElem?_eq_some_iff.1 hy).1
    have hxEq : (sortRef compare tagged)[i]'hi = x := (List.getElem_eq_iff hi).2 hx
    have hyEq : (sortRef compare tagged)[j]'hj = y := (List.getElem_eq_iff hj).2 hy
    have hrel := hget i j hi hj hij
    rw [hxEq, hyEq] at hrel
    exact hrel.1
  · intro i j x y hij hx hy hxy hyx
    have hi : i < (sortRef compare tagged).length := (List.getElem?_eq_some_iff.1 hx).1
    have hj : j < (sortRef compare tagged).length := (List.getElem?_eq_some_iff.1 hy).1
    have hxEq : (sortRef compare tagged)[i]'hi = x := (List.getElem_eq_iff hi).2 hx
    have hyEq : (sortRef compare tagged)[j]'hj = y := (List.getElem_eq_iff hj).2 hy
    have hrel := hget i j hi hj hij
    rw [hxEq, hyEq] at hrel
    exact hrel.2 hxy

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
          let j' ← insertionShift (storageMutationOps arrayStorage) (fun _ => lt) () () lo x (m + 1) j
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
      dsimp [storageMutationOps, arrayStorage, StateT.run]; rw [hwr]; rfl
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
      dsimp [storageMutationOps, arrayStorage, arrayIndices, StateT.run]; rw [hprevRead]; rfl
    rw [bind_assoc, stateT_bind_ok _ _ v v y hget]
    cases hxy : lt x y
    · simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨v', hwr, hv'⟩ := arrayWrite_mid x (i := j) (P := P ++ A' ++ [y]) (B := B) (z := z)
        (by rw [hv]; simp [List.append_assoc]) (by omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      have hset : ((storageMutationOps arrayStorage).set () x j).run v = .ok ((), v') := by
        dsimp [storageMutationOps, arrayStorage, StateT.run]; rw [hwr]; rfl
      refine ⟨v', ?_, by simpa [List.append_assoc] using hv'⟩
      rw [stateT_bind_ok _ _ v v j rfl, stateT_bind_ok _ _ v v' () hset]
      rfl
    · simp only [↓reduceIte]
      obtain ⟨v1, hwr1, hv1⟩ := arrayWrite_mid y (i := j) (P := P ++ A' ++ [y]) (B := B) (z := z)
        (by rw [hv]; simp [List.append_assoc]) (by omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      have hset1 : ((storageMutationOps arrayStorage).set () y j).run v = .ok ((), v1) := by
        dsimp [storageMutationOps, arrayStorage, StateT.run]; rw [hwr1]; rfl
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
            let j ← insertionShift (storageMutationOps arrayStorage) (fun _ => lt) () () lo value
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
        dsimp [storageMutationOps, arrayStorage, StateT.run]; rw [hread]; rfl
      have hstep :
          (do
            let value ← (storageMutationOps arrayStorage).get () i
            let j ← insertionShift (storageMutationOps arrayStorage) (fun _ => lt) () () lo value
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
    ∃ v', storageInsertion arrayStorage lt v lo hi = .ok v' ∧ v'.toList = P ++ sortRef lt M ++ Q := by
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

theorem insertionSortStable_proven : InsertionSortStable := by
  intro α _ lt hnt keys
  let tagged := keys.zipIdx.map fun (key, originalIndex) =>
    TaggedSortValue.mk key originalIndex
  let input := tagged.toArray
  let compare := fun (a b : TaggedSortValue α) => lt a.key b.key
  have hntComp : NegTransOrder compare :=
    ⟨fun a => hnt.1 a.key, fun a b c => hnt.2.1 a.key b.key c.key,
      fun a b c => hnt.2.2 a.key b.key c.key⟩
  obtain ⟨result, hrun, hlist⟩ :=
    arrayInsertion_spec hntComp input 1 input.size [] input.toList []
      (Int.le_refl 1) (by simp) rfl (by simp)
  simp only [List.nil_append, List.append_nil] at hlist
  obtain ⟨hperm, hsorted, hstable⟩ := sortRef_tagged_props hnt keys
  refine ⟨result, hrun, ?_, ?_, ?_⟩
  · rw [hlist]; exact hperm
  · rw [hlist]; exact hsorted
  · rw [hlist]; exact hstable

theorem legacyInvalidWindowRejected_proven : LegacyInvalidWindowRejected := by
  constructor
  · intro α _ lt values scratch lo hi hnt hlo hle hhi
    simp only [Int.ofNat_eq_natCast] at hhi
    have hchk : arrayCheckBounds values lo hi = .ok () := by
      unfold arrayCheckBounds
      by_cases hlt : hi < lo
      · rw [if_pos hlt]
      · rw [if_neg hlt, if_pos ⟨hlo, hhi⟩]
    let P := values.toList.take (lo - 1).toNat
    let M := arraySlice values lo hi
    let Q := values.toList.drop hi.toNat
    have hdecomp := toList_eq_take_slice_drop values lo hi hlo hle
    have hPlen : (P.length : Int) + 1 = lo := by
      simp only [P, List.length_take, Array.length_toList]; omega
    have hMlen : (M.length : Int) = hi - lo + 1 := by
      simp only [M, arraySlice, List.length_take, List.length_drop, Array.length_toList]; omega
    obtain ⟨result, hins, hresList⟩ :=
      arrayInsertion_spec hnt values lo hi P M Q hlo hdecomp hPlen hMlen
    have htsd := take_slice_drop_of_append result P (sortRef lt M) Q lo hi hlo hle hresList
      (by omega) (by rw [length_sortRef]; omega)
    have hchkWhole : arrayCheckBounds values 1 values.size = .ok () := by
      unfold arrayCheckBounds
      by_cases hlt : (values.size : Int) < 1
      · rw [if_pos hlt]
      · rw [if_neg hlt, if_pos ⟨Int.le_refl 1, Int.le_refl _⟩]
    obtain ⟨wholeResult, hinsWhole, hwholeList⟩ :=
      arrayInsertion_spec hnt values 1 values.size [] values.toList []
        (Int.le_refl 1) (by simp) rfl (by simp)
    simp only [List.nil_append, List.append_nil] at hwholeList
    refine ⟨⟨result, ?_, ?_, ?_, ?_, ?_, htsd.1, htsd.2.2⟩,
      ⟨wholeResult, ?_, ?_, ?_⟩⟩
    · unfold legacySortBounds storageLegacyOps storageLegacyRun
      simp only [storageCheckBounds_array, hchk, hins, except_bind_ok]
    · unfold legacySortIgnoredScratch legacySortBounds storageLegacyOps storageLegacyRun
      simp only [storageCheckBounds_array, hchk, hins, except_bind_ok]
    · unfold legacySortWithScratch storageLegacyOps storageLegacyRun
      simp only [storageCheckBounds_array, hchk, hins, except_bind_ok]
    · rw [hdecomp, hresList]
      exact List.Perm.append_right Q (List.Perm.append_left P (perm_sortRef lt M))
    · rw [htsd.2.1, sortedValues_iff_pairwise hnt]
      exact sorted_sortRef hnt M
    · unfold legacySortWhole legacySortBounds storageLegacyOps storageLegacyRun
      simp only [storageCheckBounds_array, arrayStorage_length, hchkWhole, hinsWhole,
        except_bind_ok]
    · rw [hwholeList]; exact perm_sortRef lt values.toList
    · rw [hwholeList, sortedValues_iff_pairwise hnt]
      exact sorted_sortRef hnt values.toList
  · intro α _ lt values scratch algorithm lo hi hle hout
    simp only [Int.ofNat_eq_natCast] at hout
    have hchk : arrayCheckBounds values lo hi = .error .boundsError := by
      unfold arrayCheckBounds
      have hnotlt : ¬ hi < lo := by omega
      have hnotok : ¬ (1 ≤ lo ∧ hi ≤ (values.size : Int)) := by
        rcases hout with h1 | h2 <;> omega
      rw [if_neg hnotlt, if_neg hnotok]
    unfold legacySortIgnoredScratch legacySortBounds legacySortWithScratch storageLegacyOps
    dsimp only
    rw [storageCheckBounds_array, hchk]
    exact ⟨rfl, rfl, rfl⟩

theorem arrayInsertion_whole {α : Type} [Inhabited α] {lt : α → α → Bool}
    (hnt : NegTransOrder lt) (values : Array α) :
    ∃ result,
      storageInsertion arrayStorage lt values 1 values.size = .ok result ∧
      List.Perm values.toList result.toList ∧
      SortedValues lt result.toList := by
  obtain ⟨result, hins, hlist⟩ :=
    arrayInsertion_spec hnt values 1 values.size [] values.toList []
      (Int.le_refl 1) (by simp) rfl (by simp)
  simp only [List.nil_append, List.append_nil] at hlist
  refine ⟨result, hins, ?_, ?_⟩
  · rw [hlist]; exact perm_sortRef lt values.toList
  · rw [hlist, sortedValues_iff_pairwise hnt]; exact sorted_sortRef hnt values.toList

theorem uintMappableDispatchCorrect_proven : UIntMappableDispatchCorrect := by
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ⟨rfl, fun c => by cases c; rfl⟩, ?_⟩
  · intro t
    cases t <;> simp [uintMappableBitInteger, unsignedIntegerType, IntTy.bits, IntTy.signed]
  · intro t _
    refine ⟨rfl, fun x y => ⟨uintMappingCorrect_proven.1 t x true, uintMappingCorrect_proven.2.1 t x y true⟩⟩
  · intro α _ lt mappableType values hnt
    obtain ⟨result, hins, hperm, hsort⟩ := arrayInsertion_whole hnt values
    unfold sortIsUIntMappable
    cases mappableType <;> exact ⟨result, hins, hperm, hsort⟩

theorem algorithmPolicyDispatchCorrect_proven : AlgorithmPolicyDispatchCorrect := by
  unfold AlgorithmPolicyDispatchCorrect
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
  · intro α _ lt threshold values hnt
    obtain ⟨result, hins, hperm, hsort⟩ := arrayInsertion_whole hnt values
    exact ⟨result, result, hins, hins, hperm, hsort, hperm, hsort⟩
  · intro α _ lt t minimum maximum reverse elemSz values hnt
    obtain ⟨result, hins, hperm, hsort⟩ := arrayInsertion_whole hnt values
    exact ⟨rfl, rfl, result, result, hins, hins, hperm, hsort, hperm, hsort⟩
  · intro α _ lt t minimum maximum reverse elemSz logSpan values hnt
    obtain ⟨result, hins, hperm, hsort⟩ := arrayInsertion_whole hnt values
    exact ⟨result, hins, hperm, hsort⟩
  · intro α _ lt values target lo hi hnt
    obtain ⟨result, hins, hperm, hsort⟩ := arrayInsertion_whole hnt values
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩,
      result, result, result, hins, hins, hins, hperm, hsort, hperm, hsort, hperm, hsort⟩

theorem checkSortedCorrect_proven : CheckSortedCorrect := by
  intro α Alg _ lt nextAlgorithm values algorithm hnt
  obtain ⟨result, hins, hperm, hsort⟩ := arrayInsertion_whole hnt values
  apply checkSortedCorrect_aux α Alg lt nextAlgorithm _ values algorithm hnt
  refine ⟨result, none, ?_, hperm, hsort⟩
  change (do
    let sorted ← storageInsertion arrayStorage lt values 1 values.size
    pure (sorted, (none : Option (Array α)))) = .ok (result, none)
  rw [hins]; rfl

theorem subArraySortCorrect_proven : SubArraySortCorrect := by
  intro α Alg _ lt nextAlgorithm view algorithm hnt hoff0 hoff1
  apply subArraySortCorrect_aux α Alg lt nextAlgorithm _ view algorithm hnt hoff0 hoff1
  intro values kw hlo hle hhi
  let P := values.toList.take (kw.lo - 1).toNat
  let M := arraySlice values kw.lo kw.hi
  let Q := values.toList.drop kw.hi.toNat
  have hdecomp := toList_eq_take_slice_drop values kw.lo kw.hi hlo hle
  have hPlen : (P.length : Int) + 1 = kw.lo := by
    simp only [P, List.length_take, Array.length_toList]; omega
  have hMlen : (M.length : Int) = kw.hi - kw.lo + 1 := by
    simp only [M, arraySlice, List.length_take, List.length_drop, Array.length_toList]; omega
  obtain ⟨sorted, hins, hresList⟩ :=
    arrayInsertion_spec hnt values kw.lo kw.hi P M Q hlo hdecomp hPlen hMlen
  have htsd := take_slice_drop_of_append sorted P (sortRef lt M) Q kw.lo kw.hi hlo hle hresList
    (by omega) (by rw [length_sortRef]; omega)
  have hsz : sorted.size = values.size := by
    rw [← Array.length_toList, ← Array.length_toList, hresList, hdecomp]
    simp [P, M, Q, length_sortRef]
  refine ⟨sorted, kw.scratch, ?_, hsz, ?_, ?_, htsd.1, htsd.2.2⟩
  · change (do
      let sorted ← storageInsertion arrayStorage lt values kw.lo kw.hi
      pure (sorted, kw.scratch)) = .ok (sorted, kw.scratch)
    rw [hins]; rfl
  · rw [htsd.2.1]; exact perm_sortRef lt M
  · rw [htsd.2.1, sortedValues_iff_pairwise hnt]; exact sorted_sortRef hnt M
theorem legacyDispatchRejectsCycles_proven : LegacyDispatchRejectsCycles := by
  constructor
  · intro α _ lt values lo hi scratch hnt hlo hle hhi
    obtain ⟨⟨expected, hbounds, _, _, hperm, hsort, htake, hdrop⟩, _⟩ :=
      legacyInvalidWindowRejected_proven.1 α lt values #[] lo hi hnt hlo hle hhi
    refine ⟨expected, ?_, hperm, hsort, htake, hdrop⟩
    unfold legacySortDispatch
    simp [hbounds, bind, Except.bind, pure, Except.pure, Option.any]
  · intro V K Alg O Kws Scratch ops vector algorithm entry order keywords lo hi scratch message hkw hsame hundef
    unfold legacySortDispatch
    rw [hkw]
    simp only [hsame, hundef, bind, Except.bind, pure, Except.pure, Option.any, ↓reduceIte]
    rfl
def entries : List Entry := [
  { id := "sorttuplescov-insorted-range-equivalence", juliaFile := "base/sort.jl",
    juliaFns := ["insorted(x, v::AbstractVector; kw...)", "insorted(x, r::AbstractRange)"],
    statement := "For every sorted sequence and order-compatible equality predicate, range membership and vector search report the same insorted result.",
    source := "base/sort.jl:427-433 (insorted docstring); base/sort.jl:465-466", status := .refuted,
    prop := ``InsortedRangeAgrees, thm := some ``insortedRangeAgrees_refuted,
    issue := "related #48388 and #44102; none found (queries: insorted range, insorted missing, insorted -0.0)" },
  { id := "sort-insertionsort-stable", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, ::InsertionSortAlg, o, kw)"],
    statement := "InsertionSort returns the stable sorted permutation of its input for every strict weak order.",
    source := "base/sort.jl:807-821 (InsertionSort docstring: stable)", status := .proven,
    prop := ``InsertionSortStable, thm := some ``insertionSortStable_proven },
  { id := "memsafety-sort-send-to-end-window", juliaFile := "base/sort.jl",
    juliaFns := ["send_to_end!(f, v; lo, hi)"],
    statement := "As required by the documented view(v, lo:hi) equivalence, send_to_end! validates lo:hi before its @inbounds loops and never issues an unchecked @inbounds access outside 1:length(v).",
    source := "base/sort.jl:616-617 (view equivalence), 620-634", status := .refuted,
    prop := ``SendToEndInBounds, thm := some ``sendToEndInBounds_refuted,
    issue := "none found (queries: send_to_end bounds; send_to_end out of bounds; PRs same)" },
  { id := "sorttuplescov-sortperm-int-range", juliaFile := "base/sort.jl",
    juliaFns := ["sortperm_int_range"],
    statement := "The integer-range fast path returns a complete permutation sorted by value, preserving input order for ties.",
    source := "base/sort.jl:2058-2081; sortperm stable-order contract", status := .todo,
    prop := ``SortpermIntRangeCorrect, thm := none },
  { id := "sorttuplescov-uint-mapping", juliaFile := "base/sort.jl",
    juliaFns := ["uint_map(::Unsigned, ForwardOrdering)", "uint_unmap(::Type{T},::T,ForwardOrdering)", "uint_map(::Signed, ForwardOrdering)", "uint_unmap(::Type{T},::Unsigned,ForwardOrdering)", "uint_map(Char, ForwardOrdering)", "uint_unmap(Char,UInt32,ForwardOrdering)", "uint_map(x, ReverseOrdering)", "uint_unmap(T, u, ReverseOrdering)"],
    statement := "Unsigned mappings round-trip every BitInteger width and preserve the selected direct order; character mapping preserves its stored bits and their order.",
    source := "base/sort.jl:2239-2257,2267-2288; uint_map docstring", status := .proven,
    prop := ``UIntMappingCorrect, thm := some ``uintMappingCorrect_proven },
  { id := "sort-uint-mappable-dispatch", juliaFile := "base/sort.jl",
    juliaFns := ["UIntMappable(T::Type, order)", "UIntMappable(T::BitIntegerType, ForwardOrdering)", "UIntMappable(Char, ForwardOrdering)", "UIntMappable(T::Type, ReverseOrdering)", "_sort!(v, IsUIntMappable, o, kw)"],
    statement := "Unsupported types report no unsigned mapping; bit integers, characters, and reverse order return their documented mapping capabilities, and IsUIntMappable dispatches both branches to a sorted permutation.",
    source := "base/sort.jl:774-780,2237,2275,2284,2289", status := .proven,
    prop := ``UIntMappableDispatchCorrect, thm := some ``uintMappableDispatchCorrect_proven },
  { id := "sort-algorithm-policy-dispatch", juliaFile := "base/sort.jl",
    juliaFns := ["Small{N}(small, big)", "Small{N}(big)", "_sort!(v, Small{N}, o, kw)", "ConsiderCountingSort(next)", "_sort!(v, ConsiderCountingSort, o::DirectOrdering, kw)", "_sort!(v, ConsiderCountingSort, o::Ordering, kw)", "maybe_reverse", "ConsiderRadixSort(next)", "_sort!(v, ConsiderRadixSort, o::DirectOrdering, kw)", "ScratchQuickSort", "BracketedSort(k)", "maybe_unsigned", "InitialOptimizations(next)", "_sort!(v, ::Union{DefaultStable, DefaultUnstable}, o, kw)", "defalg", "maybe_apply_initial_optimizations", "_sort!(v, ::SubArrayOptimization, o, kw)", "_sort!(v, ::BoolOptimization, o, kw)"],
    statement := "Policy dispatchers, algorithm constructors, default-algorithm selectors, and fallback wrappers preserve full-sort and target-selection contracts and dispatch to a sorted permutation.",
    source := "base/sort.jl:559,745,793-802,922-933,946-947,982-992,1079-1082,1224,1443-1444,1473,1592,1620-1624,2396-2399", status := .proven,
    prop := ``AlgorithmPolicyDispatchCorrect, thm := some ``algorithmPolicyDispatchCorrect_proven },
  { id := "sort-window-issorted-correct", juliaFile := "base/sort.jl",
    juliaFns := ["_issorted(v, lo, hi, o)"],
    statement := "The private window check is true exactly when each adjacent pair in the checked interval is ordered.",
    source := "base/sort.jl:1445-1451; sorted-window invariant", status := .proven,
    prop := ``WindowIssortedCorrect, thm := some ``windowIssortedCorrect_proven },
  { id := "sorttuplescov-without-missing", juliaFile := "base/sort.jl",
    juliaFns := ["WithoutMissingVector", "getindex(::WithoutMissingVector)", "setindex!(::WithoutMissingVector)", "size(::WithoutMissingVector)", "axes(::WithoutMissingVector)"],
    statement := "Validated construction permits every in-bounds read without a missing-value assertion; mutation changes only the chosen backing element, and shape metadata is preserved.",
    source := "base/sort.jl:591-608; MissingOptimization docstring", status := .proven,
    prop := ``WithoutMissingVectorCorrect, thm := some ``withoutMissingVectorCorrect_proven },
  { id := "sorttuplescov-make-scratch", juliaFile := "base/sort.jl",
    juliaFns := ["make_scratch(::Nothing,T,len)", "make_scratch(::Vector{T},T,len)", "make_scratch(::Vector,T,len)"],
    statement := "make_scratch returns backing storage that covers the requested element capacity and a view over the same backing vector.",
    source := "base/sort.jl:494-501 (make_scratch docstring)", status := .proven,
    prop := ``MakeScratchCorrect, thm := some ``makeScratchCorrect_proven },
  { id := "sort-range-search-no-overflow", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedfirst(::AbstractRange{<:Integer}, x, o)", "searchsortedlast(::AbstractRange{<:Integer}, x, o)"],
    statement := "On every nonempty sorted integer range and every real query whose floor and ceiling offsets are representable, both range searches return the documented boundary indices.",
    source := "base/sort.jl:269-299,353-357,392-396 (search docstrings)", status := .proven,
    prop := ``RangeSearchNoOverflowCorrect, thm := some ``rangeSearchNoOverflowCorrect_proven },
  { id := "sort-range-search-overflow", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedfirst(::AbstractRange{<:Integer}, x, o)", "searchsortedlast(::AbstractRange{<:Integer}, x, o)", "searchsorted(::AbstractRange{<:Real}, x, o)"],
    statement := "On every nonempty sorted integer range and every real query, range searches return the documented boundary indices.",
    source := "base/sort.jl:353-357,392-396 (search docstrings)", status := .refuted,
    prop := ``RangeSearchNonemptyCorrect, thm := some ``rangeSearchNonemptyCorrect_refuted,
    issue := "#63399 (open PR, same overflow; queries: searchsorted overflow, searchsortedfirst range, searchsorted range wrong, searchsortedlast Int8)" },
  { id := "sort-range-search-empty", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedfirst(::AbstractRange{<:Integer}, x, o)", "searchsortedlast(::AbstractRange{<:Integer}, x, o)", "searchsorted(::AbstractRange{<:Real}, x, o)"],
    statement := "On empty integer ranges, searchsortedfirst returns 1 and searchsortedlast returns 0; on finite empty real ranges, searchsorted returns the empty 1:0 range.",
    source := "base/sort.jl:301-302,353-354,392-393 (search docstrings)", status := .refuted,
    prop := ``RangeSearchEmptyCorrect, thm := some ``rangeSearchEmptyCorrect_refuted,
    issue := "none found (related: #35272, #18653 reversed-range inconsistencies; queries: searchsorted empty range, searchsortedfirst empty range, searchsorted rev range, searchsorted empty)" },
  { id := "sorttuplescov-float-range-search-overflow", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedlast(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings)", "searchsortedfirst(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings)", "searchsorted(a::AbstractRange{<:Real}, x::Real, o::FastRangeOrderings)"],
    statement := "Searching finite real ranges returns first, last, and matching-range indices without throwing.",
    source := "base/sort.jl:243-267,301-302", status := .refuted,
    prop := ``FloatRangeSearchNoThrow, thm := some ``floatRangeSearchNoThrow_refuted,
    issue := "related #34408; none found (queries: searchsorted float range InexactError, searchsortedlast range Inf, searchsorted range overflow float)" },
  { id := "sort-issorted-adjacent", juliaFile := "base/sort.jl",
    juliaFns := ["issorted(itr, order)"],
    statement := "issorted returns true exactly when no element is ordered before its predecessor.",
    source := "base/sort.jl:62-66 (issorted docstring)", status := .proven,
    prop := ``IssortedAdjacent, thm := some ``issortedAdjacent_proven },
  { id := "sort-vector-search-correct", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedfirst(v, x; kws...)", "searchsortedlast(v, x; kws...)"],
    statement := "For every sorted vector and strict weak order, first and last search return the documented boundary indices.",
    source := "base/sort.jl:353-360,392-399 (search docstrings)", status := .proven,
    prop := ``VectorSearchCorrect, thm := some ``vectorSearchCorrect_proven },
  { id := "sort-vector-u8-search-sentinel", juliaFile := "base/sort.jl",
    juliaFns := ["searchsortedlast(v, x, lo::T, hi::T, o)", "searchsorted(v, x, lo::T, hi::T, o)"],
    statement := "For each valid vector window, searchsortedlast and searchsorted only read indices inside the vector.",
    source := "base/sort.jl:203-238 (inbounds search accesses)", status := .refuted,
    prop := ``WindowSearchInBounds, thm := some ``windowSearchInBounds_refuted,
    issue := "none found (related: #31618 generalized lo/hi to T<:Integer; #30388 these methods are undocumented; queries: searchsortedlast UInt8, searchsorted lo hi, searchsorted overflow)" },
  { id := "sort-partialsort-reversed-range", juliaFile := "base/sort.jl",
    juliaFns := ["partialsort!(v, k, o; scratch)", "partialsort!(v, k; kws...)", "partialsort(v, k; kws...)"],
    statement := "For every valid integer-index sequence, including a descending range, partialsort returns the values at those positions in a fully sorted permutation of the input.",
    source := "base/sort.jl:113-122 (partialsort! contract)", status := .refuted,
    prop := ``PartialSortRangeCorrect, thm := some ``partialSortRangeCorrect_refuted,
    issue := "none found (queries: partialsort range, partialsort reversed range, partialsortperm)" },
  { id := "sort-partialsort-empty-range", juliaFile := "base/sort.jl",
    juliaFns := ["partialsort!(v, k, o; scratch)", "partialsort(v, k; kws...)"],
    statement := "An empty selection range returns an empty vector for every input length.",
    source := "base/sort.jl:113-122 (partialsort! contract)", status := .refuted,
    prop := ``PartialSortEmptyRange, thm := some ``partialSortEmptyRange_refuted,
    issue := "none found (queries: partialsort empty, partialsort non-empty, partialsort range)" },
  { id := "sort-default-stable", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v; alg, lt, by, rev, order)", "sort(v; kws...)"],
    statement := "The AbstractArray default dispatch chooses DEFAULT_STABLE and its source algorithm pipeline returns a stable sorted permutation, including under reverse ordering.",
    source := "base/sort.jl:1627-1658 (sort! contract); base/sort.jl:1550-1561 (DEFAULT_STABLE guarantee)", status := .todo,
    prop := ``SortDefaultStable, thm := none },
  { id := "sort-vector-sorted-permutation", juliaFile := "base/sort.jl",
    juliaFns := ["sort(v::AbstractVector; alg, kws...)"],
    statement := "For each post-optimization algorithm and resolved ordering, a successful sort returns a sorted permutation and leaves the source vector unchanged.",
    source := "base/sort.jl:1743-1747 (sort copy contract)", status := .todo,
    prop := ``SortVectorSortedPermutation, thm := none },
  { id := "sort-partialsortperm-index-type", juliaFile := "base/sort.jl",
    juliaFns := ["partialsortperm(v, k)", "partialsortperm!(ix, v, k)"],
    statement := "When 1:length(v) fits in eltype(ix), partialsortperm! returns the stable-sorted permutation entries; when 1:length(v) fits in keytype(v) = Int64, partialsortperm(v, k) succeeds for every valid target k of any integer type.",
    source := "base/sort.jl:1853-1854,1896-1915 (partialsortperm contract)", status := .refuted,
    prop := ``PartialSortpermIndexTypeCorrect, thm := some ``partialSortpermIndexTypeCorrect_refuted,
    issue := "none found (queries: partialsortperm, partialsortperm Int8, partialsortperm InexactError, partialsortperm eltype)" },
  { id := "sortperm-stable-permutation", juliaFile := "base/sort.jl",
    juliaFns := ["sortperm", "_sortperm", "sortperm!"],
    statement := "For each index-sorting algorithm, sortperm returns indices in sorted value order and orders equal values by ascending source index.",
    source := "base/sort.jl:1920-1926 (sortperm contract)", status := .todo,
    prop := ``SortpermStable, thm := none },
  { id := "sort-scratchquicksort-stable", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, ::ScratchQuickSort, o, kw)", "partition!(t, lo, hi, offset, o, v, rev, pivot_dest, pivot_index_offset)"],
    statement := "Untargeted ScratchQuickSort returns the stable sorted permutation for every strict weak order and pivot rule selecting an index in the current window.",
    source := "base/sort.jl:1050-1075 (ScratchQuickSort stability contract)", status := .todo,
    prop := ``ScratchQuickSortStable, thm := none },
  { id := "memsafety-sort-checked-windows", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, lo, hi, QuickSort, o)", "_issorted(v, lo, hi, o)", "_sort!(v, InsertionSort, o, kw)"],
    statement := "A valid checked window prevents out-of-bounds reads and writes in insertion sort, the sortedness check, and the public legacy quicksort.",
    source := "base/sort.jl:835-852,1445-1451,2454-2478; checked-window invariant", status := .todo,
    prop := ``CheckedWindowsInBounds, thm := none },
  { id := "memsafety-sort-count-buckets", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, CountingSort(), o, kw)"],
    statement := "Integer values between the computed extrema use only allocated counting-sort buckets when the bucket count is representable.",
    source := "base/sort.jl:948-969; counting-sort normalization invariant", status := .todo,
    prop := ``CountBucketsInBounds, thm := none },
  { id := "sorttuplescov-legacy-sort-scratch", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, lo, hi, a, o, scratch)", "_sort!(v, a::Algorithm, o, kw)"],
    statement := "Providing scratch to a supported legacy sort preserves successful sorting on a valid window.",
    source := "base/sort.jl:2570-2595 (legacy scratch interface)", status := .refuted,
    prop := ``LegacySortScratch, thm := some ``legacySortScratch_refuted,
    issue := "none found (queries: sort! QuickSort scratch, _sort! is not defined, legacy sort! QuickSort)" },
  { id := "sorttuplescov-partialquicksort-reversed-range", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, lo, hi, a::PartialQuickSort, o)", "_partialquicksort!(v, lo, hi, a, o)"],
    statement := "Every requested valid target position, including a descending range, contains the value it would contain in a fully sorted vector.",
    source := "base/sort.jl:2533-2566; PartialQuickSort target invariant", status := .refuted,
    prop := ``LegacyPartialRangeCorrect, thm := some ``legacyPartialRangeCorrect_refuted,
    issue := "related #63228; none found (queries: PartialQuickSort range, PartialQuickSort reverse)" },
  { id := "sorttuplescov-sort-dims-exception", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(A; dims, alg, lt, by, rev, order, scratch)"],
    statement := "Every out-of-range dimension reaches the explicit dimension-out-of-range exception.",
    source := "base/sort.jl:2187-2196 (dimension validation)", status := .refuted,
    prop := ``SortDimsChecked, thm := some ``sortDimsChecked_refuted,
    issue := "none found (queries: sort! dims BoundsError, sort dims out of range)" },
  { id := "sorttuplescov-sort-ntuple-alg", juliaFile := "base/sort.jl",
    juliaFns := ["sort(x::NTuple; alg, kws...)", "_sort(x::NTuple, a, o, kw)"],
    statement := "Every full sorting algorithm accepted by the NTuple sort signature returns a sorted permutation of the input tuple.",
    source := "base/sort.jl:1785-1808", status := .refuted,
    prop := ``TupleSortExplicitAlgCorrect, thm := some ``tupleSortExplicitAlgCorrect_refuted,
    issue := "related #54494; none found (queries: sort tuple alg, sort NTuple QuickSort, sort NTuple MethodError)" },
  { id := "sorttuplescov-sort-missing-scratch", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v; scratch)", "_sort!(v, MissingOptimization(next), o::DirectOrdering, kw)", "WithoutMissingVector", "make_scratch(::Vector,T,len)"],
    statement := "Calling sort!(v; scratch) with a scratch vector of eltype(v) = Union{Missing, Int32} succeeds when MissingOptimization forwards the unwrapped vector and scratch buffer.",
    source := "base/sort.jl:511-516,651-655,1017-1046,1732-1741", status := .refuted,
    prop := ``SortMissingScratchAccepted, thm := some ``sortMissingScratchAccepted_refuted,
    issue := "none found (queries: sort scratch missing reinterpret, cannot reinterpret scratch sort, make_scratch)" },
  { id := "sort-issorted-keywords", juliaFile := "base/sort.jl",
    juliaFns := ["issorted(itr; lt, by, rev, order)"],
    statement := "Keyword sortedness tests precisely the adjacent-order condition under the resolved ordering.",
    source := "base/sort.jl:62-66,86-95", status := .proven,
    prop := ``IssortedKeywordsCorrect, thm := some ``issortedKeywordsCorrect_proven },
  { id := "sort-searchsorted-equivalent-range", juliaFile := "base/sort.jl",
    juliaFns := ["searchsorted(v, x, lo, hi, o)", "searchsorted(v, x; kws...)"],
    statement := "The result contains exactly the indices equivalent to the query; an absent query produces the empty range at its insertion point.",
    source := "base/sort.jl:313-322 (searchsorted contract)", status := .proven,
    prop := ``SearchsortedEquivalentRange, thm := some ``searchsortedEquivalentRange_proven },
  { id := "sort-send-to-end-stable-partition", juliaFile := "base/sort.jl",
    juliaFns := ["send_to_end!(f, v; lo, hi)"],
    statement := "The window is partitioned by the predicate, preserves the order of nonsent values, and leaves elements outside the window unchanged.",
    source := "base/sort.jl:610-618", status := .todo,
    prop := ``SendToEndStablePartition, thm := none },
  { id := "sort-bool-sorted-permutation", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v::AbstractVector{Bool}, ::BoolOptimization, o, kw)"],
    statement := "Boolean counting sort returns a sorted permutation for every strict weak order.",
    source := "base/sort.jl:734-740,746-758", status := .proven,
    prop := ``BoolSortCorrect, thm := some ``boolSortCorrect_proven },
  { id := "sort-counting-sorted-permutation", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, CountingSort(), o, kw)"],
    statement := "Counting sort returns a permutation in the requested direct order for every BitInteger width when the bucket array is representable.",
    source := "base/sort.jl:936-943", status := .todo,
    prop := ``CountingSortCorrect, thm := none },
  { id := "sort-radix-sorted-permutation", juliaFile := "base/sort.jl",
    juliaFns := ["radix_sort!", "radix_sort_pass!"],
    statement := "Radix passes preserve every value and leave the selected final buffer in ascending unsigned order.",
    source := "base/sort.jl:1382-1429", status := .todo,
    prop := ``RadixSortCorrect, thm := none },
  { id := "sort-move-preserves-selected-values", juliaFile := "base/sort.jl",
    juliaFns := ["move!(v, target, source)"],
    statement := "Moving equally sized valid index selections preserves the input multiset and puts the source values at the target positions.",
    source := "base/sort.jl:1248-1262; move invariant", status := .todo,
    prop := ``MoveVectorCorrect, thm := none },
  { id := "sort-bracket-kernel-partition", juliaFile := "base/sort.jl",
    juliaFns := ["bracket_kernel!"],
    statement := "Bracketing preserves the input multiset, selects exactly the values between the signposts, and counts every value below the lower signpost.",
    source := "base/sort.jl:1226-1246,1323-1346", status := .todo,
    prop := ``BracketKernelCorrect, thm := none },
  { id := "sort-legacy-quicksort-correct", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, lo, hi, QuickSort, o)", "_quicksort!", "partition!", "selectpivot!"],
    statement := "Legacy quicksort returns a sorted permutation for every strict weak order.",
    source := "base/sort.jl:2409-2478; sorting contract", status := .todo,
    prop := ``QuickSortCorrect, thm := none },
  { id := "sort-legacy-mergesort-stable", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, lo, hi, MergeSort, o, scratch)", "_mergesort!"],
    statement := "Legacy mergesort returns a stable sorted permutation.",
    source := "base/sort.jl:2480-2531; MergeSort stability contract", status := .todo,
    prop := ``MergeSortStable, thm := none },
  { id := "sort-tuple-stable-permutation", juliaFile := "base/sort.jl",
    juliaFns := ["sort(x::NTuple; kws...)", "_sort(x::NTuple, a, o, kw)", "_mergesort(x::NTuple, o)"],
    statement := "The default tuple algorithm returns a stable sorted permutation; explicit algorithms retain their sorted-permutation behavior.",
    source := "base/sort.jl:1743-1747,1785-1813", status := .todo,
    prop := ``TupleSortStable, thm := none },
  { id := "sort-tuple-merge-correct", juliaFile := "base/sort.jl",
    juliaFns := ["merge(x::NTuple, y::NTuple, o)", "merge(x::NTuple, y::NTuple{0}, o)", "merge(x::NTuple{0}, y::NTuple, o)", "merge(x::NTuple{0}, y::NTuple{0}, o)"],
    statement := "Merging sorted tuples returns a sorted permutation of their concatenation.",
    source := "base/sort.jl:1814-1818; merge invariant", status := .proven,
    prop := ``TupleMergeCorrect, thm := some ``tupleMergeCorrect_proven },
  { id := "sort-missing-direct-correct", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, MissingOptimization(next), o::DirectOrdering, kw)"],
    statement := "Missing-value optimization preserves the multiset and puts missing values at the correct end while sorting nonmissing values.",
    source := "base/sort.jl:576-583,651-655", status := .todo,
    prop := ``MissingDirectCorrect, thm := none },
  { id := "sort-missing-permutation-correct", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, MissingOptimization(next), o::Perm, kw)"],
    statement := "Missing-value permutation optimization returns a stable sorting permutation, including equal and missing values.",
    source := "base/sort.jl:656-682; sortperm stability contract", status := .todo,
    prop := ``MissingPermutationCorrect, thm := none },
  { id := "sort-ieee-float-correct", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, IEEEFloatOptimization(next), o, kw)", "after_zero", "is_concrete_IEEEFloat"],
    statement := "IEEE optimization returns a sorted permutation in either direct order and preserves the input order of NaNs.",
    source := "base/sort.jl:689-697,703-731; floating-point sorting contract", status := .todo,
    prop := ``IEEEFloatOptimizationCorrect, thm := none },
  { id := "sort-check-sorted-correct", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, CheckSorted(next), o, kw)"],
    statement := "The presorted and reverse-sorted fast paths preserve the multiset and return the same sorted-order guarantee as the continuation.",
    source := "base/sort.jl:855-879", status := .proven,
    prop := ``CheckSortedCorrect, thm := some ``checkSortedCorrect_proven },
  { id := "sort-compute-extrema-correct", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, ComputeExtrema(next), o, kw)"],
    statement := "Computed extrema are sufficient for counting sort to return a sorted permutation, including reverse order and equal-valued input.",
    source := "base/sort.jl:882-905", status := .todo,
    prop := ``ComputeExtremaCountingCorrect, thm := none },
  { id := "sort-uint-vector-round-trip", juliaFile := "base/sort.jl",
    juliaFns := ["uint_map!", "uint_unmap!", "uint_map", "uint_unmap"],
    statement := "Unsigned mapping preserves vector length, maps exactly the selected window, and unmapping restores every original value at every integer width and direct ordering.",
    source := "base/sort.jl:2239-2257,2295-2310", status := .proven,
    prop := ``UIntVectorRoundTrip, thm := some ``uintVectorRoundTrip_proven },
  { id := "sort-radix-wrapper-correct", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, RadixSort(), o, kw)"],
    statement := "Radix normalization, buffer sorting, and unmapping return a sorted permutation for every BitInteger width and direct ordering.",
    source := "base/sort.jl:1017-1047", status := .todo,
    prop := ``RadixWrapperCorrect, thm := none },
  { id := "sort-chunks-correct", juliaFile := "base/sort.jl",
    juliaFns := ["sort_chunks!(Av, n, alg, order, scratch)", "sort_chunks!(Av, n, alg, order, scratch, fst, lst)"],
    statement := "Chunk sorting preserves vector length and returns a sorted permutation inside each positive-width chunk, including a shorter final chunk and supplied-scratch execution.",
    source := "base/sort.jl:2136-2154", status := .todo,
    prop := ``ChunkSortCorrect, thm := none },
  { id := "sort-dimension-copy-correct", juliaFile := "base/sort.jl",
    juliaFns := ["sort(A::AbstractArray; dims)"],
    statement := "For any valid dimension, sorting preserves the array axes and returns a sorted permutation within each original slice, in either ordering.",
    source := "base/sort.jl:2084-2099,2112-2134", status := .todo,
    prop := ``MultidimensionalCopyCorrect, thm := none },
  { id := "sort-dimension-mutation-correct", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(A::AbstractArray; dims)", "get_view", "get_value"],
    statement := "In-place dimension sorting preserves the array axes and sorts every slice without exchanging values between slices, including both allocation branches.",
    source := "base/sort.jl:2156-2185,2187-2224", status := .todo,
    prop := ``MultidimensionalMutationCorrect, thm := none },
  { id := "sort-algorithm-display-well-formed", juliaFile := "base/sort.jl",
    juliaFns := ["Base.show(io, alg::Algorithm)", "print_tree", "show_type(io, a)", "show_type(io, alg::Small)"],
    statement := "The recursive algorithm display balances its parentheses when leaf displays do, show_type forwards type names, and Small's display identifies its type and parameter.",
    source := "base/sort.jl:1597-1618", status := .proven,
    prop := ``AlgorithmDisplayWellFormed, thm := some ``algorithmDisplayWellFormed_proven },
  { id := "sort-subarray-preserves-parent", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v::UnwrappableSubArray, a::SubArrayOptimization, o, kw)"],
    statement := "Subarray sorting preserves the parent multiset, sorts the view, and leaves every parent element outside the view unchanged, with or without parent unwrapping.",
    source := "base/sort.jl:549-556,560-574", status := .proven,
    prop := ``SubArraySortCorrect, thm := some ``subArraySortCorrect_proven },
  { id := "sort-radix-chunk-covers-bits", juliaFile := "base/sort.jl",
    juliaFns := ["radix_chunk_size_heuristic"],
    statement := "For a positive representable span and 1 through 128 key bits, the heuristic returns 1 through 10 bits per pass, and whole passes cover every key bit.",
    source := "base/sort.jl:1430-1441", status := .proven,
    prop := ``RadixChunkCoversBits, thm := some ``radixChunkCoversBits_proven },
  { id := "sort-collected-permutation", juliaFile := "base/sort.jl",
    juliaFns := ["sort(v::COLLECT_ON_SORT_TYPES; kws...)"],
    statement := "The collection overload collects the iteration sequence, forwards the selected algorithm and ordering, and returns a sorted permutation.",
    source := "base/sort.jl:1743-1759,1783", status := .todo,
    prop := ``CollectedSortCorrect, thm := none },
  { id := "sort-ieee-permutation-correct", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, IEEEFloatOptimization(next), o::Perm, kw)"],
    statement := "IEEE permutation sorting returns every original index in the selected value order and breaks every tie by ascending index, including NaNs.",
    source := "base/sort.jl:719-729; sortperm stability contract", status := .todo,
    prop := ``IEEEFloatPermutationCorrect, thm := none },
  { id := "sort-legacy-invalid-window-rejected", juliaFile := "base/sort.jl",
    juliaFns := ["sort!(v, a, o)", "sort!(v, lo, hi, a, o)", "sort!(v, lo, hi, a, o, _)", "sort!(v, lo, hi, a, o, scratch::Vector)"],
    statement := "For valid windows, the legacy entry points sort the window into a permutation ordered by lt and preserve elements outside the window; for nonempty out-of-bounds windows, they reject with BoundsError.",
    source := "base/sort.jl:2571-2582", status := .proven,
    prop := ``LegacyInvalidWindowRejected, thm := some ``legacyInvalidWindowRejected_proven },
  { id := "sort-legacy-dispatch-rejects-cycles", juliaFile := "base/sort.jl",
    juliaFns := ["_sort!(v, a::Algorithm, o, kw)"],
    statement := "When entered from the keyword pipeline, legacy _sort! forwards to the 5-argument sort!, sorts the window, and returns the caller scratch; re-entering with the same legacy_dispatch_entry reports an ArgumentError.",
    source := "base/sort.jl:2586-2595", status := .proven,
    prop := ``LegacyDispatchRejectsCycles, thm := some ``legacyDispatchRejectsCycles_proven }
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
| `sort@2112` | sort-dimension-copy-correct |
| `sort_chunks!@2136` | sort-chunks-correct |
| `sort_chunks!@2141` | sort-chunks-correct |
| `sort_chunks!@2149` | sort-chunks-correct |
| `sort!@2187` | sort-dimension-mutation-correct, sorttuplescov-sort-dims-exception |
| `get_view@2206` | sort-dimension-mutation-correct |
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

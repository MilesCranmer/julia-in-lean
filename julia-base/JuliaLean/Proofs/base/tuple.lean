import JuliaLean.base.tuple
import JuliaLean.base.reduce
import JuliaLean.Registry.Types

/-!
# Specifications of `base/tuple.jl`

Each proposition below names definitions in `JuliaLean.base.tuple`. A small number of reference
expressions use Lean's list operations to state the documented collection behavior independently.
-/

namespace JuliaLean.Proofs.base.tuple

open JuliaLean JuliaLean.Registry JuliaLean.base.tuple

abbrev R (α : Type) := JuliaLean.base.tuple.R α


theorem litI64Value (x : Int) (h : IntTy.i64.min ≤ x ∧ x ≤ IntTy.i64.max) :
    (JInt.lit .i64 x).val = x := by
  change wrapInt .i64 x = x
  exact wrapInt_of_inRange .i64 x h
theorem i64Bounds : IntTy.i64.min ≤ -1 ∧ (2 ^ 62 : Nat) ≤ IntTy.i64.max := by
  constructor
  · simp [IntTy.min, IntTy.signed, IntTy.bits]
  · decide

theorem i64NatFits (n : Nat) (h : n < 2 ^ 62) :
    IntTy.i64.min ≤ (n : Int) ∧ (n : Int) ≤ IntTy.i64.max := by
  constructor
  · have hmin : IntTy.i64.min ≤ 0 := by have := i64Bounds.1; omega
    exact Int.le_trans hmin (Int.natCast_nonneg _)
  · have hn : (n : Int) < ((2 ^ 62 : Nat) : Int) := by omega
    exact Int.le_trans (Int.le_of_lt hn) i64Bounds.2

theorem i64NatValue (n : Nat) (h : n < 2 ^ 62) :
    (JInt.lit .i64 (n : Int)).val = (n : Int) :=
  litI64Value _ (i64NatFits n h)

theorem addI64Value (a b : JInt .i64)
    (h : IntTy.i64.min ≤ a.val + b.val ∧ a.val + b.val ≤ IntTy.i64.max) :
    (a + b).val = a.val + b.val := by
  change wrapInt .i64 (a.val + b.val) = _
  exact wrapInt_of_inRange .i64 _ h

theorem subI64Value (a b : JInt .i64)
    (h : IntTy.i64.min ≤ a.val - b.val ∧ a.val - b.val ≤ IntTy.i64.max) :
    (a - b).val = a.val - b.val := by
  change wrapInt .i64 (a.val - b.val) = _
  exact wrapInt_of_inRange .i64 _ h

theorem wrapI64Value (x : Int) (h : IntTy.i64.min ≤ x ∧ x ≤ IntTy.i64.max) :
    (JInt.wrap .i64 x).val = x := by
  change wrapInt .i64 x = x
  exact wrapInt_of_inRange .i64 x h


theorem mapM_map' {γ β : Type} (g : Nat → γ) (f : γ → R β) (l : List Nat) :
    (l.map g).mapM f = l.mapM (f ∘ g) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

theorem mapM_range_ok {β : Type} (n : Nat) (f : Nat → R β) (L : List β)
    (hl : L.length = n) (h : ∀ k (hk : k < L.length), f k = .ok L[k]) :
    (List.range n).mapM f = .ok L := by
  induction n generalizing f L with
  | zero =>
    cases L with
    | nil => rfl
    | cons _ _ => simp at hl
  | succ n ih =>
    cases L with
    | nil => simp at hl
    | cons b L =>
      rw [List.range_succ_eq_map, List.mapM_cons, mapM_map']
      have h0 : f 0 = .ok b := h 0 (by simp)
      have hr := ih (f ∘ Nat.succ) L (by simpa using hl)
        (fun k hk => h (k + 1) (by simp; omega))
      rw [h0, hr]
      rfl
theorem getfieldInBounds {α : Type} (t : List α) (i : Nat) (h : i < t.length) :
    getfield t ((i : Int) + 1) = .ok t[i] := by
  unfold getfield
  have hpos : (1 : Int) ≤ (i : Int) + 1 := by omega
  have hindex : ((i : Int) + 1 - 1).toNat = i := by omega
  rw [if_pos hpos, hindex, List.getElem?_eq_getElem h]

theorem getfieldBounds {α : Type} (t : List α) (i : Int)
    (h : ¬ (1 ≤ i ∧ i ≤ t.length)) : getfield t i = bounds := by
  unfold getfield
  by_cases hpos : 1 ≤ i
  · have hidx : t.length ≤ (i - 1).toNat := by omega
    rw [if_pos hpos, List.getElem?_eq_none hidx]
  · rw [if_neg hpos]

def SameOutcome {α : Type} : R α → R α → Prop
  | .ok a, .ok b => a = b
  | .error e, .error f => e.kind = f.kind
  | _, _ => False
instance instDecidableSameOutcome {α : Type} [DecidableEq α] :
    (a b : R α) → Decidable (SameOutcome a b)
  | .ok a, .ok b => inferInstanceAs (Decidable (a = b))
  | .error e, .error f => inferInstanceAs (Decidable (e.kind = f.kind))
  | .ok _, .error _ => isFalse (fun h => h)
  | .error _, .ok _ => isFalse (fun h => h)

@[simp] theorem exceptMapOk {α β : Type} (f : α → β) (x : α) :
    (f <$> (.ok x : R α)) = (.ok (f x) : R β) := rfl

/-!
Nothing to promise: prevind@109: declares a generic function with no method body.
Nothing to promise: nextind@143: declares a generic function with no method body.
Nothing to promise: rest@205: declares a generic function with no method body.
Nothing to promise: rest@213: forwards the iterator and state to Iterators.rest.
Nothing to promise: split_rest@247: declares a generic function with no method body.
Nothing to promise: valtype@319: forwards reflection to the value type.
Nothing to promise: valtype@320: forwards type reflection to eltype.
Nothing to promise: safe_tail@323: forwards the nonempty tuple to tail.
Nothing to promise: _totuple@509: forwards the typed iterator remainder to collect and splats its values.
Nothing to promise: _totuple@511: forwards the iterator remainder to collect and splats its values.
-/

/-! ## Method to property table

| Julia method | Registry property |
| --- | --- |
| `_counttuple@23` | sorttuplescov-tuple-type-methods |
| `_counttuple@24` | sorttuplescov-tuple-type-methods |
| `length@28` | sorttuplescov-tuple-basics |
| `firstindex@29` | sorttuplescov-tuple-basics |
| `lastindex@30` | sorttuplescov-tuple-basics |
| `size@31` | sorttuplescov-tuple-basics |
| `axes@32` | sorttuplescov-tuple-basics |
| `getindex@33` | tuples-integer-index |
| `getindex@34` | tuples-getindex-bool,tuples-getindex-inexact,tuples-integer-index,tuples-bool-index-accepted |
| `__safe_getindex@35` | sorttuplescov-tuple-basics |
| `getindex@36` | sorttuplescov-tuple-index-vec |
| `getindex@37` | sorttuplescov-tuple-index-vec |
| `getindex@38` | sorttuplescov-tuple-index-vec |
| `get@40` | tuples-getindex-bool,tuples-integer-index,tuples-bool-index-accepted |
| `get@41` | sorttuplescov-tuple-index-vec |
| `setindex@55` | tuples-getindex-bool,tuples-integer-index,tuples-bool-index-accepted |
| `_setindex@61` | tuples-integer-index,tuples-bool-index-accepted |
| `iterate@69` | sorttuplescov-tuple-basics |
| `keys@75` | sorttuplescov-tuple-basics |
| `prevind@109` | Nothing to promise |
| `nextind@143` | Nothing to promise |
| `prevind@145` | sorttuplescov-tuple-basics |
| `nextind@146` | sorttuplescov-tuple-basics |
| `keys@148` | sorttuplescov-tuple-iter-protocol |
| `indexed_iterate@161` | sorttuplescov-tuple-iter-protocol |
| `indexed_iterate@162` | sorttuplescov-tuple-iter-protocol |
| `indexed_iterate@163` | sorttuplescov-tuple-iter-protocol |
| `indexed_iterate@168` | sorttuplescov-tuple-iter-protocol |
| `rest@205` | Nothing to promise |
| `rest@206` | sorttuplescov-rest |
| `rest@207` | sorttuplescov-rest |
| `rest@212` | sorttuplescov-rest |
| `rest@213` | Nothing to promise |
| `split_rest@247` | Nothing to promise |
| `split_rest@248` | sorttuplescov-split-rest |
| `_split_rest@254` | sorttuplescov-split-rest |
| `_check_length_split_rest@255` | sorttuplescov-split-rest |
| `_split_rest@260` | sorttuplescov-split-rest |
| `_split_tuple@265` | tuples-split-rest-state |
| `split_rest@267` | tuples-split-rest-state |
| `first@270` | tuples-front-tail |
| `first@271` | tuples-front-tail |
| `_eltype_ntuple@279` | sorttuplescov-tuple-type-methods |
| `eltype@282` | sorttuplescov-tuple-type-methods |
| `_compute_eltype@291` | sorttuplescov-tuple-type-methods |
| `keytype@316` | sorttuplescov-tuple-type-methods |
| `keytype@317` | sorttuplescov-tuple-type-methods |
| `valtype@319` | Nothing to promise |
| `valtype@320` | Nothing to promise |
| `safe_tail@323` | Nothing to promise |
| `safe_tail@324` | sorttuplescov-tuple-basics |
| `front@344` | tuples-front-tail |
| `_front@348` | tuples-front-tail |
| `_front@349` | tuples-front-tail |
| `_front@350` | tuples-front-tail |
| `map@358` | tuples-map |
| `map@359` | tuples-map |
| `map@360` | tuples-map |
| `map@361` | tuples-map |
| `map@362` | tuples-map |
| `front@375` | tuples-front-tail |
| `front@380` | tuples-front-tail |
| `_front_type@387` | sorttuplescov-tuple-type-methods |
| `map@394` | tuples-map |
| `map@403` | tuples-map |
| `map@404` | tuples-map |
| `map@405` | tuples-map |
| `map@406` | tuples-map |
| `map@407` | tuples-map |
| `map@408` | tuples-map |
| `map@412` | tuples-map |
| `heads@421` | sorttuplescov-map-n-foreach |
| `tails@422` | sorttuplescov-map-n-foreach |
| `map@423` | sorttuplescov-map-n-foreach |
| `anyempty@424` | sorttuplescov-map-n-foreach |
| `anyempty@425` | sorttuplescov-map-n-foreach |
| `anyempty@426` | sorttuplescov-map-n-foreach |
| `map@427` | sorttuplescov-map-n-foreach |
| `map@432` | sorttuplescov-map-n-foreach |
| `fill_to_length@442` | sorttuplescov-fill-to-length |
| `fill_to_length@443` | sorttuplescov-fill-to-length |
| `fill_to_length@444` | sorttuplescov-fill-to-length |
| `fill_to_length@445` | sorttuplescov-fill-to-length |
| `tuple_type_tail@453` | sorttuplescov-tuple-type-methods |
| `(::Type{T})@470` | sorttuplescov-tuple-construction |
| `Tuple@472` | sorttuplescov-tuple-construction |
| `Tuple@473` | sorttuplescov-tuple-construction |
| `(::Type{T})@475` | sorttuplescov-tuple-construction |
| `_totuple@477` | sorttuplescov-tuple-construction |
| `_totuple_err@479` | sorttuplescov-tuple-construction |
| `_totuple@484` | sorttuplescov-tuple-construction |
| `_totuple@498` | sorttuplescov-tuple-construction |
| `_totuple@509` | Nothing to promise |
| `_totuple@511` | Nothing to promise |
| `_totuple@514` | sorttuplescov-tuple-construction |
| `_totuple@515` | sorttuplescov-tuple-construction |
| `_totuple@516` | sorttuplescov-tuple-construction |
| `_totuple@517` | sorttuplescov-tuple-construction |
| `_totuple@518` | sorttuplescov-tuple-construction |
| `_findfirst_rec@522` | tuples-find-filter |
| `_findfirst_rec@523` | tuples-find-filter |
| `_findfirst_loop@524` | tuples-find-filter |
| `findfirst@530` | tuples-find-filter |
| `findlast@532` | tuples-find-filter |
| `_findlast_rec@533` | tuples-find-filter |
| `_findlast_loop@537` | tuples-find-filter |
| `filter_rec@546` | tuples-find-filter |
| `filter@549` | tuples-find-filter |
| `isequal@553` | tuples-equality,tuples-hash-isequal |
| `_isequal@554` | tuples-equality |
| `_isequal@555` | tuples-equality,tuples-internal-comparison-errors |
| `_isequal@558` | tuples-equality,tuples-internal-comparison-errors |
| `==@567` | tuples-equality |
| `_eq@568` | tuples-equality |
| `_eq_missing@569` | tuples-equality |
| `_eq@570` | tuples-equality,tuples-internal-comparison-errors |
| `_eq_missing@580` | tuples-equality,tuples-internal-comparison-errors |
| `_eq@588` | tuples-equality,tuples-internal-comparison-errors |
| `hash@602` | tuples-hash-isequal |
| `hash@603` | hashops-tuple-hash,tuples-hash-isequal |
| `hash@604` | hashops-tuple-hash,tuples-hash-isequal |
| `<@612` | tuples-lt-lexicographic |
| `<@613` | tuples-lt-lexicographic |
| `<@614` | tuples-lt-lexicographic |
| `<@615` | tuples-lt-lexicographic |
| `<@625` | tuples-lt-lexicographic |
| `isless@639` | tuples-isless-order |
| `isless@640` | tuples-isless-order |
| `isless@641` | tuples-isless-order |
| `isless@648` | tuples-isless-order |
| `isless@652` | tuples-isless-order |
| `isempty@665` | sorttuplescov-tuple-basics |
| `isempty@666` | sorttuplescov-tuple-basics |
| `revargs@668` | tuples-reverse |
| `revargs@669` | tuples-reverse |
| `reverse@671` | tuples-reverse |
| `isassigned@681` | tuples-getindex-bool,tuples-integer-index,tuples-bool-index-accepted |
| `prod@688` | tuples-prod-empty,tuples-product-value |
| `prod@693` | tuples-prod-empty,tuples-product-value |
| `sym_in@696` | sorttuplescov-sym-in |
| `in@704` | sorttuplescov-sym-in |
| `empty@712` | sorttuplescov-tuple-basics |
| `foreach@714` | sorttuplescov-map-n-foreach |
| `foreach@715` | sorttuplescov-map-n-foreach |
| `circshift@717` | tuples-circshift |
| `circshift@718` | tuples-circshift |
| `circshift@719` | tuples-circshift |
-/

/-! ## Refutations -/

def vectorBoolIndexError {α : Type} : R α :=
  .error (.julia (.argumentError "invalid index: true of type Bool"))

def ntupleList {α : Type} (f : Nat → α) (n : Nat) : List α := (List.range n).map (fun i => f (i + 1))


def BoolIndexAgrees : Prop :=
  ∀ (t : List Int) (b : Bool) (v d : Int)
    (ntuple : (Nat → Int) → Nat → List Int),
    SameOutcome (getindexInteger t (.bool b)) vectorBoolIndexError ∧
    SameOutcome (setindexTuple ntuple cond t v (.bool b)) vectorBoolIndexError ∧
    SameOutcome (getDefault t (.bool b) d) vectorBoolIndexError ∧
    SameOutcome (.ok (isassignedTuple t (.bool b))) vectorBoolIndexError

theorem boolIndexAgrees_refuted : ¬ BoolIndexAgrees := by
  intro h
  have hbad : ¬ SameOutcome (getindexInteger [10] (.bool true)) vectorBoolIndexError := by decide
  exact hbad (h [10] true 0 0 ntupleList).1

def GetindexBoundsError : Prop :=
  ∀ (t : List Int) (ty : IntTy) (i : JInt ty),
    ¬ (1 ≤ i.val ∧ i.val ≤ t.length) →
      SameOutcome (getindexInteger t (.integer ty i)) bounds

theorem getindexBoundsError_refuted : ¬ GetindexBoundsError := by
  intro h
  have hbad : ¬ SameOutcome
      (getindexInteger ([] : List Int) (.integer .u64 (JInt.typemax .u64))) bounds := by
    decide
  exact hbad (h [] .u64 (JInt.typemax .u64) (by decide))


/-- The product-reduction documentation promises agreement between prod(t) and prod(identity,t). -/
def ProdAgrees : Prop :=
  ∀ (multiply : List (JInt .i64) → JInt .i64),
    (∀ xs, multiply xs = JInt.lit .i64 ((xs.map (fun x => x.val)).prod)) →
    ∀ (iteratorEltype : {I : Type} → JuliaLean.base.reduce.JIterator I →
      JuliaLean.base.reduce.EltypeStatus) (t : List (JInt .i64)),
    SameOutcome (prodTupleMethod multiply t)
      (liftJ (JuliaLean.base.reduce.prod_f iteratorEltype id
        (JuliaLean.base.reduce.valueReducer
          (JuliaLean.base.reduce.mul_prod JuliaLean.base.int.mul)
          (JuliaLean.base.reduce.reduce_first_mul_prod id)
          (JuliaLean.base.reduce.reduce_empty_union
            (JuliaLean.base.reduce.mul_prod JuliaLean.base.int.mul) ([] : List Unit)))
        (.values t) .initial .identity))

theorem prodAgrees_refuted : ¬ ProdAgrees := by
  intro h
  exact h (fun xs => JInt.lit .i64 ((xs.map (fun x => x.val)).prod)) (fun _ => rfl)
    (fun {_} _ => .hasEltype) []

def intTupleConversion : TupleConversion Int :=
  { typeof := fun _ => .tuple [.vararg .any none]
    eltypes := {
      empty := fun _ => false
      signature := fun _ => true
      defined := fun _ => true
      isType := fun _ => true
      emptyNTuple := fun _ => false
      element := fun _ => .any
      free := fun _ => false
      join := fun _ _ => .any }
    convert := fun _ x => .ok x }

/-- Base.split_rest promises a partition of the remainder at the supplied iteration state,
or ArgumentError when the remainder contains fewer than n elements. -/
def SplitRestAgrees : Prop :=
  ∀ (α : Type) (typing : TupleConversion α), (∀ E x, typing.convert E x = .ok x) →
  ∀ (t : List α) (n i : Nat),
    1 ≤ i → i ≤ t.length + 1 → t.length < 2 ^ 62 →
    let remaining := t.drop (i - 1)
    SameOutcome
      (splitRestTupleState typing t (n : Int)
        (.integer .i64 (JInt.lit .i64 (i : Int))))
      (if n ≤ remaining.length then
        .ok (remaining.take (remaining.length - n), remaining.drop (remaining.length - n))
       else argErr "The remaining iterator has fewer than n elements.")

theorem splitRestAgrees_refuted : ¬ SplitRestAgrees := by
  intro h
  have hbad : ¬ SameOutcome
      (splitRestTupleState intTupleConversion [1] 1
        (.integer .i64 (JInt.lit .i64 2)))
      (argErr "The remaining iterator has fewer than n elements.") := by decide
  exact hbad (h Int intTupleConversion (fun _ _ => rfl) [1] 1 2 (by decide) (by decide) (by decide))

/-! ## Proven properties -/

def TupleBasicsCorrect : Prop :=
  ∀ (α : Type) (showIndex : Index → String) (t : List α),
    lengthTuple t = t.length ∧ firstindexTuple t = 1 ∧ lastindexTuple t = t.length ∧
    (∀ d : Index, sizeTuple showIndex t d =
      if d.value = 1 then .ok t.length else argErr s!"invalid tuple dimension {showIndex d}") ∧
    axesTuple t = [oneTo t.length] ∧ keysTuple t = oneTo t.length ∧
    (∀ i : Int, 1 ≤ i → i ≤ t.length →
      ∃ x, t[(i - 1).toNat]? = some x ∧ iterateTuple t i = some (x, i + 1) ∧ safeGetindex t i = some x) ∧
    (∀ i : Int, ¬ (1 ≤ i ∧ i ≤ t.length) → iterateTuple t i = none) ∧
    (∀ i : JInt .i64,
      previndTuple t (.integer .i64 i) = .ok (i - JInt.lit .i64 1) ∧
      nextindTuple t (.integer .i64 i) = .ok (i + JInt.lit .i64 1)) ∧
    safeTailEmpty t = [] ∧ emptyTuple t = []

theorem tupleBasicsCorrect : TupleBasicsCorrect := by
  intro α showIndex t
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · intro d
    simp [sizeTuple, lengthTuple]
  · intro i hi1 hi2
    have hk : (i - 1).toNat < t.length := by omega
    refine ⟨t[(i - 1).toNat], ?_, ?_, ?_⟩
    · simp [List.getElem?_eq_getElem hk]
    · simp [iterateTuple, hi1, hi2, List.getElem?_eq_getElem hk]
    · simp [safeGetindex, hi1, List.getElem?_eq_getElem hk]
  · intro i h
    simp [iterateTuple, h]
  · intro i
    constructor
    · change Except.map (fun j => j - JInt.lit .i64 1) (Except.ok i) =
        Except.ok (i - JInt.lit .i64 1)
      rfl
    · change Except.map (fun j => j + JInt.lit .i64 1) (Except.ok i) =
        Except.ok (i + JInt.lit .i64 1)
      rfl

def indexFromNat (i : Nat) : Index := .integer .i64 (JInt.lit .i64 (i : Int))

def truePositionsAux : List Bool → Nat → List Nat
  | [], _ => []
  | selected :: rest, offset =>
      if selected then (offset + 1) :: truePositionsAux rest (offset + 1)
      else truePositionsAux rest (offset + 1)

def truePositions (b : List Bool) : List Nat := truePositionsAux b 0

theorem truePositionsAux_valid (b : List Bool) (offset : Nat) :
    ∀ i, i ∈ truePositionsAux b offset → offset < i ∧ i ≤ offset + b.length := by
  induction b generalizing offset with
  | nil => simp [truePositionsAux]
  | cons selected rest ih =>
    cases selected
    · intro i hi
      simp only [truePositionsAux, List.length_cons, Bool.false_eq_true, ↓reduceIte] at hi ⊢
      have h := ih (offset + 1) i hi
      omega
    · intro i hi
      simp only [truePositionsAux, List.length_cons, ↓reduceIte, List.mem_cons] at hi ⊢
      rcases hi with h | h
      · cases h
        omega
      · have h' := ih (offset + 1) i h
        omega

theorem truePositions_valid (b : List Bool) :
    ∀ i, i ∈ truePositions b → 1 ≤ i ∧ i ≤ b.length := by
  intro i hi
  have h := truePositionsAux_valid b 0 i hi
  omega


theorem assertIntIndexFromNat (i : Nat) :
    assertInt (indexFromNat i) = .ok (JInt.lit .i64 (i : Int)).val := rfl

theorem getindexIntegerI64 {α : Type} (t : List α) (i : JInt .i64) :
    getindexInteger t (.integer .i64 i) = getfield t i.val := by
  rfl

theorem getindexOneBased {α : Type} (t : List α) (i : Nat)
    (hlen : t.length < 2 ^ 62) (hi : 1 ≤ i ∧ i ≤ t.length) :
    getindexInteger t (indexFromNat i) = .ok t[i - 1] := by
  have hval : (JInt.lit .i64 (Int.ofNat i)).val = Int.ofNat i := by
    apply litI64Value
    constructor
    · simp [IntTy.min, IntTy.signed, IntTy.bits]
    · have hiNat : i < 2 ^ 62 := by omega
      have hiInt : (Int.ofNat i) < ((2 ^ 62 : Nat) : Int) := Int.ofNat_lt.mpr hiNat
      have hmax : ((2 ^ 62 : Nat) : Int) ≤ IntTy.i64.max := by decide
      exact Int.le_trans (Int.le_of_lt hiInt) hmax
  have hk : i - 1 < t.length := by omega
  have hfield : getfield t (Int.ofNat i) = .ok t[i - 1] := by
    have h := getfieldInBounds t (i - 1) hk
    have hcast : ((i - 1 : Nat) : Int) + 1 = (i : Int) := by omega
    rw [hcast] at h
    exact h
  rw [show indexFromNat i = .integer .i64 (JInt.lit .i64 (Int.ofNat i)) by rfl,
    getindexIntegerI64, hval, hfield]

theorem getindexVectorOneBased {α : Type} (typing : TupleConversion α)
    (hconvert : ∀ E x, typing.convert E x = .ok x) (t : List α) (hlen : t.length < 2 ^ 62) :
    ∀ r : List Nat, (∀ i ∈ r, 1 ≤ i ∧ i ≤ t.length) →
      getindexVector noCustomIndex typing t ((r.map indexFromNat).map .integer) =
        .ok (r.filterMap fun i => t[i - 1]?) := by
  intro r hvalid
  induction r with
  | nil => rfl
  | cons i rest ih =>
      have hi := hvalid i (by simp)
      have hrest : ∀ j ∈ rest, 1 ≤ j ∧ j ≤ t.length := fun j hj => hvalid j (by simp [hj])
      have ih' := ih hrest
      unfold getindexVector at ih'
      simp only [getindexVector, List.map_cons, List.mapM_cons, getindexSubscript]
      rw [getindexOneBased t i hlen hi]
      simp only [Bind.bind, Except.bind, getindexSubscript, hconvert] at ih' ⊢
      rw [ih']
      have hElem : t[i - 1]? = some t[i - 1] := List.getElem?_eq_getElem (by omega)
      simp [hElem, List.filterMap_cons, Bind.bind, Except.bind, Pure.pure, Except.pure]

def TupleIndexVecCorrect : Prop :=
  ∀ (α : Type) (t : List α), t.length < 2 ^ 62 →
    ∀ (typing : TupleConversion α), (∀ E x, typing.convert E x = .ok x) →
    ∀ (findall : List Bool → List Index),
      (∀ b, findall b = (truePositions b).map indexFromNat) →
    (∀ r : List Nat, (∀ i ∈ r, 1 ≤ i ∧ i ≤ t.length) →
      getindexVector noCustomIndex typing t ((r.map indexFromNat).map .integer) =
        .ok (r.filterMap fun i => t[i - 1]?)) ∧
    (∀ b : List Bool, b.length = t.length →
      getindexBoolVector findall typing t b =
        .ok ((truePositions b).filterMap fun i => t[i - 1]?)) ∧
    (∀ b : List Bool, b.length ≠ t.length →
      getindexBoolVector findall typing t b = bounds) ∧
    getindexColon t = t ∧
    (∀ (f : Unit → R α) (i : Index),
      getThunk f t i = if 1 ≤ i.value ∧ i.value ≤ t.length then getindexInteger t i else f ())

theorem tupleIndexVecCorrect : TupleIndexVecCorrect := by
  intro α t hlen typing hconvert findall hfindall
  refine ⟨getindexVectorOneBased typing hconvert t hlen, ?_, ?_, rfl, ?_⟩
  · intro b hb
    have hvalid : ∀ i ∈ truePositions b, 1 ≤ i ∧ i ≤ t.length := by
      intro i hi
      have hvalid' := truePositions_valid b i hi
      exact ⟨hvalid'.1, by omega⟩
    unfold getindexBoolVector
    rw [if_pos hb, hfindall]
    exact getindexVectorOneBased typing hconvert t hlen (truePositions b) hvalid
  · intro b hb
    simp [getindexBoolVector, hb]
  · intro f i
    rfl

inductive IndexReadTrace {α ι : Type} (custom : List α → ι → R α) (t : List α) :
    List (TupleSubscript ι) → List α → Prop where
  | nil : IndexReadTrace custom t [] []
  | cons {i value indices values} :
      getindexSubscript custom t i = .ok value →
      IndexReadTrace custom t indices values →
      IndexReadTrace custom t (i :: indices) (value :: values)

def GenericVectorIndexingCorrect : Prop :=
  ∀ (α ι : Type) (custom : List α → ι → R α) (typing : TupleConversion α)
    (t : List α) (indices : List (TupleSubscript ι)) (values : List α),
    IndexReadTrace custom t indices values →
    getindexVector custom typing t indices =
      values.mapM (typing.convert (tupleEltype typing.eltypes (typing.typeof t)))

theorem genericVectorIndexingCorrect : GenericVectorIndexingCorrect := by
  intro α ι custom typing t indices values h
  induction h with
  | nil => rfl
  | cons hi _ ih =>
    simp only [getindexVector, List.mapM_cons] at ih ⊢
    rw [hi]
    simp only [Bind.bind, Except.bind] at ih ⊢
    cases hc : typing.convert (tupleEltype typing.eltypes (typing.typeof t)) _ with
    | error e => rfl
    | ok value =>
      simp only [hc, Except.bind]
      rw [ih]

def FullTupleIndexVecCorrect : Prop := TupleIndexVecCorrect ∧ GenericVectorIndexingCorrect

theorem fullTupleIndexVecCorrect : FullTupleIndexVecCorrect :=
  ⟨tupleIndexVecCorrect, genericVectorIndexingCorrect⟩

def TupleIterProtocolCorrect : Prop :=
  ∀ (α σ : Type) (mismatch : String → List (List Nat) → KeysResult),
    (∀ message indices, mismatch message indices = .error .dimensionMismatch) →
    (∀ (t : List α) (others : List (List α)),
      (∀ other ∈ others, other.length = t.length) → keysMany mismatch t others = .ok (oneTo t.length)) ∧
    (∀ (t : List α) (i : Int), 1 ≤ i → i ≤ t.length →
      ∃ value, t[(i - 1).toNat]? = some value ∧
        indexedIterateTuple t i = .ok (value, i + 1)) ∧
    (∀ (itr : Iter α σ) i,
      indexedIterateGeneric itr i = match itr.first with
        | .ok none => bounds
        | .ok (some value) => .ok value
        | .error e => .error e) ∧
    (∀ (itr : Iter α σ) i state,
      indexedIterateGenericState itr i state = match itr.next state with
        | .ok none => bounds
        | .ok (some value) => .ok value
        | .error e => .error e) ∧
    (∀ (t : List α) others, (∃ other ∈ others, other.length ≠ t.length) →
      keysMany mismatch t others = .error .dimensionMismatch)

theorem tupleIterProtocolCorrect : TupleIterProtocolCorrect := by
  intro α σ mismatch hthrows
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t others h
    have hall : others.all (fun other => lengthTuple other = lengthTuple t) = true := by
      apply List.all_eq_true.mpr
      intro other hm
      exact decide_eq_true (h other hm)
    simp only [keysMany]
    rw [hall]
    rfl
  · intro t i hi1 hi2
    have hk : (i - 1).toNat < t.length := by omega
    have hfield : getfield t i = .ok t[(i - 1).toNat] := by
      have h := getfieldInBounds t (i - 1).toNat hk
      have hcast : ((i - 1).toNat : Int) + 1 = i := by omega
      rw [hcast] at h
      exact h
    refine ⟨t[(i - 1).toNat], ?_, ?_⟩
    · simp [List.getElem?_eq_getElem hk]
    · simp [indexedIterateTuple, hfield]
  · intro itr i
    cases h : itr.first with
    | error e => simp [indexedIterateGeneric, iterAt, h]
    | ok value =>
      cases value with
      | none => simp [indexedIterateGeneric, iterAt, h]
      | some pair => simp [indexedIterateGeneric, iterAt, h]
  · intro itr i state
    cases h : itr.next state with
    | error e => simp [indexedIterateGenericState, h]
    | ok value =>
      cases value with
      | none => simp [indexedIterateGenericState, h]
      | some pair => simp [indexedIterateGenericState, h]
  · intro t others hm
    obtain ⟨other, hmem, hne⟩ := hm
    have hall : others.all (fun other => lengthTuple other = lengthTuple t) = false := by
      apply Bool.eq_false_iff.mpr
      intro hall
      have he : other.length = t.length := by
        exact of_decide_eq_true (List.all_eq_true.mp hall other hmem)
      exact hne he
    simp only [keysMany]
    rw [hall]
    exact hthrows _ _

def ntupleSpec {α : Type} (f : Nat → R α) (n : Int) : R (List α) :=
  if n < 0 then argErr "tuple length should be ≥ 0"
  else (List.range n.toNat).mapM fun i => f (i + 1)



def RestCorrect : Prop :=
  ∀ (α σ : Type) (t : List α)
    (ntuple : (Nat → R α) → Int → R (List α)),
    (∀ f n, 0 ≤ n → ntuple f n = (List.range n.toNat).mapM fun i => f (i + 1)) →
    restTupleAll t = t ∧
    (∀ i : Nat, 1 ≤ i → i ≤ t.length + 1 → i < 2 ^ 62 → t.length < 2 ^ 62 →
      restTupleFrom ntuple t (indexFromNat i) = .ok (t.drop (i - 1))) ∧
    (∀ i : Nat, 1 ≤ i → i ≤ t.length + 1 → i < 2 ^ 62 → t.length < 2 ^ 62 →
      restArray sliceList t (indexFromNat i) = .ok (t.drop (i - 1))) ∧
    (∀ (States : Type) (itr : Iter α σ) (rest : Iter α σ → States → Iter α σ) state,
      restGeneric rest itr state = rest itr state)

theorem restTupleBodyCorrect {α : Type} (t : List α)
    (ntuple : (Nat → R α) → Int → R (List α))
    (hntuple : ∀ f n, 0 ≤ n → ntuple f n = (List.range n.toNat).mapM fun i => f (i + 1))
    (i : Nat) (hi1 : 1 ≤ i) (hi2 : i ≤ t.length + 1) :
    ntuple (fun x => getfield t ((x : Int) + (i : Int) - 1))
      ((t.length : Int) - (i : Int) + 1) = .ok (t.drop (i - 1)) := by
  have hcount : (t.length : Int) - i + 1 =
      ((t.length + 1 - i : Nat) : Int) := by
    by_cases hle : i ≤ t.length
    · have hsub : (t.length : Int) - i = ((t.length - i : Nat) : Int) :=
        (Int.ofNat_sub hle).symm
      rw [hsub]
      omega
    · have hieq : i = t.length + 1 := by omega
      subst i
      simp only [Int.natCast_add, Int.natCast_one]
      omega
  have hdropLen : (t.drop (i - 1)).length = t.length + 1 - i := by
    simp [List.length_drop]
    omega
  rw [hcount]
  have hNnonneg : 0 ≤ ((t.length + 1 - i : Nat) : Int) := Int.ofNat_nonneg _
  rw [hntuple _ _ hNnonneg]
  apply mapM_range_ok _ _ _ hdropLen
  intro k hk
  have hklt : k < t.length + 1 - i := by rw [← hdropLen]; exact hk
  change getfield t (((k + 1 : Nat) : Int) + (i : Int) - 1) =
    .ok (t.drop (i - 1))[k]
  have hindex : ((k + 1 : Nat) : Int) + (i : Int) - 1 = ((i + k : Nat) : Int) := by
    simp only [Int.natCast_add, Int.natCast_one]
    omega
  rw [hindex, List.getElem_drop]
  have hfield := getfieldInBounds t (i - 1 + k) (by omega)
  have hcast : ((i - 1 + k : Nat) : Int) + 1 = ((i + k : Nat) : Int) := by omega
  rw [hcast] at hfield
  exact hfield

theorem restArrayBodyCorrect {α : Type} (t : List α) (i : Nat)
    (hi1 : 1 ≤ i) (hi2 : i ≤ t.length + 1) :
    sliceList t (i : Int) (t.length : Int) = .ok (t.drop (i - 1)) := by
  by_cases hle : i ≤ t.length
  · have hdropLen : (t.drop (i - 1)).length = t.length - (i - 1) := by simp
    have htake : (t.drop (i - 1)).take (t.length - i + 1) = t.drop (i - 1) := by
      apply List.take_of_length_le
      rw [hdropLen]
      omega
    have hpos : (1 : Int) ≤ (i : Int) := by omega
    have hleInt : (i : Int) ≤ (t.length : Int) := by omega
    have hstart : ((i : Int) - 1).toNat = i - 1 := by omega
    have hspan : ((t.length : Int) - i + 1).toNat =
        t.length - i + 1 := by
      have hsub : (t.length : Int) - i = ((t.length - i : Nat) : Int) :=
        (Int.ofNat_sub hle).symm
      rw [hsub]
      have hsum : ((t.length - i : Nat) : Int) + 1 =
          ((t.length - i + 1 : Nat) : Int) := by
        simpa only [Int.natCast_one] using (Int.natCast_add (t.length - i) 1).symm
      rw [hsum]
      exact Int.toNat_natCast _
    unfold sliceList
    rw [if_neg (show ¬ ((t.length : Int) < (i : Int)) by omega),
      if_pos (show (1 : Int) ≤ (i : Int) ∧ (t.length : Int) ≤ t.length by omega),
      hstart, hspan, htake]
  · have hieq : i = t.length + 1 := by omega
    subst i
    have hlast : (t.length : Int) < ((t.length + 1 : Nat) : Int) := by omega
    simp only [sliceList, hlast, ↓reduceIte, Nat.add_sub_cancel, List.drop_length]

theorem restTupleFromInt {α : Type} (ntuple : (Nat → R α) → Int → R (List α))
    (t : List α) (i : JInt .i64) :
    restTupleFrom ntuple t (.integer .i64 i) =
      ntuple (fun x => getfield t ((x : Int) + i.val - 1))
        ((t.length : Int) - i.val + 1) := rfl

theorem restArrayInt {α : Type} (t : List α) (i : JInt .i64) :
    restArray sliceList t (.integer .i64 i) =
      sliceList t i.val (t.length : Int) := rfl

theorem restCorrect : RestCorrect := by
  intro α σ t ntuple hntuple
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i hi1 hi2 hiFit hlen
    rw [indexFromNat, restTupleFromInt, i64NatValue i hiFit]
    exact restTupleBodyCorrect t ntuple hntuple i hi1 hi2
  · intro i hi1 hi2 hiFit hlen
    rw [indexFromNat, restArrayInt, i64NatValue i hiFit]
    exact restArrayBodyCorrect t i hi1 hi2
  · intro States itr rest state
    rfl

theorem slicePrefix {α : Type} (a : List α) (cut : Nat) (hc : cut ≤ a.length) :
    sliceList a 1 (cut : Int) = .ok (a.take cut) := by
  by_cases hz : cut = 0
  · subst cut
    simp [sliceList]
  · unfold sliceList
    rw [if_neg (by omega), if_pos (by omega)]
    simp

theorem sliceSuffix {α : Type} (a : List α) (cut : Nat) (hc : cut ≤ a.length) :
    sliceList a ((cut : Int) + 1) a.length = .ok (a.drop cut) := by
  by_cases he : cut = a.length
  · subst cut
    simp [sliceList, show (a.length : Int) < (a.length : Int) + 1 by omega]
  · unfold sliceList
    rw [if_neg (by omega), if_pos (by omega)]
    have hstart : ((cut : Int) + 1 - 1).toNat = cut := by omega
    have hcount : ((a.length : Int) - ((cut : Int) + 1) + 1).toNat =
        a.length - cut := by omega
    rw [hstart, hcount, List.take_of_length_le (by simp)]

theorem splitArrayPartition {α : Type} (a : List α) (n : Nat) (hn : n ≤ a.length) :
    splitRestArray sliceList a (n : Int) =
      .ok (a.take (a.length - n), a.drop (a.length - n)) := by
  have hc : a.length - n ≤ a.length := by omega
  have hcast : (a.length : Int) - (n : Int) = ((a.length - n : Nat) : Int) := by omega
  unfold splitRestArray
  rw [show checkLengthSplitRest a.length (n : Int) = .ok () by
    unfold checkLengthSplitRest
    rw [if_neg (show ¬ ((a.length : Int) < (n : Int)) by omega)]]
  simp only [Bind.bind, Except.bind]
  rw [hcast, slicePrefix a _ hc, sliceSuffix a _ hc]
  rfl

theorem splitArrayShort {α : Type} (a : List α) (n : Nat) (hn : a.length < n) :
    ∃ message, splitRestArray sliceList a (n : Int) = argErr message := by
  refine ⟨s!"The iterator only contains {a.length} elements, but at least {(n : Int)} were requested.", ?_⟩
  unfold splitRestArray checkLengthSplitRest
  rw [if_pos (by omega)]
  rfl

def SplitRestCorrect : Prop :=
  (∀ (α : Type) (a : List α) (n : Nat), n ≤ a.length →
    splitRestArray sliceList a (n : Int) =
      .ok (a.take (a.length - n), a.drop (a.length - n))) ∧
  (∀ (α : Type) (a : List α) (n : Nat), a.length < n →
    ∃ message, splitRestArray sliceList a (n : Int) = argErr message) ∧
  (∀ (α σ States : Type) (infinite : Iter α σ → Bool)
    (rest : Iter α σ → States → Iter α σ) (collect : Iter α σ → List α)
    (itr : Iter α σ) (state : States) (n : Nat),
    (infinite itr = true →
      splitRestGeneric infinite rest collect sliceList itr (n : Int) state =
        argErr "Cannot split an infinite iterator in the middle.") ∧
    (infinite itr = false → n ≤ (collect (rest itr state)).length →
      splitRestGeneric infinite rest collect sliceList itr (n : Int) state = .ok
        ((collect (rest itr state)).take ((collect (rest itr state)).length - n),
         (collect (rest itr state)).drop ((collect (rest itr state)).length - n)))) ∧
  (∀ (α σ : Type) (collect : Iter α σ → List α) (itr : Iter α σ) (n : Nat),
    n ≤ (collect itr).length →
      splitRestCollected collect sliceList itr (n : Int) =
        .ok ((collect itr).take ((collect itr).length - n),
             (collect itr).drop ((collect itr).length - n))) ∧
  (∀ (α σ States : Type) (infinite : Iter α σ → Bool)
    (rest : Iter α σ → States → Iter α σ) (collect : Iter α σ → List α)
    (itr : Iter α σ) (state : States) (n : Nat),
    infinite itr = false → (collect (rest itr state)).length < n →
      ∃ message, splitRestGeneric infinite rest collect sliceList itr (n : Int) state =
        argErr message) ∧
  (∀ (α σ : Type) (collect : Iter α σ → List α) (itr : Iter α σ) (n : Nat),
    (collect itr).length < n →
      ∃ message, splitRestCollected collect sliceList itr (n : Int) = argErr message)

theorem splitRestCorrect : SplitRestCorrect := by
  refine ⟨(fun _ a n hn => splitArrayPartition a n hn), ?_, ?_, ?_, ?_, ?_⟩
  · intro α a n hn
    exact splitArrayShort a n hn
  · intro α σ States infinite rest collect itr state n
    constructor
    · intro hi
      simp [splitRestGeneric, hi]
    · intro hi hn
      simpa [splitRestGeneric, hi, restGeneric, splitRestCollected] using
        splitArrayPartition (collect (rest itr state)) n hn
  · intro α σ collect itr n hn
    exact splitArrayPartition (collect itr) n hn
  · intro α σ States infinite rest collect itr state n hi hn
    simpa [splitRestGeneric, hi, restGeneric, splitRestCollected] using
      splitArrayShort (collect (rest itr state)) n hn
  · intro α σ collect itr n hn
    exact splitArrayShort (collect itr) n hn

def zipColumns {α : Type} : List (List α) → Nat → List (List α)
  | _, 0 => []
  | ts, k + 1 =>
    match ts.mapM List.head? with
    | some h => if ts.isEmpty then [] else h :: zipColumns (ts.map List.tail) k
    | none => []

theorem mapOneRecEq {α β : Type} (f : α → β) (fuel : Nat) :
    ∀ t : List α, t.length ≤ fuel → mapOneRec f fuel t = t.map f := by
  induction fuel with
  | zero =>
    intro t ht
    have hnil : t = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst t
    simp [mapOneRec, mapOneEmpty]
  | succ fuel ih =>
    intro t ht
    cases t with
    | nil => simp [mapOneRec, mapOneGeneric]
    | cons a t =>
      simp only [mapOneRec, mapOneGeneric, List.map_cons]
      rw [ih t (by simpa using Nat.le_of_succ_le_succ ht)]

theorem mapOneLoopShift {α β : Type} (f : α → β) (a : α) (t : List α) :
    ∀ i k, mapOneLoop f (a :: t) (i + 1) k = mapOneLoop f t i k := by
  intro i k
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [mapOneLoop, ih]

theorem mapOneLoopFull {α β : Type} (f : α → β) (t : List α) :
    mapOneLoop f t 0 t.length = t.map f := by
  induction t with
  | nil => rfl
  | cons a t ih =>
      change mapOneLoop f (a :: t) 0 (t.length + 1) = f a :: t.map f
      simp only [mapOneLoop, List.getElem?_cons_zero]
      rw [mapOneLoopShift f a t 0 t.length]
      exact congrArg (fun xs => f a :: xs) ih
theorem mappedEffects {α β : Type} (f : α → R β) (xs : List α) :
    (mapOneRec f xs.length xs).mapM id = xs.mapM f := by
  rw [mapOneRecEq f _ _ (by omega), List.mapM_map]
  rfl

theorem mapTupleModel {α β : Type} (f : α → R β) (xs : List α) :
    mapTuple f xs = xs.mapM f := by
  unfold mapTuple
  split
  · rw [show mapOneLong f xs = xs.map f by exact mapOneLoopFull f xs, List.mapM_map]
    rfl
  · have generic : ∀ ys : List α,
        (mapOneGeneric f ys.length ys).mapM id = ys.mapM f := by
      intro ys
      have hm := mapOneRecEq f (ys.length + 1) ys (by omega)
      simp only [mapOneRec] at hm
      rw [hm, List.mapM_map]
      rfl
    cases xs with
    | nil => rfl
    | cons a xs =>
      cases xs with
      | nil => rfl
      | cons b xs =>
        cases xs with
        | nil => rfl
        | cons c xs =>
          cases xs with
          | nil => rfl
          | cons d xs => exact generic (a :: b :: c :: d :: xs)

theorem headsModel {α : Type} (ts : List (List α)) :
    heads ts = ts.mapM (fun t => getfield t 1) := by
  unfold heads
  rw [mapTupleModel]
  rfl

theorem tailsModel {α : Type} (tail : List α → R (List α)) (ts : List (List α)) :
    tails tail ts = ts.mapM tail := mapTupleModel tail ts

theorem anyempty_iff {α : Type} : ∀ ts : List (List α),
    anyemptyTuple ts.length ts = true ↔ ∃ t ∈ ts, t = []
  | [] => by simp [anyemptyTuple, anyemptyNone]
  | [] :: _ => by simp [anyemptyTuple, anyemptyEmptyTuple]
  | (a :: r) :: ts => by
    simpa only [anyemptyTuple, anyemptyNonempty, List.length_cons] using
      (show anyemptyTuple ts.length ts = true ↔ ∃ t ∈ (a :: r) :: ts, t = [] from by
        rw [anyempty_iff ts]
        simp)

theorem heads_ok {α : Type} : ∀ ts : List (List α), (∀ t ∈ ts, t ≠ []) →
    ∃ hs, ts.mapM List.head? = some hs ∧ heads ts = .ok hs
  | [], _ => ⟨[], rfl, by rw [headsModel]; rfl⟩
  | t :: ts, h => by
    obtain ⟨hs, h1, h2⟩ := heads_ok ts (fun u hu => h u (by simp [hu]))
    cases t with
    | nil => exact absurd rfl (h [] (by simp))
    | cons a r =>
      refine ⟨a :: hs, ?_, ?_⟩
      · simp [List.mapM_cons, h1]
      · rw [headsModel] at h2 ⊢
        simp only [List.mapM_cons]
        rw [h2]
        rfl

theorem heads_none {α : Type} : ∀ ts : List (List α),
    (∃ t ∈ ts, t = []) → ts.mapM List.head? = none
  | [], h => by simp at h
  | [] :: _, _ => by simp [List.mapM_cons]
  | (a :: r) :: ts, h => by
    have h' : ∃ t ∈ ts, t = [] := by
      obtain ⟨u, hu, rfl⟩ := h
      rcases List.mem_cons.1 hu with h | h
      · cases h
      · exact ⟨[], h, rfl⟩
    rw [List.mapM_cons, heads_none ts h']
    rfl

theorem tails_ok {α : Type} (tail : List α → R (List α))
    (htail : ∀ x xs, tail (x :: xs) = .ok xs) :
    ∀ ts : List (List α), (∀ t ∈ ts, t ≠ []) →
      tails tail ts = .ok (ts.map List.tail)
  | [], _ => by rw [tailsModel]; rfl
  | t :: ts, h => by
    cases t with
    | nil => exact absurd rfl (h [] (by simp))
    | cons a r =>
      rw [tailsModel]
      simp only [List.mapM_cons]
      rw [htail, show ts.mapM tail = .ok (ts.map List.tail) from by
        rw [← tailsModel]
        exact tails_ok tail htail ts (fun u hu => h u (by simp [hu]))]
      rfl

theorem mapManyRecEq {α β : Type} (tail : List α → R (List α))
    (htail : ∀ x xs, tail (x :: xs) = .ok xs) (f : List α → β) :
    ∀ (fuel : Nat) (ts : List (List α)), ts ≠ [] →
      mapManyRec tail f fuel ts = .ok ((zipColumns ts fuel).map f)
  | 0, _, _ => by simp [mapManyRec, mapManyEmpty, zipColumns]
  | fuel + 1, ts, hne => by
    by_cases he : anyemptyTuple ts.length ts = true
    · have hn := heads_none ts ((anyempty_iff ts).1 he)
      simp only [mapManyRec, mapManyLoop, he, ↓reduceIte, zipColumns, hn]
      rfl
    · have hall : ∀ t ∈ ts, t ≠ [] := by
        intro t ht heq
        exact he ((anyempty_iff ts).2 ⟨t, ht, heq⟩)
      obtain ⟨hs, h1, h2⟩ := heads_ok ts hall
      have hne' : ts.map List.tail ≠ [] := by simpa using hne
      have hie : ts.isEmpty = false := by cases ts <;> simp_all
      simp only [mapManyRec, mapManyLoop, he, ↓reduceIte, h2, tails_ok tail htail ts hall,
        Bind.bind, Except.bind, mapManyRecEq tail htail f fuel _ hne', zipColumns, h1, hie]
      rfl

theorem foreachDiscard {α β : Type} (action : α → R β) (values : List α) :
    values.foldlM (fun _ x => do let _ ← action x; pure ()) () =
      (fun _ => ()) <$> values.mapM action := by
  induction values with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldlM_cons, List.mapM_cons]
    cases h : action x with
    | error e => rfl
    | ok value =>
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at ih ⊢
      rw [ih]
      cases xs.mapM action <;> rfl

theorem mapManySourceEq {α β : Type} (tail : List α → R (List α))
    (f : List α → β) (first second : List α) (others : List (List α)) :
    mapMany tail f first second others =
      mapManyRec tail f (first.length + 1) (first :: second :: others) := by
  simp only [mapMany, mapManyRec, mapManyLoop]

def SourceMapNCorrect : Prop :=
  ∀ (α β : Type) (tail : List α → R (List α)) (f : List α → β),
    (∀ x xs, tail (x :: xs) = .ok xs) →
    (∀ ts : List (List α), mapManyEmpty f ts = []) ∧
    (∀ first second others,
      mapMany tail f first second others =
        .ok ((zipColumns (first :: second :: others) (first.length + 1)).map f))

theorem sourceMapNCorrect : SourceMapNCorrect := by
  intro α β tail f htail
  refine ⟨fun _ => rfl, ?_⟩
  intro first second others
  rw [mapManySourceEq]
  exact mapManyRecEq tail htail f _ _ (by simp)

def MapNForeachCorrect : Prop :=
  ∀ (α β σ : Type) (f : List α → β) (tail : List α → R (List α)),
    (∀ x xs, tail (x :: xs) = .ok xs) →
    (∀ (ts : List (List α)) (fuel : Nat), ts.length ≥ 3 →
      (∀ t ∈ ts, t.length ≤ fuel) →
      mapManyRec tail f fuel ts = .ok ((zipColumns ts fuel).map f)) ∧
    (∀ ts : List (List α), anyemptyTuple ts.length ts = true ↔ ∃ t ∈ ts, t = []) ∧
    (∀ (action : α → R σ) (values : List α),
      foreachTuple action values = (fun _ => ()) <$> values.mapM action) ∧
    (∀ (action : List α → R σ) (values : List α) (others : List (List α)),
      foreachTupleN action values others = (fun _ => ()) <$>
        ((List.range ((values :: others).map List.length |>.foldl min values.length)).map
          (fun i => (values :: others).filterMap fun xs => xs[i]?)).mapM action)

theorem mapNForeachCorrect : MapNForeachCorrect := by
  intro α β σ f tail htail
  refine ⟨?_, anyempty_iff, ?_, ?_⟩
  · intro ts fuel h3 hbound
    exact mapManyRecEq tail htail f fuel ts (by intro h; simp [h] at h3)
  · intro action values
    exact foreachDiscard action values
  · intro action values others
    exact foreachDiscard action _

theorem foldlMinLe : ∀ (l : List Nat) (initial : Nat),
    l.foldl min initial ≤ initial ∧ ∀ x ∈ l, l.foldl min initial ≤ x
  | [], initial => by simp
  | x :: l, initial => by
    have h := foldlMinLe l (min initial x)
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨by omega, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · omega
    · exact h.2 y hy

theorem foldlMinMem : ∀ (l : List Nat) (initial : Nat),
    l.foldl min initial = initial ∨ l.foldl min initial ∈ l
  | [], initial => by simp
  | x :: l, initial => by
    rcases foldlMinMem l (min initial x) with h | h
    · simp only [List.foldl_cons, h]
      by_cases hx : initial ≤ x
      · left; omega
      · right; simp; omega
    · right; simp [h]

theorem getindexIntPosition {α : Type} (t : List α) (i : Nat)
    (hi : i < t.length) (hlen : t.length < 2 ^ 62) :
    getindexInt t (JInt.lit .i64 ((i : Int) + 1)) = .ok t[i] := by
  have hv : (JInt.lit .i64 ((i : Int) + 1)).val = (i : Int) + 1 :=
    litI64Value _ (by have := i64Bounds; have := i64NatFits t.length hlen; omega)
  simpa only [getindexInt, hv] using getfieldInBounds t i hi

theorem indexedColumns {α : Type} (ts : List (List α)) (i : Nat)
    (h : ∀ t ∈ ts, i < t.length ∧ t.length < 2 ^ 62) :
    (mapOneRec (fun t => getindexInt t (JInt.lit .i64 ((i : Int) + 1)))
      ts.length ts).mapM id = .ok (ts.filterMap fun t => t[i]?) := by
  rw [mappedEffects]
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have ht := h t (by simp)
    have hs : ∀ t ∈ ts, i < t.length ∧ t.length < 2 ^ 62 :=
      fun t hm => h t (by simp [hm])
    simp only [List.mapM_cons, getindexIntPosition t i ht.1 ht.2, ih hs,
      List.filterMap_cons, List.getElem?_eq_getElem ht.1]
    rfl

theorem mapManyLongLoopEq {α β : Type} (f : List α → β) (first second : List α)
    (others : List (List α)) (i count : Nat)
    (h : ∀ t ∈ first :: second :: others, i + count ≤ t.length ∧ t.length < 2 ^ 62) :
    mapManyLongLoop f first second others i count =
      .ok ((List.range' i count).map fun j =>
        f ((first :: second :: others).filterMap fun t => t[j]?)) := by
  induction count generalizing i with
  | zero => rfl
  | succ count ih =>
    have hfirst := h first (by simp)
    have hsecond := h second (by simp)
    have hothers : ∀ t ∈ others, i < t.length ∧ t.length < 2 ^ 62 := by
      intro t ht
      have := h t (by simp [ht])
      exact ⟨by omega, this.2⟩
    have hrest : ∀ t ∈ first :: second :: others,
        i + 1 + count ≤ t.length ∧ t.length < 2 ^ 62 := by
      intro t ht
      have := h t ht
      exact ⟨by omega, this.2⟩
    simp only [mapManyLongLoop, getindexIntPosition first i (by omega) hfirst.2,
      getindexIntPosition second i (by omega) hsecond.2, indexedColumns others i hothers,
      ih (i + 1) hrest, List.range'_succ, List.map_cons,
      List.filterMap_cons, List.getElem?_eq_getElem (show i < first.length by omega),
      List.getElem?_eq_getElem (show i < second.length by omega)]
    rfl

def MapManyLongCorrect : Prop :=
  ∀ (α β : Type) (minimum : (List α → Nat) → List (List α) → Nat),
    (∀ xs : List (List α), xs ≠ [] →
      (∀ t ∈ xs, minimum lengthTuple xs ≤ t.length) ∧
      (∃ t ∈ xs, t.length = minimum lengthTuple xs)) →
    ∀ (f : List α → β) (first second : List α) (others : List (List α)),
      others ≠ [] → (∀ t ∈ first :: second :: others, t.length < 2 ^ 62) →
      ∀ h32 : ∀ t ∈ first :: second :: others, 32 ≤ t.length,
      let n := min first.length (min second.length (minimum lengthTuple others))
      mapManyLong minimum f first second others h32 =
        .ok ((List.range' 0 n).map fun j =>
          f ((first :: second :: others).filterMap fun t => t[j]?)) ∧
      (∀ t ∈ first :: second :: others, n ≤ t.length) ∧
      (∃ t ∈ first :: second :: others, t.length = n)

theorem mapManyLongCorrect : MapManyLongCorrect := by
  intro α β minimum hmin f first second others hne hlen h32
  have hm := hmin others hne
  let n := min first.length (min second.length (minimum lengthTuple others))
  have hbound : ∀ t ∈ first :: second :: others, n ≤ t.length := by
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | ht
    · exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
    · exact Nat.le_trans (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)) (hm.1 t ht)
  refine ⟨?_, hbound, ?_⟩
  · exact mapManyLongLoopEq f first second others 0 n
      (fun t ht => ⟨by simpa using hbound t ht, hlen t ht⟩)
  · by_cases hfirst : first.length ≤ min second.length (minimum lengthTuple others)
    · exact ⟨first, by simp, (Nat.min_eq_left hfirst).symm⟩
    · have hout : min second.length (minimum lengthTuple others) ≤ first.length := by omega
      by_cases hsecond : second.length ≤ minimum lengthTuple others
      · exact ⟨second, by simp, by rw [Nat.min_eq_right hout, Nat.min_eq_left hsecond]⟩
      · obtain ⟨t, ht, hlen⟩ := hm.2
        refine ⟨t, by simp [ht], ?_⟩
        rw [Nat.min_eq_right hout, Nat.min_eq_right (show minimum lengthTuple others ≤ second.length by omega)]
        exact hlen

def HeadsTailsCorrect : Prop :=
  ∀ (α : Type) (tail : List α → R (List α)),
    (∀ x xs, tail (x :: xs) = .ok xs) →
    ∀ ts : List (List α), (∀ t ∈ ts, t ≠ []) →
      (∃ values, heads ts = .ok values ∧ values = ts.filterMap List.head?) ∧
      tails tail ts = .ok (ts.map List.tail)

theorem headsTailsCorrect : HeadsTailsCorrect := by
  intro α tail htail ts hne
  obtain ⟨hs, hheads, hmodel⟩ := heads_ok ts hne
  refine ⟨⟨hs, hmodel, ?_⟩, tails_ok tail htail ts hne⟩
  have flatten : ∀ xs : List (List α), ∀ ys,
      xs.mapM List.head? = some ys → ys = xs.filterMap List.head? := by
    intro xs
    induction xs with
    | nil =>
      intro ys hy
      simpa using (Option.some.inj hy).symm
    | cons t xs ih =>
      intro ys hy
      cases t with
      | nil => simp [List.mapM_cons] at hy
      | cons x t =>
        cases hr : xs.mapM List.head? with
        | none => simp [List.mapM_cons, hr] at hy
        | some rest =>
          have he : x :: rest = ys := by simpa [List.mapM_cons, hr] using hy
          subst ys
          simp [ih rest hr]
  exact flatten ts hs hheads

def ArrayIndexedIterationCorrect : Prop :=
  ∀ (α A : Type) (getindex : A → Int → R α) (a : A) (i state : Int),
    (∀ value, getindex a i = .ok value →
      indexedIterateArray getindex a i state = .ok (value, i + 1)) ∧
    (∀ error, getindex a i = .error error →
      indexedIterateArray getindex a i state = .error error)

theorem arrayIndexedIterationCorrect : ArrayIndexedIterationCorrect := by
  intro α A getindex a i state
  constructor
  · intro value h
    simp [indexedIterateArray, h]
  · intro error h
    simp only [indexedIterateArray, h]
    rfl

def FullTupleIterProtocolCorrect : Prop := TupleIterProtocolCorrect ∧ ArrayIndexedIterationCorrect

theorem fullTupleIterProtocolCorrect : FullTupleIterProtocolCorrect :=
  ⟨tupleIterProtocolCorrect, arrayIndexedIterationCorrect⟩

def AllMapNCorrect : Prop := MapNForeachCorrect ∧ MapManyLongCorrect ∧ HeadsTailsCorrect ∧ SourceMapNCorrect

theorem allMapNCorrect : AllMapNCorrect :=
  ⟨mapNForeachCorrect, mapManyLongCorrect, headsTailsCorrect, sourceMapNCorrect⟩

def SymInCorrect : Prop :=
  ∀ (x : String) (itr : List String), symIn x itr = decide (x ∈ itr) ∧ inSym x itr = decide (x ∈ itr)

theorem symInCorrect : SymInCorrect := by
  intro x itr
  have hLoop : ∀ xs : List String, symIn.loop x xs = decide (x ∈ xs) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons y rest ih =>
      simp only [symIn.loop, List.mem_cons]
      by_cases hy : y = x
      · subst y
        simp
      · simp [hy, Ne.symm hy, ih]
  have h : symIn x itr = decide (x ∈ itr) := by
    simpa [symIn] using hLoop itr
  exact ⟨h, by simpa [inSym] using h⟩

def Padded {α : Type} (input : List α) (value : α) (size : Nat) (result : List α) : Prop :=
  result.length = size ∧ result.take input.length = input ∧
    ∀ i, input.length ≤ i → i < size → result[i]? = some value

def FillToLengthSpecialized : Prop :=
  (∀ (α : Type) (t : List α) (v : α) (N : Nat) (h : t.length = N),
    Padded t v N (fillToLengthSame t v N h)) ∧
  (∀ (α : Type) (v : α), Padded [] v 1 (fillToLengthEmptyOne v)) ∧
  (∀ (α : Type) (t : List α) (v : α) (h : t.length = 1),
    Padded t v 2 (fillToLengthOneTwo t v h)) ∧
  (∀ (α : Type) (v : α), Padded [] v 2 (fillToLengthEmptyTwo v))

theorem fillToLengthSpecialized : FillToLengthSpecialized := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α t v N h
    refine ⟨h, by simp [fillToLengthSame], ?_⟩
    intro i hi hl
    omega
  · intro α v
    simp only [Padded, fillToLengthEmptyOne, List.length_singleton, List.length_nil,
      List.take_zero, and_self, true_and]
    intro i hi hl
    have : i = 0 := by omega
    subst i
    rfl
  · intro α t v h
    cases t with
    | nil => simp at h
    | cons a rest =>
      have hr : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst rest
      refine ⟨by simp [fillToLengthOneTwo], by rfl, ?_⟩
      intro i hi hl
      have : i = 1 := by simpa using Nat.le_antisymm (by omega) (by simpa using hi)
      subst i
      rfl
  · intro α v
    refine ⟨rfl, rfl, ?_⟩
    intro i hi hl
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> rfl

/-! ## Reverse and front/tail -/

def ReverseCorrect : Prop := ∀ (α : Type) (t : List α), reverseTuple t = t.reverse

theorem reverseCorrect : ReverseCorrect := by
  intro α t
  induction t with
  | nil => rfl
  | cons x xs ih =>
      simp only [reverseTuple, revargs, List.reverse_cons]
      change revargs xs ++ [x] = xs.reverse ++ [x]
      have ih' : revargs xs = xs.reverse := by simpa [reverseTuple] using ih
      rw [ih']

theorem frontArgs_correct {α : Type} (t : List α) :
    frontArgs t =
      if t = [] then argErr "Cannot call front on an empty tuple." else .ok t.dropLast := by
  induction t with
  | nil => rw [frontArgs]; rfl
  | cons x xs ih =>
    cases xs with
    | nil => rw [frontArgs]; rfl
    | cons y ys =>
      have hrec : frontArgs (y :: ys) = .ok (y :: ys).dropLast := by simpa using ih
      simp [frontArgs, frontMany, hrec]

def FrontTailCorrect : Prop :=
  ∀ (α : Type) (t : List α),
    SameOutcome (frontTuple t)
      (if t = [] then argErr "Cannot call front on an empty tuple." else .ok t.dropLast) ∧
    (∀ h32 : t.length = 32,
      front32 t h32 = .ok t.dropLast) ∧
    (∀ h32 : 32 ≤ t.length, ∀ ntuple : (Nat → R α) → Nat → R (List α),
      (∀ f n, ntuple f n = (List.range n).mapM fun i => f (i + 1)) →
      ∀ (typeof : List α → TupleType) (eltypes : EltypeInterface)
        (hasType : List α → TupleType → Bool),
      let r := t.take (t.length - 1)
      frontAny32 ntuple typeof eltypes hasType t h32 =
        if hasType r (.tuple [.vararg (tupleEltype eltypes (typeof t)) none]) &&
            hasType r (frontType (typeof t)) then .ok r else .error .typeError) ∧
    (firstEmpty (α := List α) = argErr "tuple must be non-empty") ∧
    (∀ (a : α) rest, firstTuple (a :: rest) = .ok a)

theorem frontTailCorrect : FrontTailCorrect := by
  intro α t
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · change SameOutcome (frontArgs t)
      (if t = [] then argErr "Cannot call front on an empty tuple." else .ok t.dropLast)
    rw [frontArgs_correct]
    cases t <;> simp [SameOutcome, TupleError.kind, argErr]
  · intro h32
    change frontArgs t = .ok t.dropLast
    have hne : t ≠ [] := by
      intro ht
      simp [ht] at h32
    rw [frontArgs_correct]
    simp [hne]
  · intro h32 ntuple hntuple typeof eltypes hasType
    have hvalues : ntuple (fun i => getfield t (i : Int)) (t.length - 1) =
        .ok (t.take (t.length - 1)) := by
      rw [hntuple]
      apply mapM_range_ok _ _ _ (by simp)
      intro k hk
      have hk' : k < t.length := by simp at hk; omega
      simpa only [List.getElem_take, Int.natCast_add, Int.natCast_one] using getfieldInBounds t k hk'
    dsimp only
    unfold frontAny32
    dsimp only
    rw [hvalues]
    simp only [Bind.bind, Except.bind]
    cases h1 : hasType (t.take (t.length - 1)) (.tuple [.vararg (tupleEltype eltypes (typeof t)) none]) <;>
      cases h2 : hasType (t.take (t.length - 1)) (frontType (typeof t)) <;>
        simp [assertTupleType, h1, h2, Bind.bind, Except.bind]
  · intro a rest
    rfl

def IntegerIndexCorrect : Prop :=
  ∀ (α : Type) (t : List α) (ty : IntTy) (i : JInt ty) (v d : α),
    (t.length : Int) ≤ IntTy.i64.max →
    let inb := 1 ≤ i.val ∧ i.val ≤ t.length
    (inb → ∃ x, t[(i.val - 1).toNat]? = some x ∧ getindexInteger t (.integer ty i) = .ok x) ∧
    (¬ inb →
      (if i.val < IntTy.i64.min ∨ i.val > IntTy.i64.max then
        SameOutcome (getindexInteger t (.integer ty i)) (.error (.julia (.inexactError "Int64")))
       else SameOutcome (getindexInteger t (.integer ty i)) bounds)) ∧
    (getDefault t (.integer ty i) d = if inb then getindexInteger t (.integer ty i) else .ok d) ∧
    (isassignedTuple t (.integer ty i) = decide inb)

theorem integerIndexCorrect : IntegerIndexCorrect := by
  intro α t ty i v d hlen
  dsimp
  have hmin : IntTy.i64.min ≤ (0 : Int) := by
    have := i64Bounds.1
    omega
  refine ⟨?_, ?_, rfl, rfl⟩
  · intro hin
    have hfit : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max := by omega
    have hconv : convertIndex (.integer ty i) = .ok (JInt.lit .i64 i.val) := by
      cases ty <;> simp [convertIndex, JInt.convert, JInt.lit, JInt.wrap,
        wrapInt_of_inRange, liftJ, IntTy.name, hfit]
    have hk : (i.val - 1).toNat < t.length := by omega
    have hfield : getfield t i.val = .ok t[(i.val - 1).toNat] := by
      unfold getfield
      rw [if_pos hin.1]
      rw [List.getElem?_eq_getElem hk]
    have hval : (JInt.lit .i64 i.val).val = i.val := litI64Value _ hfit
    have hget : getindexInteger t (.integer ty i) = .ok t[(i.val - 1).toNat] := by
      simpa [getindexInteger, hconv, hval, Bind.bind, Except.bind] using hfield
    exact ⟨t[(i.val - 1).toNat], List.getElem?_eq_getElem hk, hget⟩
  · intro hout
    by_cases hfit : IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max
    · have hconv : convertIndex (.integer ty i) = .ok (JInt.lit .i64 i.val) := by
        cases ty <;> simp [convertIndex, JInt.convert, JInt.lit, JInt.wrap,
          wrapInt_of_inRange, liftJ, IntTy.name, hfit]
      have hfield : getfield t i.val = bounds := getfieldBounds t i.val hout
      have hval : (JInt.lit .i64 i.val).val = i.val := litI64Value _ hfit
      have hget : getindexInteger t (.integer ty i) = bounds := by
        simpa [getindexInteger, hconv, hval, Bind.bind, Except.bind] using hfield
      have hno : ¬ (i.val < IntTy.i64.min ∨ i.val > IntTy.i64.max) := by omega
      rw [if_neg hno]
      rw [hget]
      rfl
    · have hconv : convertIndex (.integer ty i) =
          .error (.julia (.inexactError "Int64")) := by
        have hty : ty ≠ .i64 := by
          intro heq
          subst ty
          exact hfit i.property
        simp [convertIndex, hty, JInt.convert, dif_neg hfit, liftJ, IntTy.name]
      have houtside : i.val < IntTy.i64.min ∨ i.val > IntTy.i64.max := by omega
      have hget : getindexInteger t (.integer ty i) =
          .error (.julia (.inexactError "Int64")) := by
        simp [getindexInteger, hconv, Bind.bind, Except.bind]
      rw [if_pos houtside]
      rw [hget]
      rfl

def SetindexCorrect : Prop :=
  ∀ (α : Type) (ntuple : (Nat → α) → Nat → List α),
    (∀ f n, ntuple f n = (List.range n).map (fun k => f (k + 1))) →
    ∀ (t : List α) (v : α) (i : Index),
      (¬ (1 ≤ i.value ∧ i.value ≤ t.length) →
        setindexTuple ntuple cond t v i = bounds) ∧
      (1 ≤ i.value ∧ i.value ≤ t.length →
        ∃ result, setindexTuple ntuple cond t v i = .ok result ∧
          result.length = t.length ∧
          ∀ k (hk : k < t.length), result[k]? =
            some (if ((k + 1 : Nat) : Int) = i.value then v else t[k]))

theorem setindexCorrect : SetindexCorrect := by
  intro α ntuple hntuple t v i
  constructor
  · intro hi
    simp [setindexTuple, hi]
  · intro hi
    refine ⟨setindexVarargs ntuple cond v i t, ?_, ?_, ?_⟩
    · simp [setindexTuple, hi]
    · simp [setindexVarargs, hntuple]
    · intro k hk
      simp [setindexVarargs, hntuple, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hk, hk]

def BigIntegerIndexCorrect : Prop :=
  ∀ (α : Type) (t : List α) (i : Int) (default : α),
    (t.length : Int) ≤ IntTy.i64.max →
    (getindexInteger t (.big i) =
      if IntTy.i64.min ≤ i ∧ i ≤ IntTy.i64.max then getfield t i
      else .error (.julia (.inexactError "Int64"))) ∧
    (getDefault t (.big i) default =
      if 1 ≤ i ∧ i ≤ t.length then getfield t i else .ok default) ∧
    (isassignedTuple t (.big i) = decide (1 ≤ i ∧ i ≤ t.length))

theorem bigIntegerIndexCorrect : BigIntegerIndexCorrect := by
  intro α t i default hlen
  have hget : getindexInteger t (.big i) =
      if IntTy.i64.min ≤ i ∧ i ≤ IntTy.i64.max then getfield t i
      else .error (.julia (.inexactError "Int64")) := by
    by_cases hfit : IntTy.i64.min ≤ i ∧ i ≤ IntTy.i64.max
    · have hval := litI64Value i hfit
      simp [getindexInteger, convertIndex, JInt.convert, hfit, liftJ,
        hval, Bind.bind, Except.bind]
    · simp [getindexInteger, convertIndex, JInt.convert, hfit, liftJ,
        IntTy.name, Bind.bind, Except.bind]
  refine ⟨hget, ?_, rfl⟩
  by_cases hin : 1 ≤ i ∧ i ≤ t.length
  · have hfit : IntTy.i64.min ≤ i ∧ i ≤ IntTy.i64.max := by
      have := i64Bounds.1
      omega
    simp [getDefault, Index.value, hin, hget, hfit]
  · simp [getDefault, Index.value, hin]

def IntegerOperationsCorrect : Prop :=
  IntegerIndexCorrect ∧ SetindexCorrect ∧ BigIntegerIndexCorrect

theorem integerOperationsCorrect : IntegerOperationsCorrect :=
  ⟨integerIndexCorrect, setindexCorrect, bigIntegerIndexCorrect⟩

def BoolAcceptedCorrect : Prop := SetindexCorrect ∧
  ∀ (α : Type) (t : List α) (b : Bool) (default : α),
    getindexInteger t (.bool b) = (if b then getfield t 1 else bounds) ∧
    getDefault t (.bool b) default =
      (if b then match t with | [] => .ok default | x :: _ => .ok x else .ok default) ∧
    isassignedTuple t (.bool b) = (b && !t.isEmpty)

theorem boolAcceptedCorrect : BoolAcceptedCorrect := by
  refine ⟨setindexCorrect, ?_⟩
  intro α t b default
  have hzero : (JInt.lit .i64 0).val = 0 := litI64Value _ (by decide)
  have hone : (JInt.lit .i64 1).val = 1 := litI64Value _ (by decide)
  cases b <;> cases t <;>
    simp [getindexInteger, convertIndex, getDefault, isassignedTuple, Index.value,
      getfield, bounds, hzero, hone, Bind.bind, Except.bind]
  constructor
  · intro h
    exfalso
    omega
  · omega

def IntegerSteppingCorrect : Prop :=
  ∀ (α : Type) (t : List α) (i : Index),
    (∀ j : JInt .i64, convertIndex i = .ok j →
      previndTuple t i = .ok (JInt.wrap .i64 (j.val - 1)) ∧
      nextindTuple t i = .ok (JInt.wrap .i64 (j.val + 1))) ∧
    (∀ e, convertIndex i = .error e →
      previndTuple t i = .error e ∧ nextindTuple t i = .error e)

theorem integerSteppingCorrect : IntegerSteppingCorrect := by
  intro α t i
  constructor
  · intro j hj
    unfold previndTuple nextindTuple
    rw [hj]
    constructor <;> rfl
  · intro e he
    simp [previndTuple, nextindTuple, he, Bind.bind, Except.bind]

/-! ## Index, mapping, comparison and hash properties -/


theorem mapTwoLoopShift {α β γ : Type} (f : α → β → γ) (a : α) (t : List α)
    (b : β) (s : List β) : ∀ i k,
    mapTwoLoop f (a :: t) (b :: s) (i + 1) k = mapTwoLoop f t s i k := by
  intro i k
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [mapTwoLoop, ih]

theorem mapTwoLoopFull {α β γ : Type} (f : α → β → γ) :
    ∀ (t : List α) (s : List β),
      mapTwoLoop f t s 0 (min t.length s.length) = List.zipWith f t s := by
  intro t
  induction t with
  | nil =>
      intro s
      simp [mapTwoLoop]
  | cons a t ih =>
      intro s
      cases s with
      | nil => simp [mapTwoLoop]
      | cons b s =>
          have hmin : min (t.length + 1) (s.length + 1) =
              min t.length s.length + 1 := by
            by_cases h : t.length ≤ s.length
            · simp [Nat.min_eq_left h, Nat.min_eq_left (by omega)]
            · have hs : s.length ≤ t.length := by omega
              simp [Nat.min_eq_right hs, Nat.min_eq_right (by omega)]
          change mapTwoLoop f (a :: t) (b :: s) 0
            (min (t.length + 1) (s.length + 1)) = f a b :: List.zipWith f t s
          rw [hmin]
          simp only [mapTwoLoop, List.getElem?_cons_zero]
          rw [mapTwoLoopShift f a t b s 0 (min t.length s.length)]
          simpa using congrArg (fun xs => f a b :: xs) (ih s)


theorem mapTwoRecEq {α β γ : Type} (f : α → β → γ) (fuel : Nat) :
    ∀ (t : List α) (s : List β), t.length ≤ fuel →
      mapTwoRec f fuel t s = List.zipWith f t s := by
  induction fuel with
  | zero =>
    intro t s ht
    have hnil : t = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst t
    simp [mapTwoRec, mapTwoEmptyEmpty]
  | succ fuel ih =>
    intro t s ht
    cases t with
    | nil => simp [mapTwoRec, mapTwoGeneric]
    | cons a t =>
      cases s with
      | nil => simp [mapTwoRec, mapTwoGeneric]
      | cons b s =>
        simp only [mapTwoRec, mapTwoGeneric, List.zipWith_cons_cons]
        rw [ih t s (by simpa using Nat.le_of_succ_le_succ ht)]

def MapCorrect : Prop :=
  ∀ (α β γ : Type) (f1 : α → β) (f2 : α → β → γ) (t : List α) (s : List β),
    mapOneEmpty f1 = [] ∧
    (∀ a, mapOneOne f1 [a] = [f1 a]) ∧
    (∀ a b, mapOneTwo f1 [a, b] = [f1 a, f1 b]) ∧
    (∀ a b c, mapOneThree f1 [a, b, c] = [f1 a, f1 b, f1 c]) ∧
    mapOneGeneric f1 t.length t = t.map f1 ∧
    mapOneLong f1 t = t.map f1 ∧
    mapTwoEmptyEmpty f2 = [] ∧ mapTwoAnyEmpty f2 t = [] ∧ mapTwoEmptyAny f2 s = [] ∧
    (∀ a b, mapTwoOne f2 [a] [b] = [f2 a b]) ∧
    (∀ a a' b b', mapTwoTwo f2 [a, a'] [b, b'] = [f2 a b, f2 a' b']) ∧
    mapTwoGeneric f2 t.length t s = List.zipWith f2 t s ∧
    mapTwoLong f2 t s = List.zipWith f2 t s

theorem mapCorrect : MapCorrect := by
  intro α β γ f1 f2 t s
  refine ⟨rfl, (fun _ => rfl), (fun _ _ => rfl), (fun _ _ _ => rfl), ?_, ?_, rfl,
    rfl, rfl, (fun _ _ => rfl), (fun _ _ _ _ => rfl), ?_, ?_⟩
  · simpa only [mapOneRec] using mapOneRecEq f1 (t.length + 1) t (by omega)
  · simpa [mapOneLong] using mapOneLoopFull f1 t
  · simpa only [mapTwoRec] using mapTwoRecEq f2 (t.length + 1) t s (by omega)
  · simpa [mapTwoLong] using mapTwoLoopFull f2 t s

def lastIndex {α : Type} (f : α → Bool) : List α → Option Nat
  | [] => none
  | x :: xs => match lastIndex f xs with
      | some i => some (i + 1)
      | none => if f x then some 1 else none

private theorem findFirstLoopModel {α : Type} (f : α → Bool) (t : List α) :
    findFirstLoop f t = JuliaLean.base.tuple.findFirstLoopLocal f t 0 t.length := rfl

theorem findFirstRecEq {α : Type} (f : α → Bool) (t : List α) (i : Nat) :
    findFirstRec f i t = (t.findIdx? f).map (· + i) := by
  induction t generalizing i with
  | nil => rfl
  | cons a r ih =>
      simp only [findFirstRec, List.findIdx?_cons]
      split
      · simp_all
      · rename_i hf
        simp [hf, ih, Option.map_map]
        congr 1
        funext x
        simp only [Function.comp_apply]
        omega

theorem findFirstLoopCoreEq {α : Type} (f : α → Bool) (t : List α) (i k : Nat)
    (h : i + k = t.length) :
    JuliaLean.base.tuple.findFirstLoopLocal f t i k =
      ((t.drop i).findIdx? f).map (· + i + 1) := by
  induction k generalizing i with
  | zero =>
      have h0 : t.length ≤ i := by omega
      simp [JuliaLean.base.tuple.findFirstLoopLocal, List.drop_eq_nil_of_le h0]
  | succ k ih =>
      have hi : i < t.length := by omega
      rw [JuliaLean.base.tuple.findFirstLoopLocal, List.getElem?_eq_getElem hi,
        ih (i + 1) (by omega), List.drop_eq_getElem_cons hi, List.findIdx?_cons]
      simp only
      split
      · simp_all
      · rename_i hf
        simp [hf, Option.map_map]
        congr 1
        funext x
        simp only [Function.comp_apply]
        omega

theorem findFirstTupleEq {α : Type} (f : α → Bool) (t : List α) :
    findFirstTuple f t = (t.findIdx? f).map (· + 1) := by
  unfold findFirstTuple
  split
  · exact findFirstRecEq f t 1
  · rw [findFirstLoopModel, findFirstLoopCoreEq f t 0 t.length (by omega)]
    simp

private theorem findLastLoopModel {α : Type} (f : α → Bool) (t : List α) :
    findLastLoop f t = JuliaLean.base.tuple.findLastLoopLocal f t t.length := rfl

theorem lastIndexAppend {α : Type} (f : α → Bool) (t : List α) (a : α) :
    lastIndex f (t ++ [a]) = if f a then some (t.length + 1) else lastIndex f t := by
  induction t with
  | nil => simp [lastIndex]
  | cons x r ih =>
      show (match lastIndex f (r ++ [a]) with
        | some k => some (k + 1)
        | none => if f x then some 1 else none) = _
      rw [ih]
      by_cases hfa : f a = true
      · simp [hfa]
      · rw [if_neg hfa, if_neg hfa] <;> rfl

theorem lastIndexEq {α : Type} (f : α → Bool) (t : List α) :
    lastIndex f t = (t.reverse.findIdx? f).map (fun r => t.length - r) := by
  induction t with
  | nil => rfl
  | cons x r ih =>
      show (match lastIndex f r with
        | some k => some (k + 1)
        | none => if f x then some 1 else none) = _
      rw [ih, List.reverse_cons, List.findIdx?_append, List.findIdx?_cons]
      cases hr : r.reverse.findIdx? f with
      | some j =>
          have hj : j < r.length := by
            have := (List.findIdx?_eq_some_iff_getElem.mp hr).1
            simpa using this
          simp <;> omega
      | none =>
          by_cases hx : f x = true <;> simp [hx] <;> omega

theorem findLastLoopCoreEq {α : Type} (f : α → Bool) (t : List α) (k : Nat)
    (h : k ≤ t.length) :
    JuliaLean.base.tuple.findLastLoopLocal f t k = lastIndex f (t.take k) := by
  induction k with
  | zero => simp [JuliaLean.base.tuple.findLastLoopLocal, lastIndex]
  | succ k ih =>
      have hk : k < t.length := by omega
      rw [JuliaLean.base.tuple.findLastLoopLocal, List.take_succ, List.getElem?_eq_getElem hk,
        Option.toList_some, lastIndexAppend, ih (by omega), List.length_take,
        Nat.min_eq_left (show k ≤ t.length by omega)]
      all_goals rfl

theorem findLastRecEq {α : Type} (f : α → Bool) (t : List α) :
    findLastRec f t = lastIndex f t := by
  unfold findLastRec
  rw [findFirstTupleEq, reverseCorrect, lastIndexEq]
  cases hr : t.reverse.findIdx? f with
  | none => rfl
  | some r =>
      have := List.findIdx?_eq_some_iff_getElem.mp hr
      obtain ⟨hlt, _, _⟩ := this
      simp at hlt
      simp
      omega

theorem findLastTupleEq {α : Type} (f : α → Bool) (t : List α) :
    findLastTuple f t = lastIndex f t := by
  unfold findLastTuple
  split
  · exact findLastRecEq f t
  · rw [findLastLoopModel, findLastLoopCoreEq f t t.length (Nat.le_refl _),
      List.take_length]

theorem filterRecEq {α : Type}
    (afoldl : (List α → α → List α) → List α → List α → List α)
    (hfold : ∀ op initial xs, afoldl op initial xs = xs.foldl op initial)
    (f : α → Bool) (t : List α) : filterRec afoldl f t = t.filter f := by
  unfold filterRec
  rw [hfold]
  suffices ∀ acc, t.foldl (fun ys x => if f x then ys ++ [x] else ys) acc =
      acc ++ t.filter f by
    simpa using this []
  induction t with
  | nil => simp
  | cons a r ih =>
      intro acc
      simp only [List.foldl_cons, List.filter_cons]
      split <;> simp [ih]

def FindFilterCorrect : Prop :=
  ∀ (α : Type) (f : α → Bool) (t : List α)
    (afoldl : (List α → α → List α) → List α → List α → List α)
    (filterVector : (α → Bool) → List α → List α),
    (∀ op initial xs, afoldl op initial xs = xs.foldl op initial) →
    (∀ predicate xs, filterVector predicate xs = xs.filter predicate) →
    findFirstTuple f t = (t.findIdx? f).map (· + 1) ∧
    findLastTuple f t = lastIndex f t ∧
    filterTuple afoldl filterVector f t = t.filter f

theorem findFilterCorrect : FindFilterCorrect := by
  intro α f t afoldl filterVector hfold hfilter
  refine ⟨findFirstTupleEq f t, findLastTupleEq f t, ?_⟩
  unfold filterTuple
  split
  · exact filterRecEq afoldl hfold f t
  · exact hfilter f t

theorem isequalRecEq {α : Type} (ops : Ops α) (t s : List α)
    (h : t.length = s.length) :
    isequalRec ops t s = .ok ((List.zipWith ops.isequal t s).all id) := by
  induction t generalizing s with
  | nil =>
      cases s with
      | nil => rfl
      | cons _ _ => simp at h
  | cons a t ih =>
      cases s with
      | nil => simp at h
      | cons b s =>
        cases he : ops.isequal a b <;> simp [isequalRec, he, ih s (by simpa using h)]

theorem isequalLongLoopEq {α : Type} (ops : Ops α) (t s : List α) (i k : Nat)
    (hl : t.length = s.length) (h : i + k = t.length) :
    isequalLongLoop ops t s i k =
      .ok ((List.zipWith ops.isequal (t.drop i) (s.drop i)).all id) := by
  induction k generalizing i with
  | zero =>
      have h1 : t.length ≤ i := by omega
      have h2 : s.length ≤ i := by omega
      rw [List.drop_eq_nil_of_le h1, List.drop_eq_nil_of_le h2]
      rfl
  | succ k ih =>
      have hi : i < t.length := by omega
      have hj : i < s.length := by omega
      rw [isequalLongLoop, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
        ih (i + 1) (by omega), List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj,
        List.zipWith_cons_cons, List.all_cons]
      simp only
      cases ops.isequal t[i] s[i] <;> simp

theorem keysManyPairEqual {α : Type} (mismatch : String → List (List Nat) → KeysResult)
    (t s : List α) (hl : t.length = s.length) :
    keysMany mismatch t [s] = .ok (oneTo t.length) := by
  have he : lengthTuple s = lengthTuple t := hl.symm
  have hall : ([s].all (fun other => lengthTuple other = lengthTuple t)) = true := by
    simp only [List.all_cons, List.all_nil, decide_eq_true he, Bool.true_and]
  simp only [keysMany]
  rw [hall]
  rfl

theorem isequalLongEq {α : Type} (ops : Ops α) (t s : List α) (i k : Nat)
    (hl : t.length = s.length) (h : i + k = t.length) :
    isequalLong ops t s i k =
      .ok ((List.zipWith ops.isequal (t.drop i) (s.drop i)).all id) := by
  rw [isequalLong, keysManyPairEqual _ t s hl]
  exact isequalLongLoopEq ops t s i k hl h

theorem isequalTupleMethodEq {α : Type} (ops : Ops α) (t s : List α) :
    isequalTuple ops t s =
      .ok (t.length == s.length && (List.zipWith ops.isequal t s).all id) := by
  unfold isequalTuple
  by_cases hl : t.length = s.length
  · have hbeq : (t.length == s.length) = true := by simp [hl]
    simp only [hbeq, Bool.true_and, ↓reduceIte]
    unfold isequalBody
    split
    · simpa using isequalLongEq ops t s 0 t.length hl (by omega)
    · exact isequalRecEq ops t s hl
  · have hbeq : (t.length == s.length) = false := by simpa using hl
    simp only [hbeq, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

def eqCode (cs : List (Option Bool)) (anymissing : Bool) : Option Bool :=
  if cs.contains (some false) then some false
  else if anymissing || cs.contains none then none else some true

def eqSpec {α : Type} (ops : Ops α) (t s : List α) : Option Bool :=
  if t.length ≠ s.length then some false
  else eqCode (List.zipWith ops.eq t s) false

theorem eqCodeNone (cs : List (Option Bool)) (m : Bool) :
    eqCode (none :: cs) m = eqCode cs true := by
  by_cases h : some false ∈ cs <;> simp [eqCode, h]

theorem eqCodeFalse (cs : List (Option Bool)) (m : Bool) :
    eqCode (some false :: cs) m = some false := by
  simp [eqCode]

theorem eqCodeTrue (cs : List (Option Bool)) (m : Bool) :
    eqCode (some true :: cs) m = eqCode cs m := by
  by_cases h : some false ∈ cs <;> by_cases h' : none ∈ cs <;> simp [eqCode, h, h']

theorem eqMissingEq {α : Type} (ops : Ops α) (t s : List α)
    (h : t.length = s.length) :
    eqMissing ops t s = .ok (eqCode (List.zipWith ops.eq t s) true) := by
  induction t generalizing s with
  | nil =>
      cases s with
      | nil => rfl
      | cons _ _ => simp at h
  | cons a t ih =>
      cases s with
      | nil => simp at h
      | cons b s =>
          rw [eqMissing, ih s (by simpa using h)]
          unfold eqCode
          cases hab : ops.eq a b with
          | none => simp [hab, eqCode]
          | some c => cases c <;> simp [hab, eqCode]

theorem eqRecEq {α : Type} (ops : Ops α) (t s : List α)
    (h : t.length = s.length) :
    eqRec ops t s = .ok (eqCode (List.zipWith ops.eq t s) false) := by
  induction t generalizing s with
  | nil =>
      cases s with
      | nil => rfl
      | cons _ _ => simp at h
  | cons a t ih =>
      cases s with
      | nil => simp at h
      | cons b s =>
          have h' : t.length = s.length := by simpa using h
          rw [eqRec]
          cases hab : ops.eq a b with
          | none =>
              simp only
              rw [eqMissingEq ops t s h']
              unfold eqCode
              simp [hab]
          | some c =>
              cases c with
              | false => simp [eqCode, hab]
              | true =>
                  simp only
                  rw [ih s h']
                  unfold eqCode
                  simp [hab]

theorem eqLongLoopEq {α : Type} (ops : Ops α) (t s : List α) (i k : Nat)
    (m : Bool) (hl : t.length = s.length) (h : i + k = t.length) :
    eqLongLoop ops t s i k m = .ok (eqCode (List.zipWith ops.eq (t.drop i) (s.drop i)) m) := by
  induction k generalizing i m with
  | zero =>
      have h1 : t.length ≤ i := by omega
      have h2 : s.length ≤ i := by omega
      rw [List.drop_eq_nil_of_le h1, List.drop_eq_nil_of_le h2]
      cases m <;> rfl
  | succ k ih =>
      have hi : i < t.length := by omega
      have hj : i < s.length := by omega
      rw [eqLongLoop, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
        List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj,
        List.zipWith_cons_cons]
      simp only
      cases hab : ops.eq t[i] s[i] with
      | none => simp only; rw [ih (i + 1) true (by omega), eqCodeNone]
      | some c =>
          cases c with
          | false => simp only; rw [eqCodeFalse]
          | true => simp only; rw [ih (i + 1) m (by omega), eqCodeTrue]

theorem eqLongEq {α : Type} (ops : Ops α) (t s : List α) (i k : Nat)
    (m : Bool) (hl : t.length = s.length) (h : i + k = t.length) :
    eqLong ops t s i k m = .ok (eqCode (List.zipWith ops.eq (t.drop i) (s.drop i)) m) := by
  rw [eqLong, keysManyPairEqual _ t s hl]
  exact eqLongLoopEq ops t s i k m hl h

theorem eqTupleMethodEq {α : Type} (ops : Ops α) (t s : List α) :
    eqTuple ops t s = .ok (eqSpec ops t s) := by
  unfold eqTuple eqBody eqSpec
  by_cases hl : t.length = s.length
  · have hne : ¬ t.length ≠ s.length := by omega
    rw [if_pos hl, if_neg hne]
    split
    · rw [eqLongEq ops t s 0 t.length false hl (by omega),
        List.drop_zero, List.drop_zero]
    · exact eqRecEq ops t s hl
  · simp [hl]

def EqualityCorrect : Prop :=
  ∀ (α : Type) (ops : Ops α) (t s : List α),
    isequalTuple ops t s =
      .ok (t.length == s.length && (List.zipWith ops.isequal t s).all id) ∧
    eqTuple ops t s = .ok (eqSpec ops t s)

theorem equalityCorrect : EqualityCorrect := by
  intro α ops t s
  exact ⟨isequalTupleMethodEq ops t s, eqTupleMethodEq ops t s⟩

def InternalComparisonErrors : Prop :=
  ∀ (α : Type) (ops : Ops α),
    (∀ message indices, ops.mismatchIndices message indices = .error .dimensionMismatch) →
    (∀ t s : List α, t.length ≠ s.length →
      isequalLong ops t s 0 t.length = .error .dimensionMismatch ∧
      eqLong ops t s 0 t.length false = .error .dimensionMismatch) ∧
    (∀ (a : α) rest,
      isequalRec ops (a :: rest) [] = .error (.julia (.methodError "_isequal")) ∧
      eqRec ops (a :: rest) [] = bounds ∧
      eqMissing ops (a :: rest) [] = bounds) ∧
    (∀ (a : α) rest,
      isequalRec ops [] (a :: rest) = .error (.julia (.methodError "_isequal")) ∧
      eqRec ops [] (a :: rest) = bounds ∧
      eqMissing ops [] (a :: rest) = bounds)

theorem internalComparisonErrors : InternalComparisonErrors := by
  intro α ops hthrows
  refine ⟨?_, (fun _ _ => ⟨rfl, rfl, rfl⟩), (fun _ _ => ⟨rfl, rfl, rfl⟩)⟩
  intro t s hlen
  have hm : keysMany ops.mismatchIndices t [s] = .error .dimensionMismatch :=
    (tupleIterProtocolCorrect α Unit ops.mismatchIndices hthrows).2.2.2.2 t [s]
      ⟨s, by simp, Ne.symm hlen⟩
  simp only [isequalLong, eqLong, hm, Bind.bind, Except.bind, and_self]

structure OpsLawful {α : Type} (ops : Ops α) : Prop where
  irrefl : ∀ a, ops.isless a a = false
  trans : ∀ a b c, ops.isless a b = true → ops.isless b c = true → ops.isless a c = true
  equiv : ∀ a b, ops.isequal a b = (!ops.isless a b && !ops.isless b a)
  incompTrans : ∀ a b c, ops.isequal a b = true → ops.isequal b c = true → ops.isequal a c = true

variable {α : Type}

theorem ltLong_eq (o : Ops α) (t s : List α) (i k : Nat) (h : i + k = min t.length s.length) :
    ltLong o t s i k = ltShort o (t.drop i) (s.drop i) := by
  induction k generalizing i with
  | zero =>
    simp only [ltLong]
    rcases Nat.lt_trichotomy t.length s.length with h' | h' | h'
    · have h1 : t.length ≤ i := by omega
      have h2 : i < s.length := by omega
      rw [List.drop_eq_nil_of_le h1, List.drop_eq_getElem_cons h2]
      simp [ltShort, h']
    · have h1 : t.length ≤ i := by omega
      have h2 : s.length ≤ i := by omega
      rw [List.drop_eq_nil_of_le h1, List.drop_eq_nil_of_le h2]
      simp [ltShort, h']
    · have h1 : s.length ≤ i := by omega
      have h2 : i < t.length := by omega
      rw [List.drop_eq_nil_of_le h1, List.drop_eq_getElem_cons h2]
      simp [ltShort]; omega
  | succ k ih =>
    have hi : i < t.length := by omega
    have hj : i < s.length := by omega
    rw [ltLong, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj]
    simp only [ltShort]
    cases o.eq t[i] s[i] with
    | none => rfl
    | some c => cases c with
      | false => rfl
      | true => exact ih (i + 1) (by omega)

def ltDecision (comparison : Option Bool × Option Bool) (later : Option Bool) : Option Bool :=
  match comparison.1 with
  | none => none
  | some false => comparison.2
  | some true => later

theorem ltShortFold (ops : Ops α) (t s : List α) :
    ltShort ops t s =
      (List.zipWith (fun a b => (ops.eq a b, ops.lt a b)) t s).foldr ltDecision
        (some (decide (t.length < s.length))) := by
  induction t generalizing s with
  | nil => cases s <;> simp [ltShort]
  | cons a t ih =>
    cases s with
    | nil => simp [ltShort]
    | cons b s =>
      simp only [ltShort, List.zipWith_cons_cons, List.foldr_cons, List.length_cons,
        Nat.add_lt_add_iff_right]
      rw [← ih]
      cases ops.eq a b with
      | none => rfl
      | some c => cases c <;> rfl

def LtLexicographic : Prop :=
  ∀ (α : Type) (ops : Ops α) (t s : List α),
    ltTupleMethod ops t s =
      (List.zipWith (fun a b => (ops.eq a b, ops.lt a b)) t s).foldr ltDecision
        (some (decide (t.length < s.length)))

theorem ltLexicographic : LtLexicographic := by
  intro α ops t s
  unfold ltTupleMethod
  split
  · rw [ltLong_eq ops t s 0 _ (by omega)]
    simpa using ltShortFold ops t s
  · exact ltShortFold ops t s

section Order

variable {o : Ops α} (hL : OpsLawful o)
include hL

theorem isequal_refl (a : α) : o.isequal a a = true := by
  rw [hL.equiv, hL.irrefl]; rfl

theorem isequal_symm (a b : α) : o.isequal a b = o.isequal b a := by
  rw [hL.equiv, hL.equiv b a, Bool.and_comm]

theorem not_lt_of_isequal {a b : α} (h : o.isequal a b = true) : o.isless a b = false := by
  rw [hL.equiv] at h
  cases hab : o.isless a b <;> simp_all

theorem lt_or_lt_of_not_isequal {a b : α} (h : o.isequal a b = false) :
    o.isless a b = true ∨ o.isless b a = true := by
  rw [hL.equiv] at h
  cases hab : o.isless a b <;> cases hba : o.isless b a <;> simp_all

theorem lt_of_lt_of_eq {a b c : α} (h1 : o.isless a b = true) (h2 : o.isequal b c = true) :
    o.isless a c = true := by
  cases hac : o.isless a c
  · exfalso
    cases hca : o.isless c a
    · have hea : o.isequal a c = true := by rw [hL.equiv, hac, hca]; rfl
      have heb : o.isequal a b = true := by
        rw [isequal_symm hL b c] at h2
        exact hL.incompTrans a c b hea h2
      rw [not_lt_of_isequal hL heb] at h1
      exact absurd h1 (by decide)
    · have := hL.trans c a b hca h1
      rw [isequal_symm hL] at h2
      rw [not_lt_of_isequal hL h2] at this
      exact absurd this (by decide)
  · rfl

theorem lt_of_eq_of_lt {a b c : α} (h1 : o.isequal a b = true) (h2 : o.isless b c = true) :
    o.isless a c = true := by
  cases hac : o.isless a c
  · exfalso
    cases hca : o.isless c a
    · have hea : o.isequal a c = true := by rw [hL.equiv, hac, hca]; rfl
      have hbc : o.isequal b c = true := by
        rw [isequal_symm hL a b] at h1
        exact hL.incompTrans b a c h1 hea
      rw [not_lt_of_isequal hL hbc] at h2
      exact absurd h2 (by decide)
    · have := hL.trans b c a h2 hca
      rw [not_lt_of_isequal hL ((isequal_symm hL a b) ▸ h1)] at this
      exact absurd this (by decide)
  · rfl

theorem islessShort_irrefl (t : List α) : islessShort o t t = false := by
  induction t with
  | nil => rfl
  | cons a r ih => simp [islessShort, hL.irrefl, ih]

theorem islessShort_trans (t s u : List α) (h1 : islessShort o t s = true)
    (h2 : islessShort o s u = true) : islessShort o t u = true := by
  induction t generalizing s u with
  | nil =>
    cases s with
    | nil => simp [islessShort] at h1
    | cons b s' => cases u with
      | nil => simp [islessShort] at h2
      | cons c u' => rfl
  | cons a r ih =>
    cases s with
    | nil => simp [islessShort] at h1
    | cons b s' => cases u with
      | nil => simp [islessShort] at h2
      | cons c u' =>
        simp only [islessShort, Bool.or_eq_true, Bool.and_eq_true] at h1 h2 ⊢
        rcases h1 with h1 | ⟨e1, r1⟩ <;> rcases h2 with h2 | ⟨e2, r2⟩
        · exact Or.inl (hL.trans a b c h1 h2)
        · exact Or.inl (lt_of_lt_of_eq hL h1 e2)
        · exact Or.inl (lt_of_eq_of_lt hL e1 h2)
        · exact Or.inr ⟨hL.incompTrans a b c e1 e2, ih s' u' r1 r2⟩

theorem islessShort_incomp (t s : List α) :
    (islessShort o t s = false ∧ islessShort o s t = false) ↔
      (t.length == s.length && (List.zipWith o.isequal t s).all id) = true := by
  induction t generalizing s with
  | nil => cases s <;> simp [islessShort]
  | cons a r ih =>
    cases s with
    | nil => simp [islessShort]
    | cons b s' =>
      have ihs := ih s'
      simp only [List.length_cons, Nat.add_right_cancel_iff, List.zipWith_cons_cons,
        List.all_cons, id] at ihs ⊢
      cases hab : o.isequal a b
      · rcases lt_or_lt_of_not_isequal hL hab with h | h
        · simp [islessShort, h]
        · simp [islessShort, h]
      · have hba : o.isequal b a = true := by rw [isequal_symm hL]; exact hab
        simp [islessShort, not_lt_of_isequal hL hab, not_lt_of_isequal hL hba, hab, hba]
        simpa using ihs

theorem islessLong_eq (t s : List α) (i k : Nat) (h : i + k = min t.length s.length) :
    islessLong o t s i k = islessShort o (t.drop i) (s.drop i) := by
  induction k generalizing i with
  | zero =>
    simp only [islessLong]
    rcases Nat.lt_trichotomy t.length s.length with h' | h' | h'
    · have h1 : t.length ≤ i := by omega
      have h2 : i < s.length := by omega
      rw [List.drop_eq_nil_of_le h1, List.drop_eq_getElem_cons h2]
      simp [islessShort, h']
    · have h1 : t.length ≤ i := by omega
      have h2 : s.length ≤ i := by omega
      rw [List.drop_eq_nil_of_le h1, List.drop_eq_nil_of_le h2]
      simp [islessShort, h']
    · have h1 : s.length ≤ i := by omega
      have h2 : i < t.length := by omega
      rw [List.drop_eq_nil_of_le h1, List.drop_eq_getElem_cons h2]
      simp [islessShort]; omega
  | succ k ih =>
    have hi : i < t.length := by omega
    have hj : i < s.length := by omega
    rw [islessLong, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj, List.drop_eq_getElem_cons hi, List.drop_eq_getElem_cons hj]
    simp only [islessShort]
    cases he : o.isequal t[i] s[i]
    · simp
    · simp [not_lt_of_isequal hL he, ih (i + 1) (by omega)]

theorem isless_eq (t s : List α) : islessTuple o t s = islessShort o t s := by
  unfold islessTuple
  split
  · rw [islessLong_eq hL t s 0 _ (by omega)]; simp
  · rfl

end Order

def IslessStrictWeakOrder : Prop :=
  ∀ (α : Type) (ops : Ops α), OpsLawful ops →
    (∀ t, islessTuple ops t t = false) ∧
    (∀ t s u, islessTuple ops t s = true → islessTuple ops s u = true →
      islessTuple ops t u = true) ∧
    (∀ t s, (islessTuple ops t s = false ∧ islessTuple ops s t = false) ↔
      isequalTuple ops t s = .ok true)

theorem islessStrictWeakOrder : IslessStrictWeakOrder := by
  intro α ops hL
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rw [isless_eq hL]
    exact islessShort_irrefl hL t
  · intro t s u h1 h2
    rw [isless_eq hL] at h1 h2 ⊢
    exact islessShort_trans hL t s u h1 h2
  · intro t s
    rw [isless_eq hL, isless_eq hL, isequalTupleMethodEq]
    constructor
    · intro he
      exact congrArg Except.ok ((islessShort_incomp hL t s).mp he)
    · intro he
      exact (islessShort_incomp hL t s).mpr (Except.ok.inj he)



theorem hashLongLoopFoldr {α : Type} (ops : Ops α) (t : List α) :
    ∀ k out, k ≤ t.length →
      hashLongLoop ops t k out = (t.take k).foldr ops.hash out := by
  intro k
  induction k with
  | zero =>
      intro out _
      simp [hashLongLoop]
  | succ k ih =>
      intro out hk
      have hlt : k < t.length := by omega
      simp [hashLongLoop, List.getElem?_eq_getElem hlt]
      rw [ih _ (by omega)]
      rw [List.take_succ_eq_append_getElem hlt]
      rw [List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil]

theorem hashLongFoldr {α : Type} (ops : Ops α) (t : List α) (h : Nat) :
    hashLong ops t h = t.foldr ops.hash (h ^^^ tupleHashSeed) := by
  unfold hashLong
  rw [hashLongLoopFoldr ops t t.length _ (by omega)]
  simp

theorem hashTupleFoldr {α : Type} (ops : Ops α) (t : List α) (h : Nat) :
    hashTuple ops t h = t.foldr ops.hash (h ^^^ tupleHashSeed) := by
  induction t with
  | nil => rfl
  | cons a t ih => simp [hashTuple, ih]

theorem hashTupleMethodFoldr {α : Type} (ops : Ops α) (t : List α) (h : Nat) :
    hashTupleMethod ops t h = t.foldr ops.hash (h ^^^ tupleHashSeed) := by
  unfold hashTupleMethod
  split
  · exact hashLongFoldr ops t h
  · exact hashTupleFoldr ops t h

theorem foldrHashCongr {α : Type} (ops : Ops α)
    (hc : ∀ a b h, ops.isequal a b = true → ops.hash a h = ops.hash b h)
    (t s : List α) (hlen : t.length = s.length)
    (he : (List.zipWith ops.isequal t s).all id = true) (seed : Nat) :
    t.foldr ops.hash seed = s.foldr ops.hash seed := by
  induction t generalizing s with
  | nil =>
      cases s with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons a t ih =>
      cases s with
      | nil => simp at hlen
      | cons b s =>
          simp only [List.zipWith_cons_cons, List.all_cons, id, Bool.and_eq_true] at he
          simp only [List.foldr_cons]
          rw [ih s (by simpa using hlen) he.2, hc a b _ he.1]


def HashIsequal : Prop :=
  ∀ (α : Type) (ops : Ops α),
    (∀ a b h, ops.isequal a b = true → ops.hash a h = ops.hash b h) →
    ∀ t s h, isequalTuple ops t s = .ok true →
      hashTupleMethod ops t h = hashTupleMethod ops s h

theorem hashIsequal : HashIsequal := by
  intro α ops hc t s h he
  have hspec := (equalityCorrect α ops t s).1
  rw [hspec] at he
  have he' := Except.ok.inj he
  simp only [Bool.and_eq_true, beq_iff_eq] at he'
  rcases he' with ⟨hlen, hfields⟩
  rw [hashTupleMethodFoldr ops t h, hashTupleMethodFoldr ops s h]
  exact foldrHashCongr ops hc t s hlen hfields _

def TupleHashConsistency : Prop := HashIsequal

theorem tupleHashConsistency_proven : TupleHashConsistency := hashIsequal

/-! ## Type and constructor contracts -/

def TupleTypeMethodsCorrect : Prop :=
  (∀ T n (arity : NTupleArity T n), countTupleSpecific n T arity = n) ∧
  (∀ T, countTupleFallback T = none) ∧
  (∀ (join : TupleType → TupleType → TupleType) (free : TupleType → Bool) a b,
    computeEltype free join (.union a b) =
      if free (.union a b) then .any else
        join (computeEltype free join a) (computeEltype free join b)) ∧
  (∀ (α : Type) (typeof : List α → TupleType) (t : List α),
    keytypeValue typeof t = .atom "Int64") ∧
  (∀ T : TupleType, keytypeType T = .atom "Int64") ∧
  (∀ ty n, tupleTypeTail (.tuple [.vararg ty (some n)]) = .ok (.tuple [.vararg ty (some (n - 1))])) ∧
  (∀ ty tys, tupleTypeTail (.tuple (.type ty :: tys)) = .ok (.tuple tys))

theorem tupleTypeMethodsCorrect : TupleTypeMethodsCorrect := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T n arity; rfl
  · intro T; rfl
  · intro join free a b
    rfl
  · intro α typeof t; rfl
  · intro T; rfl
  · intro ty n; simp [tupleTypeTail]
  · intro ty tys; simp [tupleTypeTail, argtail]
theorem combineHomogeneous (join : TupleType → TupleType → TupleType)
    (hjoin : ∀ T, join T T = T) (ty : TupleType) (n : Nat) :
    computeEltype.combine join id ty ((List.replicate n ty).map .type) = ty := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.map_replicate] at ih ⊢
    cases ty <;> simp [computeEltype.combine, List.replicate_succ,
      paramType, unwrapVararg, hjoin, ih]

def ElementTypeCorrect : Prop :=
  (∀ (free : TupleType → Bool) (join : TupleType → TupleType → TupleType),
    (∀ T, join T T = T) → ∀ ty n,
    free (.tuple ((List.replicate (n + 1) ty).map .type)) = false →
      computeEltype free join (.tuple ((List.replicate (n + 1) ty).map .type)) = ty) ∧
  (∀ (ops : EltypeInterface) T E,
    eltypeNTuple ops T true true false E = E ∧
    eltypeNTuple ops T true false false E = .bottom ∧
    eltypeNTuple ops T false false true E = .bottom) ∧
  (∀ (ops : EltypeInterface) T,
    (ops.empty T = true → tupleEltype ops T = .bottom) ∧
    (ops.empty T = false → ops.signature T = true →
      ops.defined T = true → ops.isType T = true → tupleEltype ops T = ops.element T)) ∧
  (∀ ty parameters,
    frontType (.tuple (.type ty :: parameters)) =
      .tuple ((.type ty :: parameters).dropLast))

theorem elementTypeCorrect : ElementTypeCorrect := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro free join hjoin ty n hfree
    simp only [List.replicate_succ, List.map_cons] at hfree
    simpa only [computeEltype, computeEltype.compute,
      List.replicate_succ, List.map_cons, paramType, unwrapVararg, id_eq,
      hfree, Bool.false_eq_true, ↓reduceIte] using combineHomogeneous join hjoin ty n
  · intro ops T E
    exact ⟨rfl, rfl, rfl⟩
  · intro ops T
    constructor
    · intro he
      simp [tupleEltype, he]
    · intro he hs hd ht
      simp [tupleEltype, eltypeNTuple, he, hs, hd, ht]
  · intro ty parameters
    simp [frontType, isTupleDataType, isVatuple, typeParameters, List.dropLast_eq_take]

def FrontTypeFallbackCorrect : Prop :=
  ∀ T, isTupleDataType T = false ∨ isVatuple T = true →
    frontType T = .tuple [.vararg .any none]

theorem frontTypeFallbackCorrect : FrontTypeFallbackCorrect := by
  intro T ht
  rcases ht with ht | ht <;> simp [frontType, ht]

/-- Runtime type checks, closed tuple types, and promote_typejoin's upper-bound law. -/
structure FrontTypingLaws {α : Type} (typeOf : α → TupleType)
    (typeof : List α → TupleType) (hasType : List α → TupleType → Bool)
    (ops : EltypeInterface) (Checks : α → TupleType → Prop) : Prop where
  tupleType : ∀ xs, typeof xs = .tuple ((xs.map typeOf).map .type)
  ownTuple : ∀ xs, hasType xs (typeof xs) = true
  ownValue : ∀ x, Checks x (typeOf x)
  anyValue : ∀ x, Checks x .any
  joined : ∀ x A B, Checks x A ∨ Checks x B → Checks x (ops.join A B)
  vararg : ∀ xs E, hasType xs (.tuple [.vararg E none]) = true ↔ ∀ x ∈ xs, Checks x E
  closed : ∀ xs, ops.free (typeof xs) = false
  nonempty : ∀ xs, xs ≠ [] → ops.empty (typeof xs) = false
  nonemptyNTuple : ∀ xs, xs ≠ [] → ops.emptyNTuple (typeof xs) = false
  definedElement : ∀ xs x, x ∈ xs →
    ops.signature (typeof xs) = true → ops.defined (typeof xs) = true →
      ops.isType (typeof xs) = true ∧ Checks x (ops.element (typeof xs))

theorem combineAccepts {α : Type} (ops : EltypeInterface) (Checks : α → TupleType → Prop)
    (hany : ∀ x, Checks x .any)
    (hjoin : ∀ x A B, Checks x A ∨ Checks x B → Checks x (ops.join A B))
    (fields : List TupleType) :
    ∀ result x, Checks x result ∨ (∃ A ∈ fields, Checks x A) →
      Checks x (computeEltype.combine ops.join id result (fields.map .type)) := by
  induction fields with
  | nil =>
    intro result x h
    simpa [computeEltype.combine] using h
  | cons A fields ih =>
    intro result x h
    by_cases ha : result = .any
    · subst result
      simpa [computeEltype.combine] using hany x
    · have hstep : computeEltype.combine ops.join id result ((A :: fields).map .type) =
          computeEltype.combine ops.join id (ops.join A result) (fields.map .type) := by
        cases result <;> simp_all [computeEltype.combine, paramType, unwrapVararg]
      rw [hstep]
      apply ih
      rcases h with hr | ⟨B, hB, hx⟩
      · exact Or.inl (hjoin x A result (Or.inr hr))
      · rcases List.mem_cons.mp hB with hB | hB
        · subst B
          exact Or.inl (hjoin x A result (Or.inl hx))
        · exact Or.inr ⟨B, hB, hx⟩

theorem tupleEltypeAccepts {α : Type} (typeOf : α → TupleType)
    (typeof : List α → TupleType) (hasType : List α → TupleType → Bool)
    (ops : EltypeInterface) (Checks : α → TupleType → Prop)
    (laws : FrontTypingLaws typeOf typeof hasType ops Checks)
    (t : List α) (x : α) (hx : x ∈ t) :
    Checks x (tupleEltype ops (typeof t)) := by
  have hne : t ≠ [] := by intro h; simp [h] at hx
  have hcompute : Checks x (computeEltype ops.free ops.join (typeof t)) := by
    have hf := laws.closed t
    rw [laws.tupleType t] at hf ⊢
    cases t with
    | nil => simp at hx
    | cons a rest =>
      simp only [List.map_cons] at hf
      simp only [List.map_cons, computeEltype, computeEltype.compute, id_eq,
        hf, Bool.false_eq_true, ↓reduceIte, paramType, unwrapVararg]
      apply combineAccepts ops Checks laws.anyValue laws.joined
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        exact Or.inl (laws.ownValue a)
      · exact Or.inr ⟨typeOf x, List.mem_map.mpr ⟨x, hx, rfl⟩, laws.ownValue x⟩
  unfold tupleEltype
  rw [laws.nonempty t hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hs : ops.signature (typeof t) = true
  · rw [if_pos hs]
    unfold eltypeNTuple
    by_cases hd : ops.defined (typeof t) = true
    · obtain ⟨ht, hvalue⟩ := laws.definedElement t x hx hs hd
      simpa [hd, ht] using hvalue
    · simpa [hd, laws.nonemptyNTuple t hne] using hcompute
  · simpa [hs] using hcompute

def FrontPrefixCorrect : Prop :=
  ∀ (α : Type) (typeOf : α → TupleType) (typeof : List α → TupleType)
    (hasType : List α → TupleType → Bool) (ops : EltypeInterface)
    (Checks : α → TupleType → Prop),
    FrontTypingLaws typeOf typeof hasType ops Checks →
    ∀ (ntuple : (Nat → R α) → Nat → R (List α)),
      (∀ f n, ntuple f n = (List.range n).mapM fun i => f (i + 1)) →
      ∀ (t : List α) (h32 : 32 ≤ t.length),
        frontAny32 ntuple typeof ops hasType t h32 = .ok (t.take (t.length - 1))

theorem frontPrefixCorrect : FrontPrefixCorrect := by
  intro α typeOf typeof hasType ops Checks laws ntuple hntuple t h32
  have hne : t ≠ [] := by intro h; simp [h] at h32
  have hfront : frontType (typeof t) = typeof (t.take (t.length - 1)) := by
    rw [laws.tupleType t, laws.tupleType (t.take (t.length - 1))]
    cases t with
    | nil => contradiction
    | cons a rest =>
      simp [frontType, isTupleDataType, isVatuple, typeParameters, List.map_take]
  have hfirst : hasType (t.take (t.length - 1))
      (.tuple [.vararg (tupleEltype ops (typeof t)) none]) = true := by
    apply (laws.vararg _ _).mpr
    intro x hx
    exact tupleEltypeAccepts typeOf typeof hasType ops Checks laws t x (List.mem_of_mem_take hx)
  have hsecond : hasType (t.take (t.length - 1)) (frontType (typeof t)) = true := by
    rw [hfront]
    exact laws.ownTuple _
  have h := (frontTailCorrect α t).2.2.1 h32 ntuple hntuple typeof ops hasType
  dsimp only at h
  simpa only [hfirst, hsecond, Bool.true_and, ↓reduceIte] using h

def FullFrontCorrect : Prop := FrontTailCorrect ∧ FrontPrefixCorrect

theorem fullFrontCorrect : FullFrontCorrect := ⟨frontTailCorrect, frontPrefixCorrect⟩

def ReflectionCasesCorrect : Prop :=
  (∀ (ops : EltypeInterface) T,
    eltypeNTuple ops T false false false .bottom = computeEltype ops.free ops.join T) ∧
  (∀ (ops : EltypeInterface) T,
    ops.empty T = false → ops.signature T = false →
      tupleEltype ops T = computeEltype ops.free ops.join T) ∧
  (∀ (free : TupleType → Bool) (join : TupleType → TupleType → TupleType) parameters,
    free (.tuple parameters) = true → computeEltype free join (.tuple parameters) = .any) ∧
  (∀ (free : TupleType → Bool) (join : TupleType → TupleType → TupleType),
    free (.tuple []) = false → computeEltype free join (.tuple []) = .bottom) ∧
  (∀ (free : TupleType → Bool) (join : TupleType → TupleType → TupleType) n parameters,
    free (.tuple (.value n :: parameters)) = false →
      computeEltype free join (.tuple (.value n :: parameters)) = .bottom) ∧
  (∀ parameters, isVatuple (.tuple parameters) = false →
    frontType (.tuple parameters) = .tuple parameters.dropLast) ∧
  (∀ name T, tupleTypeTail T = .error (.julia (.methodError "tuple_type_tail")) →
    tupleTypeTail (.unionAll name T) = .error (.julia (.methodError "tuple_type_tail"))) ∧
  (∀ name T U, tupleTypeTail T = .ok U →
    tupleTypeTail (.unionAll name T) = .ok (.unionAll name U)) ∧
  (∀ A B A' B', tupleTypeTail A = .ok A' → tupleTypeTail B = .ok B' →
    tupleTypeTail (.union A B) = .ok (.union A' B')) ∧
  (∀ T, isTupleDataType T = false →
    (∀ name body, T ≠ .unionAll name body) → (∀ A B, T ≠ .union A B) →
      tupleTypeTail T = .error (.julia (.methodError "tuple_type_tail"))) ∧
  (∀ (α : Type) (typeof : List α → TupleType) (ops : EltypeInterface) t,
    valtypeValue typeof ops t = tupleEltype ops (typeof t)) ∧
  (∀ (ops : EltypeInterface) T, valtypeType ops T = tupleEltype ops T)

theorem reflectionCasesCorrect : ReflectionCasesCorrect := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ops T; rfl
  · intro ops T he hs
    simp [tupleEltype, he, hs]
  · intro free join parameters h
    simp [computeEltype, computeEltype.compute, h]
  · intro free join h
    simp [computeEltype, computeEltype.compute, h]
  · intro free join n parameters h
    simp [computeEltype, computeEltype.compute, h, unwrapVararg, paramType]
  · intro parameters hv
    simp [frontType, isTupleDataType, hv, typeParameters, List.dropLast_eq_take]
  · intro name T h
    simp [tupleTypeTail, h, Except.map]
  · intro name T U h
    simp [tupleTypeTail, h, Except.map]
  · intro A B A' B' hA hB
    simp [tupleTypeTail, hA, hB, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro T ht hu hb
    cases T <;> simp_all [isTupleDataType, tupleTypeTail]
  · intro α typeof ops t; rfl
  · intro ops T; rfl

def SafeLookupOutside : Prop :=
  ∀ (α : Type) (t : List α) (i : Int),
    ¬ (1 ≤ i ∧ i ≤ t.length) → safeGetindex t i = none

theorem safeLookupOutside : SafeLookupOutside := by
  intro α t i hi
  unfold safeGetindex
  by_cases hp : 1 ≤ i
  · rw [if_pos hp]
    exact List.getElem?_eq_none (by omega)
  · simp [hp]

def ComputedElementSound : Prop :=
  ∀ (α : Type) (ops : EltypeInterface) (Checks : α → TupleType → Prop),
    (∀ x, Checks x .any) →
    (∀ x A B, Checks x A ∨ Checks x B → Checks x (ops.join A B)) →
    ∀ (parameters : List TupleParam) (x : α),
      ops.free (.tuple parameters) = false →
      (∀ parameter ∈ parameters, ∃ T, paramType (unwrapVararg parameter) = some T) →
      (∃ parameter ∈ parameters, ∃ T,
        paramType (unwrapVararg parameter) = some T ∧ Checks x T) →
      Checks x (computeEltype ops.free ops.join (.tuple parameters))

theorem computedElementSound : ComputedElementSound := by
  intro α ops Checks hany hjoin parameters x hclosed htypes hx
  cases parameters with
  | nil => simp at hx
  | cons first rest =>
    obtain ⟨T, hT⟩ := htypes first (by simp)
    have hrest : ∀ parameter ∈ rest, ∃ T, paramType (unwrapVararg parameter) = some T :=
      fun p hp => htypes p (by simp [hp])
    simp only [computeEltype, computeEltype.compute, id_eq, hclosed,
      Bool.false_eq_true, ↓reduceIte, hT]
    have combine : ∀ (ps : List TupleParam) (result : TupleType),
        (∀ p ∈ ps, ∃ T, paramType (unwrapVararg p) = some T) →
        (Checks x result ∨ ∃ p ∈ ps, ∃ T, paramType (unwrapVararg p) = some T ∧ Checks x T) →
        Checks x (computeEltype.combine ops.join id result ps) := by
      intro ps
      induction ps with
      | nil =>
        intro result _ hs
        simpa [computeEltype.combine] using hs
      | cons p ps ih =>
        intro result hps hs
        obtain ⟨E, hE⟩ := hps p (by simp)
        by_cases ha : result = .any
        · subst result
          simpa [computeEltype.combine] using hany x
        · have step : computeEltype.combine ops.join id result (p :: ps) =
              computeEltype.combine ops.join id (ops.join E result) ps := by
            cases result <;> simp_all [computeEltype.combine]
          rw [step]
          apply ih _ (fun q hq => hps q (by simp [hq]))
          rcases hs with hr | ⟨q, hq, F, hF, hxF⟩
          · exact Or.inl (hjoin x E result (Or.inr hr))
          · rcases List.mem_cons.mp hq with hq | hq
            · subst q
              have heq : E = F := Option.some.inj (hE.symm.trans hF)
              subst F
              exact Or.inl (hjoin x E result (Or.inl hxF))
            · exact Or.inr ⟨q, hq, F, hF, hxF⟩
    apply combine rest T hrest
    obtain ⟨p, hp, E, hE, hxE⟩ := hx
    rcases List.mem_cons.mp hp with hp | hp
    · subst p
      have heq : T = E := Option.some.inj (hT.symm.trans hE)
      subst E
      exact Or.inl hxE
    · exact Or.inr ⟨p, hp, E, hE, hxE⟩

def FullTupleTypeMethodsCorrect : Prop :=
  TupleTypeMethodsCorrect ∧ ElementTypeCorrect ∧ FrontTypeFallbackCorrect ∧
  ReflectionCasesCorrect ∧ ComputedElementSound

theorem fullTupleTypeMethodsCorrect : FullTupleTypeMethodsCorrect :=
  ⟨tupleTypeMethodsCorrect, elementTypeCorrect, frontTypeFallbackCorrect,
    reflectionCasesCorrect, computedElementSound⟩

def FullTupleBasicsCorrect : Prop := TupleBasicsCorrect ∧ IntegerSteppingCorrect ∧
  SafeLookupOutside ∧ isemptyEmpty = true ∧
  ∀ (α : Type) (a : α) (rest : List α), isemptyNonempty (a :: rest) = false

theorem fullTupleBasicsCorrect : FullTupleBasicsCorrect :=
  ⟨tupleBasicsCorrect, integerSteppingCorrect, safeLookupOutside, rfl, fun _ _ _ => rfl⟩


inductive IterTrace {α σ : Type} (itr : Iter α σ) : Option σ → List α → Prop where
  | nil (state) : IterTrace itr state []
  | cons {state value next rest} :
      iterAt itr state = .ok (some (value, next)) →
      IterTrace itr (some next) rest → IterTrace itr state (value :: rest)

def convertedFields {α : Type} (hasType : α → TupleType → Bool)
    (convert : TupleType → α → R α) (fields : List TupleType) (values : List α) : R (List α) :=
  (fields.zip values).mapM fun (field, value) =>
    if hasType value field then .ok value else convert field value

theorem totupleContinueTrace {α σ : Type} [ToString TupleType]
    (hasType : α → TupleType → Bool) (convert : TupleType → α → R α)
    (fieldtype : TupleType → Nat → TupleType) (rest : Iter α σ → σ → Iter α σ)
    (collectTyped : TupleType → Iter α σ → R (List α)) (collectAny : Iter α σ → R (List α))
    (hfield : ∀ field fields, fieldtype (.tuple ((field :: fields).map .type)) 1 = field)
    (itr : Iter α σ) (fields : List TupleType) :
    ∀ state values, fields.length = values.length → IterTrace itr (some state) values →
      totupleContinue hasType convert fieldtype rest collectTyped collectAny fields.length itr
        (.tuple (fields.map .type)) state = convertedFields hasType convert fields values := by
  induction fields with
  | nil =>
    intro state values hlen _
    have hv : values = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst values
    simp [totupleContinue, totupleEmpty, convertedFields]
    rfl
  | cons field fields ih =>
    intro state values hlen htrace
    cases values with
    | nil => simp at hlen
    | cons value values =>
      cases htrace with
      | cons hfirst hrest =>
        have hl : fields.length = values.length := by simpa using hlen
        have hfield' : fieldtype (.tuple (.type field :: fields.map .type)) 1 = field :=
          hfield field fields
        simp only [totupleContinue, List.map_cons, List.length_cons, totupleFixed,
          splatArgs, hfield', iterAt] at hfirst ⊢
        rw [hfirst]
        simp only [Bind.bind, Except.bind]
        have htype : tupleTypeTail (.tuple (.type field :: fields.map .type)) =
            .ok (.tuple (fields.map .type)) := by rfl
        rw [htype]
        simp only [Except.bind]
        rw [ih _ values hl hrest]
        unfold convertedFields
        simp only [List.zip_cons_cons, List.mapM_cons]
        cases hvalue : (if hasType value field then (.ok value : R α) else convert field value) <;>
          simp [hvalue, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem totupleFixedTrace {α σ : Type} {types : List Type} [ToString TupleType]
    (hasType : α → TupleType → Bool) (convert : TupleType → α → R α)
    (fieldtype : TupleType → Nat → TupleType) (rest : Iter α σ → σ → Iter α σ)
    (collectTyped : TupleType → Iter α σ → R (List α)) (collectAny : Iter α σ → R (List α))
    (hfield : ∀ field fields, fieldtype (.tuple ((field :: fields).map .type)) 1 = field)
    (iterate : Iter α σ → CurriedArgs types (R (Option (α × σ))))
    (itr : Iter α σ) (states : ArgPack types) (field : TupleType) (fields : List TupleType)
    (value : α) (nextState : σ) (values : List α)
    (hfirst : splatArgs (iterate itr) states = .ok (some (value, nextState)))
    (hlen : fields.length = values.length) (htrace : IterTrace itr (some nextState) values) :
    totupleFixed hasType convert fieldtype rest collectTyped collectAny (fields.length + 1)
      iterate itr (.tuple ((field :: fields).map .type)) states =
        convertedFields hasType convert (field :: fields) (value :: values) := by
  simp only [totupleFixed, hfield, hfirst, Bind.bind, Except.bind]
  have htype : tupleTypeTail (.tuple ((field :: fields).map .type)) =
      .ok (.tuple (fields.map .type)) := by rfl
  rw [htype]
  simp only [Except.bind]
  rw [totupleContinueTrace hasType convert fieldtype rest collectTyped collectAny hfield
    itr fields nextState values hlen htrace]
  unfold convertedFields
  simp only [List.zip_cons_cons, List.mapM_cons]
  cases hvalue : (if hasType value field then (.ok value : R α) else convert field value) <;>
    simp [hvalue, Bind.bind, Except.bind, Pure.pure, Except.pure]

def TupleConstructionCorrect : Prop :=
  ∀ [ToString TupleType],
  (∀ (α : Type) (isT : List α → Bool) convert x, isT x = true → tupleTypeCall isT convert x = .ok x) ∧
  (∀ (α β : Type) (getindex : β → R α) x value,
    getindex x = .ok value → tupleRef getindex x = .ok [value] ∧ tupleArray0 getindex x = .ok [value]) ∧
  (∀ (α σ : Type) (take : Iter α σ → Nat → Iter α σ)
    (collect : TupleType → Iter α σ → R (List α)) T E N itr result,
    totupleLong take collect T E N itr = .ok result → result.length = N + 32) ∧
  (∀ (α : Type) (values : List α),
    totupleArrayFast values = values ∧ totupleSimpleVectorFast values = values ∧
      totupleNamedTupleFast values = values) ∧
  (∀ (α : Type) (first second : α), totuplePairFast first second = [first, second]) ∧
  (∀ (α : Type) x, totupleNumberFast (α := α) x = [x]) ∧
  (∀ (α σ : Type) (types : List Type) (itr : Iter α σ) (states : ArgPack types),
    totupleEmpty itr states = [])

theorem tupleConstructionCorrect : TupleConstructionCorrect := by
  intro showType
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α isT convert x h
    simp [tupleTypeCall, h]
  · intro α β getindex x value h
    simp [tupleRef, tupleArray0, h, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro α σ take collect T E N itr result h
    unfold totupleLong at h
    cases hc : collect E (take itr (N + 32)) with
    | error e => simp [hc, Bind.bind, Except.bind] at h
    | ok values =>
      simp only [hc, Bind.bind, Except.bind] at h
      by_cases hl : values.length = N + 32
      · have hv : values = result := by simpa [hl] using h
        subst result
        exact hl
      · simp [hl, totupleError, argErr] at h
  · intro α values; exact ⟨rfl, rfl, rfl⟩
  · intro α first second; rfl
  · intro α x; rfl
  · intro α σ types itr states; rfl

def TupleConversionCorrect : Prop :=
  ∀ (α : Type) (isT : List α → Bool) (convert : List α → R (List α)),
    (∀ xs ys, convert xs = .ok ys → isT ys = true) →
    (∀ xs ys, tupleTypeCall isT convert xs = .ok ys → isT ys = true) ∧
    (∀ xs ys, isT xs = false → convert xs = .ok ys →
      tupleTypeCall isT convert xs = .ok ys) ∧
    (∀ xs e, isT xs = false → convert xs = .error e →
      tupleTypeCall isT convert xs = .error e)

theorem tupleConversionCorrect : TupleConversionCorrect := by
  intro α isT convert hconvert
  refine ⟨?_, ?_, ?_⟩
  · intro xs ys h
    unfold tupleTypeCall at h
    split at h
    · rename_i ht
      have heq : xs = ys := Except.ok.inj h
      simpa [← heq] using ht
    · exact hconvert xs ys h
  · intro xs ys ht hc
    simpa [tupleTypeCall, ht] using hc
  · intro xs e ht hc
    simpa [tupleTypeCall, ht] using hc

inductive CompleteIterTrace {α σ : Type} (itr : Iter α σ) : Option σ → List α → Prop where
  | nil {state} : iterAt itr state = .ok none → CompleteIterTrace itr state []
  | cons {state value next rest} :
      iterAt itr state = .ok (some (value, next)) →
      CompleteIterTrace itr (some next) rest → CompleteIterTrace itr state (value :: rest)

theorem mapMResultLength {α β : Type} (f : α → R β) (xs : List α) :
    ∀ ys, xs.mapM f = .ok ys → ys.length = xs.length := by
  induction xs with
  | nil =>
    intro ys h
    simpa using congrArg List.length (Except.ok.inj h).symm
  | cons x xs ih =>
    intro ys h
    cases hx : f x with
    | error e => simp [List.mapM_cons, hx, Bind.bind, Except.bind] at h
    | ok value =>
      cases hr : xs.mapM f with
      | error e => simp [List.mapM_cons, hx, hr, Bind.bind, Except.bind] at h
      | ok rest =>
        have heq : value :: rest = ys := by
          simpa [List.mapM_cons, hx, hr, Bind.bind, Except.bind, Pure.pure, Except.pure] using h
        subst ys
        simpa using congrArg Nat.succ (ih rest hr)


def VariadicTupleConstructionCorrect : Prop :=
  ∀ [ToString TupleType], ∀ (α σ : Type) (types : List Type)
    (hasType : α → TupleType → Bool) (convert : TupleType → α → R α)
    (fieldtype : TupleType → Nat → TupleType) (rest1 : Iter α σ → σ → Iter α σ)
    (iterate : Iter α σ → CurriedArgs types (R (Option (α × σ))))
    (rest : Iter α σ → CurriedArgs types (Iter α σ))
    (collectTyped : TupleType → Iter α σ → R (List α))
    (collectAny : Iter α σ → R (List α)),
    (∀ field fields, fieldtype (.tuple ((field :: fields).map .type)) 1 = field) →
    (∀ E itr values, CompleteIterTrace itr none values →
      collectTyped E itr = values.mapM (convert E)) →
    (∀ itr values, CompleteIterTrace itr none values → collectAny itr = .ok values) →
    (∀ E itr states values, CompleteIterTrace (splatArgs (rest itr) states) none values →
      totupleVararg (types := types) rest collectTyped E itr states = values.mapM (convert E) ∧
      totupleAny (types := types) rest collectAny itr states = .ok values) ∧
    (∀ count T itr states, splatArgs (iterate itr) states = .ok none →
      totupleFixed hasType convert fieldtype rest1 collectTyped collectAny (count + 1) iterate itr T states =
        argErr s!"too few elements for tuple type {T}") ∧
    (∀ field fields itr states value nextState values,
      splatArgs (iterate itr) states = .ok (some (value, nextState)) →
      fields.length = values.length → IterTrace itr (some nextState) values →
      totupleFixed hasType convert fieldtype rest1 collectTyped collectAny (fields.length + 1) iterate itr
        (.tuple ((field :: fields).map .type)) states =
      convertedFields hasType convert (field :: fields) (value :: values))

theorem variadicTupleConstructionCorrect : VariadicTupleConstructionCorrect := by
  intro showType α σ types hasType convert fieldtype rest1 iterate rest collectTyped collectAny
    hfield htyped hany
  refine ⟨?_, ?_, ?_⟩
  · intro E itr states values htrace
    exact ⟨htyped E (splatArgs (rest itr) states) values htrace,
      hany (splatArgs (rest itr) states) values htrace⟩
  · intro count T itr states h
    simp [totupleFixed, h, totupleError, Bind.bind, Except.bind]
  · intro field fields itr states value nextState values hfirst hlen htrace
    exact totupleFixedTrace hasType convert fieldtype rest1 collectTyped collectAny hfield
      iterate itr states field fields value nextState values hfirst hlen htrace

def TupleWrapperCorrect : Prop :=
  ∀ [ToString TupleType], ∀ (α σ : Type) (hasType : α → TupleType → Bool)
    (convert : TupleType → α → R α) (fieldtype : TupleType → Nat → TupleType)
    (nfields : TupleType → Nat) (rest0 : Iter α σ → Iter α σ) (rest1 : Iter α σ → σ → Iter α σ)
    (take : Iter α σ → Nat → Iter α σ) (collectTyped : TupleType → Iter α σ → R (List α))
    (collectAny : Iter α σ → R (List α)),
    (∀ field fields, fieldtype (.tuple ((field :: fields).map .type)) 1 = field) →
    (∀ fields : List TupleType, nfields (.tuple (fields.map .type)) = fields.length) →
    (∀ (fields : List TupleType) itr values, fields.length = values.length → IterTrace itr none values →
      tupleFromIterator hasType convert fieldtype nfields rest0 rest1 take collectTyped collectAny
        (.tuple (fields.map .type)) itr = convertedFields hasType convert fields values) ∧
    (∀ E itr values, E ≠ .any → collectTyped E (rest0 itr) = .ok values →
      tupleFromIterator hasType convert fieldtype nfields rest0 rest1 take collectTyped collectAny
        (.tuple [.vararg E none]) itr = .ok values) ∧
    (∀ itr values, collectAny (rest0 itr) = .ok values →
      tupleFromIterator hasType convert fieldtype nfields rest0 rest1 take collectTyped collectAny
        (.tuple [.vararg .any none]) itr = .ok values)

theorem tupleWrapperCorrect : TupleWrapperCorrect := by
  intro showType α σ hasType convert fieldtype nfields rest0 rest1 take collectTyped collectAny hfield hcount
  refine ⟨?_, ?_, ?_⟩
  · intro fields itr values hlen htrace
    cases fields with
    | nil =>
      have hv : values = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
      subst values
      simp [tupleFromIterator, totupleDispatch, totupleEmpty, convertedFields]
      rfl
    | cons field fields =>
      cases values with
      | nil => simp at hlen
      | cons value values =>
        cases htrace with
        | cons hfirst hrest =>
          have hl : fields.length = values.length := by simpa using hlen
          have hf := totupleFixedTrace (types := []) hasType convert fieldtype rest1 collectTyped collectAny
            hfield (fun itr => itr.first) itr .nil field fields value _ values hfirst hl hrest
          have hc : nfields (.tuple (.type field :: fields.map .type)) = fields.length + 1 := by
            simpa using hcount (field :: fields)
          simpa [tupleFromIterator, totupleDispatch, hc, List.length_cons] using hf
  · intro E itr values hE hcollect
    cases E <;> simp_all [tupleFromIterator, totupleDispatch, totupleVararg, splatArgs,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  · intro itr values hcollect
    simp [tupleFromIterator, totupleDispatch, totupleAny, splatArgs, hcollect,
      Bind.bind, Except.bind, Pure.pure, Except.pure]

def TupleLongConstructionCorrect : Prop :=
  ∀ [ToString TupleType], ∀ (α σ : Type) (take : Iter α σ → Nat → Iter α σ)
    (collect : TupleType → Iter α σ → R (List α)) (convert : TupleType → α → R α),
    (∀ E itr values, CompleteIterTrace itr none values → collect E itr = values.mapM (convert E)) →
    ∀ T E N itr values, CompleteIterTrace (take itr (N + 32)) none values →
      totupleLong take collect T E N itr =
        match values.mapM (convert E) with
        | .error e => .error e
        | .ok output => if values.length = N + 32 then .ok output
          else argErr s!"too few elements for tuple type {T}"

theorem tupleLongConstructionCorrect : TupleLongConstructionCorrect := by
  intro showType α σ take collect convert htyped T E N itr values htrace
  unfold totupleLong
  dsimp only
  rw [htyped E (take itr (N + 32)) values htrace]
  cases hm : values.mapM (convert E) with
  | error e => rfl
  | ok output =>
    have hl : output.length = values.length := mapMResultLength (convert E) values output hm
    by_cases hlen : values.length = N + 32 <;>
      simp [Bind.bind, Except.bind, hl, hlen, totupleError]

def FullTupleConstructionCorrect : Prop :=
  TupleConstructionCorrect ∧ TupleConversionCorrect ∧ VariadicTupleConstructionCorrect ∧
    TupleWrapperCorrect ∧ TupleLongConstructionCorrect

theorem fullTupleConstructionCorrect : FullTupleConstructionCorrect :=
  ⟨tupleConstructionCorrect, tupleConversionCorrect, variadicTupleConstructionCorrect,
    tupleWrapperCorrect, tupleLongConstructionCorrect⟩

theorem tupleWrapCongr (t : IntTy) {a b : Int}
    (h : a % ((2 ^ t.bits : Nat) : Int) = b % ((2 ^ t.bits : Nat) : Int)) :
    wrapInt t a = wrapInt t b := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] at h ⊢ <;>
    simp at h ⊢ <;> omega

theorem tupleWrapMod (t : IntTy) (z : Int) :
    wrapInt t z % ((2 ^ t.bits : Nat) : Int) = z % ((2 ^ t.bits : Nat) : Int) := by
  cases t <;> simp only [wrapInt, IntTy.signed, IntTy.bits] <;> simp <;> omega

theorem tupleWrapMulLeft (t : IntTy) (a b : Int) :
    wrapInt t (wrapInt t a * b) = wrapInt t (a * b) :=
  tupleWrapCongr t (by rw [Int.mul_emod, tupleWrapMod, ← Int.mul_emod])

theorem foldProductValue (xs : List (JInt .i64)) (acc : JInt .i64) :
    (xs.foldl (· * ·) acc).val = wrapInt .i64 (acc.val * (xs.map (fun x => x.val)).prod) := by
  induction xs generalizing acc with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.prod_nil, Int.mul_one]
    exact (wrapInt_of_inRange .i64 acc.val acc.property).symm
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    change wrapInt .i64 (wrapInt .i64 (acc.val * x.val) * (xs.map (fun v => v.val)).prod) =
      wrapInt .i64 (acc.val * (x.val * (xs.map (fun v => v.val)).prod))
    rw [tupleWrapMulLeft, Int.mul_assoc]

def TupleProductCorrect : Prop :=
  ∀ (multiply : List (JInt .i64) → JInt .i64),
    (∀ first rest, multiply (first :: rest) = rest.foldl (· * ·) first) →
    ∀ t : List (JInt .i64),
      prodTupleMethod multiply t = .ok (JInt.lit .i64 ((t.map (fun x => x.val)).prod))

theorem tupleProductCorrect : TupleProductCorrect := by
  intro multiply hmul t
  cases t with
  | nil => rfl
  | cons x xs =>
    change (Except.ok (multiply (x :: xs)) : R (JInt .i64)) =
      Except.ok (JInt.lit .i64 (((x :: xs).map (fun v => v.val)).prod))
    rw [hmul]
    apply congrArg Except.ok
    apply Subtype.ext
    exact foldProductValue xs x

def rotateRight {α : Type} (t : List α) (shift : Nat) : List α :=
  t.drop (t.length - shift) ++ t.take (t.length - shift)

theorem rotateRightLength {α : Type} (t : List α) (shift : Nat) (hs : shift ≤ t.length) :
    (rotateRight t shift).length = t.length := by
  simp only [rotateRight, List.length_append, List.length_drop, List.length_take]
  omega

theorem getindexIntValue {α : Type} (t : List α) (i : JInt .i64) :
    getindexInt t i = getfield t i.val := rfl

theorem getindexIntNat {α : Type} (t : List α) (k : Nat)
    (hk : k < t.length) (hlen : t.length < 2 ^ 62) :
    getindexInt t (JInt.lit .i64 ((k : Int) + 1)) = .ok t[k] := by
  have hv := i64NatValue (k + 1) (by omega)
  simp only [Int.natCast_add, Int.natCast_one] at hv
  rw [getindexIntValue, hv]
  exact getfieldInBounds t k hk

theorem circshiftLongRotation {α : Type} (mod1 : Int → Nat → Nat)
    (ntuple : (Nat → R α) → Nat → R (List α))
    (hntuple : ∀ f n, ntuple f n = (List.range n).mapM fun i => f (i + 1))
    (t : List α) (shift : Int) (hl : 3 ≤ t.length) (hlen : t.length < 2 ^ 62)
    (hj : 1 ≤ mod1 shift t.length ∧ mod1 shift t.length ≤ t.length) :
    circshiftTupleLong mod1 ntuple t shift hl =
      .ok (rotateRight t (mod1 shift t.length)) := by
  let j := mod1 shift t.length
  have hj1 : 1 ≤ j := hj.1
  have hj2 : j ≤ t.length := hj.2
  have hrot := rotateRightLength t j hj2
  have hd : (t.drop (t.length - j)).length = j := by simp; omega
  unfold circshiftTupleLong
  rw [hntuple]
  apply mapM_range_ok _ _ _ hrot
  intro k hk
  have hkt : k < t.length := by omega
  change getindexInt t (JInt.lit .i64 (((k + 1 : Nat) : Int) - (j : Int) +
    if k + 1 > j then 0 else (t.length : Int))) = .ok (rotateRight t j)[k]
  by_cases hkj : k < j
  · have hb : ¬ k + 1 > j := by omega
    rw [if_neg hb]
    have hidx : (((k + 1 : Nat) : Int) - (j : Int) + (t.length : Int)) =
        ((t.length - j + k : Nat) : Int) + 1 := by omega
    rw [hidx, getindexIntNat t (t.length - j + k) (by omega) hlen]
    unfold rotateRight at hk ⊢
    rw [List.getElem_append_left (by omega), List.getElem_drop]
  · have hb : k + 1 > j := by omega
    rw [if_pos hb]
    have hidx : (((k + 1 : Nat) : Int) - (j : Int) + 0) =
        ((k - j : Nat) : Int) + 1 := by omega
    rw [hidx, getindexIntNat t (k - j) (by omega) hlen]
    unfold rotateRight at hk ⊢
    rw [List.getElem_append_right (by omega), List.getElem_take]
    simp only [hd]

def CircshiftCorrect : Prop :=
  (∀ (α : Type) (t : List α) shift hsmall,
    circshiftTupleSmall t shift hsmall = t) ∧
  (∀ (α : Type) (iseven : Int → Bool),
    (∀ z, iseven z = decide (z % 2 = 0)) → ∀ (t : List α) shift hlen,
    circshiftTupleTwo iseven t shift hlen = if shift % 2 = 0 then t else t.reverse) ∧
  (∀ (α : Type) (mod1 : Int → Nat → Nat),
    (∀ s n, 0 < n → 1 ≤ mod1 s n ∧ mod1 s n ≤ n ∧
      (mod1 s n : Int) % (n : Int) = s % (n : Int)) →
    ∀ (ntuple : (Nat → R α) → Nat → R (List α)),
      (∀ f n, ntuple f n = (List.range n).mapM fun i => f (i + 1)) →
    ∀ (t : List α) (shift : Int) (hl : 3 ≤ t.length), t.length < 2 ^ 62 →
      circshiftTupleLong mod1 ntuple t shift hl =
        .ok (rotateRight t (mod1 shift t.length)))

theorem circshiftCorrect : CircshiftCorrect := by
  refine ⟨?_, ?_, ?_⟩
  · intro α t shift h
    rfl
  · intro α iseven heven t shift h
    simp only [circshiftTupleTwo, heven, decide_eq_true_eq, reverseCorrect α t]
  · intro α mod1 hmod ntuple hntuple t shift hl hlen
    have hm := hmod shift t.length (by omega)
    exact circshiftLongRotation mod1 ntuple hntuple t shift hl hlen ⟨hm.1, hm.2.1⟩

/-! ## Property registry coverage -/

private def entry (id : String) (functions statement source : String) (status : Status)
    (prop : Lean.Name) (proofName : Option Lean.Name) (issue : String := "") : Entry :=
  { id := id, juliaFile := "base/tuple.jl", juliaFns := functions.splitOn ", "
    statement := statement, source := source, status := status, prop := prop,
    thm := proofName, issue := issue }

def entries : List Entry := [
  entry "tuples-split-rest-state" "split_rest(t::Tuple, n, i), _split_tuple"
    "Base.split_rest promises the tail starting at itr_state, partitioned into all but its last n elements and its last n elements; a short remainder must raise ArgumentError."
    "Base.split_rest docstring, base/tuple.jl:215-246,265-267"
    .refuted ``SplitRestAgrees (some ``splitRestAgrees_refuted)
    "Existing refutation retained in repro/tuples-split-rest-state.jl",
  entry "tuples-getindex-bool" "getindex(t::Tuple, i::Integer), setindex(t::Tuple, v, i::Integer), get(t::Tuple, i::Integer, default), isassigned(v::Tuple, i::Integer)"
    "Scalar-index consistency promise from Base.to_index: Bool is rejected with ArgumentError by indexing and its set, get, and isassigned counterparts. This claim is refuted for tuples."
    "base/indices.jl:259; base/tuple.jl:34,40,55-64,681-684"
    .refuted ``BoolIndexAgrees (some ``boolIndexAgrees_refuted)
    "Existing refutation retained in repro/tuples-getindex-bool.jl",
  entry "tuples-bool-index-accepted" "getindex(t::Tuple,i::Integer), get(t::Tuple,i::Integer,default), setindex(t::Tuple,v,i::Integer), _setindex, isassigned(v::Tuple,i::Integer)"
    "Bool tuple indices use the integer values zero and one; get returns its default outside bounds, isassigned tests bounds, and setindex preserves every unselected field."
    "base/tuple.jl:34,40,55-64,681-684"
    .proven ``BoolAcceptedCorrect (some ``boolAcceptedCorrect),
  entry "tuples-getindex-inexact" "getindex(t::Tuple, i::Integer)"
    "Bounds-error consistency promise: every out-of-bounds Integer index raises BoundsError, as the tuple setindex docstring promises. This includes unrepresentable UInt indices and is refuted for getindex."
    "base/tuple.jl:34,43-54; Julia manual indexing rules"
    .refuted ``GetindexBoundsError (some ``getindexBoundsError_refuted)
    "Existing refutation retained in repro/tuples-getindex-inexact.jl",
  entry "tuples-prod-empty" "prod(x::Tuple{}), prod(x::Tuple{Int,Vararg{Int}})"
    "Product-reduction consistency promise: prod(t) agrees with prod(identity,t), including an empty tuple with no reduction identity. The statement calls the source-mirrored generic prod."
    "base/reduce.jl (prod reduction behavior); base/tuple.jl:688,693"
    .refuted ``ProdAgrees (some ``prodAgrees_refuted)
    "Existing refutation retained in repro/tuples-prod-empty.jl",
  entry "tuples-product-value" "prod(x::Tuple{}), prod(x::Tuple{Int,Vararg{Int}})"
    "Tuple product is the mathematical product reduced to the signed 64-bit range; the empty product is one."
    "base/tuple.jl:688,693; prod docstring and integer overflow semantics"
    .proven ``TupleProductCorrect (some ``tupleProductCorrect),
  entry "tuples-reverse" "reverse(t::Tuple), revargs() , revargs(x, r...)"
    "Tuple reversal returns all elements in reverse order."
    "base/tuple.jl:668-671"
    .proven ``ReverseCorrect (some ``reverseCorrect),
  entry "tuples-front-tail" "front(t::Tuple), front(t::NTuple{32,Any}), front(t::Any32), first(::Tuple{}), first(t::Tuple)"
    "front returns all but the last element, and first returns the first element or throws for an empty tuple."
    "base/tuple.jl:270-271,344-384; base/essentials.jl:523-542"
    .proven ``FullFrontCorrect (some ``fullFrontCorrect),
  entry "tuples-integer-index" "getindex(t::Tuple, i::Int), getindex(t::Tuple, i::Integer), setindex(t::Tuple, v, i::Integer), get(t::Tuple, i::Integer, default), isassigned(v::Tuple, i::Integer)"
    "For every fixed-width or BigInt index, tuple indexing returns the selected value or the documented conversion/bounds error; get defaults out of bounds, isassigned tests bounds, and setindex preserves unselected fields."
    "base/tuple.jl:33-34,40,55-64,681-684"
    .proven ``IntegerOperationsCorrect (some ``integerOperationsCorrect),
  entry "tuples-map" "map(f, t::Tuple{}), map(f, t::Tuple{Any}), map(f, t::Tuple{Any,Any}), map(f, t::Tuple{Any,Any,Any}), map(f, t::Tuple), map(f, t::Any32), map(f, t::Tuple,s::Tuple), map(f, t::Any32,s::Any32)"
    "Mapping one tuple preserves its length and order; mapping two tuples applies f to corresponding fields up to the shorter length."
    "base/tuple.jl:358-419"
    .proven ``MapCorrect (some ``mapCorrect),
  entry "tuples-find-filter" "findfirst(f::Function,t::Tuple), findlast(f::Function,t::Tuple), filter(f,t::Tuple)"
    "findfirst and findlast return the first and last matching indices, and filter keeps matching values in order."
    "base/tuple.jl:522-549"
    .proven ``FindFilterCorrect (some ``findFilterCorrect),
  entry "tuples-equality" "isequal(t1::Tuple,t2::Tuple), _isequal, ==(t1::Tuple,t2::Tuple), _eq, _eq_missing"
    "Tuple isequal is true exactly when lengths and all corresponding fields agree; tuple == combines three-valued field comparisons, with false taking precedence over missing."
    "base/tuple.jl:553-599"
    .proven ``EqualityCorrect (some ``equalityCorrect),
  entry "tuples-internal-comparison-errors" "_isequal(t1::Tuple,t2::Tuple), _isequal(t1::Any32,t2::Any32), _eq(t1::Tuple,t2::Tuple), _eq_missing, _eq(t1::Any32,t2::Any32)"
    "Internal long-tuple comparisons reject mismatched eachindex lengths, and recursive comparisons preserve the dispatch or bounds error when one tuple ends first."
    "base/tuple.jl:554-565,568-599; eachindex mismatch contract"
    .proven ``InternalComparisonErrors (some ``internalComparisonErrors),
  entry "tuples-hash-isequal" "hash(t::Tuple,h::UInt), hash(t::Any32,h::UInt)"
    "When element hashing agrees on isequal values, isequal tuples have equal hashes for every seed."
    "hash docstring; base/tuple.jl:602-610"
    .proven ``HashIsequal (some ``hashIsequal),
  entry "hashops-tuple-hash" "hash(t::Tuple,h::UInt), hash(t::Any32,h::UInt), isequal(t1::Tuple,t2::Tuple)"
    "Tuples with corresponding isequal fields hash equally for every initial seed."
    "hash docstring; base/tuple.jl:553-565,602-610"
    .proven ``TupleHashConsistency (some ``tupleHashConsistency_proven),
  entry "tuples-lt-lexicographic" "<(::Tuple{},::Tuple{}), <(::Tuple{},::Tuple), <(::Tuple,::Tuple{}), <(t1::Tuple,t2::Tuple), <(t1::Any32,t2::Any32)"
    "The first unequal or missing field comparison decides tuple <; equal prefixes are ordered by length."
    "base/tuple.jl:612-637"
    .proven ``LtLexicographic (some ``ltLexicographic),
  entry "tuples-isless-order" "isless(::Tuple{},::Tuple{}), isless(::Tuple{},::Tuple), isless(::Tuple,::Tuple{}), isless(t1::Tuple,t2::Tuple), isless(t1::Any32,t2::Any32)"
    "A strict weak element order with isequal as incomparability induces a strict weak tuple order."
    "base/tuple.jl:639-661; isless docstring"
    .proven ``IslessStrictWeakOrder (some ``islessStrictWeakOrder),
  entry "sorttuplescov-split-rest" "split_rest(itr,n::Int,state...), _split_rest(itr,n::Int), _check_length_split_rest, _split_rest(a::Union{AbstractArray,Core.SimpleVector},n::Int)"
    "Splitting a finite remainder partitions it into its prefix and last n elements; too few elements and infinite iterators raise ArgumentError."
    "Base.split_rest docstring; base/tuple.jl:215-263"
    .proven ``SplitRestCorrect (some ``splitRestCorrect),
  entry "sorttuplescov-rest" "rest(t::Tuple), rest(t::Tuple,i), rest(a::Union{Array,Memory,Core.SimpleVector},i)"
    "Tuple and array rest return the suffix beginning at i, with rest(t) returning the full tuple."
    "Base.rest docstring; base/tuple.jl:174-213"
    .proven ``RestCorrect (some ``restCorrect),
  entry "sorttuplescov-tuple-basics" "length, firstindex, lastindex, size, axes, getindex, __safe_getindex, iterate, keys, prevind, nextind, isempty, empty, safe_tail"
    "Tuple length, one-based axes and keys, indexing, iteration, index stepping, emptiness and safe-tail behavior match the one-dimensional collection contract."
    "base/tuple.jl:28-75,145-146,323-324,665-666,712"
    .proven ``FullTupleBasicsCorrect (some ``fullTupleBasicsCorrect),
  entry "sorttuplescov-tuple-index-vec" "getindex(t::Tuple,r::AbstractArray{<:Any,1}), getindex(t::Tuple,b::AbstractArray{Bool,1}), getindex(t::Tuple,c::Colon), get(f::Callable,t::Tuple,i::Integer)"
    "Index vectors select fields in order, Boolean masks select true fields and reject length mismatch, colon returns the tuple, and get invokes its default thunk out of bounds."
    "base/tuple.jl:36-41"
    .proven ``FullTupleIndexVecCorrect (some ``fullTupleIndexVecCorrect),
  entry "sorttuplescov-tuple-iter-protocol" "keys(t::Tuple,t2::Tuple...), indexed_iterate(t::Tuple,i,state), indexed_iterate(a::Union{Array,Memory},i,state), indexed_iterate(I,i), indexed_iterate(I,i,state)"
    "Multiple tuple keys require equal lengths; indexed_iterate yields the indexed value and next state, or BoundsError for exhausted generic iterators."
    "base/tuple.jl:148-172"
    .proven ``FullTupleIterProtocolCorrect (some ``fullTupleIterProtocolCorrect),
  entry "sorttuplescov-map-n-foreach" "heads, tails, anyempty, map(f,t1::Tuple,t2::Tuple,ts::Tuple...), map(f,t1::Any32,t2::Any32,ts::Any32...), foreach"
    "N-argument map stops at the shortest tuple and foreach calls f on values or corresponding zipped values in order."
    "map and foreach behavior; base/tuple.jl:420-439,714-715"
    .proven ``AllMapNCorrect (some ``allMapNCorrect),
  entry "sorttuplescov-sym-in" "sym_in(x::Symbol,itr::Tuple{Vararg{Symbol}}), in(x::Symbol,itr::Tuple{Vararg{Symbol}})"
    "sym_in and in report whether x occurs in the symbol tuple."
    "base/tuple.jl:696-704"
    .proven ``SymInCorrect (some ``symInCorrect),
  entry "sorttuplescov-fill-to-length" "fill_to_length(t::NTuple{N,Any},val,::Val{N}), fill_to_length(t::Tuple{},val,::Val{1}), fill_to_length(t::Tuple{Any},val,::Val{2}), fill_to_length(t::Tuple{},val,::Val{2})"
    "The specialized fill_to_length methods return the original tuple or pad it with val to the requested length."
    "base/tuple.jl:442-445"
    .proven ``FillToLengthSpecialized (some ``fillToLengthSpecialized),
  entry "tuples-circshift" "circshift(t::Tuple{}, shift::Integer), circshift(t::Tuple{Any}, shift::Integer), circshift(t::Tuple{Any,Any}, shift::Integer), circshift(x::Tuple{Any,Any,Any,Vararg{Any,N}}, shift::Integer)"
    "Tuple circshift returns the same elements as a right rotation by shift modulo the tuple length."
    "base/tuple.jl:717-724; circshift docstring"
    .proven ``CircshiftCorrect (some ``circshiftCorrect),
  entry "sorttuplescov-tuple-type-methods" "_counttuple(::Type{<:NTuple{N,Any}}), _counttuple(::Type), _eltype_ntuple, eltype(::Type{<:Tuple}), _compute_eltype, keytype, valtype, tuple_type_tail, _front_type"
    "Tuple type reflection reports tuple arity and element/key/value types, and tuple_type_tail removes one field or one fixed Vararg element."
    "base/tuple.jl:23-24,279-320,453-468"
    .proven ``FullTupleTypeMethodsCorrect (some ``fullTupleTypeMethodsCorrect),
  entry "sorttuplescov-tuple-construction" "(::Type{T})(x::Tuple), Tuple(x::Ref), Tuple(x::Array{T,0}), (::Type{T})(itr), _totuple, _totuple_err"
    "Tuple construction preserves compatible tuples, converts incompatible tuples to their target type, preserves iterator order for fixed, variable-length and generic targets, and reports conversion or insufficient-length errors."
    "base/tuple.jl:470-518"
    .proven ``FullTupleConstructionCorrect (some ``fullTupleConstructionCorrect)
]

end JuliaLean.Proofs.base.tuple

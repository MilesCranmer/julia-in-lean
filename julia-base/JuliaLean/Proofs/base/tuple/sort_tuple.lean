import JuliaLean.base.tuple
import JuliaLean.Proofs.base.tuple.sort_common
/-!
Value-level methods of `base/tuple.jl` (master `bbfa0ce4150`) that the `Tuples`
area does not model: indexing helpers, iteration, `rest` and `split_rest`,
`n`-argument `map`, `foreach`, `sym_in`. A tuple is the `List α` of its
elements (the `Tuples` convention). An iterator is a finite list of the values
it produces (with a flag for `IteratorSize(itr) == IsInfinite()`), a vector is
the `List α` of its elements indexed from 1.
-/

namespace JuliaLean.SortTuplesCov

open JuliaLean
open JuliaLean.Tuples (R Err getfield bounds argErr liftJ Idx getindex getindexColon
  getindexLogical ntupleInt splitRestVector checkLengthSplitRest restTuple indexedIterate
  fillToLength I64)

namespace Tup

variable {α β : Type}

end Tup

open Tup

/-! ## Properties -/

/-- Basic tuple accessors (`base/tuple.jl:28-38,69-75,145-146,323-324,665-666,712`):
`length`, `firstindex`, `lastindex`, `axes` and `keys` describe `1:length(t)`;
`size(t, d)` is `length(t)` for `d == 1` of any `Integer` type and
`ArgumentError` otherwise; `iterate` yields `t[1]`, ..., `t[end]` and then
`nothing`; `prevind`/`nextind` are `Int(i)∓1` (wrapping, `InexactError` outside
`Int`); `__safe_getindex` reads in bounds for `1 ≤ i ≤ length(t)`; `t[:]` is
`t`; `isempty` tests for `()`; `empty` is `()`; `safe_tail` drops the first
element and maps `()` to `()`. -/
def TupleBasicsCorrect : Prop :=
  ∀ (α : Type) (t : List α),
    length t = t.length ∧ firstindex t = 1 ∧ lastindex t = t.length ∧
    axes t = [t.length] ∧ keys t = t.length ∧
    (∀ d : Idx, size t d = if d.val = 1 then .ok t.length else argErr "invalid tuple dimension") ∧
    (∀ i : Int, 1 ≤ i → i ≤ t.length →
      ∃ x, t[(i - 1).toNat]? = some x ∧ iterate t i = .ok (some (x, i + 1)) ∧
        safeGetindex t i = some x) ∧
    (∀ i : Int, ¬ (1 ≤ i ∧ i ≤ t.length) → iterate t i = .ok none) ∧
    (∀ (ty : IntTy) (i : JInt ty), IntTy.i64.min ≤ i.val → i.val ≤ IntTy.i64.max →
      prevind t (.int ty i) = .ok (JInt.wrap .i64 (i.val - 1)) ∧
      nextind t (.int ty i) = .ok (JInt.wrap .i64 (i.val + 1))) ∧
    (∀ (ty : IntTy) (i : JInt ty), ¬ (IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max) →
      prevind t (.int ty i) = .error (.jl (.inexactError "Int64")) ∧
      nextind t (.int ty i) = .error (.jl (.inexactError "Int64"))) ∧
    getindexColonAll t = t ∧ isempty t = t.isEmpty ∧ empty t = [] ∧
    safeTail t = t.tail

/-- Vector and logical indexing of tuples and `get(f, t, i)`
(`base/tuple.jl:36-41`): `t[r]` is the tuple of `t[ri]` in order, or the first
exception among them; `t[b]` for a `Bool` vector of the same length keeps the
elements where `b` is true and throws `BoundsError` for a different length;
`get(f, t, i)` is `t[i]` when `i in 1:length(t)` and `f()` otherwise. -/
def TupleIndexVecCorrect : Prop :=
  ∀ (α : Type) (t : List α), t.length < 2 ^ 62 →
    (∀ r : List Nat, (∀ i ∈ r, 1 ≤ i ∧ i ≤ t.length) →
      getindexVec t (r.map fun (i : Nat) => Idx.int .i64 (JInt.lit .i64 (i : Int))) =
        .ok (r.filterMap fun i => t[i - 1]?)) ∧
    (∀ r : List Nat, (∀ i ∈ r, i < 2 ^ 62) → (∃ i ∈ r, ¬ (1 ≤ i ∧ i ≤ t.length)) →
      ∃ e, getindexVec t (r.map fun (i : Nat) => Idx.int .i64 (JInt.lit .i64 (i : Int))) = .error e) ∧
    (∀ b : List Bool, b.length = t.length →
      getindexLogical t b = .ok ((t.zip b).filterMap fun (x, c) => if c then some x else none)) ∧
    (∀ b : List Bool, b.length ≠ t.length → getindexLogical t b = bounds) ∧
    (∀ (f : Unit → R α) (i : Idx),
      getF f t i = if 1 ≤ i.val ∧ i.val ≤ t.length then getindex t i else f ())

/-- `keys(t, t2...)` (`base/tuple.jl:148-157`) is `OneTo(length(t))` when all
lengths agree and `DimensionMismatch` otherwise; the `indexed_iterate` methods
(`base/tuple.jl:161-172`) return the `i`-th element and `i+1` for tuples and
arrays (`BoundsError` outside `1:length`), and for other iterators the result
of `iterate`, with `BoundsError` at exhaustion. -/
def TupleIterProtocolCorrect : Prop :=
  ∀ (α σ : Type),
    (∀ (n : Nat) (lens : List Nat),
      keysMany n lens = if ∀ m ∈ lens, m = n then some n else none) ∧
    (∀ (t : List α) (i : Nat), 1 ≤ i → i ≤ t.length →
      ∃ x, t[i - 1]? = some x ∧ indexedIterate t i = .ok (x, i + 1) ∧
        indexedIterateArray t i = .ok (x, i + 1)) ∧
    (∀ (t : List α) (i : Nat), ¬ (1 ≤ i ∧ i ≤ t.length) →
      indexedIterate t i = bounds ∧ indexedIterateArray t i = bounds) ∧
    (∀ (I : Iter α σ) i, indexedIterateGen I i = match I.first with
      | none => bounds | some x => .ok x) ∧
    (∀ (I : Iter α σ) i s, indexedIterateGenState I i s = match I.next s with
      | none => bounds | some x => .ok x)

/-- `Base.rest` (`base/tuple.jl:174-213`): `rest(t) = t`; for a tuple and a
valid iteration state `1 ≤ i ≤ length(t)+1`, `rest(t, i)` is the tuple of the
elements from `i` on, a state past the end throws `ArgumentError` and `i < 1`
throws `BoundsError`; for arrays `rest(a, i)` is `a[i:end]` (empty past the end,
`BoundsError` for `i < 1` when elements remain); for other iterators it
iterates from `state`. -/
def RestCorrect : Prop :=
  ∀ (α σ : Type) (t : List α),
    restAll t = t ∧
    (∀ i : Nat, 1 ≤ i → i ≤ t.length + 1 → t.length < 2 ^ 62 →
      restTuple t (JInt.lit .i64 i) = .ok (t.drop (i - 1))) ∧
    (∀ i : Nat, i > t.length + 1 → i < 2 ^ 62 → t.length < 2 ^ 62 →
      ∃ msg, restTuple t (JInt.lit .i64 i) = argErr msg) ∧
    (∀ i : Nat, i ≥ 1 → i < 2 ^ 61 → t.length < 2 ^ 61 →
      restArray t (JInt.lit .i64 i) = .ok (t.drop (i - 1))) ∧
    (∀ i : Int, i < 1 → -2 ^ 61 < i → 0 < t.length → t.length < 2 ^ 61 →
      restArray t (JInt.lit .i64 i) = bounds) ∧
    (∀ (I : Iter α σ), restIter I none = I) ∧
    (∀ (I : Iter α σ) s, (restIter I (some s)).first = I.next s ∧ (restIter I (some s)).next = I.next)

/-- `Base.split_rest` (`base/tuple.jl:215-263`): for every array, vector or
finite iterator and `0 ≤ n ≤` (number of remaining elements) the result is
`(rest_but_n, last_n)` whose concatenation is the remaining elements, with
`last_n` of length `n`; a larger `n` throws `ArgumentError` (the length check),
an infinite iterator throws `ArgumentError`. -/
def SplitRestCorrect : Prop :=
  ∀ (α : Type) (a : List α) (n : Nat), a.length < 2 ^ 62 → n < 2 ^ 62 →
    (n ≤ a.length →
      splitRestArray a (JInt.lit .i64 n) = .ok (a.take (a.length - n), a.drop (a.length - n)) ∧
      splitRestIter false a (JInt.lit .i64 n) =
        .ok ((a.take (a.length - n)).map some, a.drop (a.length - n))) ∧
    (n > a.length →
      (∃ msg, splitRestArray a (JInt.lit .i64 n) = argErr msg) ∧
      (∃ msg, splitRestIter false a (JInt.lit .i64 n) = argErr msg)) ∧
    (∃ msg, splitRestIter true a (JInt.lit .i64 n) = argErr msg) ∧
    checkLengthSplitRest a.length (JInt.lit .i64 n) =
      if a.length < n then argErr "The iterator only contains len elements, but at least n were requested."
      else .ok ()

/-- `map(f, t1, t2, ts...)` with at least three tuples (`base/tuple.jl:420-439`)
applies `f` to the tuples of `k`-th elements and stops at the shortest tuple, as
`map` over vectors does, for short and long tuples; `foreach(f, t)` applies `f`
to the elements in order and `foreach(f, t, ts...)` to the zipped tuples. -/
def MapNForeachCorrect : Prop :=
  ∀ (α β σ : Type) (f : List α → β) (ts : List (List α)), ts.length ≥ 3 →
    (ts.all (fun t => t.length ≥ 32) = false → ∀ K, (∀ t ∈ ts, t.length ≤ K) →
      mapN f ts = .ok ((zipN ts K).map f)) ∧
    (ts.all (fun t => t.length ≥ 32) = true →
      let n := (ts.map List.length).foldl min (ts.headD []).length
      (∀ t ∈ ts, n ≤ t.length) ∧ (∃ t ∈ ts, t.length = n) ∧
      mapN f ts = .ok ((List.range n).map fun i => f (ts.filterMap fun t => t[i]?))) ∧
    (∀ (g : σ → α → σ) s t, foreach g s t = t.foldl g s) ∧
    (∀ (g : σ → List α → σ) s t us, foreachN g s t us = (zipN (t :: us) t.length).foldl g s)

/-- `sym_in(x, itr)` and `x in itr` for a tuple of symbols
(`base/tuple.jl:695-704`) test membership. -/
def SymInCorrect : Prop :=
  ∀ (x : String) (itr : List String), symInLoop x itr = decide (x ∈ itr) ∧ inSym x itr = decide (x ∈ itr)

/-- The specialised `fill_to_length` methods of `base/tuple.jl:442-445` return
`t` for `length(t) == N`, `(val,)` for `((), Val(1))`, `(t..., val)` for a
1-tuple and `Val(2)`, and `(val, val)` for `((), Val(2))`. -/
def FillToLengthSpecialized : Prop :=
  ∀ (α : Type) (t : List α) (v : α) (a : α), t.length < 2 ^ 62 →
    fillToLength t v (JInt.lit .i64 t.length) = .ok t ∧
    fillToLength [] v (JInt.lit .i64 1) = .ok [v] ∧
    fillToLength [a] v (JInt.lit .i64 2) = .ok [a, v] ∧
    fillToLength [] v (JInt.lit .i64 2) = .ok [v, v]

end JuliaLean.SortTuplesCov

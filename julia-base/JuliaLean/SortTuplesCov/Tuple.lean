import JuliaLean.SortTuplesCov.Common

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

/-- `length(t) = nfields(t)`, `firstindex(t) = 1`, `lastindex(t) = length(t)`,
`base/tuple.jl:28-30`. -/
def length (t : List α) : Nat := t.length
def firstindex (_ : List α) : Int := 1
def lastindex (t : List α) : Int := t.length

/-- `d == 1` for an `Integer` `d` (exact mixed comparison; `true == 1`). -/
def idxIsOne : Idx → Bool
  | .int _ v => v.val == 1
  | .bool b => b

/-- `size(t, d::Integer) = (d == 1) ? length(t) : throw(ArgumentError(...))`,
`base/tuple.jl:31`. -/
def size (t : List α) (d : Idx) : R Nat :=
  if idxIsOne d then .ok t.length else argErr "invalid tuple dimension"

/-- `axes(t) = (OneTo(length(t)),)` (`base/tuple.jl:32`) and
`keys(t) = OneTo(length(t))` (`base/tuple.jl:75`): the length of the `OneTo`. -/
def axes (t : List α) : List Nat := [t.length]
def keys (t : List α) : Nat := t.length

/-- `__safe_getindex(t, i::Int) = getfield(t, i, false)`, `base/tuple.jl:35`: the
access is unchecked; `none` marks an out-of-bounds read (undefined behaviour). -/
def safeGetindex (t : List α) (i : Int) : Option α :=
  if 1 ≤ i then t[(i - 1).toNat]? else none

/-- `getindex(t, r::AbstractArray{<:Any,1}) = (eltype(t)[t[ri] for ri in r]...,)`,
`base/tuple.jl:36`, for an index vector `r` of `Integer` values (not `Bool`s,
whose vectors take the method of line 37). -/
def getindexVec (t : List α) (r : List Idx) : R (List α) := r.mapM (getindex t)

/-- `getindex(t, c::Colon) = t`, `base/tuple.jl:38`. -/
def getindexColonAll (t : List α) : List α := t

/-- `i in 1:length(t)` for an `Integer` `i`. -/
def idxInRange (i : Idx) (n : Nat) : Bool := decide (1 ≤ i.val ∧ i.val ≤ n)

/-- `get(f::Callable, t::Tuple, i::Integer) = i in 1:length(t) ? getindex(t, i) : f()`,
`base/tuple.jl:41`; `f()` is the thunk `f`. -/
def getF (f : Unit → R α) (t : List α) (i : Idx) : R α :=
  if idxInRange i t.length then getindex t i else f ()

/-- `iterate(t::Tuple, i::Int=1) = (1 <= i <= length(t)) ? (t[i], i + 1) : nothing`,
`base/tuple.jl:69-73`. -/
def iterate (t : List α) (i : Int := 1) : R (Option (α × Int)) :=
  if 1 ≤ i ∧ i ≤ t.length then do
    let x ← getfield t i
    pure (some (x, i + 1))
  else .ok none

/-- `Int(i)` for an `Integer` `i`: `InexactError` outside `Int`. -/
def idxToInt : Idx → R (JInt .i64)
  | .int _ v => liftJ (JInt.convert .i64 v.val)
  | .bool b => .ok (JInt.lit .i64 (if b then 1 else 0))

/-- `prevind(t, i::Integer) = Int(i)-1` and `nextind(t, i::Integer) = Int(i)+1`,
`base/tuple.jl:145-146` (wrapping `Int` arithmetic). -/
def prevind (_ : List α) (i : Idx) : R (JInt .i64) := do
  let j ← idxToInt i
  pure (j - JInt.lit .i64 1)
def nextind (_ : List α) (i : Idx) : R (JInt .i64) := do
  let j ← idxToInt i
  pure (j + JInt.lit .i64 1)

/-- `keys(t::Tuple, t2::Tuple...)`, `base/tuple.jl:148-157`: `OneTo(length(t))`
when every `t2` has the length of `t`, else `DimensionMismatch` (`none`). The
tuples are given by their lengths. -/
def keysMany (lent : Nat) (lens : List Nat) : Option Nat :=
  if lens.all (· == lent) then some lent else none

/-- `indexed_iterate(a::Union{Array,Memory}, i::Int, state=1) = (a[i], i+1)`,
`base/tuple.jl:162` (checked `a[i]`). -/
def indexedIterateArray (a : List α) (i : Int) : R (α × Int) := do
  let x ← getfield a i
  pure (x, i + 1)

/-- A generic iterator: `iterate(I)` returns `first`, and `iterate(I, state)`
returns `next state`. -/
structure Iter (α σ : Type) where
  first : Option (α × σ)
  next : σ → Option (α × σ)

/-- `indexed_iterate(I, i)`, `base/tuple.jl:163-167`: `iterate(I)`, and
`BoundsError` when it returns `nothing`. -/
def indexedIterateGen {σ : Type} (I : Iter α σ) (_ : Int) : R (α × σ) :=
  match I.first with
  | none => bounds
  | some x => .ok x

/-- `indexed_iterate(I, i, state)`, `base/tuple.jl:168-172`. -/
def indexedIterateGenState {σ : Type} (I : Iter α σ) (_ : Int) (state : σ) : R (α × σ) :=
  match I.next state with
  | none => bounds
  | some x => .ok x

/-- `rest(t::Tuple) = t`, `base/tuple.jl:206`. -/
def restAll (t : List α) : List α := t

/-- `rest(a::Union{Array,Memory,Core.SimpleVector}, i=1) = a[(i::Int):end]`,
`base/tuple.jl:212`. -/
def restArray (a : List α) (i : JInt .i64) : R (List α) :=
  getindexColon a i (JInt.lit .i64 a.length)

/-- `rest(itr, state...) = Iterators.rest(itr, state...)`, `base/tuple.jl:213`:
the lazy iterator that starts from `state` (or from the beginning). -/
def restIter {σ : Type} (I : Iter α σ) (state : Option σ) : Iter α σ :=
  match state with
  | none => I
  | some s => { first := I.next s, next := I.next }

/-- The values an iterator produces from `start`, with at most `fuel` steps. -/
def Iter.collectFrom {σ : Type} (I : Iter α σ) : Nat → Option (α × σ) → List α
  | 0, _ => []
  | _ + 1, none => []
  | k + 1, some (x, s) => x :: I.collectFrom k (I.next s)

/-- `_split_rest(a::Union{AbstractArray, Core.SimpleVector}, n::Int)`,
`base/tuple.jl:260-263`: `_check_length_split_rest(length(a), n)`, then
`(a[begin:end-n], a[end-n+1:end])` with checked `UnitRange{Int}` slices. -/
def splitRestArray (a : List α) (n : JInt .i64) : R (List α × List α) := do
  checkLengthSplitRest a.length n
  let len : JInt .i64 := JInt.lit .i64 a.length
  let x ← getindexColon a (JInt.lit .i64 1) (len - n)
  let y ← getindexColon a (len - n + JInt.lit .i64 1) len
  pure (x, y)

/-- `split_rest(itr, n::Int, state...)`, `base/tuple.jl:248-254`: `ArgumentError`
for an infinite iterator; otherwise `_split_rest(rest(itr, state...), n)`, which
collects the remaining values `rest` into a `Vector` and splits that with the
`Vector` method of `base/bitarray.jl` (`splitRestVector`). -/
def splitRestIter (infinite : Bool) (rest : List α) (n : JInt .i64) :
    R (List (Option α) × List α) :=
  if infinite then argErr "Cannot split an infinite iterator in the middle."
  else splitRestVector rest n (JInt.lit .i64 1)

/-- `safe_tail(t::Tuple) = tail(t)`, `safe_tail(t::Tuple{}) = ()`, `base/tuple.jl:323-324`. -/
def safeTail : List α → List α
  | [] => []
  | _ :: r => r

/-! ### `map` with `n ≥ 3` tuples, `base/tuple.jl:421-439` -/

/-- `heads(ts::Tuple...) = map(t -> t[1], ts)`, `base/tuple.jl:421`. -/
def heads : List (List α) → R (List α)
  | [] => .ok []
  | t :: ts => do
    let x ← getfield t 1
    let r ← heads ts
    pure (x :: r)

/-- `tails(ts::Tuple...) = map(tail, ts)`, `base/tuple.jl:422`. -/
def tails : List (List α) → R (List (List α))
  | [] => .ok []
  | t :: ts => do
    let x ← JuliaLean.Tuples.tail t
    let r ← tails ts
    pure (x :: r)

/-- `anyempty(x::Tuple{}, xs...) = true`, `anyempty(x::Tuple, xs...) = anyempty(xs...)`,
`anyempty() = false`, `base/tuple.jl:424-426`. -/
def anyempty : List (List α) → Bool
  | [] => false
  | [] :: _ => true
  | (_ :: _) :: xs => anyempty xs

/-- `map(f, ::Tuple{}, ::Tuple{}...) = ()` (`base/tuple.jl:423`) and
`map(f, t1, t2, ts...)` (`base/tuple.jl:427-431`): stop when any tuple is
empty, else `f(heads...)` followed by the map of the tails. `fuel` is the
recursion depth (a tuple length bound). -/
def mapRec (f : List α → β) : Nat → List (List α) → R (List β)
  | 0, _ => .ok []
  | k + 1, ts =>
    if anyempty ts then .ok [] else do
      let h ← heads ts
      let tl ← tails ts
      let r ← mapRec f k tl
      pure (f h :: r)

/-- `map(f, t1::Any32, t2::Any32, ts::Any32...)`, `base/tuple.jl:432-439`:
`n = min(length(t1), length(t2), minimum(length, ts))`, then
`A[i] = f(t1[i], t2[i], map(t -> t[i], ts)...)` for `i = 1:n`. -/
def mapLoop (f : List α → β) (ts : List (List α)) : R (List β) :=
  let n := (ts.map List.length).foldl min (ts.headD []).length
  (List.range n).mapM fun (i : Nat) => do
    let xs ← ts.mapM fun t => getfield t ((i : Int) + 1)
    pure (f xs)

/-- `map` over `ts = [t1, t2, ...]` (at least 3 tuples): the `Any32` method when
every tuple has at least 32 elements, else the recursive one. -/
def mapN (f : List α → β) (ts : List (List α)) : R (List β) :=
  if ts.all (fun t => t.length ≥ 32) then mapLoop f ts
  else mapRec f ((ts.map List.length).foldl max 0) ts

/-! ### `foreach`, `sym_in`, `isempty`, `empty` -/

/-- `foreach(f, itr::Tuple) = foldl((_, x) -> (f(x); nothing), itr, init=nothing)`,
`base/tuple.jl:714`. The effect of `f(x)` is a state update `f s x`. -/
def foreach {σ : Type} (f : σ → α → σ) (s : σ) (t : List α) : σ :=
  t.foldl f s

/-- `zip(itr, itrs...)`: tuples of the `k`-th elements, up to the shortest. -/
def zipN : List (List α) → Nat → List (List α)
  | _, 0 => []
  | ts, k + 1 =>
    match ts.mapM List.head? with
    | some h => if ts.isEmpty then [] else h :: zipN (ts.map List.tail) k
    | none => []

/-- `foreach(f, itr::Tuple, itrs::Tuple...) = foldl((_, xs) -> (f(xs...); nothing),
zip(itr, itrs...), init=nothing)`, `base/tuple.jl:715`. -/
def foreachN {σ : Type} (f : σ → List α → σ) (s : σ) (t : List α) (ts : List (List α)) : σ :=
  (zipN (t :: ts) t.length).foldl f s

/-- `sym_in(x::Symbol, itr::Tuple{Vararg{Symbol}})`, `base/tuple.jl:696-703`:
the loop `for y in itr; y === x && return true; end; return false`. Symbols
are strings. -/
def symInLoop (x : String) : List String → Bool
  | [] => false
  | y :: r => if y == x then true else symInLoop x r

/-- `in(x::Symbol, itr::Tuple{Vararg{Symbol}}) = sym_in(x, itr)`, `base/tuple.jl:704`. -/
def inSym (x : String) (itr : List String) : Bool := symInLoop x itr

/-- `isempty(x::Tuple{}) = true`, `isempty(x::Tuple) = false`, `base/tuple.jl:665-666`. -/
def isempty : List α → Bool
  | [] => true
  | _ :: _ => false

/-- `empty(x::Tuple) = ()`, `base/tuple.jl:712`. -/
def empty (_ : List α) : List α := []

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

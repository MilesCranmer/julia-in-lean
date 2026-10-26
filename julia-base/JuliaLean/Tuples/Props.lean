import JuliaLean.Tuples.NamedTuple
import JuliaLean.Float.Basic

/-! Properties of the tuple model, stated as Julia documents or obviously promises them. -/

namespace JuliaLean.Tuples

open JuliaLean.Float

instance instDecidableSameOutcome {α : Type} [DecidableEq α] : (a b : R α) → Decidable (SameOutcome a b)
  | .ok a, .ok b => inferInstanceAs (Decidable (a = b))
  | .error e, .error f => inferInstanceAs (Decidable (e.kind = f.kind))
  | .ok _, .error _ => isFalse (fun h => h)
  | .error _, .ok _ => isFalse (fun h => h)

/-- An `Int` literal. -/
abbrev I64 (x : Int) : JInt .i64 := JInt.lit .i64 x

/-- `split_rest(v::Vector, n, i)` with the uninitialised slots dropped, used as
the reference for tuples and named tuples with `n ≥ 0`. -/
def splitRestRef {β : Type} (v : List β) (n i : JInt .i64) : R (List β × List β) :=
  (splitRestVector v n i).map fun (f, l) => (f.filterMap id, l)

/-! ## Refuted properties -/

/-- `split_rest(t, n, i)` on a tuple or named tuple agrees with `split_rest` on
the corresponding `Vector` (same values or same exception type) for every
valid iteration state `1 ≤ i ≤ length(t)+1` and `n ≥ 0`. -/
def SplitRestAgrees : Prop :=
  (∀ (t : List Int) (n i : Nat), 1 ≤ i → i ≤ t.length + 1 → n < 2 ^ 62 → t.length < 2 ^ 62 →
    SameOutcome (splitRestTuple t (I64 n) (I64 i)) (splitRestRef t (I64 n) (I64 i))) ∧
  (∀ (t : NT Int) (n i : Nat), (ntNames t).Nodup → 1 ≤ i → i ≤ t.length + 1 → n < 2 ^ 62 →
    t.length < 2 ^ 62 →
    SameOutcome (splitRestNT t (I64 n) (I64 i)) (splitRestRef t (I64 n) (I64 i)))

/-- `split_rest(v, n)` either throws or returns `(rest_but_n, last_n)` whose
concatenation is `v`. -/
def SplitRestPartition : Prop :=
  ∀ (v : List Int) (n : JInt .i64),
    match splitRestVector v n (I64 1) with
    | .ok (f, l) => f ++ l.map some = v.map some
    | .error _ => True

/-- `haskey(nt, k)` and `get(nt, k, d)` accept every `Integer` key `k`, as
their signatures `key::Union{Integer, Symbol}` declare: `haskey` is
`1 ≤ k ≤ length(nt)` and `get` returns the field or the default. -/
def HaskeyInteger : Prop :=
  ∀ (nt : NT Int) (t : IntTy) (k : JInt t) (d : Int),
    haskeyNT nt (.int (.int t k)) = .ok (decide (1 ≤ k.val ∧ k.val ≤ nt.length)) ∧
    getNT nt (.int (.int t k)) d =
      (if 1 ≤ k.val ∧ k.val ≤ nt.length then getfield (ntValues nt) k.val else .ok d)

/-- `findall(in(b), t)` returns the indices `i` with `t[i] in b`, i.e. it equals
`findall(x -> x in b, t)`, for tuples of `Float64` and vectors `b`. -/
def FindallInAgrees : Prop :=
  ∀ (t b : List F64), findallIn F64.isequal t b = findallPred F64.eq t b

/-- Indexing a tuple with a `Bool` scalar (`getindex`, `Base.setindex`, `get`,
`isassigned`) throws `ArgumentError` as the same operations on a `Vector` do. -/
def BoolIndexAgrees : Prop :=
  ∀ (t : List Int) (b : Bool) (v d : Int),
    SameOutcome (getindex t (.bool b)) vecBoolIndex ∧
    SameOutcome (setindex t v (.bool b)) vecBoolIndex ∧
    SameOutcome (get t (.bool b) d) vecBoolIndex ∧
    SameOutcome (isassigned t (.bool b)) vecBoolIndex

/-- Indexing a tuple with a `UnitRange{Bool}` agrees with indexing it by the
same `Bool` values collected into a `Vector{Bool}` (logical indexing). The
`UnitRange{Bool}` values are `false:false`, `false:true`, `true:false`, `true:true`. -/
def BoolRangeLogical : Prop :=
  ∀ (t : List Int) (lo : Bool) (len : Nat),
    (lo = true → len ≤ 1) → (lo = false → 1 ≤ len ∧ len ≤ 2) →
    SameOutcome (getindexBoolRange t lo len) (getindexLogical t (boolRangeValues lo len))

/-- `t[i]` throws `BoundsError` for every integer index outside `1:length(t)`,
as `Base.setindex(t, v, i)` does. -/
def GetindexBoundsError : Prop :=
  ∀ (t : List Int) (ty : IntTy) (i : JInt ty),
    ¬ (1 ≤ i.val ∧ i.val ≤ t.length) → SameOutcome (getindex t (.int ty i)) bounds

/-- `prod(t)` agrees with `prod(identity, t)` for every tuple of `Int`. -/
def ProdAgrees : Prop := ∀ (t : List (JInt .i64)), SameOutcome (prodTuple t) (prodGeneric t)

/-! ## Proven properties -/

/-- `ntuple(f, n)` for `n` of any integer type returns `(f(1), ..., f(n))`,
throws `ArgumentError` for negative `n` and `InexactError` when `n` is not an
`Int`; `ntuple(f, Val(N))` likewise. -/
def NtupleCorrect : Prop :=
  (∀ (α : Type) [DecidableEq α] (f : Nat → α) (t : IntTy) (n : JInt t),
    SameOutcome (ntuple f t n)
      (if n.val < IntTy.i64.min ∨ n.val > IntTy.i64.max then .error (.jl (.inexactError ""))
       else if n.val < 0 then argErr ""
       else .ok ((List.range n.val.toNat).map fun k => f (k + 1)))) ∧
  (∀ (α : Type) [DecidableEq α] (f : Nat → α) (N : JInt .i64),
    SameOutcome (ntupleVal f N)
      (if N.val < 0 then argErr "" else .ok ((List.range N.val.toNat).map fun k => f (k + 1))))

/-- `Base.fill_to_length(t, v, Val(N))` pads `t` with `v` to length `N`, and
throws `ArgumentError` when `length(t) > N`. -/
def FillToLengthCorrect : Prop :=
  ∀ (α : Type) [DecidableEq α] (t : List α) (v : α) (N : JInt .i64),
    SameOutcome (fillToLength t v N)
      (if (t.length : Int) > N.val then argErr ""
       else .ok (t ++ List.replicate (N.val - t.length).toNat v))

/-- Both `reverse` methods (`revargs` and the `NTuple` method) reverse the tuple. -/
def ReverseCorrect : Prop :=
  ∀ (α : Type) (t : List α), revargs t = t.reverse ∧ reverseNTuple t = .ok t.reverse

/-- `Base.front`, `Base.tail`, `first` and `last` return all but the last
element, all but the first, the first and the last element; on `()` `front`,
`tail` and `first` throw `ArgumentError` and `last` throws `BoundsError`. -/
def FrontTailCorrect : Prop :=
  ∀ (α : Type) [DecidableEq α] (t : List α),
    SameOutcome (front t) (if t = [] then argErr "" else .ok t.dropLast) ∧
    SameOutcome (tail t) (if t = [] then argErr "" else .ok t.tail) ∧
    SameOutcome (first t) (match t with | [] => argErr "" | a :: _ => .ok a) ∧
    SameOutcome (last t) (match t.getLast? with | none => bounds | some a => .ok a)

/-- Scalar integer indices of every `BitInteger` type: `t[i]` is the element
when `1 ≤ i ≤ length(t)`, else `BoundsError` (`InexactError` when `i` is not an
`Int`); `Base.setindex` replaces the element or throws `BoundsError`; `get`
returns the element or the default; `isassigned` tests the bounds. -/
def IntegerIndexCorrect : Prop :=
  ∀ (α : Type) [DecidableEq α] (t : List α) (ty : IntTy) (i : JInt ty) (v d : α),
    (t.length : Int) ≤ IntTy.i64.max →
    let inb := 1 ≤ i.val ∧ i.val ≤ t.length
    let elt : R α := match t[(i.val - 1).toNat]? with | some a => .ok a | none => bounds
    SameOutcome (getindex t (.int ty i))
      (if inb then elt
       else if i.val < IntTy.i64.min ∨ i.val > IntTy.i64.max then .error (.jl (.inexactError ""))
       else bounds) ∧
    SameOutcome (setindex t v (.int ty i)) (if inb then .ok (t.set (i.val - 1).toNat v) else bounds) ∧
    SameOutcome (get t (.int ty i) d) (if inb then elt else .ok d) ∧
    isassigned t (.int ty i) = .ok (decide inb)

/-- `t[a:b]` for `Int` endpoints (including the `front`/`tail` shortcuts of
long ranges) agrees with `Vector` indexing: the slice when `a:b` is empty or
inside `1:length(t)`, else `BoundsError`. -/
def UnitRangeIndexCorrect : Prop :=
  ∀ (α : Type) [DecidableEq α] (t : List α) (a b : JInt .i64), b.val - a.val < 2 ^ 62 →
    SameOutcome (getindexColon t a b)
      (if b.val < a.val then .ok []
       else if 1 ≤ a.val ∧ b.val ≤ t.length then
         .ok ((t.drop (a.val - 1).toNat).take (b.val - a.val + 1).toNat)
       else bounds)

/-- `zipWith` for three lists, stopping at the shortest. -/
def zip3With {α β γ δ : Type} (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | a :: r, b :: s, c :: u => f a b c :: zip3With f r s u
  | _, _, _ => []

/-- `map` over one, two or three tuples applies `f` elementwise and stops at
the shortest tuple, as `map` over `Vector`s does (through `zip`). -/
def MapCorrect : Prop :=
  ∀ (α β γ δ : Type) (f1 : α → δ) (f2 : α → β → δ) (f3 : α → β → γ → δ)
    (t : List α) (s : List β) (u : List γ),
    map1 f1 t = t.map f1 ∧ map2 f2 t s = List.zipWith f2 t s ∧ map3 f3 t s u = zip3With f3 t s u

/-- The last index (one-based) whose element satisfies `f`. -/
def lastIndex {α : Type} (f : α → Bool) : List α → Option Nat
  | [] => none
  | a :: r => match lastIndex f r with
    | some k => some (k + 1)
    | none => if f a then some 1 else none

/-- `findfirst(f, t)` and `findlast(f, t)` return the first and last index
whose element satisfies `f` (or `nothing`), and `filter(f, t)` keeps exactly
those elements in order, for short and long tuples. -/
def FindFilterCorrect : Prop :=
  ∀ (α : Type) (f : α → Bool) (t : List α),
    findfirst f t = (t.findIdx? f).map (· + 1) ∧ findlast f t = lastIndex f t ∧
    filter f t = t.filter f

/-- `x in t` for a tuple agrees with the generic `in(x, itr) = any(==(x), itr)`
used for `Vector`s, including three-valued `missing` results. -/
def InCorrect : Prop :=
  ∀ (α : Type) (eq : α → α → Option Bool) (x : α) (t : List α),
    inTuple eq x t = anyGo (fun y => eq y x) t false

/-- Elementwise three-valued conjunction of `==`, as for `Vector`s. -/
def eqSpec {α : Type} (o : Ops α) (t s : List α) : Option Bool :=
  if t.length ≠ s.length then some false
  else
    let cs := List.zipWith o.eq t s
    if cs.contains (some false) then some false
    else if cs.contains none then none else some true

/-- `isequal(t, s)` holds iff the tuples have the same length and are
elementwise `isequal`; `t == s` is `false` for different lengths and otherwise
the three-valued conjunction of the elementwise `==` (as for `Vector`s), for
short and long tuples. -/
def EqualityCorrect : Prop :=
  ∀ (α : Type) (o : Ops α) (t s : List α),
    isequal o t s = (t.length == s.length && (List.zipWith o.isequal t s).all id) ∧
    eq o t s = eqSpec o t s

/-- `t < s` on tuples is the lexicographic comparison of `ltRec` (the first
position where `==` is not `true` decides: `missing` gives `missing`, `false`
gives `t[i] < s[i]`; otherwise the shorter tuple is smaller) for long tuples too. -/
def LtLexicographic : Prop :=
  ∀ (α : Type) (o : Ops α) (t s : List α), lt o t s = ltRec o t s

/-- Element `isless` is a strict weak order whose incomparability is `isequal`
(Julia's requirement on `isless`). -/
structure Lawful {α : Type} (o : Ops α) : Prop where
  irrefl : ∀ a, o.isless a a = false
  trans : ∀ a b c, o.isless a b = true → o.isless b c = true → o.isless a c = true
  equiv : ∀ a b, o.isequal a b = (!o.isless a b && !o.isless b a)
  incompTrans : ∀ a b c, o.isequal a b = true → o.isequal b c = true → o.isequal a c = true

/-- For lawful elements, `isless` on tuples (every method, including the
`Tuple{BitInteger,BitInteger}` specialisation) is a strict weak order whose
incomparability is tuple `isequal`, and `cmp(t, s) == 0` iff `isequal(t, s)`. -/
def IslessStrictWeakOrder : Prop :=
  ∀ (α : Type) (o : Ops α), Lawful o →
    (∀ t, isless o t t = false) ∧
    (∀ t s u, isless o t s = true → isless o s u = true → isless o t u = true) ∧
    (∀ t s, (isless o t s = false ∧ isless o s t = false) ↔ isequal o t s = true) ∧
    (∀ t s, (cmp o t s = 0) ↔ isequal o t s = true) ∧
    (∀ a1 a2 b1 b2, islessPair o a1 a2 b1 b2 = isless o [a1, a2] [b1, b2])

/-- If element `hash` is consistent with element `isequal`, then
`isequal(t, s)` implies `hash(t, h) == hash(s, h)` for tuples (both methods)
and for named tuples. -/
def HashIsequal : Prop :=
  ∀ (α : Type) (o : Ops α), (∀ a b h, o.isequal a b = true → o.hash a h = o.hash b h) →
    (∀ t s h, isequal o t s = true → hash o t h = hash o s h) ∧
    (∀ (oid : List String → Nat) (a b : NT α) h,
      isequalNT o a b = true → hashNT o oid a h = hashNT o oid b h)

/-- `merge(a, b)` lists the names of `a` then the names only in `b`, takes
each value from `b` when present there and from `a` otherwise;
`structdiff(a, b)` keeps the fields of `a` not named in `b`;
`Base.setindex(nt, v, k)` sets field `k` to `v`; `nt[names]` returns the
requested fields in order. -/
def NamedTupleCorrect : Prop :=
  ∀ (α : Type) (a b : NT α), (ntNames a).Nodup → (ntNames b).Nodup →
    ntNames (merge a b) = mergeNames (ntNames a) (ntNames b) ∧
    (∀ k, lookup (merge a b) k = (lookup b k).or (lookup a k)) ∧
    (∀ bn : List String,
      ntNames (structdiff a bn) = (ntNames a).filter (fun n => !bn.contains n) ∧
      ∀ k, lookup (structdiff a bn) k = if bn.contains k then none else lookup a k) ∧
    (∀ (v : α) (k k' : String), lookup (setindexNT a v k) k' = if k' = k then some v else lookup a k') ∧
    (∀ idxs : List String, idxs.Nodup → (∀ k ∈ idxs, (lookup a k).isSome) →
      ∃ r, getindexNames a idxs = .ok r ∧ ntNames r = idxs ∧ ∀ k ∈ idxs, lookup r k = lookup a k)

end JuliaLean.Tuples

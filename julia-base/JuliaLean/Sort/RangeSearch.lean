import JuliaLean.Core
import JuliaLean.Registry.Types

/-!
`searchsortedfirst`/`searchsortedlast`/`searchsorted` on integer ranges,
`base/sort.jl:269-302` (master `bbfa0ce4150`).

Scope: ranges whose `first`, `step` and `last` share the element type `T`
(`UnitRange{T}`, and `StepRange{T,T}` for signed `T`), searched for a value
`x::T` of the same type. On `Int64` ranges this is the default case
`searchsortedfirst(r, x::Int)`. The four `FastRangeOrderings`
(`Forward`, `Reverse`, `Lt(<)`, `ReverseOrdering(Lt(<))`) compare
`BitInteger`s identically to `<` (`isless` on integers is `<`), so the ordering
is the Boolean `rev` (`ReverseOrdering`).
-/

namespace JuliaLean.Sort

open JuliaLean JuliaLean.Registry

/-- `lt(o, a, b)` for a `FastRangeOrderings` value on integers,
`base/ordering.jl:118-121`: `rev` is `o isa ReverseOrdering`. -/
def rangeLt {t : IntTy} (rev : Bool) (a b : JInt t) : Bool :=
  if rev then decide (b.val < a.val) else decide (a.val < b.val)

/-- `y + 1` with the `Int` literal `1`: the sum is computed in
`promote_type(T, Int64)` (`base/int.jl`), wrapping there. -/
def addOneInt {t : IntTy} (y : JInt t) : Int :=
  wrapInt (IntTy.promote t .i64) (y.val + 1)

/-- The `::keytype(a)` return annotation converts the result to `Int`. -/
def toKeytype (y : Int) : Jl JInt64 := JInt.convert .i64 y

/-- `searchsortedlast(a::AbstractRange{<:Integer}, x::Real, o::FastRangeOrderings)`,
`base/sort.jl:269-283`. `floor(Integer, x)` and `ceil(Integer, x)` are `x`
for an integer `x`. `len` is `length(a)`. -/
def rangeSearchLast {t : IntTy} (f h l : JInt t) (len : JInt64) (x : JInt t)
    (rev : Bool) : Jl JInt64 :=
  if rangeLt rev x f then pure (JInt.lit .i64 0)                 -- sort.jl:272-273
  else if h.val = 0 ∨ !(rangeLt rev x l) then pure len            -- sort.jl:274-275
  else do
    -- sort.jl:277-281: both branches are `fld(x - f, h) + 1` for integer x
    let q ← JInt.fld (x - f) h
    toKeytype (addOneInt q)

/-- `searchsortedfirst(a::AbstractRange{<:Integer}, x::Real, o::FastRangeOrderings)`,
`base/sort.jl:285-299`. `length(a) + 1` is `Int` arithmetic. -/
def rangeSearchFirst {t : IntTy} (f h l : JInt t) (len : JInt64) (x : JInt t)
    (rev : Bool) : Jl JInt64 :=
  if !(rangeLt rev f x) then pure (JInt.lit .i64 1)               -- sort.jl:288-289
  else if h.val = 0 ∨ rangeLt rev l x then pure (len + JInt.lit .i64 1)  -- sort.jl:290-291
  else do
    -- sort.jl:293-297: both branches are `cld(x - f, h) + 1` for integer x
    let q ← JInt.cld (x - f) h
    toKeytype (addOneInt q)

/-- `searchsorted(a::AbstractRange{<:Real}, x::Real, o)`, `base/sort.jl:301-302`:
the pair of endpoints of `searchsortedfirst(a,x,o):searchsortedlast(a,x,o)`. -/
def rangeSearchsorted {t : IntTy} (f h l : JInt t) (len : JInt64) (x : JInt t)
    (rev : Bool) : Jl (JInt64 × JInt64) := do
  let a ← rangeSearchFirst f h l len x rev
  let b ← rangeSearchLast f h l len x rev
  pure (a, b)

/-- The `i`-th element (1-based) of the arithmetic progression, as a mathematical integer. -/
def rangeElem {t : IntTy} (f h : JInt t) (i : Int) : Int := f.val + (i - 1) * h.val

/-- The `first`, `step`, `last`, `length` of a Julia integer range with `len`
elements and nonzero step (`UnitRange{T}`, `StepRange{T,T}`):
a nonempty range has `last == first + (len-1)*step` (`base/range.jl:353-387`);
an empty one stores `last = first - 1` for a positive step and `first + 1`
for a negative step (`steprange_last_empty`, `base/range.jl:389-397`;
`unitrange_last`, `base/range.jl:439-441`). The length is an `Int` below
`typemax(Int)`, so that `length(a) + 1` is representable. -/
def RangeValid {t : IntTy} (f h l : JInt t) (len : JInt64) : Prop :=
  0 ≤ len.val ∧ len.val < IntTy.max .i64 ∧ h.val ≠ 0 ∧
    (if len.val = 0 then l.val = f.val - (if 0 < h.val then 1 else -1)
     else l.val = rangeElem f h len.val)

/-- `collect(a)` is sorted under the ordering (`issorted`, base/sort.jl:48-60):
increasing for `Forward`, decreasing for `Reverse`, unless it has fewer than two elements. -/
def RangeSorted {t : IntTy} (h : JInt t) (len : JInt64) (rev : Bool) : Prop :=
  2 ≤ len.val → if rev then h.val < 0 else 0 < h.val

/-- `lt(o, a, b)` on the mathematical element values. -/
def elemLt (rev : Bool) (a b : Int) : Bool :=
  if rev then decide (b < a) else decide (a < b)

/-- Docstring contract of `searchsortedfirst` (base/sort.jl:353-357) on the
vector `collect(a)` of length `n`: the indices before the result hold exactly
the values ordered before `x`. -/
def FirstContract (n : Int) (before : Int → Bool) (r : Int) : Prop :=
  1 ≤ r ∧ r ≤ n + 1 ∧ (∀ i, 1 ≤ i → i < r → before i = true) ∧
    (∀ i, r ≤ i → i ≤ n → before i = false)

/-- Docstring contract of `searchsortedlast` (base/sort.jl:392-396): the
indices up to the result hold exactly the values not ordered after `x`. -/
def LastContract (n : Int) (notAfter : Int → Bool) (r : Int) : Prop :=
  0 ≤ r ∧ r ≤ n ∧ (∀ i, 1 ≤ i → i ≤ r → notAfter i = true) ∧
    (∀ i, r < i → i ≤ n → notAfter i = false)

/-- Both range methods return the docstring answers for `collect(a)`. -/
def RangeAnswers {t : IntTy} (f h l : JInt t) (len : JInt64) (x : JInt t) (rev : Bool) : Prop :=
  (∃ r, rangeSearchFirst f h l len x rev = .ok r ∧
      FirstContract len.val (fun i => elemLt rev (rangeElem f h i) x.val) r.val) ∧
  (∃ r, rangeSearchLast f h l len x rev = .ok r ∧
      LastContract len.val (fun i => !(elemLt rev x.val (rangeElem f h i))) r.val)

/-- On every nonempty sorted integer range and every `x` of its element type,
`searchsortedfirst`/`searchsortedlast` (hence `searchsorted`) agree with the
docstring answer on `collect(a)`. -/
def RangeSearchNonemptyCorrect : Prop :=
  ∀ (t : IntTy) (f h l : JInt t) (len : JInt64) (x : JInt t) (rev : Bool),
    RangeValid f h l len → RangeSorted h len rev → 1 ≤ len.val →
    RangeAnswers f h l len x rev

/-- On every empty integer range (sorted under every ordering) the answers are
`searchsortedfirst == 1` and `searchsortedlast == 0`, i.e. `searchsorted` is `1:0`. -/
def RangeSearchEmptyCorrect : Prop :=
  ∀ (t : IntTy) (f h l : JInt t) (len : JInt64) (x : JInt t) (rev : Bool),
    RangeValid f h l len → len.val = 0 →
    rangeSearchFirst f h l len x rev = .ok (JInt.lit .i64 1) ∧
    rangeSearchLast f h l len x rev = .ok (JInt.lit .i64 0)

/-- The same agreement holds whenever `x - first(a)` neither overflows `T`
nor equals `typemin(T)` for signed `T` (where `fld`/`cld` by `-1` overflow). -/
def RangeSearchNoOverflowCorrect : Prop :=
  ∀ (t : IntTy) (f h l : JInt t) (len : JInt64) (x : JInt t) (rev : Bool),
    RangeValid f h l len → RangeSorted h len rev → 1 ≤ len.val →
    t.min + (if t.signed then 1 else 0) ≤ x.val - f.val → x.val - f.val ≤ t.max →
    RangeAnswers f h l len x rev

/-! ### Refutations -/

/-- `Int8(-100):Int8(100)` searched for `Int8(50)`: `x - first(a)` wraps to `-106`. -/
theorem rangeSearchNonemptyCorrect_refuted : ¬ RangeSearchNonemptyCorrect := by
  intro h
  have hv : RangeValid (t := .i8) (JInt.lit .i8 (-100)) (JInt.lit .i8 1) (JInt.lit .i8 100)
      (JInt.lit .i64 201) := by unfold RangeValid rangeElem; decide
  have hs : RangeSorted (t := .i8) (JInt.lit .i8 1) (JInt.lit .i64 201) false := by
    unfold RangeSorted; decide
  obtain ⟨_, r, hr, hc⟩ := h .i8 _ _ _ _ (JInt.lit .i8 50) false hv hs (by decide)
  have e : rangeSearchLast (t := .i8) (JInt.lit .i8 (-100)) (JInt.lit .i8 1) (JInt.lit .i8 100)
      (JInt.lit .i64 201) (JInt.lit .i8 50) false = .ok (JInt.lit .i64 (-105)) := rfl
  rw [e] at hr
  cases hr
  exact absurd hc.1 (by decide)

/-- The `Int64` instance with `x::Int`: `typemin(Int):2:2^62` (length `3*2^61+1`)
searched for `2^62-1` gives negative indices. -/
theorem rangeSearchInt64Overflow :
    rangeSearchLast (t := .i64) (JInt.lit .i64 (-(2^63))) (JInt.lit .i64 2) (JInt.lit .i64 (2^62))
      (JInt.lit .i64 (3 * 2^61 + 1)) (JInt.lit .i64 (2^62 - 1)) false =
      .ok (JInt.lit .i64 (-2305843009213693952)) ∧
    rangeSearchFirst (t := .i64) (JInt.lit .i64 (-(2^63))) (JInt.lit .i64 2) (JInt.lit .i64 (2^62))
      (JInt.lit .i64 (3 * 2^61 + 1)) (JInt.lit .i64 (2^62 - 1)) false =
      .ok (JInt.lit .i64 (-2305843009213693951)) :=
  ⟨rfl, rfl⟩

/-- `searchsortedfirst(1:0, 0; rev=true)` returns `0`. -/
theorem rangeSearchEmptyCorrect_refuted : ¬ RangeSearchEmptyCorrect := by
  intro h
  have hv : RangeValid (t := .i64) (JInt.lit .i64 1) (JInt.lit .i64 1) (JInt.lit .i64 0)
      (JInt.lit .i64 0) := by unfold RangeValid rangeElem; decide
  have e : rangeSearchFirst (t := .i64) (JInt.lit .i64 1) (JInt.lit .i64 1) (JInt.lit .i64 0)
      (JInt.lit .i64 0) (JInt.lit .i64 0) true = .ok (JInt.lit .i64 0) := rfl
  have := (h .i64 _ _ _ _ (JInt.lit .i64 0) true hv (by decide)).1
  rw [e] at this
  cases this

/-- `searchsorted(5:4, 5; rev=true)` is `1:1`, a nonempty answer for an empty range. -/
theorem rangeSearchEmptyLast :
    rangeSearchLast (t := .i64) (JInt.lit .i64 5) (JInt.lit .i64 1) (JInt.lit .i64 4)
      (JInt.lit .i64 0) (JInt.lit .i64 5) true = .ok (JInt.lit .i64 1) := rfl

end JuliaLean.Sort

import JuliaLean.Core
import JuliaLean.MultidimCov.ArrayV2Find
import JuliaLean.MultidimCov.ArrayV2Grow

/-!
`findfirst`/`findlast` specialisations for integer ranges and scalar
`getindex(::AbstractRange, ::Integer)` (master `base/array.jl:2534-2555`,
`2728-2736`, `3224-3230`).

A range with `BitInteger` element type `t` is given by its fields: `OneTo(n)`
by `n = r.stop ≥ 0`; a unit range by `first(r)` and `last(r)` and the first key
`k1 = first(keys(r))` (`1` for `UnitRange`, the start for an
`IdentityUnitRange`); a `StepRange{T,T}` by `first`, `step ≠ 0` and its length,
its normalised `last` being `first + (len-1)*step` (`first - step` when empty).
Every key type is `Int` (`keytype(r) == Int`, `LinearIndices`), so
`convert(keytype(r), x)` is `toInt`. A query value is a mathematical integer with
its `BitInteger` type; mixed comparisons are exact, arithmetic wraps in the
promoted type (`wrapInt`).
-/

namespace JuliaLean.MultidimCov.ArrayV2

open JuliaLean (IntTy wrapInt)

/-- `collect(OneTo(n))`. -/
def oneToList (n : Int) : List Int := (List.range n.toNat).map fun k : Nat => (k : Int) + 1

/-- `collect(r)` of a unit range `f:l`. -/
def unitList (f l : Int) : List Int := (List.range (l - f + 1).toNat).map fun k : Nat => f + (k : Int)

/-- `collect(r)` of a step range with `len` elements. -/
def stepList (f s : Int) (len : Nat) : List Int := (List.range len).map fun k : Nat => f + (k : Int) * s

/-- The index of the first element of `xs` (keys `1:length(xs)`) satisfying `q`. -/
def firstIdx (q : Int → Bool) (xs : List Int) : Option Int :=
  ((pairsV xs).find? fun pr => q pr.2).map Prod.fst

/-- base/array.jl:2534 `findfirst(p::Fix2{==/isequal}, r::OneTo)`:
`1 <= p.x <= r.stop ? convert(keytype(r), p.x) : nothing`. -/
def m2534 (n x : Int) : R (Option Int) :=
  if 1 ≤ x ∧ x ≤ n then do let i ← toInt x; pure (some i) else .ok none

/-- base/array.jl:2537 `findfirst(::typeof(iszero), ::OneTo) = nothing`. -/
def m2537 (_n : Int) : R (Option Int) := .ok none

/-- base/array.jl:2538 `findfirst(::typeof(isone), r::OneTo) = isempty(r) ? nothing : oneunit(keytype(r))`. -/
def m2538 (n : Int) : R (Option Int) := if n = 0 then .ok none else .ok (some 1)

/-- base/array.jl:2540 `findfirst(p::Fix2{==/isequal}, r::AbstractUnitRange{<:Integer})`:
`first(r) <= p.x <= last(r) || return nothing; i1 = first(keys(r));
return i1 + oftype(i1, p.x - first(r))`. `p.x - first(r)` wraps in
`promote_type(typeof(p.x), t)`; `oftype(i1, ·)` is `convert(Int, ·)`; `i1 + ·` wraps in `Int`. -/
def m2540 (t s : IntTy) (k1 f l x : Int) : R (Option Int) :=
  if ¬ (f ≤ x ∧ x ≤ l) then .ok none else do
  let d := wrapInt (s.promote t) (x - f)
  let c ← toInt d
  pure (some (wrap64 (k1 + c)))

/-- `isempty(r::StepRange)`: `(r.start != r.stop) & ((r.step > 0) != (r.stop > r.start))`. -/
def stepEmpty (f s l : Int) : Bool := (f != l) && (decide (0 < s) != decide (f < l))

/-- base/array.jl:2546 `findfirst(p::Fix2{==/isequal}, r::StepRange{T,T})`, `l = last(r)`:
`isempty(r) && return nothing; minimum(r) <= p.x <= maximum(r) || return nothing;
d = p.x - first(r); iszero(d % step(r)) || return nothing;
return convert(keytype(r), d ÷ step(r) + 1)`. `d`, `%` and `÷` are in `t`
(`÷` throws `DivideError` for `typemin ÷ -1`), `+ 1` in `promote_type(t, Int)`. -/
def m2546 (t : IntTy) (f s l x : Int) : R (Option Int) :=
  if stepEmpty f s l then .ok none else
  let mn := if 0 < s then f else l
  let mx := if 0 < s then l else f
  if ¬ (mn ≤ x ∧ x ≤ mx) then .ok none else
  let d := wrapInt t (x - f)
  if Int.tmod d s ≠ 0 then .ok none else
  if t.signed ∧ d = t.min ∧ s = -1 then .error .divide else do
  let q := wrapInt (t.promote .i64) (Int.tdiv d s + 1)
  let i ← toInt q
  pure (some i)

/-- The ranges the specialisations dispatch on (`StepRange{T,T}` with `len` elements). -/
inductive IRange where
  | oneTo (t : IntTy) (n : Int)
  | unit (t : IntTy) (k1 f l : Int)
  | step (t : IntTy) (f s : Int) (len : Nat)

def IRange.eltype : IRange → IntTy
  | .oneTo t _ | .unit t _ _ _ | .step t _ _ _ => t

def IRange.first : IRange → Int
  | .oneTo _ _ => 1
  | .unit _ _ f _ => f
  | .step _ f _ _ => f

/-- `collect(r)`. -/
def IRange.elems : IRange → List Int
  | .oneTo _ n => oneToList n
  | .unit _ _ f l => unitList f l
  | .step _ f s len => stepList f s len

/-- `findfirst(==(x), r)` / `findfirst(isequal(x), r)` with `x` of type `s`, by dispatch. -/
def findEq (s : IntTy) (x : Int) : IRange → R (Option Int)
  | .oneTo _ n => m2534 n x
  | .unit t k1 f l => m2540 t s k1 f l x
  | .step t f st len => m2546 t f st (f + ((len : Int) - 1) * st) x

/-- base/array.jl:2554 `findfirst(::typeof(iszero), r::AbstractRange) =
findfirst(==(zero(first(r))), r)` (the `OneTo` method 2537 is more specific). -/
def m2554 : IRange → R (Option Int)
  | .oneTo _ n => m2537 n
  | r => findEq r.eltype 0 r

/-- base/array.jl:2555 `findfirst(::typeof(isone), r::AbstractRange) =
findfirst(==(one(first(r))), r)` (the `OneTo` method 2538 is more specific). -/
def m2555 : IRange → R (Option Int)
  | .oneTo _ n => m2538 n
  | r => findEq r.eltype 1 r

/-- The predicates the `findlast` specialisations accept. -/
inductive RangePred where
  | eq (s : IntTy) (x : Int)
  | iszero
  | isone

def findFirstPred (r : IRange) : RangePred → R (Option Int)
  | .eq s x => findEq s x r
  | .iszero => m2554 r
  | .isone => m2555 r

/-- base/array.jl:2728 `findlast(p, r::AbstractUnitRange{<:Integer}) = findfirst(p, r)`. -/
def m2728 (t : IntTy) (k1 f l : Int) (p : RangePred) : R (Option Int) := findFirstPred (.unit t k1 f l) p

/-- base/array.jl:2733 `findlast(p, r::StepRange{T,S}) = findfirst(p, r)`. -/
def m2733 (t : IntTy) (f s : Int) (len : Nat) (p : RangePred) : R (Option Int) :=
  findFirstPred (.step t f s len) p

/-! ### Scalar `getindex` of a range -/

/-- `unsafe_getindex(v::OneTo{T}, i) = convert(T, i)` behind the generic
`_getindex(v::AbstractRange, i)` (`checkbounds` first), base/range.jl:952, 984. -/
def getOneTo (t : IntTy) (n i : Int) : R Int :=
  if ¬ (1 ≤ i ∧ i ≤ n) then .error .bounds else
  if t.min ≤ i ∧ i ≤ t.max then .ok i else .error .inexact

/-- base/range.jl:968 `_getindex(v::UnitRange{T<:OverflowSafe}, i::Integer)`:
`val = v.start + (i - oneunit(i))` in `promote_type(T, typeof(i))`;
`_in_unit_range(v, val, i) || throw_boundserror(v, i)`; `val % T`. -/
def getUnit (t it : IntTy) (f l i : Int) : R Int :=
  let val := wrapInt (t.promote it) (f + wrapInt it (i - 1))
  if 0 < i ∧ val ≤ l ∧ f ≤ val then .ok (wrapInt t val) else .error .bounds

/-- base/range.jl:952 `_getindex(v::AbstractRange, i)` for a `StepRange{T,T}`:
`checkbounds` (base/range.jl:976 for `BitInteger64` element and index types,
`firstindex(v) <= i <= lastindex(v)` otherwise), then base/range.jl:985
`convert(T, first(v) + (i - oneunit(i))*step_hp(v))` in the promoted type. -/
def getStep (t it : IntTy) (f s : Int) (len : Nat) (i : Int) : R Int :=
  let l := f + ((len : Int) - 1) * s
  let inb : Bool :=
    if t.bits ≤ 64 ∧ it.bits ≤ 64 then
      let res := s * wrapInt it (i - 1) + f
      decide (0 < i) && (if 0 < s then decide (res ≤ l) else decide (res ≥ l))
    else decide (1 ≤ i ∧ i ≤ len)
  if ¬ inb then .error .bounds else
  let P := it.promote t
  let val := wrapInt P (f + wrapInt P (wrapInt it (i - 1) * s))
  if t.min ≤ val ∧ val ≤ t.max then .ok val else .error .inexact

/-- base/array.jl:3224 `getindex(v::AbstractRange, i::Integer)`: a `Bool` index
throws `ArgumentError`, any other index goes to `_getindex(v, i)`. -/
def m3224 (r : IRange) (it : IntTy) (isBool : Bool) (i : Int) : R Int :=
  if isBool then .error .argument else
  match r with
  | .oneTo t n => getOneTo t n i
  | .unit t _ f l => getUnit t it f l i
  | .step t f s len => getStep t it f s len i

/-! ### Lemmas -/

theorem pairsV_map_self (n : Nat) :
    pairsV (oneToList n) = (oneToList n).map fun i => (i, i) := by
  induction n with
  | zero => simp [oneToList, pairsV, idxFrom]
  | succ n ih =>
    simp only [oneToList, Int.toNat_natCast] at ih ⊢
    rw [List.range_succ, List.map_append, List.map_append]
    unfold pairsV at ih ⊢
    rw [idxFrom_append, ih]
    simp [idxFrom]; omega

theorem find_oneTo (n : Nat) (x : Int) :
    (oneToList n).find? (fun i => i == x) = if 1 ≤ x ∧ x ≤ n then some x else none := by
  induction n with
  | zero => rw [show oneToList ((0 : Nat) : Int) = [] by simp [oneToList], List.find?_nil, if_neg (by omega)]
  | succ n ih =>
    simp only [oneToList, Int.toNat_natCast] at ih ⊢
    rw [List.range_succ, List.map_append, List.find?_append, ih]
    by_cases h : 1 ≤ x ∧ x ≤ (n : Int)
    · rw [if_pos h, if_pos (by omega)]; rfl
    · rw [if_neg h]
      simp only [Option.none_or, List.map_cons, List.map_nil, List.find?_cons, List.find?_nil]
      by_cases h2 : x = (n : Int) + 1
      · subst h2; simp; omega
      · rw [if_neg (by omega)]
        cases hb : ((n : Int) + 1 == x) <;> simp_all

theorem firstIdx_oneTo (n x : Int) (hn : 0 ≤ n) :
    firstIdx (fun i => i == x) (oneToList n) = if 1 ≤ x ∧ x ≤ n then some x else none := by
  unfold firstIdx
  obtain ⟨m, rfl⟩ : ∃ m : Nat, n = m := ⟨n.toNat, by omega⟩
  rw [pairsV_map_self, List.find?_map]
  have : ((fun pr : Int × Int => pr.2 == x) ∘ fun i => (i, i)) = fun i => i == x := rfl
  rw [this, find_oneTo]
  split <;> rfl

/-! ### Properties -/

/-- `findfirst` on `OneTo(n)` (`n` at most `typemax(Int)`, so every element is an
`Int` key) agrees with the scan of `collect(OneTo(n))` for `==(x)`/`isequal(x)`
with any integer `x`, `iszero` and `isone`. -/
def P2534 : Prop := ∀ n x : Int, 0 ≤ n → n ≤ typemaxInt →
    m2534 n x = .ok (firstIdx (fun i => i == x) (oneToList n)) ∧
    m2537 n = .ok (firstIdx (fun i => i == 0) (oneToList n)) ∧
    m2538 n = .ok (firstIdx (fun i => i == 1) (oneToList n))

theorem p2534 : P2534 := by
  intro n x h0 h1
  unfold typemaxInt at h1
  refine ⟨?_, ?_, ?_⟩
  · rw [firstIdx_oneTo n x h0]; unfold m2534
    split
    · rw [toInt_ok' (by omega) (by omega)]; rfl
    · rfl
  · rw [firstIdx_oneTo n 0 h0, if_neg (by omega)]; rfl
  · rw [firstIdx_oneTo n 1 h0]; unfold m2538
    by_cases hz : n = 0
    · rw [if_pos hz, if_neg (by omega)]
    · rw [if_neg hz, if_pos (by omega)]

/-- Whether the element list of a range lies in its element type. -/
def IRange.Fits (r : IRange) : Prop :=
  match r with
  | .oneTo t n => 0 ≤ n ∧ n ≤ t.max
  | .unit t _ f l => t.min ≤ f ∧ f ≤ t.max ∧ t.min ≤ l ∧ l ≤ t.max ∧ f - 1 ≤ l
  | .step t f s len => s ≠ 0 ∧ t.min ≤ f ∧ f ≤ t.max ∧ t.min ≤ f + ((len : Int) - 1) * s ∧
      f + ((len : Int) - 1) * s ≤ t.max

/-- The parts of the scan contract the overflowing arithmetic cannot break: on
unit and step ranges, `findfirst` and `findlast` with `==(x)`, `isequal(x)`,
`iszero` or `isone` return `nothing` for an empty range and for `x` outside
`[minimum(r), maximum(r)]`, `findlast` equals `findfirst` (each value occurs at
most once), and on a unit range a value between the endpoints is never reported
missing. (The index itself can be wrong: refuted entry
`ranges-operations-findfirst-overflow`.) -/
def PRangeFindBounds : Prop :=
  (∀ (t s : IntTy) (k1 f l x : Int), (x < f ∨ l < x) → m2540 t s k1 f l x = .ok none) ∧
  (∀ (t s : IntTy) (k1 f l x : Int), f ≤ x → x ≤ l → m2540 t s k1 f l x ≠ .ok none) ∧
  (∀ (t : IntTy) (f s x : Int), s ≠ 0 → m2546 t f s (f - s) x = .ok none) ∧
  (∀ (t : IntTy) (f s : Int) (len : Nat) (x : Int), s ≠ 0 →
    (x < min f (f + ((len : Int) - 1) * s) ∨ max f (f + ((len : Int) - 1) * s) < x) →
    m2546 t f s (f + ((len : Int) - 1) * s) x = .ok none) ∧
  (∀ (t : IntTy) (k1 f l : Int) (p : RangePred), m2728 t k1 f l p = findFirstPred (.unit t k1 f l) p) ∧
  (∀ (t : IntTy) (f s : Int) (len : Nat) (p : RangePred), m2733 t f s len p = findFirstPred (.step t f s len) p) ∧
  (∀ r : IRange, m2554 r = match r with | .oneTo _ _ => .ok none | _ => findEq r.eltype 0 r) ∧
  (∀ r : IRange, m2555 r = match r with
    | .oneTo _ n => (if n = 0 then .ok none else .ok (some 1)) | _ => findEq r.eltype 1 r)

theorem pRangeFindBounds : PRangeFindBounds := by
  refine ⟨?_, ?_, ?_, ?_, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, ?_, ?_⟩
  · intro t s k1 f l x h; unfold m2540; rw [if_pos (by omega)]
  · intro t s k1 f l x h1 h2; unfold m2540; rw [if_neg (by omega)]
    simp only [bind, Except.bind, pure, Except.pure]
    split <;> simp
  · intro t f s x hs; unfold m2546 stepEmpty
    rw [if_pos (by
      have h1 : (f != f - s) = true := by simp; omega
      by_cases h : 0 < s <;> simp [h1, h] <;> omega)]
  · intro t f s len x hs h; unfold m2546
    split
    · rfl
    · simp only []
      rw [if_pos (by split <;> omega)]
  · intro r; cases r <;> rfl
  · intro r; cases r <;> rfl

/-- Scalar indexing of a range agrees with indexing `collect(r)`: a `Bool`
index throws `ArgumentError`; any other index `i` (a value of its `BitInteger`
type `it`) gives `collect(r)[i]` for `1 <= i <= length(r)` and `BoundsError`
otherwise. -/
def P3224 : Prop := ∀ (r : IRange) (it : IntTy) (i : Int), r.Fits → it.min ≤ i → i ≤ it.max →
    m3224 r it true i = .error .argument ∧
    m3224 r it false i = (if h : 1 ≤ i ∧ i ≤ r.elems.length then .ok (r.elems[(i - 1).toNat]'(by omega))
      else .error .bounds)

/-- `(-10:2:-1)[UInt(1)]` throws `InexactError`; `collect(-10:2:-1)[1] == -10`. -/
theorem m3224_unsigned : m3224 (.step .i64 (-10) 2 5) .u64 false 1 = .error .inexact := by rfl

theorem p3224_refuted : ¬ P3224 := by
  intro h
  have := (h (.step .i64 (-10) 2 5) .u64 1
    (by refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits])
    (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]) (by simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits])).2
  rw [m3224_unsigned] at this
  simp [IRange.elems, stepList] at this

end JuliaLean.MultidimCov.ArrayV2

import JuliaLean.RangesCov.Access

/-!
Equality, `cmp`, `intersect`/`union`, `_findin`, `issubset` and `in` methods of
`base/range.jl` (master `bbfa0ce4150`, lines 1141-1308, 1474-1488).
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JuliaLean.RangesCov

open JuliaLean JuliaLean.Registry

set_option linter.unusedSimpArgs false

namespace Compare

/-! ### Equality -/

/-- `_has_length_one(r::OrdinalRange) = first(r) == last(r)`, base/range.jl:1167. -/
def hasLengthOneOrdinal (r : Rng) : Bool := Ranges.Num.eq (Ranges.first r) (Ranges.last r)

/-- `_has_length_one(r::AbstractRange) = isone(length(r))`, base/range.jl:1168 (Float64
`StepRangeLen`). -/
def hasLengthOneSrl (r : FloatRanges.SRL) : Bool := decide (r.len.val = 1)

/-- The shared body of `==(r::T, s::T) where {T<:AbstractRange}` (base/range.jl:1141-1145),
`==(r::OrdinalRange, s::OrdinalRange)` (1147-1151) and
`==(r::Union{StepRange{T},StepRangeLen{T,T}}, s::...)` (1161-1165), for ordinal ranges. -/
def eqOrdinal (r s : Rng) : Bool :=
  if Ranges.isEmpty r then Ranges.isEmpty s
  else if hasLengthOneOrdinal r then hasLengthOneOrdinal s && Ranges.Num.eq (Ranges.first r) (Ranges.first s)
  else Ranges.Num.eq (Ranges.first r) (Ranges.first s) && Ranges.Num.eq (Ranges.step r) (Ranges.step s) &&
    Ranges.Num.eq (Ranges.last r) (Ranges.last s)

/-- `==(r::AbstractUnitRange, s::AbstractUnitRange)`, base/range.jl:1153-1154. -/
def eqUnit (r s : Rng) : Bool :=
  (Access.isemptyUnit r && Access.isemptyUnit s) ||
    (Ranges.Num.eq (Ranges.first r) (Ranges.first s) && Ranges.Num.eq (Ranges.last r) (Ranges.last s))

/-- `==(r::OneTo, s::OneTo) = last(r) == last(s)`, base/range.jl:1156. -/
def eqOneTo (r s : Rng) : Bool := Ranges.Num.eq (Ranges.last r) (Ranges.last s)

/-- `==(r::T, s::T) where {T<:Union{StepRangeLen,LinRange}}`, base/range.jl:1158-1159, for
`StepRangeLen{Float64,TwicePrecision{Float64},TwicePrecision{Float64},Int}`. -/
def eqSrl (r s : FloatRanges.SRL) : Bool :=
  (decide (r.len.val = 0) && decide (s.len.val = 0)) ||
    (Float.F64.eq r.first s.first && decide (r.len = s.len) && Float.F64.eq r.last s.last)

/-! ### `cmp`, base/range.jl:1185-1194 -/

/-- `cmp(x, y)` for Float64 elements, base/operators.jl:526. -/
def cmpF (x y : F64) : Int :=
  if Float.F64.isless x y then -1 else if Float.F64.isless y x then 1 else 0

/-- `cmp(x::Integer, y::Integer)`, base/operators.jl:537. -/
def cmpI (x y : Int) : Int := if x < y then -1 else if y < x then 1 else 0

/-- `cmp(r1::T, r2::T) where {T <: AbstractRange}`, base/range.jl:1185-1194, for plain
Float64 `StepRangeLen`s (`firstindex` is 1 for both). -/
def cmpFsrl (r1 r2 : FSRL) : Int :=
  if r1.len.val = 0 ∨ r2.len.val = 0 then cmpI (if r2.len.val = 0 then 1 else 0) (if r1.len.val = 0 then 1 else 0)
  else
    let f1 := Access.unsafeGetindexF r1 (FloatRanges.i64 1)
    let f2 := Access.unsafeGetindexF r2 (FloatRanges.i64 1)
    if !Float.F64.isequal f1 f2 then cmpF f1 f2
    else
      let n := if r1.len.val ≤ r2.len.val then r1.len else r2.len
      let x1 := Access.unsafeGetindexF r1 n
      let x2 := Access.unsafeGetindexF r2 n
      if !Float.F64.isequal x1 x2 then cmpF x1 x2 else cmpI r1.len.val r2.len.val

/-- The elements of a Float64 `StepRangeLen`, `r[1], ..., r[length(r)]`. -/
def elemsF (r : FSRL) : List F64 :=
  (List.range r.len.val.toNat).map (fun (k : Nat) => Access.unsafeGetindexF r (FloatRanges.i64 ((k : Int) + 1)))

/-- `cmp(A::AbstractVector, B::AbstractVector)`, base/abstractarray.jl: lexicographic with
`isequal`/`isless`, then lengths. -/
def cmpVec : List F64 → List F64 → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if !Float.F64.isequal a b then (if Float.F64.isless a b then -1 else 1) else cmpVec as bs

/-! ### Set operations -/

/-- `intersect(r::OneTo, s::OneTo) = OneTo(min(r.stop,s.stop))`, base/range.jl:1196. -/
def intersectOneTo (r s : Rng) : Jl Rng := Colon.oneTo (Ranges.Num.min r.stop s.stop)

/-- `union(r::OneTo, s::OneTo) = OneTo(max(r.stop,s.stop))`, base/range.jl:1197. -/
def unionOneTo (r s : Rng) : Jl Rng := Colon.oneTo (Ranges.Num.max r.stop s.stop)

/-- `intersect(r::AbstractUnitRange{<:Integer}, s::AbstractUnitRange{<:Integer})`,
base/range.jl:1199: `max(first(r),first(s)):min(last(r),last(s))`. -/
def intersectUnit (r s : Rng) : Jl Rng :=
  Colon.colonPromote2 (Ranges.Num.max (Ranges.first r) (Ranges.first s))
    (Ranges.Num.min (Ranges.last r) (Ranges.last s))

/-- `intersect(i::Integer, r::AbstractUnitRange{<:Integer}) = range(max(i, first(r)), length=in(i, r))`,
base/range.jl:1201. -/
def intersectScalar (i : Num) (r : Rng) : Jl Ranges.ResultRng := do
  let m ← Ranges.contains i r
  Ranges.rangeStartLength (Ranges.Num.max i (Ranges.first r)) (Ranges.Num.lit .bool (if m then 1 else 0))

/-- `intersect(r::AbstractUnitRange{<:Integer}, i::Integer) = intersect(i, r)`, base/range.jl:1203. -/
def intersectScalarRight (r : Rng) (i : Num) : Jl Ranges.ResultRng := intersectScalar i r

/-- `intersect(r1::AbstractRange, r2::AbstractRange)`, base/range.jl:1267-1275, on the
element lists: iterate the shorter range, `unique` it, and keep the elements `in` the
other one. -/
def intersectGeneric {α : Type} [BEq α] (r1 r2 : List α) (mem : α → List α → Bool) : List α :=
  if r1.length > r2.length then (r2.eraseDups).filter (fun x => mem x r1)
  else (r1.eraseDups).filter (fun x => mem x r2)

/-- `intersect(r1, r2, r3, r...)`, base/range.jl:1277-1283: a left fold. -/
def intersectMany {α : Type} (inter : α → α → α) (r1 r2 r3 : α) (rs : List α) : α :=
  rs.foldl inter (inter (inter r1 r2) r3)

/-- `issubset(r::OneTo, s::OneTo) = r.stop <= s.stop`, base/range.jl:1305. -/
def issubsetOneTo (r s : Rng) : Bool := decide (r.stop.val ≤ s.stop.val)

/-! ### Membership -/

/-- `in(x::Real, r::AbstractRange{<:Real}) = _in_range(x, r)`, base/range.jl:1474, and
`in(x::T, r::AbstractRange{T})`, base/range.jl:1477, for Float64 `StepRangeLen`. -/
def inReal (x : F64) (r : FloatRanges.SRL) : Jl Bool := r.contains x

/-- `in(x::AbstractChar, r::AbstractRange{<:AbstractChar})`, base/range.jl:1485-1488,
for a `StepRange{Char,Int}` (`minimum`/`maximum` via `min`/`max` of the endpoints). -/
def inChar (x : Nat) (r : Colon.CharRng) : Bool :=
  let empty := r.start != r.stop && (decide (r.step > 0) != decide (r.stop > r.start))
  !empty && (if r.step = 0 then x == r.start
    else decide (min r.start r.stop ≤ x) && decide (x ≤ max r.start r.stop) &&
      decide ((Colon.charSub x r.start) % r.step = 0))

/-! ### Properties -/

theorem max_zero_ty (n : Num) : (Ranges.Num.max (Ranges.Num.zero n.ty) n).ty = n.ty := by
  rcases n with ⟨ty, v⟩
  cases ty with
  | bool => rfl
  | bit t => cases t <;> rfl

theorem oneTo_eq (n : Num) : Colon.oneTo n = Ranges.oneTo n := by
  unfold Colon.oneTo Colon.oneToT Ranges.oneTo
  by_cases h : n.ty = .bool
  · simp [h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · have hc : Ranges.Num.cast n.ty (Ranges.Num.max (Ranges.Num.zero n.ty) n) =
        .ok (Ranges.Num.max (Ranges.Num.zero n.ty) n) := by
      have := cast_self (Ranges.Num.max (Ranges.Num.zero n.ty) n)
      rwa [max_zero_ty] at this
    simp [h, hc, bind, Except.bind, pure, Except.pure]

theorem num_eq_refl (x : Num) : Ranges.Num.eq x x = true := by simp [Ranges.Num.eq]

/-- Integer range equality: constructed same-type unit ranges are `==` exactly when they
have the same elements (both empty, or the same nonempty endpoints); `OneTo(n) == OneTo(m)`
iff `max(0,n) == max(0,m)`; the ordinal method is reflexive, equates all empty ranges,
and `_has_length_one` of a Float64
`StepRangeLen` is `length(r) == 1`. -/
def IntegerEquality : Prop :=
  (∀ t : IntTy, ∀ x y x' y' : JInt t, ∀ r s,
    Colon.unitRangeSame (mkI t x) (mkI t y) = .ok r → Colon.unitRangeSame (mkI t x') (mkI t y') = .ok s →
    (eqUnit r s = true ↔ ((y.val < x.val ∧ y'.val < x'.val) ∨ (x.val ≤ y.val ∧ x = x' ∧ y = y')))) ∧
  (∀ t : IntTy, ∀ x y : JInt t, ∀ r s, Colon.oneTo (mkI t x) = .ok r → Colon.oneTo (mkI t y) = .ok s →
    (eqOneTo r s = true ↔ max 0 x.val = max 0 y.val)) ∧
  (∀ r : Rng, eqOrdinal r r = true) ∧
  (∀ r s : Rng, Ranges.isEmpty r = true → (eqOrdinal r s = Ranges.isEmpty s)) ∧
  (∀ r : FloatRanges.SRL, hasLengthOneSrl r = decide (r.len.val = 1))

theorem integerEquality_proven : IntegerEquality := by
  refine ⟨?_, ?_, ?_, ?_, fun _ => rfl⟩
  · intro t x y x' y' r s hr hs
    have hcr := Colon.unitRangeConstruction_proven.1 t x y r hr
    have hcs := Colon.unitRangeConstruction_proven.1 t x' y' s hs
    rw [Colon.unitRangeSame_mkI] at hr hs
    have hkr : r.kind = .unit := by split at hr <;> (cases hr; rfl)
    have hks : s.kind = .unit := by split at hs <;> (cases hs; rfl)
    have hfr : (Ranges.first r).val = x.val := by simp [Ranges.first, hkr, hcr.1]
    have hfs : (Ranges.first s).val = x'.val := by simp [Ranges.first, hks, hcs.1]
    have hlr : (x.val ≤ y.val → (Ranges.last r).val = y.val) ∧
        (y.val < x.val → (Ranges.last r).val = x.val - 1) := by
      refine ⟨fun h => ?_, fun h => (hcr.2.2 h).1⟩
      simp [Ranges.last, hcr.2.1 h]
    have hls : (x'.val ≤ y'.val → (Ranges.last s).val = y'.val) ∧
        (y'.val < x'.val → (Ranges.last s).val = x'.val - 1) := by
      refine ⟨fun h => ?_, fun h => (hcs.2.2 h).1⟩
      simp [Ranges.last, hcs.2.1 h]
    have hxe : x = x' ↔ x.val = x'.val := Subtype.ext_iff
    have hye : y = y' ↔ y.val = y'.val := Subtype.ext_iff
    rw [hxe, hye]
    simp only [eqUnit, Access.isemptyUnit, Ranges.Num.eq, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, hfr, hfs]
    by_cases h1 : x.val ≤ y.val <;> by_cases h2 : x'.val ≤ y'.val
    · rw [hlr.1 h1, hls.1 h2]; omega
    · rw [hlr.1 h1, hls.2 (by omega)]; omega
    · rw [hlr.2 (by omega), hls.1 h2]; omega
    · rw [hlr.2 (by omega), hls.2 (by omega)]; omega
  · intro t x y r s hr hs
    rw [Colon.oneTo_mkI] at hr hs
    cases hr; cases hs
    have hz : wrapInt t 0 = 0 := wrapInt_of_inRange t 0 (by cases t <;> decide)
    have hwx : wrapInt t x.val = x.val := wrapInt_of_inRange t _ x.property
    have hwy : wrapInt t y.val = y.val := wrapInt_of_inRange t _ y.property
    simp only [eqOneTo, Ranges.last, Ranges.Num.eq, mkI_val, wrap_val', hz, decide_eq_true_eq]
    by_cases hx : 0 < x.val <;> by_cases hy : 0 < y.val <;> simp [hx, hy, hwx, hwy, hz] <;> omega
  · intro r
    unfold eqOrdinal
    split
    · assumption
    · split <;> simp [num_eq_refl, *]
  · intro r s h
    simp [eqOrdinal, h]

/-- `r == s` for two Float64 `StepRangeLen{Float64,TwicePrecision,TwicePrecision}` implies
equal elements (== on AbstractArrays compares elements). -/
def SrlEqElementwise : Prop :=
  ∀ (r s : FloatRanges.SRL), eqSrl r s = true → r.len.val ≥ 0 →
    ∀ i : I64, 1 ≤ i.val → i.val ≤ r.len.val → Float.F64.eq (r.unsafeGet i) (s.unsafeGet i) = true

/-- `StepRangeLen(TwicePrecision(0.0), TwicePrecision(0.1), 4)`. -/
def srlA : FloatRanges.SRL :=
  ⟨⟨Float.F64.ofBits 0, Float.F64.ofBits 0⟩, ⟨Float.F64.ofBits 0x3fb999999999999a, Float.F64.ofBits 0⟩,
    FloatRanges.i64 4, FloatRanges.i64 1⟩

/-- `StepRangeLen(TwicePrecision(0.0), TwicePrecision(nextfloat(0.1)), 4)`. -/
def srlB : FloatRanges.SRL :=
  ⟨⟨Float.F64.ofBits 0, Float.F64.ofBits 0⟩, ⟨Float.F64.ofBits 0x3fb999999999999b, Float.F64.ofBits 0⟩,
    FloatRanges.i64 4, FloatRanges.i64 1⟩

theorem srlEqElementwise_refuted : ¬ SrlEqElementwise := by
  intro h
  have he : eqSrl srlA srlB = true := by decide +kernel
  have hx := h srlA srlB he (by decide) (FloatRanges.i64 2) (by decide) (by decide)
  have hn : Float.F64.eq (srlA.unsafeGet (FloatRanges.i64 2)) (srlB.unsafeGet (FloatRanges.i64 2)) = false := by
    decide +kernel
  rw [hn] at hx
  cases hx

/-- `cmp(r1, r2)` of two Float64 ranges of the same type is the lexicographic `cmp` of
their element vectors (cmp docstring; `cmp(::AbstractVector, ::AbstractVector)`). -/
def CmpLexicographic : Prop :=
  ∀ r1 r2 : FSRL, 0 ≤ r1.len.val → 0 ≤ r2.len.val → cmpFsrl r1 r2 = cmpVec (elemsF r1) (elemsF r2)

/-- `StepRangeLen(0.0, 0.1, 4)`. -/
def fsrlA : FSRL := ⟨Float.F64.ofBits 0, Float.F64.ofBits 0x3fb999999999999a, FloatRanges.i64 4, FloatRanges.i64 1⟩
/-- `StepRangeLen(0.0, nextfloat(0.1), 4)`. -/
def fsrlB : FSRL := ⟨Float.F64.ofBits 0, Float.F64.ofBits 0x3fb999999999999b, FloatRanges.i64 4, FloatRanges.i64 1⟩

theorem cmpLexicographic_refuted : ¬ CmpLexicographic := by
  intro h
  have hc := h fsrlA fsrlB (by decide) (by decide)
  have h1 : cmpFsrl fsrlA fsrlB = 0 := by decide +kernel
  have h2 : cmpVec (elemsF fsrlA) (elemsF fsrlB) = -1 := by decide +kernel
  rw [h1, h2] at hc
  cases hc

/-- Set operations: `intersect`/`union` of `OneTo`s are `OneTo(min)`/`OneTo(max)` of the
stops; integer unit/unit intersection is `max(first):min(last)`, and both agree with the
model's `intersect`; `intersect(r, i)` is `intersect(i, r)`; the generic intersection
keeps exactly the deduplicated elements of the shorter input that are `in` the other;
the n-ary intersection is a left fold. -/
def SetOperations : Prop :=
  (∀ r s : Rng, intersectOneTo r s = Colon.oneTo (Ranges.Num.min r.stop s.stop) ∧
    unionOneTo r s = Colon.oneTo (Ranges.Num.max r.stop s.stop)) ∧
  (∀ r s : Rng, r.kind = .oneTo → s.kind = .oneTo → intersectOneTo r s = Ranges.intersect r s) ∧
  (∀ r s : Rng, intersectUnit r s = Colon.colonPromote2 (Ranges.Num.max (Ranges.first r) (Ranges.first s))
    (Ranges.Num.min (Ranges.last r) (Ranges.last s))) ∧
  (∀ (r : Rng) (i : Num), intersectScalarRight r i = intersectScalar i r) ∧
  (∀ (α : Type) [BEq α] (r1 r2 : List α) (mem : α → List α → Bool) (x : α),
    x ∈ intersectGeneric r1 r2 mem → (mem x r1 = true ∨ mem x r2 = true)) ∧
  (∀ (α : Type) (inter : α → α → α) (a b c : α), intersectMany inter a b c [] = inter (inter a b) c)

theorem setOperations_proven : SetOperations := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, ?_, fun _ _ => rfl, fun _ _ => rfl, ?_, fun _ _ _ _ _ => rfl⟩
  · intro r s hr hs
    simp only [intersectOneTo, Ranges.intersect, hr, hs, and_self, ite_true, Ranges.last]
    exact oneTo_eq _
  · intro α _ r1 r2 mem x hx
    unfold intersectGeneric at hx
    split at hx
    · exact Or.inl (List.mem_filter.mp hx).2
    · exact Or.inr (List.mem_filter.mp hx).2

/-- Searching and subsets: `_findin(r, span)` (base/range.jl:1286-1303) returns
`1:length(r)` when an increasing range lies inside `span`; `issubset(::OneTo, ::OneTo)`
compares stops and agrees with the model's `issubset`. -/
def FindinSubset : Prop :=
  (∀ r span n : Rng, ∀ len : Num, r.kind = .unit → (Ranges.step r).val > 0 →
    (Ranges.first span).val ≤ (Ranges.first r).val → (Ranges.last r).val ≤ (Ranges.last span).val →
    Ranges.length r = .ok len → Ranges.colon2 (Ranges.Num.lit (.bit .i64) 1) len = .ok n →
    Ranges.findallInUnit r span = .ok n) ∧
  (∀ r s : Rng, r.kind = .oneTo → s.kind = .oneTo → Ranges.issubset r s = .ok (issubsetOneTo r s))

theorem findinSubset_proven : FindinSubset := by
  refine ⟨?_, ?_⟩
  · intro r span n len hk hs h1 h2 hl hn
    simp [Ranges.findallInUnit, hs, hk, show (Ranges.first r).val ≥ (Ranges.first span).val by omega,
      h2, hl, bind, Except.bind, pure, Except.pure, hn]
  · intro r s hr hs
    unfold Ranges.issubset
    rw [if_pos ⟨hr, hs⟩]
    rfl

/-- Membership: `in(x::Real, r)` and `in(x::T, r::AbstractRange{T})` are `_in_range`;
for `Char` ranges, the first element is a member of a nonempty range and characters
outside `[minimum, maximum]` are not members (base/range.jl:1485-1488). -/
def MembershipMethods : Prop :=
  (∀ (x : F64) (r : FloatRanges.SRL), inReal x r = r.contains x) ∧
  (∀ r : Colon.CharRng, (r.start != r.stop && (decide (r.step > 0) != decide (r.stop > r.start))) = false →
    inChar r.start r = true) ∧
  (∀ (x : Nat) (r : Colon.CharRng), r.step ≠ 0 → (x < min r.start r.stop ∨ max r.start r.stop < x) →
    inChar x r = false)

theorem membershipMethods_proven : MembershipMethods := by
  refine ⟨fun _ _ => rfl, ?_, ?_⟩
  · intro r h
    simp only [inChar, h, Bool.not_false, Bool.true_and]
    split
    · simp
    · simp [Colon.charSub]
      all_goals omega
  · intro x r hs hx
    simp only [inChar, hs, ite_false]
    rcases hx with hx | hx <;> simp <;> omega

def entries : List Entry := []

end Compare

end JuliaLean.RangesCov

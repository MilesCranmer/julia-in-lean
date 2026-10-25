import JuliaLean.ArrayOps.Pure
import JuliaLean.ArrayOps.VecProps

/-!
Properties of the non-mutating operations, searches, reductions and index
machinery, and the refutations.
-/

namespace JuliaLean.ArrayOps

open JuliaLean
open JuliaLean.Float

/-! ### Specifications -/

/-- `v` with the window `s:n` (1-based, `1 ≤ s ≤ n ≤ length(v)`) reversed. -/
def reverseWindow {α : Type} (v : List α) (s n : Nat) : List α :=
  v.take (s - 1) ++ ((v.drop (s - 1)).take (n + 1 - s)).reverse ++ v.drop n

/-- Rotation to the right by `k` positions (`0 ≤ k < length(v)`): the last `k`
elements move to the front. -/
def rotateRight {α : Type} (v : List α) (k : Nat) : List α :=
  v.drop (v.length - k) ++ v.take (v.length - k)

/-- The last 1-based index `j ≤ i` with `f(v[j])`, if any. -/
def lastUpTo {α : Type} (f : α → Bool) (v : List α) (i : Int) : Option Int :=
  (((List.range v.length).map (fun (k : Nat) => (k : Int) + 1)).reverse).find? fun j =>
    decide (j ≤ i) && (v[(j - 1).toNat]?.map f).getD false

/-- The first 1-based index `j ≥ i` with `f(v[j])`, if any. -/
def firstAtLeast {α : Type} (f : α → Bool) (v : List α) (i : Int) : Option Int :=
  ((List.range v.length).map (fun (k : Nat) => (k : Int) + 1)).find? fun j =>
    decide (i ≤ j) && (v[(j - 1).toNat]?.map f).getD false

/-- `findmax`'s promise for a nonempty vector: `(v[i], i)` where `v[i]` is not
`isless` than any element and every earlier element is `isless` than it. -/
def IsFirstExtremum (lt : F64 → F64 → Bool) (v : List F64) (r : F64 × Nat) : Prop :=
  1 ≤ r.2 ∧ r.2 ≤ v.length ∧ v[r.2 - 1]? = some r.1 ∧
  (∀ y ∈ v, lt r.1 y = false) ∧ (∀ j, 1 ≤ j → j < r.2 → ∀ y, v[j - 1]? = some y → lt y r.1 = true)

/-- Product of the values of a list of integers. -/
def prodVal {t : IntTy} (v : List (JInt t)) : Int := (v.map (·.val)).foldr (· * ·) 1

/-- Sum of the values of a list of integers. -/
def sumVal {t : IntTy} (v : List (JInt t)) : Int := (v.map (·.val)).foldr (· + ·) 0

/-! ### Statements -/

/-- `reverse!(v, start, stop)` for indices of any integer type: for
`1 ≤ start ≤ stop ≤ length(v)` it reverses exactly `v[start:stop]`; for
`stop ≤ start` it leaves `v` unchanged. -/
def ReverseBangSpec : Prop :=
  ∀ (α : Type) [Inhabited α] (s t : IntTy) (v : List α) (start : JInt s) (stop : JInt t), v.length < 2 ^ 62 →
    IntTy.i64.min ≤ start.val → start.val ≤ IntTy.i64.max →
    IntTy.i64.min ≤ stop.val → stop.val ≤ IntTy.i64.max →
    (stop.val ≤ start.val → reverseBang v start stop = .ok v) ∧
    (1 ≤ start.val → start.val ≤ stop.val → stop.val ≤ v.length →
      reverseBang v start stop = .ok (reverseWindow v start.val.toNat stop.val.toNat))

/-- `reverse(v, start, stop)` agrees with `reverse!(copy(v), start, stop)`: same result,
or the same exception, for all indices. -/
def ReverseCopyAgrees : Prop :=
  ∀ (α : Type) [Inhabited α] (s t : IntTy) (v : List α) (start : JInt s) (stop : JInt t), v.length < 2 ^ 62 →
    reverseCopy v start stop = (reverseBang v start stop).map (·.map some)

/-- `circshift!(v, k)` and `circshift(v, k)` rotate right by `mod(k, length(v))` for a
shift of every integer type, including `typemin` and `typemax`. -/
def CircshiftSpec : Prop :=
  ∀ (α : Type) [Inhabited α] (t : IntTy) (v : List α) (k : JInt t), v.length < 2 ^ 62 →
    circshiftBang v k = .ok (rotateRight v (modShift k v.length).toNat) ∧
    circshift v k = rotateRight v (modShift k v.length).toNat

/-- `repeat(v; inner, outer)` with nonnegative `Int` counts returns each entry repeated
`inner` times, the whole repeated `outer` times, or throws `OverflowError` exactly when
`length(v)*inner` or `length(v)*inner*outer` exceeds `typemax(Int)`. -/
def RepeatSpec : Prop :=
  ∀ (α : Type) (v : List α) (inner outer : JInt64), v.length < 2 ^ 62 → 0 ≤ inner.val → 0 ≤ outer.val →
    repeatVec v (some inner) (some outer) =
      if v.length * inner.val ≤ IntTy.i64.max ∧ v.length * inner.val * outer.val ≤ IntTy.i64.max
      then .ok (List.flatten (List.replicate outer.val.toNat
        (v.flatMap fun x => List.replicate inner.val.toNat x)))
      else .error (.overflowError "checked_mul")

/-- `copyto!(a, doffs, a, soffs, n)` on one array behaves as copying from an
unaliased copy of `a`, for overlapping blocks in either direction and all integer
types of offsets and count. -/
def CopytoAliasSpec : Prop :=
  ∀ (α : Type) (s t u : IntTy) (a : List α) (doffs : JInt s) (soffs : JInt t) (n : JInt u), a.length < 2 ^ 62 →
    copyto a doffs none soffs n = copyto a doffs (some a) soffs n ∧
    (1 ≤ doffs.val → 1 ≤ soffs.val → 0 < n.val → doffs.val + n.val ≤ a.length + 1 →
      soffs.val + n.val ≤ a.length + 1 →
      copyto a doffs none soffs n = .ok (a.take (doffs.val - 1).toNat ++
        (a.drop (soffs.val - 1).toNat).take n.val.toNat ++ a.drop (doffs.val - 1 + n.val).toNat))

/-- `findnext(f, v, i)` returns the next index after or including `i` whose element
satisfies `f` (or `nothing`), and `findprev(f, v, i)` the previous one before or
including `i`, for every start `i` representable as `Int`. -/
def FindAllStarts : Prop :=
  ∀ (α : Type) (t : IntTy) (f : α → Bool) (v : List α) (i : JInt t), v.length < 2 ^ 62 →
    IntTy.i64.min ≤ i.val → i.val ≤ IntTy.i64.max →
    (findnext f v i).map (·.map (·.val)) = .ok (firstAtLeast f v i.val) ∧
    (findprev f v i).map (·.map (·.val)) = .ok (lastUpTo f v i.val)

/-- The same promise for starts in the documented range: `findnext` from
`1 ≤ i` (including past the end) and `findprev` from `i ≤ length(v)` (including
before the start). -/
def FindInRange : Prop :=
  ∀ (α : Type) (t : IntTy) (f : α → Bool) (v : List α) (i : JInt t), v.length < 2 ^ 62 →
    IntTy.i64.min ≤ i.val → i.val ≤ IntTy.i64.max →
    (1 ≤ i.val → (findnext f v i).map (·.map (·.val)) = .ok (firstAtLeast f v i.val)) ∧
    (i.val ≤ v.length → (findprev f v i).map (·.map (·.val)) = .ok (lastUpTo f v i.val))

/-- `findmax(v)` returns the first element that no other element is `isless`-greater
than, with its index; `findmin(v)` the first minimal one with `NaN` below every number
(`isgreater`); both throw `ArgumentError` on an empty vector. -/
def FindExtremaSpec : Prop :=
  ∀ (v : List F64), v.length < 2 ^ 62 →
    (v = [] → (∃ m, findmax v = .error (.argumentError m)) ∧ ∃ m, findmin v = .error (.argumentError m)) ∧
    (v ≠ [] → ∃ r r', findmax v = .ok r ∧ IsFirstExtremum F64.isless v r ∧
      findmin v = .ok r' ∧ IsFirstExtremum isgreater v r')

/-- `sum(v)` and `prod(v)` for a vector of any `BitInteger` type equal the exact sum and
product reduced (wrapping) into the documented result type (`Int`/`UInt` for narrower
types), whatever the pairwise association; in particular `sum(T[])` is zero and
`prod(T[])` is one of that type. -/
def SumProdSpec : Prop :=
  ∀ (t : IntTy) (v : List (JInt t)), v.length < 2 ^ 62 →
    sum v = JInt.wrap (sumTy t) (sumVal v) ∧ prod v = JInt.wrap (sumTy t) (prodVal v)

/-- `accumulate(op, v; init)` returns `[op(init, v[1]), op(op(init, v[1]), v[2]), ...]`,
and `cumsum(v)` of a `BitInteger` vector the running sums wrapped into the widened type. -/
def AccumulateSpec : Prop :=
  (∀ (α β : Type) (op : β → α → β) (init : β) (first : α → β) (v : List α),
    accumulate op (some init) first v = (v.scanl op init).tail) ∧
  (∀ (t : IntTy) (v : List (JInt t)), v.length < 2 ^ 62 →
    (cumsum v).map (·.val) =
      ((List.range v.length).map fun k => wrapInt (sumTy t) (sumVal (v.take (k + 1)))))

/-- `diff(v)` has `max(length(v) - 1, 0)` entries `v[i+1] - v[i]`, wrapping in the
element type. -/
def DiffSpec : Prop :=
  ∀ (t : IntTy) (v : List (JInt t)), v.length < 2 ^ 62 →
    (diff v).length = v.length - 1 ∧
    ∀ k (h : k + 1 < v.length),
      (diff v)[k]? = some (JInt.wrap t (v[k + 1].val - v[k].val))

/-- `vcat(r1, r2, ...)` of `Int` unit ranges whose lengths fit in `Int` is the
concatenation of their elements, or `OverflowError` when the total length exceeds
`typemax(Int)`. -/
def VcatRangesSpec : Prop :=
  ∀ (rs : List (JInt64 × JInt64)),
    (∀ r ∈ rs, r.1.val ≤ r.2.val + 1 ∧ r.2.val - r.1.val + 1 ≤ IntTy.i64.max) →
    vcatRanges rs =
      if (rs.map fun r => r.2.val - r.1.val + 1).foldr (· + ·) 0 ≤ IntTy.i64.max
      then .ok (rs.flatMap fun r => unitElems r.1 r.2)
      else .error (.overflowError "checked_add")

/-- `v[i]` for an index of any integer type whose value fits `to_index`
(`UInt` always does) returns the element when `checkbounds(Bool, v, i)` holds and
throws `BoundsError` otherwise. -/
def GetindexCheckbounds : Prop :=
  ∀ (α : Type) (t : IntTy) (v : List α) (i : JInt t), v.length < 2 ^ 62 →
    (t = .u64 ∨ (IntTy.i64.min ≤ i.val ∧ i.val ≤ IntTy.i64.max)) →
    (getindex v i).map some = if checkboundsInt v i then .ok v[(i.val - 1).toNat]? else .error .boundsError

/-- Indexing a vector, its `LinearIndices` or its `CartesianIndices` with an integer of
any type outside `1:length(v)` throws `BoundsError`. -/
def OutOfRangeBoundsError : Prop :=
  ∀ (α : Type) (t : IntTy) (v : List α) (i : JInt t), v.length < 2 ^ 62 → ¬ (1 ≤ i.val ∧ i.val ≤ v.length) →
    errOf (getindex v i) = some .boundsError ∧
    errOf (linearGet v.length i) = some .boundsError ∧
    errOf (cartesianGet v.length i) = some .boundsError

/-- For a vector of length `n` and an `Int` index `i`, `LinearIndices(v)[CartesianIndices(v)[i]]`
is `i` for `i ∈ 1:n`, and both conversions throw `BoundsError` outside. -/
def LinearCartesianRoundTrip : Prop :=
  ∀ (n : Nat) (i : JInt64),
    (cartesianGet n i >>= linearOfCartesian n) = linearGet n i ∧
    linearGet n i = (if 1 ≤ i.val ∧ i.val ≤ n then .ok i else .error .boundsError) ∧
    cartesianGet n i = (if 1 ≤ i.val ∧ i.val ≤ n then .ok i else .error .boundsError)

/-! ### Refutations -/

/-- `reverse!([1,2,3], 5, 5)` returns the vector, `reverse([1,2,3], 5, 5)` throws. -/
theorem reverseWindowOutside :
    errOf (reverseBang [1, 2, 3] (JInt.lit .i64 5) (JInt.lit .i64 5) : Jl (List Int)) = none ∧
    errOf (reverseCopy [(1 : Int), 2, 3] (JInt.lit .i64 5) (JInt.lit .i64 5)) = some .boundsError := by
  decide +kernel

theorem reverseCopyAgrees_refuted : ¬ ReverseCopyAgrees := by
  intro h
  have e := congrArg errOf (h Int .i64 .i64 [1, 2, 3] (JInt.lit .i64 5) (JInt.lit .i64 5) (by decide))
  revert e
  decide +kernel

/-- `findnext(iseven, [1,2], 0)` throws `BoundsError` although index `2` follows `0`. -/
theorem findnextZero :
    errOf (findnext (fun x : Int => x % 2 == 0) [1, 2] (JInt.lit .i64 0)) = some .boundsError := by
  decide +kernel

theorem findAllStarts_refuted : ¬ FindAllStarts := by
  intro h
  have e := congrArg errOf (h Int .i64 (fun x : Int => x % 2 == 0) [1, 2] (JInt.lit .i64 0)
    (by decide) (by decide) (by decide)).1
  revert e
  decide +kernel

/-- `LinearIndices(v)[UInt(2)^63]` throws `InexactError` for a 3-element vector,
while `v[UInt(2)^63]` throws `BoundsError`. -/
theorem linearIndicesUInt :
    errOf (linearGet 3 (JInt.lit .u64 (2 ^ 63))) = some (.inexactError "Int64") ∧
    errOf (getindex [(1 : Int), 2, 3] (JInt.lit .u64 (2 ^ 63))) = some .boundsError := by
  decide +kernel

theorem outOfRangeBoundsError_refuted : ¬ OutOfRangeBoundsError := by
  intro h
  have e := (h Int .u64 [1, 2, 3] (JInt.lit .u64 (2 ^ 63)) (by decide) (by decide)).2.1
  revert e
  decide +kernel

end JuliaLean.ArrayOps

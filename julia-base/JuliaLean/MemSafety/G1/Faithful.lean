import JuliaLean.ArrayOps
import JuliaLean.Combinatorics
import JuliaLean.Dicts
import JuliaLean.IOBuffers
import JuliaLean.Reduce
import JuliaLean.Strings

/-!
Source-path models for the unchecked accesses in group 1.  Every public
property below calls a function that computes the accessed span from the same
arguments as the Julia function.  A span is zero-based and half-open, although
the Julia source expressions cited in the docstrings are one-based.
-/

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

structure Access where
  capacity : Nat
  start : Nat
  count : Nat
  deriving Repr, DecidableEq

def Access.safe (a : Access) : Prop := a.start + a.count ≤ a.capacity

def accessesSafe (xs : List Access) : Prop := ∀ a ∈ xs, a.safe

def at0 (capacity index : Nat) : Access := ⟨capacity, index, 1⟩
def span0 (capacity start count : Nat) : Access := ⟨capacity, start, count⟩

/-! ## Checks followed by scalar accesses and copies -/

/-- `checkbounds(A, i)` followed by the access at `base/array.jl:212,243,1039`.
The `Int` index is converted to the zero-based storage ordinal only on the
successful branch. -/
def checkedScalarAccess (length : Nat) (i : Int) : List Access :=
  if 1 ≤ i ∧ i ≤ length then [at0 length (i - 1).toNat] else []

def CheckedScalarInBounds : Prop :=
  ∀ length i, accessesSafe (checkedScalarAccess length i)

theorem checkedScalarInBounds_proven : CheckedScalarInBounds := by
  intro length i
  unfold checkedScalarAccess accessesSafe Access.safe at0
  split <;> simp_all
  omega

def fitsInt (x : Int) : Bool := decide (-2 ^ 63 ≤ x ∧ x ≤ 2 ^ 63 - 1)

/-- `_copyto_impl!`, `base/array.jl:299-315`.  The source checks `n`, both
starting indices and both remaining lengths before converting the three
`Integer` arguments to `Int` and constructing the two `MemoryRef`s. -/
def checkedCopyAccesses (destLength srcLength : Nat) (doffs soffs n : Int) : List Access :=
  if n = 0 then []
  else if 0 < n ∧ 1 ≤ doffs ∧ doffs + n - 1 ≤ destLength ∧
      1 ≤ soffs ∧ soffs + n - 1 ≤ srcLength ∧
      fitsInt doffs ∧ fitsInt soffs ∧ fitsInt n then
    [span0 destLength (doffs - 1).toNat n.toNat,
     span0 srcLength (soffs - 1).toNat n.toNat]
  else []

def CheckedCopyInBounds : Prop :=
  ∀ destLength srcLength doffs soffs n,
    accessesSafe (checkedCopyAccesses destLength srcLength doffs soffs n)

theorem checkedCopyInBounds_proven : CheckedCopyInBounds := by
  intro destLength srcLength doffs soffs n
  unfold checkedCopyAccesses accessesSafe Access.safe span0
  split
  · simp
  · split
    · intro a ha
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · simp only [Access.safe, span0]
        have hs : ((doffs - 1).toNat : Int) = doffs - 1 :=
          Int.toNat_of_nonneg (by omega)
        have hn : (n.toNat : Int) = n := Int.toNat_of_nonneg (by omega)
        omega
      · simp only [Access.safe, span0]
        have hs : ((soffs - 1).toNat : Int) = soffs - 1 :=
          Int.toNat_of_nonneg (by omega)
        have hn : (n.toNat : Int) = n := Int.toNat_of_nonneg (by omega)
        omega
    · simp

/-- `copy(a::Array)`, `getindex(A, :)`, and `setindex!(A, X, :)` allocate or
use arrays whose storage length is the copied element count,
`base/array.jl:391-399,995-1001,1088-1095`. -/
def exactCopyAccesses (length : Nat) : List Access :=
  if length = 0 then [] else [span0 length 0 length, span0 length 0 length]

def ExactCopyInBounds : Prop := ∀ length, accessesSafe (exactCopyAccesses length)

theorem exactCopyInBounds_proven : ExactCopyInBounds := by
  intro length
  simp [exactCopyAccesses, accessesSafe, Access.safe, span0]

def ArrayCheckedCopiesInBounds : Prop := CheckedCopyInBounds ∧ ExactCopyInBounds

theorem arrayCheckedCopiesInBounds_proven : ArrayCheckedCopiesInBounds :=
  ⟨checkedCopyInBounds_proven, exactCopyInBounds_proven⟩

/-! ## Axis-derived loops -/

/-- The access trace of a loop over `eachindex`, `axes`, `keys`, or `pairs` of
the same linear storage. -/
def axisAccesses (length : Nat) : List Access :=
  (List.range length).map (at0 length)

def AxisLoopInBounds : Prop := ∀ length, accessesSafe (axisAccesses length)

theorem axisLoopInBounds_proven : AxisLoopInBounds := by
  intro length a h
  simp only [axisAccesses, List.mem_map] at h
  obtain ⟨i, hi, rfl⟩ := h
  simp only [List.mem_range] at hi
  simp [Access.safe, at0]
  omega

/-- The `afoldl` callback writes at its current one-based accumulator and
returns the successor, once for each remaining argument. -/
def literalFoldAccesses (capacity : Nat) : Nat → List Unit → List Access
  | _, [] => []
  | i, _ :: rest => at0 capacity (i - 1) :: literalFoldAccesses capacity (i + 1) rest

/-- `getindex(::Type{T}, vals...)`, non-`NTuple` branch:
allocate `length(vals)` elements and invoke `afoldl(1, vals...)`. -/
def literalAccesses (valueCount : Nat) : List Access :=
  literalFoldAccesses valueCount 1 (List.replicate valueCount ())

private theorem literalFold_safe (capacity i : Nat) (values : List Unit)
    (hi : 1 ≤ i) (h : i - 1 + values.length ≤ capacity) :
    accessesSafe (literalFoldAccesses capacity i values) := by
  induction values generalizing i with
  | nil => simp [literalFoldAccesses, accessesSafe]
  | cons v vs ih =>
      simp only [literalFoldAccesses, accessesSafe, List.mem_cons, forall_eq_or_imp]
      constructor
      · simp only [Access.safe, at0, List.length_cons] at *
        omega
      · apply ih
        · omega
        · simp only [List.length_cons] at h
          omega

def LiteralInBounds : Prop := ∀ n, accessesSafe (literalAccesses n)

theorem literalInBounds_proven : LiteralInBounds := by
  intro n
  unfold literalAccesses
  apply literalFold_safe
  · omega
  · simp

/-! ## Multidimensional Array indexing -/

def shapeProduct (dims : List Nat) : Nat := dims.foldr (· * ·) 1

def normalizeDims (dims : List Nat) (n : Nat) : List Nat :=
  dims ++ List.replicate (n - dims.length) 1

def normalizeCoords (coords : List Int) (n : Nat) : List Int :=
  coords ++ List.replicate (n - coords.length) 1

/-- `_sub2ind_recurse`, `base/abstractarray.jl:3165-3208`, for one-based Array
axes. -/
def sub2ind : List Nat → List Int → Int
  | [], _ => 1
  | _, [] => 1
  | [_], [i] => i
  | d :: ds, i :: is => i + d * (sub2ind ds is - 1)

def cartesianChecked (dims : List Nat) (coords : List Int) : Bool :=
  let n := max dims.length coords.length
  let ds := normalizeDims dims n
  let is := normalizeCoords coords n
  (ds.zip is).all fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1

/-- `checkbounds` followed by `_sub2ind`/`_to_linear_index`,
`base/array.jl:231-236,974-977,1042-1051`.  Missing or extra coordinates are
normalized with singleton trailing axes, as `checkbounds_indices` does. -/
def checkedCartesianAccess (dims : List Nat) (coords : List Int) : List Access :=
  if cartesianChecked dims coords then
    let n := max dims.length coords.length
    let ds := normalizeDims dims n
    let is := normalizeCoords coords n
    [at0 (shapeProduct ds) (sub2ind ds is - 1).toNat]
  else []

private theorem sub2ind_bounds : ∀ dims coords,
    dims.length = coords.length →
    (∀ p ∈ dims.zip coords, 1 ≤ p.2 ∧ p.2 ≤ p.1) →
    1 ≤ sub2ind dims coords ∧ sub2ind dims coords ≤ shapeProduct dims
  | [], [], _, _ => by simp [sub2ind, shapeProduct]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | [d], [i], _, h => by
      have hi := h (d, i) (by simp)
      simpa [sub2ind, shapeProduct] using hi
  | d :: d2 :: ds, i :: i2 :: is, hlen, h => by
      have hd := h (d, i) (by simp)
      have htail : ∀ p ∈ (d2 :: ds).zip (i2 :: is), 1 ≤ p.2 ∧ p.2 ≤ p.1 := by
        intro p hp
        exact h p (List.mem_cons_of_mem _ hp)
      have hlen' : (d2 :: ds).length = (i2 :: is).length := by simpa using hlen
      have ih := sub2ind_bounds (d2 :: ds) (i2 :: is) hlen' htail
      change 1 ≤ i + (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ∧
        i + (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ≤
          (d : Int) * shapeProduct (d2 :: ds)
      have hm0 : 0 ≤ (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) :=
        Int.mul_nonneg (by omega) (by omega)
      have hm1 : (d : Int) * (sub2ind (d2 :: ds) (i2 :: is) - 1) ≤
          (d : Int) * ((shapeProduct (d2 :: ds) : Int) - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have hid : (d : Int) * ((shapeProduct (d2 :: ds) : Int) - 1) =
          (d : Int) * shapeProduct (d2 :: ds) - d := by
        rw [Int.mul_sub, Int.mul_one]
      rw [hid] at hm1
      omega

private theorem normalized_lengths (dims : List Nat) (coords : List Int) :
    (normalizeDims dims (max dims.length coords.length)).length =
      (normalizeCoords coords (max dims.length coords.length)).length := by
  simp [normalizeDims, normalizeCoords]
  omega

def CheckedCartesianInBounds : Prop :=
  ∀ dims coords, accessesSafe (checkedCartesianAccess dims coords)

theorem checkedCartesianInBounds_proven : CheckedCartesianInBounds := by
  intro dims coords a ha
  simp only [checkedCartesianAccess] at ha
  split at ha
  · simp only [List.mem_singleton] at ha
    subst a
    simp only [Access.safe, at0]
    have hb := sub2ind_bounds
      (normalizeDims dims (max dims.length coords.length))
      (normalizeCoords coords (max dims.length coords.length))
      (normalized_lengths dims coords)
      (fun p hp => of_decide_eq_true (List.all_eq_true.mp ‹cartesianChecked dims coords = true› p hp))
    have hc : ((sub2ind (normalizeDims dims (max dims.length coords.length))
        (normalizeCoords coords (max dims.length coords.length)) - 1).toNat : Int) =
        sub2ind (normalizeDims dims (max dims.length coords.length))
          (normalizeCoords coords (max dims.length coords.length)) - 1 :=
      Int.toNat_of_nonneg (by omega)
    omega
  · simp at ha

/-- `filter(f, a::Array)`, `base/array.jl:3020-3029`.  The destination index is
incremented only when the predicate keeps the element. -/
def filterAccesses (capacity : Nat) : Nat → List Bool → List Access
  | _, [] => []
  | j, keep :: rest => at0 capacity j :: filterAccesses capacity (if keep then j + 1 else j) rest

private theorem filterAccesses_safe (capacity j : Nat) (keep : List Bool)
    (h : j + keep.length ≤ capacity) : accessesSafe (filterAccesses capacity j keep) := by
  induction keep generalizing j with
  | nil => simp [filterAccesses, accessesSafe]
  | cons b rest ih =>
      cases b with
      | false =>
          simp only [filterAccesses, Bool.false_eq_true, ↓reduceIte, accessesSafe,
            List.mem_cons, forall_eq_or_imp]
          constructor
          · simp [Access.safe, at0]
            simp only [List.length_cons] at h
            omega
          · apply ih
            simp only [List.length_cons] at h
            omega
      | true =>
          simp only [filterAccesses, ↓reduceIte, accessesSafe, List.mem_cons,
            forall_eq_or_imp]
          constructor
          · simp [Access.safe, at0]
            simp only [List.length_cons] at h
            omega
          · apply ih
            simp only [List.length_cons] at h
            omega

def FilterAllocatedInBounds : Prop :=
  ∀ keep, accessesSafe (filterAccesses keep.length 0 keep)

theorem filterAllocatedInBounds_proven : FilterAllocatedInBounds := by
  intro keep
  apply filterAccesses_safe
  omega

/-- `filter!(f, a)`, `base/array.jl:3066-3079`.  Both the iteration and the
compaction destination begin at `firstindex(a)`; the destination advances only
after a kept value. -/
def filterBangAccesses (length j : Nat) (keep : List Bool) : List Access :=
  filterAccesses length j keep

def FilterBangInBounds : Prop :=
  ∀ keep, accessesSafe (filterBangAccesses keep.length 0 keep)

theorem filterBangInBounds_proven : FilterBangInBounds := by
  intro keep
  unfold filterBangAccesses
  exact filterAccesses_safe keep.length 0 keep (by omega)

def FilterLoopsInBounds : Prop :=
  FilterAllocatedInBounds ∧ AxisLoopInBounds ∧ FilterBangInBounds

theorem filterLoopsInBounds_proven : FilterLoopsInBounds :=
  ⟨filterAllocatedInBounds_proven, axisLoopInBounds_proven, filterBangInBounds_proven⟩

/-! ## Vector compaction and iterator-indexed search -/

def uniqueAccesses (capacity : Nat) : Nat → Nat → List Bool → List Access
  | _, _, [] => []
  | current, i, fresh :: rest =>
      at0 capacity i ::
        if fresh then at0 capacity (current + 1) :: uniqueAccesses capacity (current + 1) (i + 1) rest
        else uniqueAccesses capacity current (i + 1) rest

private theorem uniqueAccesses_safe (capacity current i : Nat) (fresh : List Bool)
    (hc : current < i) (hi : i + fresh.length ≤ capacity) :
    accessesSafe (uniqueAccesses capacity current i fresh) := by
  induction fresh generalizing current i with
  | nil => simp [uniqueAccesses, accessesSafe]
  | cons b rest ih =>
      cases b with
      | false =>
          simp only [uniqueAccesses, Bool.false_eq_true, ↓reduceIte, accessesSafe,
            List.mem_cons, forall_eq_or_imp]
          constructor
          · simp [Access.safe, at0]
            simp only [List.length_cons] at hi
            omega
          · apply ih <;> simp only [List.length_cons] at hi ⊢ <;> omega
      | true =>
          simp only [uniqueAccesses, ↓reduceIte, accessesSafe, List.mem_cons,
            forall_eq_or_imp]
          refine ⟨?_, ?_, ?_⟩
          · simp [Access.safe, at0]
            simp only [List.length_cons] at hi
            omega
          · simp [Access.safe, at0]
            simp only [List.length_cons] at hi
            omega
          · apply ih <;> simp only [List.length_cons] at hi ⊢ <;> omega

/-- `unique!`, `base/set.jl:373-405`: the first input is read at `firstindex`,
then `i` advances every iteration while `current` advances only for a fresh
value. -/
def uniqueTrace (fresh : List Bool) : List Access :=
  if fresh = [] then []
  else at0 (fresh.length + 1) 0 :: uniqueAccesses (fresh.length + 1) 0 1 fresh

def UniqueInBounds : Prop := ∀ fresh, accessesSafe (uniqueTrace fresh)

theorem uniqueInBounds_proven : UniqueInBounds := by
  intro fresh
  by_cases h : fresh = []
  · simp [uniqueTrace, h, accessesSafe]
  · simp only [uniqueTrace, h, ↓reduceIte, accessesSafe, List.mem_cons, forall_eq_or_imp]
    constructor
    · simp [Access.safe, at0]
    · apply uniqueAccesses_safe <;> omega

/-- `_indexed_allunique`, `base/set.jl:579-592`, compares each position only
with later indices from the same `eachindex` iterator. -/
def indexedAlluniqueAccesses (length : Nat) : List Access :=
  (List.range length).flatMap fun i =>
    at0 length i :: (List.range (length - i - 1)).map fun k => at0 length (i + k + 1)

def IndexedAlluniqueInBounds : Prop :=
  ∀ length, accessesSafe (indexedAlluniqueAccesses length)

theorem indexedAlluniqueInBounds_proven : IndexedAlluniqueInBounds := by
  intro length a ha
  simp only [indexedAlluniqueAccesses, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_map] at ha
  obtain ⟨i, hi, rfl | ⟨k, hk, rfl⟩⟩ := ha
  · simp [Access.safe, at0]
    omega
  · simp [Access.safe, at0]
    omega

def SetUniqueInBounds : Prop := UniqueInBounds ∧ IndexedAlluniqueInBounds

theorem setUniqueInBounds_proven : SetUniqueInBounds :=
  ⟨uniqueInBounds_proven, indexedAlluniqueInBounds_proven⟩

/-- `reverse!`, `base/array.jl:2317-2333`.  After converting and checking both
endpoints, `k` counts the exact midpoint-bounded swap loop. -/
def reverseAccesses (length : Nat) (start stop : Int) : List Access :=
  if stop > start ∧ 1 ≤ start ∧ start ≤ length ∧ 1 ≤ stop ∧ stop ≤ length then
    let s := (start - 1).toNat
    let n := (stop - 1).toNat
    (List.range ((n - s + 1) / 2)).flatMap fun k =>
      [at0 length (s + k), at0 length (n - k)]
  else []

def ReverseInBounds : Prop := ∀ length start stop,
  accessesSafe (reverseAccesses length start stop)

theorem reverseInBounds_proven : ReverseInBounds := by
  intro length start stop a ha
  simp only [reverseAccesses] at ha
  split at ha
  · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at ha
    obtain ⟨k, hk, rfl | rfl⟩ := ha
    · simp only [Access.safe, at0]
      have hs : ((start - 1).toNat : Int) = start - 1 := Int.toNat_of_nonneg (by omega)
      have hn : ((stop - 1).toNat : Int) = stop - 1 := Int.toNat_of_nonneg (by omega)
      have hk' : k < (stop - start + 1).toNat := by
        have hd : 0 < (stop - start).toNat := by omega
        have hdiv : (((stop - start).toNat + 1) / 2) ≤ (stop - start).toNat := by omega
        omega
      omega
    · simp only [Access.safe, at0]
      have hs : ((start - 1).toNat : Int) = start - 1 := Int.toNat_of_nonneg (by omega)
      have hn : ((stop - 1).toNat : Int) = stop - 1 := Int.toNat_of_nonneg (by omega)
      omega
  · simp at ha

def sortedFindAccesses (capacityV capacityW : Nat) : Nat → Nat →
    List Int → List Int → Nat → List Access
  | _, _, [], _, _ => []
  | _, _, _, [], _ => []
  | _, _, _, _, 0 => []
  | i, j, vi :: vs, wj :: ws, fuel + 1 =>
      [at0 capacityV i, at0 capacityW j] ++
      if vi < wj then sortedFindAccesses capacityV capacityW (i + 1) j vs (wj :: ws) fuel
      else if wj < vi then sortedFindAccesses capacityV capacityW i (j + 1) (vi :: vs) ws fuel
      else sortedFindAccesses capacityV capacityW (i + 1) j vs (wj :: ws) fuel

private theorem sortedFindAccesses_safe : ∀ fuel capacityV capacityW i j v w,
    i + v.length ≤ capacityV → j + w.length ≤ capacityW →
    accessesSafe (sortedFindAccesses capacityV capacityW i j v w fuel)
  | 0, _, _, _, _, v, w, _, _ => by
      cases v <;> cases w <;> simp [sortedFindAccesses, accessesSafe]
  | fuel + 1, capacityV, capacityW, i, j, v, w, hv, hw => by
      cases v with
      | nil => simp [sortedFindAccesses, accessesSafe]
      | cons vi vs =>
        cases w with
        | nil => simp [sortedFindAccesses, accessesSafe]
        | cons wj ws =>
          intro a ha
          simp only [sortedFindAccesses, List.mem_append, List.mem_cons,
            List.mem_singleton, List.not_mem_nil, or_false] at ha
          rcases ha with (rfl | rfl) | ha
          · simp [Access.safe, at0]
            simp only [List.length_cons] at hv
            omega
          · simp [Access.safe, at0]
            simp only [List.length_cons] at hw
            omega
          · split at ha
            · exact sortedFindAccesses_safe _ _ _ _ _ _ _ (by
                simp only [List.length_cons] at hv
                omega) hw a ha
            · split at ha
              · exact sortedFindAccesses_safe _ _ _ _ _ _ _ hv (by
                  simp only [List.length_cons] at hw
                  omega) a ha
              · exact sortedFindAccesses_safe _ _ _ _ _ _ _ (by
                  simp only [List.length_cons] at hv
                  omega) hw a ha

/-- `_findin` uses `pairs(a)`, and `_sortedfindin` advances only iterators
created by `keys(v)` and `eachindex(w)`, `base/array.jl:2903-2955`. -/
def findLoopAccesses (v w : List Int) : List Access :=
  axisAccesses v.length ++ sortedFindAccesses v.length w.length 0 0 v w (v.length + w.length + 1)

def FindLoopsInBounds : Prop := ∀ v w, accessesSafe (findLoopAccesses v w)

theorem findLoopsInBounds_proven : FindLoopsInBounds := by
  intro v w a ha
  simp only [findLoopAccesses, List.mem_append] at ha
  rcases ha with ha | ha
  · exact axisLoopInBounds_proven v.length a ha
  · exact sortedFindAccesses_safe _ v.length w.length 0 0 v w (by omega) (by omega) a ha

def ArrayIteratorLoopsInBounds : Prop := ReverseInBounds ∧ FindLoopsInBounds

theorem arrayIteratorLoopsInBounds_proven : ArrayIteratorLoopsInBounds :=
  ⟨reverseInBounds_proven, findLoopsInBounds_proven⟩

/-! ## Allocation-sized Array callers -/

/-- A `HasLength`/`HasShape` iterator carries the documented iterator-trait
invariant that its yielded count equals `length(itr)`. -/
structure SizedIteration where
  reported : Nat
  yielded : Nat
  exactLength : yielded = reported

/-- `setindex_widen_up_to` and `collect_to!`, `base/array.jl:875-911`, for a
sized iterator.  The latter's built-in PartitionIterator violation is
separately refuted by `iterators-partition-range-overflow`. -/
def collectWidenAccesses (itr : SizedIteration) : List Access :=
  (List.range itr.yielded).map (at0 itr.reported)

def CollectWidenInBounds : Prop :=
  ∀ itr, accessesSafe (collectWidenAccesses itr)

theorem collectWidenInBounds_proven : CollectWidenInBounds := by
  intro itr a ha
  simp only [collectWidenAccesses, List.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  simp only [List.mem_range] at hi
  simp [Access.safe, at0]
  have heq := itr.exactLength
  omega

/-- Every caller of `__safe_setindex!`, `base/array.jl:124-162,445-466,
1358-1386,1776-1801`, obtains its index from the newly allocated length or
from the exact range just grown at the front or back. -/
def safeSetindexCallerAccesses (old added : Nat) : List Access :=
  let newLength := old + added
  (List.range added).flatMap fun k =>
    [at0 newLength (old + k), at0 newLength k]

def SafeSetindexCallersInBounds : Prop :=
  ∀ old added, accessesSafe (safeSetindexCallerAccesses old added)

theorem safeSetindexCallersInBounds_proven : SafeSetindexCallersInBounds := by
  intro old added a ha
  simp only [safeSetindexCallerAccesses, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
  obtain ⟨k, hk, rfl | rfl⟩ := ha <;> simp [Access.safe, at0] <;> omega

/-- Array assignment through an index vector, `base/array.jl:1063-1074`.
`setindex_shape_check` and `checkbounds(A, I)` are executed before `unalias`;
the two unaliased arrays preserve their lengths and axes. -/
def scatterAccesses (capacity : Nat) (indices : List Int) (sourceLength : Nat) : List Access :=
  if sourceLength = indices.length ∧ indices.all (fun i => 1 ≤ i ∧ i ≤ capacity) then
    axisAccesses sourceLength ++ axisAccesses indices.length ++
      indices.map fun i => at0 capacity (i - 1).toNat
  else []

def ScatterInBounds : Prop :=
  ∀ capacity indices sourceLength, accessesSafe (scatterAccesses capacity indices sourceLength)

theorem scatterInBounds_proven : ScatterInBounds := by
  intro capacity indices sourceLength a ha
  simp only [scatterAccesses] at ha
  split at ha
  · rename_i hc
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · rw [List.mem_append] at ha
      rcases ha with ha | ha
      · exact axisLoopInBounds_proven sourceLength a ha
      · exact axisLoopInBounds_proven indices.length a ha
    · simp only [List.mem_map] at ha
      obtain ⟨i, hi, hia⟩ := ha
      subst a
      simp only [Access.safe, at0]
      have hb := of_decide_eq_true (List.all_eq_true.mp hc.2 i hi)
      have hic : ((i - 1).toNat : Int) = i - 1 := Int.toNat_of_nonneg (by omega)
      omega
  · simp at ha

def ArrayAllocatedCallersInBounds : Prop :=
  CollectWidenInBounds ∧ SafeSetindexCallersInBounds ∧ ScatterInBounds

theorem arrayAllocatedCallersInBounds_proven : ArrayAllocatedCallersInBounds :=
  ⟨collectWidenInBounds_proven, safeSetindexCallersInBounds_proven, scatterInBounds_proven⟩

/-- `_insert!`, `base/array.jl:1871-1877`: `_growat!` first checks
`1 ≤ i ≤ oldLength+1` and increases the logical length by one. -/
def insertAccesses (oldLength : Nat) (i : Int) : List Access :=
  if 1 ≤ i ∧ i ≤ oldLength + 1 then
    [at0 (oldLength + 1) (i - 1).toNat]
  else []

def InsertInBounds : Prop := ∀ oldLength i,
  accessesSafe (insertAccesses oldLength i)

theorem insertInBounds_proven : InsertInBounds := by
  intro oldLength i
  unfold insertAccesses accessesSafe
  split
  · intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    simp only [Access.safe, at0]
    have hi : ((i - 1).toNat : Int) = i - 1 := Int.toNat_of_nonneg (by omega)
    omega
  · simp

def deleteCopyAccesses (capacity p q count : Nat) : List Access :=
  (List.range count).flatMap fun k =>
    [at0 capacity (p - 1 + k), at0 capacity (q - 1 + k)]

def deleteIndicesLoop (capacity : Nat) : Nat → Nat → List Nat → List Access
  | p, q, [] => deleteCopyAccesses capacity p q (capacity + 1 - q)
  | p, q, i :: rest =>
      if q ≤ i ∧ i ≤ capacity then
        deleteCopyAccesses capacity p q (i - q) ++
          at0 capacity (i - 1) ::
          deleteIndicesLoop capacity (p + (i - q)) (i + 1) rest
      else []

/-- `_deleteat!(a, inds)` and the Bool-mask overload,
`base/array.jl:1970-2014`.  The first index is checked, every later index must
be at least the current source cursor and at most `length(a)`, and both cursors
advance by the exact copied gap. -/
def deleteIndicesAccesses (capacity : Nat) (inds : List Nat) : List Access :=
  match inds with
  | [] => []
  | p :: rest =>
      if 1 ≤ p ∧ p ≤ capacity then
        at0 capacity (p - 1) :: deleteIndicesLoop capacity p (p + 1) rest
      else []

private theorem deleteCopy_safe (capacity p q count : Nat)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hd : p + count ≤ capacity + 1)
    (hs : q + count ≤ capacity + 1) :
    accessesSafe (deleteCopyAccesses capacity p q count) := by
  intro a ha
  simp only [deleteCopyAccesses, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
  obtain ⟨k, hk, rfl | rfl⟩ := ha <;> simp [Access.safe, at0] <;> omega

private theorem deleteIndicesLoop_safe : ∀ fuel capacity p q inds,
    inds.length ≤ fuel → 1 ≤ p → p < q → q ≤ capacity + 1 →
    accessesSafe (deleteIndicesLoop capacity p q inds)
  | _, _, _, _, [], _, hp, hpq, hq => by
      apply deleteCopy_safe <;> omega
  | 0, _, _, _, _ :: _, h, _, _, _ => by simp at h
  | fuel + 1, capacity, p, q, i :: rest, hfuel, hp, hpq, hq => by
      simp only [deleteIndicesLoop]
      split
      · intro a ha
        simp only [List.mem_append, List.mem_cons] at ha
        rcases ha with ha | rfl | ha
        · apply deleteCopy_safe capacity p q (i - q) <;> omega
        · simp [Access.safe, at0]; omega
        · apply deleteIndicesLoop_safe fuel capacity (p + (i - q)) (i + 1) rest
          all_goals simp only [List.length_cons] at hfuel ⊢ <;> omega
      · simp [accessesSafe]

def DeleteIndicesInBounds : Prop := ∀ capacity inds,
  accessesSafe (deleteIndicesAccesses capacity inds)

theorem deleteIndicesInBounds_proven : DeleteIndicesInBounds := by
  intro capacity inds
  cases inds with
  | nil => simp [deleteIndicesAccesses, accessesSafe]
  | cons p rest =>
    simp only [deleteIndicesAccesses]
    split
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp [Access.safe, at0]; omega
      · exact deleteIndicesLoop_safe rest.length capacity p (p + 1) rest
          (by omega) (by omega) (by omega) (by omega) a ha
    · simp [accessesSafe]

/-- The two `vcat` loops, `base/array.jl:2351-2364`: the first computes the
total allocation, and the second advances `nd` by each current vector length. -/
def vcatTrace (capacity : Nat) : Nat → List Nat → List Access
  | _, [] => []
  | dest, n :: rest =>
      span0 capacity dest n :: span0 n 0 n :: vcatTrace capacity (dest + n) rest

private theorem vcatTrace_safe (capacity dest : Nat) (lengths : List Nat)
    (h : dest + lengths.sum ≤ capacity) : accessesSafe (vcatTrace capacity dest lengths) := by
  induction lengths generalizing dest with
  | nil => simp [vcatTrace, accessesSafe]
  | cons n rest ih =>
      simp only [vcatTrace, accessesSafe, List.mem_cons, forall_eq_or_imp,
        List.sum_cons] at h ⊢
      refine ⟨?_, ?_, ?_⟩
      · simp [Access.safe, span0]; omega
      · simp [Access.safe, span0]
      · apply ih; omega

def vcatAccesses (lengths : List Nat) : List Access :=
  let total := lengths.sum
  if total ≤ 2 ^ 63 - 1 then vcatTrace total 0 lengths else []

def VcatInBounds : Prop := ∀ lengths, accessesSafe (vcatAccesses lengths)

theorem vcatInBounds_proven : VcatInBounds := by
  intro lengths
  unfold vcatAccesses
  dsimp
  split
  · apply vcatTrace_safe; omega
  · simp [accessesSafe]

/-! ## Bootstrap and broadcast helpers -/

def strcatAccesses (xBytes yBytes : Nat) : List Access :=
  [span0 (xBytes + yBytes) 0 xBytes,
   span0 (xBytes + yBytes) xBytes yBytes]

def BootstrapStrcatInBounds : Prop := ∀ xBytes yBytes,
  accessesSafe (strcatAccesses xBytes yBytes)

theorem bootstrapStrcatInBounds_proven : BootstrapStrcatInBounds := by
  intro xBytes yBytes
  simp [strcatAccesses, accessesSafe, Access.safe, span0]

/-- `conj!`, `base/abstractarraymath.jl:194`, calls `broadcast!` with the same
array as source and destination; broadcast's axis check and iterator therefore
compute the identical ordinal for both accesses. -/
def broadcastConjAccesses (length : Nat) : List Access :=
  axisAccesses length ++ axisAccesses length

def BroadcastConjInBounds : Prop := ∀ length,
  accessesSafe (broadcastConjAccesses length)

theorem broadcastConjInBounds_proven : BroadcastConjInBounds := by
  intro length a ha
  simp only [broadcastConjAccesses, List.mem_append] at ha
  rcases ha with ha | ha <;> exact axisLoopInBounds_proven length a ha

def zipMul : List Nat → List Nat → List Nat
  | d :: ds, c :: cs => d * c :: zipMul ds cs
  | _, _ => []

def repeatCoords (inner : Bool) : List Nat → List Nat → List Int → List Int → List Int
  | d :: ds, c :: cs, i :: is, j :: js =>
      (if inner then (i - 1) * c + j else i + d * (j - 1)) ::
        repeatCoords inner ds cs is js
  | _, _, _, _ => []

def coordsWithin (dims : List Nat) (coords : List Int) : Prop :=
  dims.length = coords.length ∧
    ∀ p ∈ dims.zip coords, 1 ≤ p.2 ∧ p.2 ≤ p.1

def coordsWithinB (dims : List Nat) (coords : List Int) : Bool :=
  decide (dims.length = coords.length) &&
    (dims.zip coords).all fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1

private theorem coordsWithinB_true (dims : List Nat) (coords : List Int)
    (h : coordsWithinB dims coords = true) : coordsWithin dims coords := by
  unfold coordsWithinB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun p hp => of_decide_eq_true (List.all_eq_true.mp h.2 p hp)⟩

def uncheckedCartesianAccess (dims : List Nat) (coords : List Int) : List Access :=
  [at0 (shapeProduct dims) (sub2ind dims coords - 1).toNat]

private theorem uncheckedCartesian_safe (dims : List Nat) (coords : List Int)
    (h : coordsWithin dims coords) : accessesSafe (uncheckedCartesianAccess dims coords) := by
  intro a ha
  simp only [uncheckedCartesianAccess, List.mem_singleton] at ha
  subst a
  simp only [Access.safe, at0]
  have hb := sub2ind_bounds dims coords h.1 h.2
  have hc : ((sub2ind dims coords - 1).toNat : Int) = sub2ind dims coords - 1 :=
    Int.toNat_of_nonneg (by omega)
  omega

private theorem repeatHead_bounds (d c : Nat) (i j : Int) (inner : Bool)
    (hi : 1 ≤ i ∧ i ≤ d) (hj : 1 ≤ j ∧ j ≤ c) :
    let out := if inner then (i - 1) * c + j else i + d * (j - 1)
    1 ≤ out ∧ out ≤ d * c := by
  dsimp
  cases inner with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hm0 : 0 ≤ (d : Int) * (j - 1) := Int.mul_nonneg (by omega) (by omega)
      have hm1 : (d : Int) * (j - 1) ≤ (d : Int) * ((c : Int) - 1) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have heq : (d : Int) * ((c : Int) - 1) = d * c - d := by
        rw [Int.mul_sub, Int.mul_one]
      rw [heq] at hm1
      omega
  | true =>
      simp only [↓reduceIte]
      have hm0 : 0 ≤ (i - 1) * (c : Int) := Int.mul_nonneg (by omega) (by omega)
      have hm1 : (i - 1) * (c : Int) ≤ ((d : Int) - 1) * c :=
        Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
      have heq : ((d : Int) - 1) * c = d * c - c := by
        rw [Int.sub_mul, Int.one_mul]
      rw [heq] at hm1
      omega

private theorem repeatCoords_within : ∀ dims counts I J inner,
    dims.length = counts.length → coordsWithin dims I → coordsWithin counts J →
    coordsWithin (zipMul dims counts) (repeatCoords inner dims counts I J)
  | [], [], [], [], _, _, _, _ => by simp [coordsWithin, zipMul, repeatCoords]
  | d :: ds, c :: cs, i :: is, j :: js, inner, hlen, hI, hJ => by
      have hItail : coordsWithin ds is :=
        ⟨by simpa [coordsWithin] using hI.1,
         fun p hp => hI.2 p (List.mem_cons_of_mem _ hp)⟩
      have hJtail : coordsWithin cs js :=
        ⟨by simpa [coordsWithin] using hJ.1,
         fun p hp => hJ.2 p (List.mem_cons_of_mem _ hp)⟩
      have htail := repeatCoords_within ds cs is js inner (by simpa using hlen) hItail hJtail
      constructor
      · simpa [zipMul, repeatCoords] using congrArg Nat.succ htail.1
      · intro p hp
        simp only [zipMul, repeatCoords, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · apply repeatHead_bounds
          · exact hI.2 (d, i) (by simp)
          · exact hJ.2 (c, j) (by simp)
        · exact htail.2 p hp
  | [], _ :: _, _, _, _, h, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | _ :: _, _ :: _, [], _, _, _, h, _ => by simp [coordsWithin] at h
  | _ :: _, _ :: _, _ :: _, [], _, _, _, h => by simp [coordsWithin] at h

/-- Generic `repeat_outer`/`repeat_inner`, `base/abstractarraymath.jl:583-611`.
The function computes `TIJ` componentwise from the two Cartesian loop indices,
then computes the unchecked column-major linear ordinal of `out[IJ]`. -/
def genericRepeatAccesses (dims counts : List Nat) (I J : List Int) (inner : Bool) : List Access :=
  if dims.length = counts.length && coordsWithinB dims I && coordsWithinB counts J then
    let outDims := zipMul dims counts
    let IJ := repeatCoords inner dims counts I J
    uncheckedCartesianAccess outDims IJ ++ uncheckedCartesianAccess dims I
  else []

def GenericRepeatInBounds : Prop := ∀ dims counts I J inner,
  accessesSafe (genericRepeatAccesses dims counts I J inner)

theorem genericRepeatInBounds_proven : GenericRepeatInBounds := by
  intro dims counts I J inner a ha
  simp only [genericRepeatAccesses] at ha
  split at ha
  · simp only [List.mem_append] at ha
    have hI : coordsWithin dims I := coordsWithinB_true dims I (by simp_all)
    have hJ : coordsWithin counts J := coordsWithinB_true counts J (by simp_all)
    rcases ha with ha | ha
    · apply uncheckedCartesian_safe _ _ (repeatCoords_within dims counts I J inner
        (by simp_all) hI hJ) a ha
    · exact uncheckedCartesian_safe dims I hI a ha
  · simp at ha

/-! ## Deprecated no-shift SubString constructor -/

/-- The representation invariant required by every operation on a `SubString`:
its signed offset and code-unit count describe a span inside the parent. -/
def validSubString (ss : Strings.JSub) : Prop :=
  0 ≤ ss.offset.val ∧ 0 ≤ ss.ncu.val ∧
    ss.offset.val + ss.ncu.val ≤ ss.str.bytes.length

/-- The first deprecated method at `base/deprecated.jl:704-710`. The old
arguments are a zero-based offset and a signed code-unit count. It computes both
endpoints, validates them, and calls `raw_substring` with bounds checks removed. -/
def deprecatedNoshiftString (s : Strings.JStr) (i n : JInt64) : Strings.SJl Strings.JSub :=
  let first := i + Strings.ix 1
  if !(decide (i.val = 0) && decide (n.val = 0)) then
    match Strings.prevind s (n + i + Strings.ix 1) with
    | .error e => .error e
    | .ok last =>
      if !Strings.isvalidAt s first then .error (.stringIndexError first.val)
      else if !Strings.isvalidAt s last then .error (.stringIndexError last.val)
      else Strings.rawSubstring s first n false
  else Strings.rawSubstring s first n false

/-- The second deprecated method at `base/deprecated.jl:717-723`, through the
unchecked `raw_substring` call. `SubString{T}(ss)` after that call only wraps
the returned view and cannot repair an invalid offset or count. -/
def deprecatedNoshiftSubString (s : Strings.JSub) (i n : JInt64) : Strings.SJl Strings.JSub :=
  let first := i + Strings.ix 1
  let localView := s.view
  if !(decide (i.val = 0) && decide (n.val = 0)) then
    match Strings.prevind localView (n + i + Strings.ix 1) with
    | .error e => .error e
    | .ok last =>
      if !Strings.isvalidAt localView first then .error (.stringIndexError first.val)
      else if !Strings.isvalidAt localView last then .error (.stringIndexError last.val)
      else Strings.rawSubstring s.str (first + s.offset) n false
  else Strings.rawSubstring s.str (first + s.offset) n false

/-- Both deprecated public caller paths must preserve the SubString
representation invariant on every successful result. -/
def DeprecatedSubstringValid : Prop :=
  (∀ s i n ss, deprecatedNoshiftString s i n = .ok ss → validSubString ss) ∧
  (∀ s i n ss, validSubString s →
    deprecatedNoshiftSubString s i n = .ok ss → validSubString ss)

theorem deprecatedSubstringValid_refuted : ¬ DeprecatedSubstringValid := by
  intro h
  let result : Strings.JSub :=
    ⟨Strings.strABC, Strings.ix 2, Strings.ix (-1)⟩
  have hr : deprecatedNoshiftString Strings.strABC (Strings.ix 2) (Strings.ix (-1)) =
      .ok result := by decide
  have hv := h.1 Strings.strABC (Strings.ix 2) (Strings.ix (-1)) result hr
  have hn : (Strings.ix (-1)).val = -1 := by decide
  have hnonneg : 0 ≤ result.ncu.val := hv.2.1
  change 0 ≤ (Strings.ix (-1)).val at hnonneg
  rw [hn] at hnonneg
  omega

/-! ## Vector capacity changes -/

structure VectorState where
  capacity : Nat
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq

/-- Array representation invariant checked explicitly by the growth internals
at `base/array.jl:1120-1125,1173-1179`. -/
def VectorState.valid (a : VectorState) : Prop :=
  1 ≤ a.offset ∧ a.offset - 1 + a.length ≤ a.capacity

/-- `_growbeg!`'s no-copy branch and `_growat!`'s preferred-start branch,
`base/array.jl:1151-1168,1230-1256`. -/
def frontGrowthAccesses (a : VectorState) (i delta : Nat) : List Access :=
  if delta = 0 then []
  else if delta ≤ a.offset - 1 then
    if i = 1 then
      [span0 a.capacity (a.offset - delta - 1) (a.length + delta)]
    else if 1 < i ∧ i ≤ a.length ∧ i ≤ a.length / 2 then
      [span0 a.capacity (a.offset - delta - 1) i,
       span0 a.capacity (a.offset - 1) i,
       span0 a.capacity (a.offset - delta - 1 + i - 1) delta]
    else []
  else []

def FrontGrowthInBounds : Prop := ∀ a, a.valid → ∀ i delta,
  accessesSafe (frontGrowthAccesses a i delta)

theorem frontGrowthInBounds_proven : FrontGrowthInBounds := by
  intro a hv i delta
  unfold VectorState.valid at hv
  unfold frontGrowthAccesses accessesSafe
  split
  · simp
  · split
    · split
      · intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        simp [Access.safe, span0]
        omega
      · split
        · intro x hx
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> simp [Access.safe, span0] <;> omega
        · simp
    · simp

/-- `_growat!`'s in-place tail branch, `base/array.jl:1257-1262`. -/
def tailGrowthAccesses (a : VectorState) (i delta : Nat) : List Access :=
  let newLength := a.length + delta
  if 1 < i ∧ i ≤ a.length ∧ a.offset - 1 + newLength ≤ a.capacity then
    [span0 a.capacity (a.offset - 1 + i - 1) (a.length - i + 1),
     span0 a.capacity (a.offset - 1 + delta + i - 1) (a.length - i + 1),
     span0 a.capacity (a.offset - 1 + i - 1) delta]
  else []

def TailGrowthInBounds : Prop := ∀ a, a.valid → ∀ i delta,
  accessesSafe (tailGrowthAccesses a i delta)

theorem tailGrowthInBounds_proven : TailGrowthInBounds := by
  intro a hv i delta
  unfold VectorState.valid at hv
  unfold tailGrowthAccesses accessesSafe
  dsimp
  split
  · intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [Access.safe, span0] <;> omega
  · simp

/-- `_deletebeg!` and `_deleteend!`, `base/array.jl:1278-1310`. -/
def edgeDeleteAccesses (a : VectorState) (delta : Nat) (front : Bool) : List Access :=
  if delta ≤ a.length then
    if front then
      [span0 a.capacity (a.offset - 1) delta,
       span0 a.capacity (a.offset - 1 + delta) (a.length - delta)]
    else [span0 a.capacity (a.offset - 1 + a.length - delta) delta]
  else []

def EdgeDeleteInBounds : Prop := ∀ a, a.valid → ∀ delta front,
  accessesSafe (edgeDeleteAccesses a delta front)

theorem edgeDeleteInBounds_proven : EdgeDeleteInBounds := by
  intro a hv delta front
  unfold VectorState.valid at hv
  unfold edgeDeleteAccesses accessesSafe
  split
  · cases front <;> simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false, forall_eq_or_imp]
    · simp [Access.safe, span0]
      omega
    · constructor <;> simp [Access.safe, span0] <;> omega
  · simp

/-- The non-front branch of `_deleteat!`, `base/array.jl:1312-1326`.
The front branch is separately refuted by the wrapping-range witness in
`arrayops-deleteat-range-overflow`. -/
def deleteAtTailAccesses (a : VectorState) (i delta : Nat) : List Access :=
  if 1 ≤ i ∧ i ≤ a.length ∧ i + delta ≤ a.length + 1 ∧
      ¬(2 * i + delta ≤ a.length) then
    [span0 a.capacity (a.offset - 1 + i - 1) (a.length + 1 - delta - i),
     span0 a.capacity (a.offset - 1 + i + delta - 1) (a.length + 1 - delta - i)]
  else []

def DeleteAtTailInBounds : Prop := ∀ a, a.valid → ∀ i delta,
  accessesSafe (deleteAtTailAccesses a i delta)

theorem deleteAtTailInBounds_proven : DeleteAtTailInBounds := by
  intro a hv i delta
  unfold VectorState.valid at hv
  unfold deleteAtTailAccesses accessesSafe
  split
  · intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> simp [Access.safe, span0] <;> omega
  · simp

/-- The direct-allocation branch of `sizehint!`, plus the `first=true` branch's
restored reference after `_growbeg!`, `base/array.jl:1617-1647`. -/
def sizehintAccesses (a : VectorState) (requested : Nat) (first : Bool) : List Access :=
  let size := max requested a.length
  let increment := size - a.length
  let start := if first then increment else 0
  [span0 size start a.length, span0 size start a.length]

def SizehintInBounds : Prop := ∀ a, a.valid → ∀ requested first,
  accessesSafe (sizehintAccesses a requested first)

theorem sizehintInBounds_proven : SizehintInBounds := by
  intro a hv requested first x hx
  simp only [sizehintAccesses, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> simp only [Access.safe, span0]
  all_goals split <;> omega

def SimpleVectorMovesInBounds : Prop :=
  FrontGrowthInBounds ∧ TailGrowthInBounds ∧ EdgeDeleteInBounds ∧
  DeleteAtTailInBounds ∧ SizehintInBounds

theorem simpleVectorMovesInBounds_proven : SimpleVectorMovesInBounds :=
  ⟨frontGrowthInBounds_proven, tailGrowthInBounds_proven, edgeDeleteInBounds_proven,
   deleteAtTailInBounds_proven, sizehintInBounds_proven⟩

/-- Exact `overallocation` computation reused from the IOBuffer/Array source
model (`base/array.jl:1102-1112`). -/
def overallocationNat (n : Nat) : Nat :=
  (JuliaLean.IOBuffers.overallocation (JuliaLean.IOBuffers.i n)).val.toNat

def centeredCapacity (base length delta : Nat) : Nat :=
  max (overallocationNat base) (length + 2 * delta + 1)

def centeredOffset (capacity newLength : Nat) : Nat :=
  (capacity - newLength) / 2 + 1

/-- The newly allocated branches of `_growbeg_internal!` and `_growat!`,
`base/array.jl:1116-1148,1263-1274`.  `site` is `none` for grow-begin and the
checked insertion index for grow-at. -/
def centeredAllocationAccesses (a : VectorState) (delta : Nat) (site : Option Nat) : List Access :=
  let newLength := a.length + delta
  let base := match site with | none => a.length | some _ => a.capacity
  let newCapacity := centeredCapacity base a.length delta
  let newOffset := centeredOffset newCapacity newLength
  if newCapacity ≤ 2 ^ 63 - 1 then
    match site with
    | none =>
      [span0 a.capacity (a.offset - 1) a.length,
       span0 newCapacity (newOffset + delta - 1) a.length,
       span0 newCapacity (newOffset - 1) 0]
    | some i =>
      if 1 < i ∧ i ≤ a.length then
        [span0 a.capacity (a.offset - 1) (i - 1),
         span0 newCapacity (newOffset - 1) (i - 1),
         span0 a.capacity (a.offset + i - 2) (a.length - i + 1),
         span0 newCapacity (newOffset + delta + i - 2) (a.length - i + 1),
         span0 newCapacity (newOffset - 1) 0]
      else []
  else []

def CenteredAllocationInBounds : Prop := ∀ a, a.valid → ∀ delta site,
  accessesSafe (centeredAllocationAccesses a delta site)

private theorem centered_layout (base length delta : Nat) :
    let cap := centeredCapacity base length delta
    let newLength := length + delta
    let off := centeredOffset cap newLength
    1 ≤ off ∧ off + newLength - 1 ≤ cap := by
  dsimp [centeredCapacity, centeredOffset]
  have hc : length + 2 * delta + 1 ≤
      max (overallocationNat base) (length + 2 * delta + 1) := Nat.le_max_right _ _
  omega

theorem centeredAllocationInBounds_proven : CenteredAllocationInBounds := by
  intro a hv delta site
  unfold VectorState.valid at hv
  cases site with
  | none =>
    simp only [centeredAllocationAccesses]
    dsimp
    split
    · unfold accessesSafe
      intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · simp [Access.safe, span0]; omega
      · simp only [Access.safe, span0]
        have hl := centered_layout a.length a.length delta
        omega
      · simp only [Access.safe, span0]
        have hl := centered_layout a.length a.length delta
        omega
    · simp [accessesSafe]

  | some i =>
    simp only [centeredAllocationAccesses]
    dsimp
    split
    · split
      · unfold accessesSafe
        intro x hx
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · simp [Access.safe, span0]; omega
        · simp only [Access.safe, span0]
          have hl := centered_layout a.capacity a.length delta
          omega
        · simp [Access.safe, span0]; omega
        · simp only [Access.safe, span0]
          have hl := centered_layout a.capacity a.length delta
          omega
        · simp only [Access.safe, span0]
          have hl := centered_layout a.capacity a.length delta
          omega
      · simp [accessesSafe]
    · simp [accessesSafe]

/-- `_growbeg_internal!`'s in-memory centering branch, lines 1134-1140 and
1148.  It first computes the proposed offset from the allocation formula, then
the branch recomputes the offset from the existing capacity. -/
def centeredSameMemoryAccesses (a : VectorState) (delta : Nat) : List Access :=
  let newLength := a.length + delta
  let proposedCapacity := centeredCapacity a.length a.length delta
  let proposedOffset := centeredOffset proposedCapacity newLength
  if newLength < a.capacity ∧ proposedOffset < a.capacity - newLength then
    let newOffset := centeredOffset a.capacity newLength
    let clearEnd := min (newOffset + delta) (a.offset + a.length)
    [span0 a.capacity (a.offset - 1) a.length,
     span0 a.capacity (newOffset + delta - 1) a.length,
     span0 a.capacity (a.offset - 1) (clearEnd - a.offset),
     span0 a.capacity (newOffset - 1) 0]
  else []

def CenteredSameMemoryInBounds : Prop := ∀ a, a.valid → ∀ delta,
  accessesSafe (centeredSameMemoryAccesses a delta)

theorem centeredSameMemoryInBounds_proven : CenteredSameMemoryInBounds := by
  intro a hv delta
  unfold VectorState.valid at hv
  unfold centeredSameMemoryAccesses accessesSafe
  dsimp
  split
  · intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp [Access.safe, span0]; omega
    · simp only [Access.safe, span0]
      have hl :
          let off := centeredOffset a.capacity (a.length + delta)
          1 ≤ off ∧ off + (a.length + delta) - 1 ≤ a.capacity := by
        dsimp [centeredOffset]
        omega
      omega
    · simp [Access.safe, span0]
      omega
    · simp only [Access.safe, span0]
      dsimp [centeredOffset]
      omega
  · simp

/-- `_growend_internal!`, `base/array.jl:1171-1208`, including its in-memory
queue-compaction branch and its allocated branch. -/
def endGrowthAccesses (a : VectorState) (delta : Nat) : List Access :=
  let newLength := a.length + delta
  let needed := a.offset - 1 + newLength
  if a.capacity < needed then
    if a.offset - 1 > newLength ∧ a.offset - 1 - newLength > newLength / 4 then
      let newOffset := newLength / 8 + 1
      [span0 a.capacity (a.offset - 1) a.length,
       span0 a.capacity (newOffset - 1) a.length,
       span0 a.capacity (newOffset - 1) 0,
       span0 a.capacity (max a.offset (newOffset + a.length) - 1)
         (a.offset + a.length - max a.offset (newOffset + a.length))]
    else
      let newCapacity := max (overallocationNat a.capacity) needed
      [span0 a.capacity (a.offset - 1) a.length,
       span0 newCapacity (a.offset - 1) a.length,
       span0 newCapacity (a.offset - 1) 0]
  else []

def EndGrowthInBounds : Prop := ∀ a, a.valid → ∀ delta,
  accessesSafe (endGrowthAccesses a delta)

theorem endGrowthInBounds_proven : EndGrowthInBounds := by
  intro a hv delta
  unfold VectorState.valid at hv
  unfold endGrowthAccesses accessesSafe
  dsimp
  split
  · split
    · intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · simp [Access.safe, span0]; omega
      · simp [Access.safe, span0, at0]; omega
      · simp [Access.safe, span0]; omega
      · simp [Access.safe, span0]; omega
    · intro x hx
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · simp [Access.safe, span0]; omega
      · simp only [Access.safe, span0]
        have hm : a.offset - 1 + (a.length + delta) ≤
            max (overallocationNat a.capacity) (a.offset - 1 + (a.length + delta)) :=
          Nat.le_max_right _ _
        omega
      · simp only [Access.safe, span0]
        have hm : a.offset - 1 + (a.length + delta) ≤
            max (overallocationNat a.capacity) (a.offset - 1 + (a.length + delta)) :=
          Nat.le_max_right _ _
        omega
  · simp

def AllocatingGrowthInBounds : Prop :=
  CenteredAllocationInBounds ∧ CenteredSameMemoryInBounds ∧ EndGrowthInBounds

theorem allocatingGrowthInBounds_proven : AllocatingGrowthInBounds :=
  ⟨centeredAllocationInBounds_proven, centeredSameMemoryInBounds_proven,
   endGrowthInBounds_proven⟩

/-- Bootstrap `include`, `base/Base_compiler.jl:13-25`: the global vector has
offset one; the equality branch calls the full `_growend!` model with delta
one, and the other branch updates size before writing `len+1`. -/
def bootstrapIncludeAccesses (length capacity : Nat) : List Access :=
  if length ≤ capacity then
    if length = capacity then
      endGrowthAccesses ⟨capacity, 1, length⟩ 1 ++ [at0 (length + 1) length]
    else [at0 capacity length]
  else []

def BootstrapIncludeInBounds : Prop := ∀ length capacity,
  accessesSafe (bootstrapIncludeAccesses length capacity)

theorem bootstrapIncludeInBounds_proven : BootstrapIncludeInBounds := by
  intro length capacity a ha
  simp only [bootstrapIncludeAccesses] at ha
  split at ha
  · split at ha
    · simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact endGrowthInBounds_proven ⟨capacity, 1, length⟩ (by
          simp [VectorState.valid]; omega) 1 a ha
      · simp [Access.safe, at0]
    · simp only [List.mem_singleton] at ha
      subst a
      simp [Access.safe, at0]
      omega
  · simp at ha

def BootstrapInBounds : Prop := BootstrapIncludeInBounds ∧ BootstrapStrcatInBounds

theorem bootstrapInBounds_proven : BootstrapInBounds :=
  ⟨bootstrapIncludeInBounds_proven, bootstrapStrcatInBounds_proven⟩

/-! ## `wrap(Array, ::Memory, ...)` -/

def checkedDims (dims : List Int) : Option Nat :=
  if dims.all (fun d => 0 ≤ d) ∧ shapeProduct (dims.map Int.toNat) ≤ 2 ^ 63 - 1 then
    some (shapeProduct (dims.map Int.toNat))
  else none

/-- The three Memory overloads of `wrap`, `base/array.jl:3260-3278`.  Conversion
to `Dims` and `Core.checked_dims` happen before `_wrap` compares the computed
element count with the full Memory length. -/
def wrapMemoryAccesses (memoryLength : Nat) (dims : List Int) : List Access :=
  match checkedDims dims with
  | some length => if length ≤ memoryLength then [span0 memoryLength 0 length] else []
  | none => []

def WrapMemoryInBounds : Prop :=
  ∀ memoryLength dims, accessesSafe (wrapMemoryAccesses memoryLength dims)

theorem wrapMemoryInBounds_proven : WrapMemoryInBounds := by
  intro memoryLength dims
  unfold wrapMemoryAccesses
  split
  · split
    · simp [accessesSafe, Access.safe, span0, *]
    · simp [accessesSafe]
  · simp [accessesSafe]

/-! ## String and SubString storage -/

/-- Every byte position that `isvalid(s, i)` can inspect.  `_thisind_str` first
reads `i`, then its continuation-byte slow path reads at most the three
preceding code units (`base/strings/string.jl:252-271`). -/
def stringIsvalidAccesses (length : Nat) (i : Int) : List Access :=
  if 1 ≤ i ∧ i ≤ length then
    (List.range (min 4 i.toNat)).map fun k => at0 length (i.toNat - 1 - k)
  else []

def StringIsvalidInBounds : Prop :=
  ∀ length i, accessesSafe (stringIsvalidAccesses length i)

theorem stringIsvalidInBounds_proven : StringIsvalidInBounds := by
  intro length i a ha
  simp only [stringIsvalidAccesses] at ha
  split at ha
  · simp only [List.mem_map] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    simp only [List.mem_range] at hk
    simp [Access.safe, at0]
    have hi : i.toNat ≤ length := by
      have hic : (i.toNat : Int) = i := Int.toNat_of_nonneg (by omega)
      omega
    omega
  · simp at ha

/-- The two checked constructor calls at `base/strings/substring.jl:76-84`.
The empty-range branch returns first; the other branch checks the range before
calling `isvalid` at its two computed endpoints. -/
def substringConstructorAccesses (parentLength : Nat) (i j : Int) : List Access :=
  if i ≤ j ∧ 1 ≤ i ∧ j ≤ parentLength then
    stringIsvalidAccesses parentLength i ++ stringIsvalidAccesses parentLength j
  else []

def SubstringConstructorInBounds : Prop :=
  ∀ parentLength i j, accessesSafe (substringConstructorAccesses parentLength i j)

theorem substringConstructorInBounds_proven : SubstringConstructorInBounds := by
  intro parentLength i j a ha
  simp only [substringConstructorAccesses] at ha
  split at ha
  · simp only [List.mem_append] at ha
    rcases ha with ha | ha
    · exact stringIsvalidInBounds_proven parentLength i a ha
    · exact stringIsvalidInBounds_proven parentLength j a ha
  · simp at ha

structure SubView where
  parentLength : Nat
  offset : Nat
  length : Nat
  deriving Repr, DecidableEq

/-- The representation invariant stated at `base/strings/substring.jl:142-143`. -/
def SubView.valid (s : SubView) : Prop := s.offset + s.length ≤ s.parentLength

/-- `SubString(s) = raw_substring(s, 1, ncodeunits(s))`, line 117, computes the
whole parent span. -/
def wholeSubstringAccess (parentLength : Nat) : List Access :=
  [span0 parentLength 0 parentLength]

/-- `codeunit`, `getindex`, and `isvalid` for SubString,
`base/strings/substring.jl:146-171`.  The SubString check is executed before
adding its stored offset to the caller's index. -/
def subViewAccesses (s : SubView) (i : Int) : List Access :=
  if 1 ≤ i ∧ i ≤ s.length then
    let parentIndex : Int := s.offset + i
    at0 s.parentLength (parentIndex - 1).toNat ::
      stringIsvalidAccesses s.parentLength parentIndex
  else []

def SubstringIndexInBounds : Prop :=
  SubstringConstructorInBounds ∧
  (∀ parentLength, accessesSafe (wholeSubstringAccess parentLength)) ∧
  ∀ s, s.valid → ∀ i, accessesSafe (subViewAccesses s i)

theorem substringIndexInBounds_proven : SubstringIndexInBounds := by
  refine ⟨substringConstructorInBounds_proven, ?_, ?_⟩
  · intro parentLength
    simp [wholeSubstringAccess, accessesSafe, Access.safe, span0]
  · intro s hs i
    unfold SubView.valid at hs
    unfold subViewAccesses accessesSafe
    split
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp only [Access.safe, at0]
        have hc : (((s.offset : Int) + i - 1).toNat : Int) = s.offset + i - 1 :=
          Int.toNat_of_nonneg (by omega)
        omega
      · exact stringIsvalidInBounds_proven s.parentLength (s.offset + i) a ha
    · simp

/-- String-backed IOBuffer constructors, `base/strings/io.jl:288-307`: a String
wraps all its bytes, while a SubString view starts at its stored parent offset
and has exactly its stored byte length. -/
def stringIOAccesses (s : SubView) : List Access :=
  [span0 s.parentLength s.offset s.length]

def StringIOInBounds : Prop := ∀ s, s.valid → accessesSafe (stringIOAccesses s)

theorem stringIOInBounds_proven : StringIOInBounds := by
  intro s hs
  unfold SubView.valid at hs
  simpa [stringIOAccesses, accessesSafe, Access.safe, span0] using hs

/-- `StringMemory(n)`, `base/iobuffer.jl:166-168`: `_string_n` converts `n` to
`Csize_t` and, on success, returns exactly `n` bytes for `unsafe_wrap`. -/
def stringMemoryAccesses (n : Int) : List Access :=
  if 0 ≤ n ∧ n ≤ 2 ^ 63 - 1 then [span0 n.toNat 0 n.toNat] else []

def StringMemoryInBounds : Prop := ∀ n, accessesSafe (stringMemoryAccesses n)

theorem stringMemoryInBounds_proven : StringMemoryInBounds := by
  intro n
  unfold stringMemoryAccesses
  split <;> simp [accessesSafe, Access.safe, span0]

/-- String repetition, `base/strings/substring.jl:289-306`.  The checked
`n*r` allocation is partitioned into `r` blocks; the one-byte branch reads the
only source byte and fills the same allocation. -/
def repeatStringAccesses (width count : Nat) : List Access :=
  if count = 0 ∨ width = 0 then []
  else if width = 1 then [at0 width 0, span0 count 0 count]
  else (List.range count).map fun j => span0 (width * count) (j * width) width

def RepeatStringInBounds : Prop :=
  ∀ width count, accessesSafe (repeatStringAccesses width count)

theorem repeatStringInBounds_proven : RepeatStringInBounds := by
  intro width count
  unfold repeatStringAccesses
  split
  · simp [accessesSafe]
  · split
    · simp [accessesSafe, Access.safe, at0, span0, *]
    · intro a ha
      simp only [List.mem_map] at ha
      obtain ⟨j, hj, rfl⟩ := ha
      simp only [List.mem_range] at hj
      simp only [Access.safe, span0]
      have hm := Nat.mul_le_mul_right width (Nat.succ_le_iff.mpr hj)
      simpa [Nat.succ_mul, Nat.mul_comm, Nat.add_comm] using hm

/-- The two `_string` loops, `base/strings/substring.jl:215-283`.  `widths`
are the `ncodeunits`/`sizeof` values selected by the first type-dispatch loop;
the second loop uses the same dispatch and advances `offs` by each returned
width. -/
def stringBuildTrace (capacity : Nat) : Nat → List Nat → List Access
  | _, [] => []
  | offset, width :: rest =>
      span0 capacity offset width :: stringBuildTrace capacity (offset + width) rest

private theorem stringBuildTrace_safe (capacity offset : Nat) (widths : List Nat)
    (h : offset + widths.sum ≤ capacity) :
    accessesSafe (stringBuildTrace capacity offset widths) := by
  induction widths generalizing offset with
  | nil => simp [stringBuildTrace, accessesSafe]
  | cons width rest ih =>
      simp only [stringBuildTrace, accessesSafe, List.mem_cons, forall_eq_or_imp,
        List.sum_cons] at h ⊢
      constructor
      · simp [Access.safe, span0]
        omega
      · apply ih
        omega

def stringBuildAccesses (widths : List Nat) : List Access :=
  let total := widths.sum
  if total ≤ 2 ^ 63 - 1 then stringBuildTrace total 0 widths else []

def StringBuildInBounds : Prop := ∀ widths,
  accessesSafe (stringBuildAccesses widths)

theorem stringBuildInBounds_proven : StringBuildInBounds := by
  intro widths
  unfold stringBuildAccesses
  dsimp
  split
  · apply stringBuildTrace_safe
    omega
  · simp [accessesSafe]

/-! ## IOBuffer reads and take paths -/

structure BufferState where
  capacity : Nat
  size : Int
  ptr : Int
  offsetOrCompacted : Int
  mark : Int
  readable : Bool
  writable : Bool
  seekable : Bool
  reinit : Bool
  deriving Repr, DecidableEq

def BufferState.offset (io : BufferState) : Int := max 0 io.offsetOrCompacted

/-- `translate_seek_position`, `base/iobuffer.jl:500-510`, uses widened
arithmetic and clamps back to `Int`. -/
def BufferState.translate (io : BufferState) (n : Int) : Int :=
  max (-2 ^ 63) (min (n + io.offsetOrCompacted + 1) (2 ^ 63 - 1))

/-- Field invariants stated at `base/iobuffer.jl:55-93`, including the
translated-mark relation for a non-seekable buffer proved for reachable
buffers by `JuliaLean.IOBuffers.reachable_inv`. -/
def BufferState.valid (io : BufferState) : Prop :=
  io.capacity < 2 ^ 63 - 1 ∧
  0 ≤ io.offset ∧ io.offset ≤ io.size ∧ io.size ≤ io.capacity ∧
  io.offset + 1 ≤ io.ptr ∧ io.ptr ≤ io.size + 1 ∧
  (io.seekable = false → 0 ≤ io.mark →
    io.offset + 1 ≤ io.translate io.mark ∧ io.translate io.mark ≤ io.ptr)

/-- Dense `peek(from, T)`, `base/iobuffer.jl:418-430`. -/
def ioPeekAccesses (io : BufferState) (width : Nat) : List Access :=
  if io.readable ∧ (width : Int) ≤ io.size - io.ptr + 1 then
    [span0 io.capacity (io.ptr - 1).toNat width]
  else []

/-- `read(from, UInt8)`, `base/iobuffer.jl:438-448`. -/
def ioReadByteAccesses (io : BufferState) : List Access :=
  if io.readable ∧ io.ptr ≤ io.size then
    [at0 io.capacity (io.ptr - 1).toNat]
  else []

/-- Memory-backed `take!`, `base/iobuffer.jl:758-786`. -/
def ioTakeAccesses (io : BufferState) : List Access :=
  if io.reinit then []
  else if io.seekable then
    let count := (io.size - io.offset).toNat
    if count = 0 then [] else [span0 io.capacity io.offset.toNat count]
  else
    let count := (io.size - io.ptr + 1).toNat
    if count = 0 then [] else [span0 io.capacity (io.ptr - 1).toNat count]

def BufferState.usedStart (io : BufferState) : Int :=
  if io.seekable then io.offset + 1
  else if io.mark > -1 then min io.ptr (io.translate io.mark)
  else io.ptr

/-- `get_used_span` followed by the exact-size copy in `unsafe_takestring!` or
`takestring!`, `base/iobuffer.jl:795-859`. -/
def ioTakeStringAccesses (io : BufferState) : List Access :=
  let start := io.usedStart
  let count := (io.size - start + 1).toNat
  if count = 0 then []
  else [span0 io.capacity (start - 1).toNat count, span0 count 0 count]

def IOBufferOperationsInBounds : Prop := ∀ io, io.valid →
  (∀ width, accessesSafe (ioPeekAccesses io width)) ∧
  accessesSafe (ioReadByteAccesses io) ∧
  accessesSafe (ioTakeAccesses io) ∧
  accessesSafe (ioTakeStringAccesses io)

private theorem ioUsedStart_bounds (io : BufferState) (h : io.valid) :
    io.offset + 1 ≤ io.usedStart ∧ io.usedStart ≤ io.size + 1 := by
  unfold BufferState.valid at h
  unfold BufferState.usedStart
  split
  · omega
  · split
    · have hnot : ¬io.seekable = true := by assumption
      have hseek : io.seekable = false := by
        cases hq : io.seekable with
        | false => rfl
        | true => exact (hnot hq).elim
      have hm := h.2.2.2.2.2.2 hseek (by omega)
      omega
    · omega

theorem ioBufferOperationsInBounds_proven : IOBufferOperationsInBounds := by
  intro io hv
  unfold BufferState.valid at hv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro width
    unfold ioPeekAccesses accessesSafe
    split
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      simp only [Access.safe, span0]
      have hp : ((io.ptr - 1).toNat : Int) = io.ptr - 1 :=
        Int.toNat_of_nonneg (by omega)
      omega
    · simp
  · unfold ioReadByteAccesses accessesSafe
    split
    · intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      simp only [Access.safe, at0]
      have hp : ((io.ptr - 1).toNat : Int) = io.ptr - 1 :=
        Int.toNat_of_nonneg (by omega)
      omega
    · simp
  · unfold ioTakeAccesses accessesSafe
    split
    · simp
    · split
      · dsimp
        split
        · simp
        · intro a ha
          simp only [List.mem_singleton] at ha
          subst a
          simp only [Access.safe, span0]
          have ho : (io.offset.toNat : Int) = io.offset := Int.toNat_of_nonneg (by omega)
          have hc : ((io.size - io.offset).toNat : Int) = io.size - io.offset :=
            Int.toNat_of_nonneg (by omega)
          omega
      · dsimp
        split
        · simp
        · intro a ha
          simp only [List.mem_singleton] at ha
          subst a
          simp only [Access.safe, span0]
          have hp : ((io.ptr - 1).toNat : Int) = io.ptr - 1 :=
            Int.toNat_of_nonneg (by omega)
          have hc : ((io.size - io.ptr + 1).toNat : Int) = io.size - io.ptr + 1 :=
            Int.toNat_of_nonneg (by omega)
          omega
  · have hs := ioUsedStart_bounds io (by
      unfold BufferState.valid
      exact hv)
    unfold ioTakeStringAccesses accessesSafe
    dsimp
    split
    · simp
    · intro a ha
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · simp only [Access.safe, span0]
        have hp : ((io.usedStart - 1).toNat : Int) = io.usedStart - 1 :=
          Int.toNat_of_nonneg (by omega)
        have hc : ((io.size - io.usedStart + 1).toNat : Int) =
            io.size - io.usedStart + 1 := Int.toNat_of_nonneg (by omega)
        omega
      · simp [Access.safe, span0]

/-! ## Dimensional reductions -/

/-- Two-axis presentation of `check_reducedims`, `base/reducedim.jl:205-233`.
`columns` denotes the column-major flattening of all tail Cartesian axes; the
same computation applies recursively to any number of tail axes. -/
def reductionChoices (rows cols resultRows resultCols : Nat) : Option (Bool × Bool) :=
  let reduceRows := if resultRows = 1 then some true else if resultRows = rows then some false else none
  let reduceCols := if resultCols = 1 then some true else if resultCols = cols then some false else none
  match reduceRows, reduceCols with
  | some r, some c => some (r, c)
  | _, _ => none

def reduceLeadingBlock (rows cols : Nat) (reduceRows reduceCols : Bool) : Nat :=
  if reduceRows then
    if reduceCols then rows * cols else rows
  else if reduceCols ∧ rows = 1 then cols
  else if reduceCols then 0
  else 1

def reduceSlowAccesses (rows cols resultRows resultCols : Nat) : List Access :=
  match reductionChoices rows cols resultRows resultCols with
  | none => []
  | some (reduceRows, reduceCols) =>
    (List.range cols).flatMap fun j =>
      (List.range rows).flatMap fun i =>
        let ri := if reduceRows then 0 else i
        let rj := if reduceCols then 0 else j
        [at0 (rows * cols) (i + rows * j),
         at0 (resultRows * resultCols) (ri + resultRows * rj)]

/-- Fast `_mapreducedim!`, lines 256-268.  `check_reducedims` computes the
leading block, then `ibase` advances by exactly that block for every output
slot. -/
def reduceFastAccesses (rows cols resultRows resultCols : Nat) : List Access :=
  match reductionChoices rows cols resultRows resultCols with
  | none => []
  | some (reduceRows, reduceCols) =>
    let block := reduceLeadingBlock rows cols reduceRows reduceCols
    if block > 16 then
      (List.range (resultRows * resultCols)).flatMap fun i =>
        [at0 (resultRows * resultCols) i,
         span0 (rows * cols) (i * block) block]
    else []

def ReductionAccessesInBounds : Prop :=
  ∀ rows cols rr rc,
    accessesSafe (reduceSlowAccesses rows cols rr rc) ∧
    accessesSafe (reduceFastAccesses rows cols rr rc)

private theorem reductionChoices_shape (rows cols rr rc : Nat) (br bc : Bool)
    (h : reductionChoices rows cols rr rc = some (br, bc)) :
    rr = (if br then 1 else rows) ∧ rc = (if bc then 1 else cols) := by
  unfold reductionChoices at h
  repeat' split at h
  all_goals simp_all

private theorem reduceLeading_product (rows cols rr rc : Nat) (br bc : Bool)
    (hc : reductionChoices rows cols rr rc = some (br, bc))
    (hp : 0 < reduceLeadingBlock rows cols br bc) :
    (rr * rc) * reduceLeadingBlock rows cols br bc = rows * cols := by
  obtain ⟨rfl, rfl⟩ := reductionChoices_shape rows cols rr rc br bc hc
  cases br <;> cases bc
  · simp [reduceLeadingBlock]
  · by_cases hr : rows = 1 <;> simp_all [reduceLeadingBlock]
  · simp [reduceLeadingBlock, Nat.mul_comm]
  · simp [reduceLeadingBlock]

theorem reductionAccessesInBounds_proven : ReductionAccessesInBounds := by
  intro rows cols rr rc
  constructor
  · intro a ha
    simp only [reduceSlowAccesses] at ha
    split at ha
    · simp at ha
    · rename_i br bc hc
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at ha
      obtain ⟨j, hj, i, hi, rfl | rfl⟩ := ha
      · simp only [Access.safe, at0]
        have hm := Nat.mul_le_mul_left rows (Nat.succ_le_iff.mpr hj)
        rw [Nat.mul_succ] at hm
        omega
      · simp only [Access.safe, at0]
        obtain ⟨rfl, rfl⟩ := reductionChoices_shape rows cols rr rc br bc hc
        cases br <;> cases bc <;> simp_all [Access.safe, at0]
        all_goals
          have hm := Nat.mul_le_mul_left rows (Nat.succ_le_iff.mpr hj)
          rw [Nat.mul_succ] at hm
          omega
  · intro a ha
    simp only [reduceFastAccesses] at ha
    split at ha
    · simp at ha
    · rename_i br bc hc
      split at ha
      · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at ha
        obtain ⟨i, hi, rfl | rfl⟩ := ha
        · simp [Access.safe, at0]
          omega
        · simp only [Access.safe, span0]
          have heq := reduceLeading_product rows cols rr rc br bc hc (by omega)
          have hm := Nat.mul_le_mul_right (reduceLeadingBlock rows cols br bc)
            (Nat.succ_le_iff.mpr hi)
          rw [Nat.succ_mul] at hm
          omega
      · simp at ha

/-! Arbitrary-dimensional reduction model used by the registry entry. -/

def reductionFlags : List Nat → List Nat → Option (List Bool)
  | [], [] => some []
  | a :: as, r :: rs =>
      if r = 1 then (reductionFlags as rs).map (true :: ·)
      else if r = a then (reductionFlags as rs).map (false :: ·)
      else none
  | _, _ => none

def reducedShape : List Bool → List Nat → List Nat
  | b :: bs, a :: as => (if b then 1 else a) :: reducedShape bs as
  | _, _ => []

def reducedCoords : List Bool → List Int → List Int
  | b :: bs, i :: is => (if b then 1 else i) :: reducedCoords bs is
  | _, _ => []

def selectedProduct : List Bool → List Nat → Nat
  | b :: bs, a :: as => (if b then a else 1) * selectedProduct bs as
  | _, _ => 1

def leadingReductions : Bool → List Bool → List Nat → Bool
  | _, [], [] => true
  | had, b :: bs, a :: as =>
      let ok := !(had && b && a > 1)
      ok && leadingReductions (had || !b) bs as
  | _, _, _ => false

def reductionBlockND (dims : List Nat) (flags : List Bool) : Nat :=
  if leadingReductions false flags dims then selectedProduct flags dims else 0

def reduceSlowNDAccesses (dims resultDims : List Nat) (coord : List Int) : List Access :=
  if resultDims.length ≤ dims.length then
    let result := normalizeDims resultDims dims.length
    match reductionFlags dims result with
    | some flags =>
      if coordsWithinB dims coord then
        uncheckedCartesianAccess dims coord ++
          uncheckedCartesianAccess (reducedShape flags dims) (reducedCoords flags coord)
      else []
    | none => []
  else []

def reduceFastNDAccesses (dims resultDims : List Nat) : List Access :=
  if resultDims.length ≤ dims.length ∧ 0 < shapeProduct dims then
    let result := normalizeDims resultDims dims.length
    match reductionFlags dims result with
    | some flags =>
      let block := reductionBlockND dims flags
      if block > 16 then
        (List.range (shapeProduct (reducedShape flags dims))).flatMap fun i =>
          [at0 (shapeProduct (reducedShape flags dims)) i,
           span0 (shapeProduct dims) (i * block) block]
      else []
    | none => []
  else []

private theorem reductionFlags_lengths : ∀ dims result flags,
    reductionFlags dims result = some flags →
    flags.length = dims.length ∧ result = reducedShape flags dims
  | [], [], [], _ => by simp [reductionFlags, reducedShape]
  | a :: as, r :: rs, flags, h => by
      simp only [reductionFlags] at h
      split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨fs, hfs, rfl⟩ := h
        have ih := reductionFlags_lengths as rs fs hfs
        simp [reducedShape, ih.1, ih.2, *]
      · split at h
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨fs, hfs, rfl⟩ := h
          have ih := reductionFlags_lengths as rs fs hfs
          simp [reducedShape, ih.1, ih.2, *]
        · simp at h
  | [], _ :: _, _, h => by simp [reductionFlags] at h
  | _ :: _, [], _, h => by simp [reductionFlags] at h

private theorem reducedCoords_within : ∀ flags dims coord,
    flags.length = dims.length → coordsWithin dims coord →
    coordsWithin (reducedShape flags dims) (reducedCoords flags coord)
  | [], [], [], _, _ => by simp [coordsWithin, reducedShape, reducedCoords]
  | b :: bs, a :: as, i :: is, hlen, hc => by
      have htail : coordsWithin as is :=
        ⟨by simpa [coordsWithin] using hc.1,
         fun p hp => hc.2 p (List.mem_cons_of_mem _ hp)⟩
      have ih := reducedCoords_within bs as is (by simpa using hlen) htail
      constructor
      · simp [reducedShape, reducedCoords, ih.1]
      · intro p hp
        simp only [reducedShape, reducedCoords, List.zip_cons_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · cases b <;> simp_all
          exact hc.2 (a, i) (by simp)
        · exact ih.2 p hp
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp [coordsWithin] at h

private theorem selectedProduct_identity : ∀ flags dims,
    flags.length = dims.length →
    shapeProduct (reducedShape flags dims) * selectedProduct flags dims = shapeProduct dims
  | [], [], _ => by simp [shapeProduct, reducedShape, selectedProduct]
  | b :: bs, a :: as, h => by
      have ih := selectedProduct_identity bs as (by simpa using h)
      cases b with
      | false =>
          simp only [reducedShape, selectedProduct, Bool.false_eq_true, ↓reduceIte,
            Nat.one_mul, shapeProduct, List.foldr_cons]
          change (a * shapeProduct (reducedShape bs as)) * selectedProduct bs as =
            a * shapeProduct as
          calc
            (a * shapeProduct (reducedShape bs as)) * selectedProduct bs as =
                a * (shapeProduct (reducedShape bs as) * selectedProduct bs as) := by
                  rw [Nat.mul_assoc]
            _ = a * shapeProduct as := by rw [ih]
      | true =>
          simp only [reducedShape, selectedProduct, ↓reduceIte, Nat.one_mul,
            shapeProduct, List.foldr_cons]
          change shapeProduct (reducedShape bs as) *
              (a * selectedProduct bs as) = a * shapeProduct as
          calc
            shapeProduct (reducedShape bs as) * (a * selectedProduct bs as) =
                a * (shapeProduct (reducedShape bs as) * selectedProduct bs as) := by ac_rfl
            _ = a * shapeProduct as := by rw [ih]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

def ReductionNDAccessesInBounds : Prop := ∀ dims resultDims,
  (∀ coord, accessesSafe (reduceSlowNDAccesses dims resultDims coord)) ∧
  accessesSafe (reduceFastNDAccesses dims resultDims)

theorem reductionNDAccessesInBounds_proven : ReductionNDAccessesInBounds := by
  intro dims resultDims
  constructor
  · intro coord a ha
    simp only [reduceSlowNDAccesses] at ha
    split at ha
    · split at ha
      · rename_i flags hf
        split at ha
        · have hs := reductionFlags_lengths dims (normalizeDims resultDims dims.length) flags hf
          have hc := coordsWithinB_true dims coord (by assumption)
          simp only [List.mem_append] at ha
          rcases ha with ha | ha
          · exact uncheckedCartesian_safe dims coord hc a ha
          · exact uncheckedCartesian_safe _ _
              (reducedCoords_within flags dims coord hs.1 hc) a ha
        · simp at ha
      · simp at ha
    · simp at ha
  · intro a ha
    simp only [reduceFastNDAccesses] at ha
    split at ha
    · split at ha
      · rename_i flags hf
        split at ha
        · simp only [List.mem_flatMap, List.mem_range, List.mem_cons,
            List.mem_singleton, List.not_mem_nil, or_false] at ha
          obtain ⟨i, hi, rfl | rfl⟩ := ha
          · simp [Access.safe, at0]; omega
          · simp only [Access.safe, span0]
            have hs := reductionFlags_lengths dims (normalizeDims resultDims dims.length) flags hf
            have hid := selectedProduct_identity flags dims hs.1
            have hlead : leadingReductions false flags dims = true := by
              unfold reductionBlockND at *
              split at * <;> simp_all
            have hb : reductionBlockND dims flags = selectedProduct flags dims := by
              simp [reductionBlockND, hlead]
            rw [hb]
            have hm := Nat.mul_le_mul_right (selectedProduct flags dims)
              (Nat.succ_le_iff.mpr hi)
            rw [Nat.succ_mul, hid] at hm
            omega
        · simp at ha
      · simp at ha
    · simp at ha

/-! ## `repeat` -/

/-- Vector `repeat_outer`, `base/abstractarraymath.jl:573-581`.  The source
length and repetition count determine both allocation and every copied block. -/
def repeatVectorAccesses (size count : Nat) : List Access :=
  (List.range count).map fun j => span0 (size * count) (j * size) size

def RepeatVectorInBounds : Prop :=
  ∀ size count, accessesSafe (repeatVectorAccesses size count)

theorem repeatVectorInBounds_proven : RepeatVectorInBounds := by
  intro size count a h
  simp only [repeatVectorAccesses, List.mem_map] at h
  obtain ⟨j, hj, rfl⟩ := h
  simp only [List.mem_range] at hj
  simp only [Access.safe, span0]
  have hm := Nat.mul_le_mul_right size (Nat.succ_le_iff.mpr hj)
  simpa [Nat.succ_mul, Nat.mul_comm, Nat.add_comm] using hm

/-- Matrix `repeat_outer`, `base/abstractarraymath.jl:559-571`.  One span is
copied for each input column in each `(i,j)` output tile. -/
def repeatMatrixAccesses (rows cols rowCopies colCopies : Nat) : List Access :=
  (List.range colCopies).flatMap fun j =>
    (List.range rowCopies).flatMap fun i =>
      (List.range cols).map fun q =>
        span0 ((rows * rowCopies) * (cols * colCopies))
          (i * rows + (rows * rowCopies) * (j * cols + q)) rows

def RepeatMatrixInBounds : Prop :=
  ∀ rows cols m n, accessesSafe (repeatMatrixAccesses rows cols m n)

theorem repeatMatrixInBounds_proven : RepeatMatrixInBounds := by
  intro rows cols m n a ha
  simp only [repeatMatrixAccesses, List.mem_flatMap, List.mem_range, List.mem_map] at ha
  obtain ⟨j, hj, i, hi, q, hq, rfl⟩ := ha
  simp only [Access.safe, span0]
  let outRows := rows * m
  let col := j * cols + q
  have hiBlock : i * rows + rows ≤ outRows := by
    have h := Nat.mul_le_mul_right rows (Nat.succ_le_iff.mpr hi)
    simpa [outRows, Nat.succ_mul, Nat.mul_comm, Nat.add_comm] using h
  have hcol : col + 1 ≤ cols * n := by
    have hjmul := Nat.mul_le_mul_right cols (Nat.succ_le_iff.mpr hj)
    have hq1 : q + 1 ≤ cols := Nat.succ_le_iff.mpr hq
    dsimp [col]
    calc
      j * cols + q + 1 = j * cols + (q + 1) := by omega
      _ ≤ j * cols + cols := Nat.add_le_add_left hq1 _
      _ = (j + 1) * cols := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ n * cols := hjmul
      _ = cols * n := Nat.mul_comm _ _
  calc
    i * rows + outRows * col + rows = (i * rows + rows) + outRows * col := by omega
    _ ≤ outRows + outRows * col := Nat.add_le_add_right hiBlock _
    _ = outRows * (col + 1) := by rw [Nat.mul_succ]; omega
    _ ≤ outRows * (cols * n) := Nat.mul_le_mul_left outRows hcol

def RepeatVectorMatrixInBounds : Prop := RepeatVectorInBounds ∧ RepeatMatrixInBounds

theorem repeatVectorMatrixInBounds_proven : RepeatVectorMatrixInBounds :=
  ⟨repeatVectorInBounds_proven, repeatMatrixInBounds_proven⟩

private theorem matrixIndexSafe (rows cols row col : Nat) (hr : row < rows) (hc : col < cols) :
    (at0 (rows * cols) (row + rows * col)).safe := by
  simp only [Access.safe, at0]
  have h := Nat.mul_le_mul_left rows (Nat.succ_le_iff.mpr hc)
  rw [Nat.mul_succ] at h
  omega

/-! ## Swaps, inverse permutations, sets, and replacement -/

/-- `swapcols!`/`swaprows!`, `base/combinatorics.jl:103-123`.  The early
equal-index branch performs no access; otherwise both scalar indices are
checked before the opposite axis is traversed. -/
def swapMatrixAccesses (rows cols : Nat) (i j : Int) (columns : Bool) : List Access :=
  if i = j then []
  else
    let checkedLength := if columns then cols else rows
    let loopLength := if columns then rows else cols
    if 1 ≤ i ∧ i ≤ checkedLength ∧ 1 ≤ j ∧ j ≤ checkedLength then
      (List.range loopLength).flatMap fun k =>
        if columns then
          [at0 (rows * cols) (k + rows * (i - 1).toNat),
           at0 (rows * cols) (k + rows * (j - 1).toNat)]
        else
          [at0 (rows * cols) ((i - 1).toNat + rows * k),
           at0 (rows * cols) ((j - 1).toNat + rows * k)]
    else []

def SwapMatrixInBounds : Prop :=
  ∀ rows cols i j columns, accessesSafe (swapMatrixAccesses rows cols i j columns)

theorem swapMatrixInBounds_proven : SwapMatrixInBounds := by
  intro rows cols i j columns
  by_cases heq : i = j
  · simp [swapMatrixAccesses, heq, accessesSafe]
  · cases columns with
    | false =>
      simp only [swapMatrixAccesses, heq, Bool.false_eq_true, ↓reduceIte]
      by_cases hb : 1 ≤ i ∧ i ≤ (rows : Int) ∧ 1 ≤ j ∧ j ≤ (rows : Int)
      · rw [if_pos hb]
        intro a ha
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at ha
        obtain ⟨k, hk, rfl | rfl⟩ := ha
        · apply matrixIndexSafe <;> omega
        · apply matrixIndexSafe <;> omega
      · rw [if_neg hb]
        simp [accessesSafe]
    | true =>
      simp only [swapMatrixAccesses, heq, ↓reduceIte]
      by_cases hb : 1 ≤ i ∧ i ≤ (cols : Int) ∧ 1 ≤ j ∧ j ≤ (cols : Int)
      · rw [if_pos hb]
        intro a ha
        simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at ha
        obtain ⟨k, hk, rfl | rfl⟩ := ha
        · apply matrixIndexSafe <;> omega
        · apply matrixIndexSafe <;> omega
      · rw [if_neg hb]
        simp [accessesSafe]

private def invpermLoop (capacity : Nat) : List Int → List Nat → List Access
  | [], _ => []
  | j :: rest, seen =>
      if 1 ≤ j ∧ j ≤ capacity then
        let k := (j - 1).toNat
        at0 capacity k :: if k ∈ seen then [] else invpermLoop capacity rest (k :: seen)
      else []

/-- `invperm`, `base/combinatorics.jl:286-296`: enumeration reads each input
position, then the value is range-checked before indexing the length-sized
inverse vector. -/
def invpermAccesses (values : List Int) : List Access :=
  axisAccesses values.length ++ invpermLoop values.length values []

def InvpermInBounds : Prop := ∀ values, accessesSafe (invpermAccesses values)

private theorem invpermLoop_safe (capacity : Nat) (values : List Int) (seen : List Nat) :
    accessesSafe (invpermLoop capacity values seen) := by
  induction values generalizing seen with
  | nil => simp [invpermLoop, accessesSafe]
  | cons j rest ih =>
      simp only [invpermLoop]
      split
      · simp only [accessesSafe, List.mem_cons, forall_eq_or_imp]
        constructor
        · simp [Access.safe, at0]
          omega
        · split
          · simp [accessesSafe]
          · exact ih _
      · simp [accessesSafe]

theorem invpermInBounds_proven : InvpermInBounds := by
  intro values a ha
  simp only [invpermAccesses, List.mem_append] at ha
  rcases ha with ha | ha
  · exact axisLoopInBounds_proven values.length a ha
  · exact invpermLoop_safe values.length values [] a ha

def CombinatoricsAccessesInBounds : Prop := SwapMatrixInBounds ∧ InvpermInBounds

theorem combinatoricsAccessesInBounds_proven : CombinatoricsAccessesInBounds :=
  ⟨swapMatrixInBounds_proven, invpermInBounds_proven⟩

private def firstLive : List Bool → Nat → Option Nat
  | [], _ => none
  | live :: rest, k => if live then some k else firstLive rest (k + 1)

private theorem firstLive_lt (slots : List Bool) (base k : Nat)
    (h : firstLive slots base = some k) : k < base + slots.length := by
  induction slots generalizing base with
  | nil => simp [firstLive] at h
  | cons live rest ih =>
      simp only [firstLive] at h
      split at h
      · simp_all
      · have := ih (base + 1) h
        simp only [List.length_cons]
        omega

/-- `pop!(::Set)`, `base/set.jl:139-157`.  `ht_keyindex` is represented by a
search over the Dict slot array and therefore can return only an existing slot. -/
def setPopAccesses (slots : List Bool) : List Access :=
  match firstLive slots 0 with
  | none => []
  | some i => [at0 slots.length i]

def SetPopInBounds : Prop := ∀ slots, accessesSafe (setPopAccesses slots)

theorem setPopInBounds_proven : SetPopInBounds := by
  intro slots
  unfold setPopAccesses
  split
  · simp [accessesSafe]
  · rename_i i h
    simp only [accessesSafe, List.mem_singleton, forall_eq, Access.safe, at0]
    have := firstLive_lt slots 0 i h
    omega

/-- Array `replace` and `replace!`, `base/set.jl:804-896,947-976`.  The public
paths pass either `A` itself or `_similar_or_copy(A)`, which has the same axes;
the loop obtains every index from `eachindex(A)`. -/
def replaceArrayAccesses (length : Nat) : List Access :=
  (List.range length).flatMap fun i => [at0 length i, at0 length i]

def ReplaceArrayInBounds : Prop := ∀ length, accessesSafe (replaceArrayAccesses length)

theorem replaceArrayInBounds_proven : ReplaceArrayInBounds := by
  intro length a ha
  simp only [replaceArrayAccesses, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ha
  obtain ⟨i, hi, ha⟩ := ha
  rcases ha with rfl | rfl <;> simp [Access.safe, at0] <;> omega

/-- Dict `replace!`, `base/set.jl:980-1009`.  `skip_deleted_floor!` and each
subsequent `skip_deleted` search the slot vector and return the next live slot. -/
def replaceDictAccesses (slots : List Bool) : List Access :=
  (List.range slots.length).filterMap fun i => if slots[i]? = some true then some (at0 slots.length i) else none

def ReplaceDictInBounds : Prop := ∀ slots, accessesSafe (replaceDictAccesses slots)

theorem replaceDictInBounds_proven : ReplaceDictInBounds := by
  intro slots a ha
  simp only [replaceDictAccesses, List.mem_filterMap] at ha
  obtain ⟨i, hi, h⟩ := ha
  split at h
  · simp only [Option.some.injEq] at h
    subst a
    simp only [Access.safe, at0]
    exact Nat.succ_le_iff.mpr (List.mem_range.mp hi)
  · simp at h

def SetReplaceInBounds : Prop := ReplaceArrayInBounds ∧ ReplaceDictInBounds

theorem setReplaceInBounds_proven : SetReplaceInBounds :=
  ⟨replaceArrayInBounds_proven, replaceDictInBounds_proven⟩

/-! ## Runtime and operating-system cells -/

/-- The `cglobal` objects loaded or stored at `base/gcutils.jl:163` and
`base/libdl.jl:517` are declared C globals of exactly the requested scalar
type, so `cglobal` computes offset zero in a one-cell object. -/
def runtimeCellAccesses (perform : Bool) : List Access :=
  if perform then [at0 1 0] else []

def RuntimeCellInBounds : Prop := ∀ perform,
  accessesSafe (runtimeCellAccesses perform)

theorem runtimeCellInBounds_proven : RuntimeCellInBounds := by
  intro perform
  cases perform <;> simp [runtimeCellAccesses, accessesSafe, Access.safe, at0]

/-- `FormatMessage`, `base/libc.jl:395-410`: `FormatMessageW` returns the
number of UTF-16 units in its allocated result and Julia allocates the same
number of destination units. -/
def formatMessageAccesses (returnedLength : Nat) : List Access :=
  [span0 returnedLength 0 returnedLength, span0 returnedLength 0 returnedLength]

def FormatMessageInBounds : Prop :=
  ∀ n, accessesSafe (formatMessageAccesses n)

theorem formatMessageInBounds_proven : FormatMessageInBounds := by
  intro n
  simp [formatMessageAccesses, accessesSafe, Access.safe, span0]

/-- `uv_os_get_group`, `base/libc.jl:581-603`, returns a null-terminated
pointer array.  Julia loads position `length(members)+1` and stops on the
sentinel.  `some` represents a member pointer and `none` the sentinel. -/
def groupMemberAccesses (capacity : Nat) : List (Option Unit) → Nat → List Access
  | [], _ => []
  | none :: _, k => [at0 capacity k]
  | some _ :: rest, k => at0 capacity k :: groupMemberAccesses capacity rest (k + 1)

def groupMembers (members : Nat) : List (Option Unit) :=
  List.replicate members (some ()) ++ [none]

def GroupMembersInBounds : Prop :=
  ∀ members, accessesSafe (groupMemberAccesses (members + 1) (groupMembers members) 0)

private theorem groupMemberAccesses_safe (capacity : Nat) (xs : List (Option Unit)) (k : Nat)
    (h : k + xs.length ≤ capacity) : accessesSafe (groupMemberAccesses capacity xs k) := by
  induction xs generalizing k with
  | nil => simp [groupMemberAccesses, accessesSafe]
  | cons head rest ih =>
      cases head with
      | none =>
          simp only [List.length_cons] at h
          simp only [groupMemberAccesses, accessesSafe, List.mem_singleton, forall_eq,
            Access.safe, at0]
          omega
      | some _ =>
          simp only [List.length_cons] at h
          simp only [groupMemberAccesses, accessesSafe, List.mem_cons, forall_eq_or_imp]
          constructor
          · simp [Access.safe, at0]
            omega
          · apply ih
            omega

theorem groupMembersInBounds_proven : GroupMembersInBounds := by
  intro members
  apply groupMemberAccesses_safe
  simp [groupMembers]

def LibcBuffersInBounds : Prop := FormatMessageInBounds ∧ GroupMembersInBounds

theorem libcBuffersInBounds_proven : LibcBuffersInBounds :=
  ⟨formatMessageInBounds_proven, groupMembersInBounds_proven⟩

end JuliaLean.MemSafety.G1

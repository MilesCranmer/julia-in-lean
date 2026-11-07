import JuliaLean.Proofs.base.abstractarray.memory_safety_access
import JuliaLean.base.iobuffer

namespace JuliaLean.MemSafety.G1

open JuliaLean

set_option maxRecDepth 2000

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

end JuliaLean.MemSafety.G1

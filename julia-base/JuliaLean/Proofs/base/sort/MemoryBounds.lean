import JuliaLean.Proofs.base.runtime_internals.Common
import JuliaLean.Proofs.base.sort

namespace JuliaLean.MemSafety.G4

/-- The `k`th iteration of a checked `lo:hi` loop. This models the public
`checkbounds(v, lo:hi)` followed by the loops in `base/sort.jl`. -/
def checkedIntervalIndex (len : Nat) (lo hi : Int) (k : Nat) : Option Int :=
  if 1 ≤ lo ∧ lo ≤ hi ∧ hi ≤ len ∧ k < (hi - lo + 1).toNat then some (lo + k) else none

def CheckedIntervalInBounds : Prop :=
  ∀ (len : Nat) (lo hi : Int) (k : Nat) (i : Int),
    checkedIntervalIndex len lo hi k = some i → InBounds len i

/-- `send_to_end!` assigns `i=lo` and immediately reads `v[i]` when `lo≤hi`,
without the bounds check promised by its view equivalence. -/
def sendToEndFirstIndex (lo hi : Int) : Option Int := if lo ≤ hi then some lo else none

def SendToEndInBounds : Prop :=
  ∀ (len : Nat) (lo hi i : Int), sendToEndFirstIndex lo hi = some i → InBounds len i

/-- Extrema computed by the preceding `ComputeExtrema` pass. -/
def listMinMax : List Nat → Option (Nat × Nat)
  | [] => none
  | x :: xs =>
      match listMinMax xs with
      | none => some (x, x)
      | some (lo, hi) => some (min x lo, max x hi)

/-- Counting sort computes the extrema from the input, subtracts the minimum,
and indexes its `range+1` counters, `base/sort.jl:893-966,2057-2078`. -/
def sortCountIndex (values : List Nat) (k : Nat) : Option (Nat × Int) :=
  match values[k]?, listMinMax values with
  | some value, some (minimum, maximum) =>
      some (maximum - minimum + 1, value - minimum + 1)
  | _, _ => none

def SortCountBucketInBounds : Prop :=
  ∀ (values : List Nat) (k countLen : Nat) (i : Int),
    sortCountIndex values k = some (countLen, i) → InBounds countLen i

inductive SortMemory where
  | vector
  | scratch

/-- ScratchQuickSort, BracketedSort, MergeSort, and the legacy quicksort first
check `lo:hi`, normalize it to a one-based scratch span, then select either a
current or end position in the vector or scratch allocation. -/
def sortPartitionIndex (len : Nat) (lo hi : Int) (k : Nat) (toEnd : Bool)
    (memory : SortMemory) : Option (Nat × Int) :=
  if 1 ≤ lo ∧ lo ≤ hi ∧ hi ≤ len ∧ k < (hi - lo + 1).toNat then
    match memory with
    | .vector => some (len, if toEnd then hi else lo + k)
    | .scratch => some ((hi - lo + 1).toNat, if toEnd then hi - lo + 1 else k + 1)
  else none

def SortPartitionInBounds : Prop :=
  ∀ (len : Nat) (lo hi : Int) (k : Nat) (toEnd : Bool) (memory : SortMemory)
    (objectLen : Nat) (i : Int),
    sortPartitionIndex len lo hi k toEnd memory = some (objectLen, i) → InBounds objectLen i

/-- The IEEE Perm branch runs only when the index vector equals `eachindex` of
the data array, then uses those stored indices for `o.data[i]`. -/
def sortPermDataIndex (dataAxes indices : List Int) (k : Nat) : Option Int :=
  if indices = dataAxes then indices[k]? else none

def SortPermDataInBounds : Prop :=
  ∀ (dataAxes indices : List Int) (k : Nat) (i : Int),
    sortPermDataIndex dataAxes indices k = some i → i ∈ dataAxes

/-- Boolean sort first scans the checked window, then fills the `count` prefix
and remaining suffix. `count` is computed from the input values. -/
inductive BoolSortPhase where
  | scan
  | first
  | second

def boolSortIndex (xs : List Bool) (first : Bool) (phase : BoolSortPhase) (k : Nat) : Option Int :=
  let count := xs.count first
  match phase with
  | .scan => if k < xs.length then some (k + 1) else none
  | .first => if k < count then some (k + 1) else none
  | .second => if k < xs.length - count then some (count + k + 1) else none

def BoolSortInBounds : Prop :=
  ∀ (xs : List Bool) (first : Bool) (phase : BoolSortPhase) (k : Nat) (i : Int),
    boolSortIndex xs first phase k = some i → InBounds xs.length i

/-- Radix sort computes `mask=2^chunk-1`, then `(x>>shift)&mask`; modulo by
`mask+1` is the same low-bit selection used for the two counter indices. -/
def sortRadixIndices (chunk x : Nat) : Nat × Nat :=
  let bucket := x % (2 ^ chunk)
  (bucket + 1, bucket + 2)

def SortRadixBucketInBounds : Prop :=
  ∀ (chunk x : Nat), let p := sortRadixIndices chunk x
    1 ≤ p.1 ∧ p.1 ≤ 2 ^ chunk + 1 ∧ 1 ≤ p.2 ∧ p.2 ≤ 2 ^ chunk + 1

/-- The source-native first search reads only valid array slots. The result holds
for every Boolean comparison, without a sortedness or ordering premise. -/
def VectorSearchFirstInBounds : Prop :=
  ∀ (α : Type) (lt : α → α → Bool) (v : Array α) (x : α), v.size < 2 ^ 62 →
    ∀ i, JuliaLean.base.sort.searchsortedfirstBounds JuliaLean.base.sort.arrayVectorOps
      (fun _ a b => JuliaLean.Proofs.base.sort.pureCompare lt a b) () v x
      (JInt.lit .i64 1) (JInt.lit .i64 v.size) ≠ .invalidAccess i



theorem checkedIntervalInBounds : CheckedIntervalInBounds := by
  intro len lo hi k i h
  unfold checkedIntervalIndex at h
  split at h
  · simp only [Option.some.injEq] at h
    subst i
    unfold InBounds
    omega
  · contradiction

theorem sendToEndInBounds_refuted : ¬ SendToEndInBounds := by
  intro h
  have hz := h 1 0 1 0 (by simp [sendToEndFirstIndex])
  unfold InBounds at hz
  omega

private theorem listMinMax_bounds : ∀ (values : List Nat) (lo hi : Nat),
    listMinMax values = some (lo, hi) → ∀ value ∈ values, lo ≤ value ∧ value ≤ hi
  | [], _, _, h => by simp [listMinMax] at h
  | x :: xs, lo, hi, h => by
      simp only [listMinMax] at h
      cases hm : listMinMax xs with
      | none =>
          simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          intro value hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · omega
          · cases xs with
            | nil => simp at hv
            | cons y ys =>
                have hsome : listMinMax (y :: ys) ≠ none := by
                  simp only [listMinMax]
                  cases listMinMax ys <;> simp
                exact False.elim (hsome hm)
      | some p =>
          rcases p with ⟨a, b⟩
          simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          intro value hv
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact ⟨Nat.min_le_left _ _, Nat.le_max_left _ _⟩
          · have hb := listMinMax_bounds xs a b hm value hv
            exact ⟨Nat.le_trans (Nat.min_le_right _ _) hb.1,
              Nat.le_trans hb.2 (Nat.le_max_right _ _)⟩

theorem sortCountBucketInBounds : SortCountBucketInBounds := by
  intro values k countLen i h
  unfold sortCountIndex at h
  cases hv : values[k]? with
  | none => simp [hv] at h
  | some value =>
      cases hm : listMinMax values with
      | none => simp [hv, hm] at h
      | some p =>
          rcases p with ⟨minimum, maximum⟩
          simp only [hv, hm, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hk : k < values.length := (List.getElem?_eq_some_iff.mp hv).1
          have hmem : value ∈ values := by
            have he : values[k] = value := by simpa [List.getElem?_eq_getElem hk] using hv
            rw [← he]
            exact List.getElem_mem hk
          have hb := listMinMax_bounds values minimum maximum hm value hmem
          unfold InBounds
          omega

theorem sortPartitionInBounds : SortPartitionInBounds := by
  intro len lo hi k toEnd memory objectLen i h
  unfold sortPartitionIndex at h
  split at h
  · cases memory <;> split at h <;>
      simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
      rcases h with ⟨rfl, rfl⟩ <;> unfold InBounds <;> omega
  · contradiction

theorem sortPermDataInBounds : SortPermDataInBounds := by
  intro dataAxes indices k i h
  unfold sortPermDataIndex at h
  split at h
  · rename_i heq
    have hk : k < indices.length := List.getElem?_eq_some_iff.mp h |>.1
    have hi : indices[k] = i := by simpa [List.getElem?_eq_getElem hk] using h
    rw [← heq, ← hi]
    exact List.getElem_mem hk
  · contradiction

theorem boolSortInBounds : BoolSortInBounds := by
  intro xs first phase k i h
  have hc : xs.count first ≤ xs.length := List.count_le_length
  cases phase with
  | scan =>
      by_cases hk : k < xs.length
      · simp [boolSortIndex, hk] at h
        subst i
        unfold InBounds
        omega
      · simp [boolSortIndex, hk] at h
  | first =>
      by_cases hk : k < xs.count first
      · simp [boolSortIndex, hk] at h
        subst i
        unfold InBounds
        omega
      · simp [boolSortIndex, hk] at h
  | second =>
      by_cases hk : k < xs.length - xs.count first
      · simp [boolSortIndex, hk] at h
        subst i
        unfold InBounds
        omega
      · simp [boolSortIndex, hk] at h

theorem sortRadixBucketInBounds : SortRadixBucketInBounds := by
  intro chunk x
  dsimp [sortRadixIndices]
  have hp : 0 < 2 ^ chunk := Nat.two_pow_pos chunk
  have hm := Nat.mod_lt x hp
  omega

namespace NativeSearch

open JuliaLean.base.sort JuliaLean.Proofs.base.sort

private theorem firstLoop_safe {α : Type} (lt : α → α → Bool) (v : Array α) (x : α)
    (sizeBound : v.size < 2 ^ 62) :
    ∀ (fuel : Nat) (lo len : Int) (hi : SearchIndex),
      1 ≤ lo → 0 ≤ len → lo + len ≤ v.size + 1 →
      ∀ i, firstSearchLoop arrayVectorOps (fun _ a b => pureCompare lt a b) () v x
        fuel (I64Idx lo) hi (I64Idx len) ≠ .invalidAccess i := by
  have hmin : IntTy.min .i64 ≤ 0 := by decide
  have hmax : (2 ^ 62 : Int) < IntTy.max .i64 := by decide
  intro fuel
  induction fuel with
  | zero =>
      intro lo len hi hlo hlen hspan i
      simp [firstSearchLoop]
  | succ fuel ih =>
      intro lo len hi hlo hlen hspan i
      unfold firstSearchLoop
      rw [I64Idx_val (by omega) (by omega)]
      by_cases hz : len = 0
      · simp [hz]
      · rw [if_neg hz]
        have half : indexHalf (I64Idx len) = I64Idx (len / 2) :=
          half_I64Idx hlen (by omega)
        have middle : indexAdd (I64Idx lo) (I64Idx (len / 2)) = I64Idx (lo + len / 2) :=
          add_I64Idx (by omega) (by omega) (by omega) (by omega)
        have hmiddle : 1 ≤ lo + len / 2 ∧ lo + len / 2 ≤ v.size := by omega
        have middleValue : (I64Idx (lo + len / 2)).val = lo + len / 2 :=
          I64Idx_val (by omega) (by omega)
        simp only [half, middle, middleValue]
        obtain ⟨value, read⟩ := arrayVectorOps_read_some hmiddle.1 hmiddle.2
        rw [read]
        simp only [pureCompare]
        cases compare : lt value x
        · exact ih lo (len / 2) (I64Idx (lo + len / 2)) hlo (by omega) (by omega) i
        · rw [add_I64Idx (by omega) (by omega) (by decide) (by decide),
            add_I64Idx (by omega) (by omega) (by decide) (by decide),
            sub_I64Idx (by omega) (by omega) (by omega) (by omega)]
          exact ih (lo + len / 2 + 1) (len - (len / 2 + 1)) hi
            (by omega) (by omega) (by omega) i

theorem first_safe {α : Type} (lt : α → α → Bool) (v : Array α) (x : α)
    (sizeBound : v.size < 2 ^ 62) :
    ∀ i, searchsortedfirstBounds arrayVectorOps (fun _ a b => pureCompare lt a b) ()
      v x (JInt.lit .i64 1) (JInt.lit .i64 v.size) ≠ .invalidAccess i := by
  have hmin : IntTy.min .i64 ≤ 0 := by decide
  have hmax : (2 ^ 62 : Int) < IntTy.max .i64 := by decide
  unfold searchsortedfirstBounds
  change ∀ i, firstSearchLoop arrayVectorOps (fun _ a b => pureCompare lt a b) () v x
    ((indexSub (indexAdd (I64Idx v.size) (I64Idx 1)) (I64Idx 1)).val.toNat + 2)
    (I64Idx 1) (indexAdd (I64Idx v.size) (I64Idx 1))
    (indexSub (indexAdd (I64Idx v.size) (I64Idx 1)) (I64Idx 1)) ≠ .invalidAccess i
  have high : indexAdd (I64Idx v.size) (I64Idx 1) = I64Idx (v.size + 1) :=
    add_I64Idx (by omega) (by omega) (by decide) (by decide)
  have length : indexSub (I64Idx (v.size + 1)) (I64Idx 1) = I64Idx v.size := by
    rw [sub_I64Idx (by omega) (by omega) (by decide) (by decide)]
    congr 1
    omega
  simp only [high, length]
  exact firstLoop_safe lt v x sizeBound _ 1 v.size (I64Idx (v.size + 1))
    (by decide) (by omega) (by omega)

end NativeSearch



theorem vectorSearchFirstInBounds : VectorSearchFirstInBounds := by
  intro α lt v x sizeBound
  exact NativeSearch.first_safe lt v x sizeBound


end JuliaLean.MemSafety.G4

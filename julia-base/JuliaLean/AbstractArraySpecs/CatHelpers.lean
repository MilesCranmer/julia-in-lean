import JuliaLean.AbstractArraySpecs.Cat
import JuliaLean.AbstractArraySpecs.Basic

/-! Independent contracts for `cat_size`, `cat_length`, `cat_ndims`, `cat_similar`
and `dims2cat(::Val)`. Sizes are axis cardinalities, lengths count elements, and
allocations have the requested dimensions and element count, regardless of the
exemplar. The output element type is the type parameter `β` of `CatOut β`.
The allocation models abstract available memory; dimensions must satisfy the
Array constructor's checked-dimensions requirements. -/

namespace JuliaLean.AbstractArraySpecs

open JuliaLean

/-- `cat_size(A)` lists the cardinality of each axis. -/
def CatSizeAllSpec : Prop :=
  ∀ {α : Type} (A : Arr α), A.WF → (catSizeAll (.arr A)).map (·.val) = A.axes.map Ax.len

/-- `cat_length(A)` counts A's elements. -/
def CatLengthSpec : Prop :=
  ∀ {α : Type} (A : Arr α), A.WF → (catLength (.arr A)).val = A.data.length

/-- `cat_ndims(A)` is the number of independent axis coordinates. -/
def CatNdimsSpec : Prop :=
  ∀ {α : Type} (A : Arr α), catNdims (.arr A) = A.axes.length

theorem catSizeAllSpec_proven : CatSizeAllSpec := by
  intro α A hA
  simp only [catSizeAll, sizeA, List.map_map]
  apply List.map_congr_left
  intro r hr
  exact axLength_val (hA.1 r hr)

theorem catLengthSpec_proven : CatLengthSpec := by
  intro α A hA
  exact lengthA_val A hA

/-- The trailing-singleton rule for every positive `Integer` dimension, including
values above `typemax(Int)`: after the explicit axes the size is 1. -/
def CatSizeAllIntegerSpec : Prop :=
  ∀ {α : Type} (A : Arr α) (d : Int), A.WF → 1 ≤ d →
    catSizeIntegerDim A d = .ok (i64 (((A.axes.map Ax.len)[(d - 1).toNat]?).getD 1))

theorem catSizeAllIntegerSpec_refuted : ¬ CatSizeAllIntegerSpec := by
  intro h
  let A : Arr Int := ⟨[], .linear, [7]⟩
  have bad := h A (tmax + 1) (by decide) (by decide)
  revert bad
  decide

theorem catNdimsSpec_proven : CatNdimsSpec := by intro α A; rfl

/-- Dimensions accepted by `Core.checked_dims` and the Memory length check. -/
def ShapeOK (shape : List I64) : Prop :=
  (∀ n ∈ shape, 0 ≤ n.val ∧ n.val < tmax) ∧ (shape.map (·.val)).foldl (· * ·) 1 ≤ tmax

/-- The requested shape and its number of cells, stated independently of allocation. -/
def Allocated {β : Type} (shape : List I64) (r : R (CatOut β)) : Prop :=
  ∃ out, r = .ok out ∧ out.shape.map (·.val) = shape.map (·.val) ∧
    out.cells.length = (shape.map (fun n => n.val.toNat)).prod

/-- The allocator returns the requested shape on valid dimensions and rejects a
negative dimension with `ArgumentError`. -/
def AllocationContract {β : Type} (shape : List I64) (r : R (CatOut β)) : Prop :=
  (ShapeOK shape → Allocated shape r) ∧
    ((∃ n ∈ shape, n.val < 0) → r = .error .argumentError)

def CatSimilarTupleSpec : Prop :=
  ∀ {α β : Type} (A : Item α) (shape : List I64), AllocationContract shape (catSimilarTuple (β := β) A shape)
def CatSimilarVectorSpec : Prop :=
  ∀ {α β : Type} (A : Item α) (shape : List I64), AllocationContract shape (catSimilarVector (β := β) A shape)
def CatSimilarArrayTupleSpec : Prop :=
  ∀ {α β : Type} (A : Arr α) (shape : List I64), AllocationContract shape (catSimilarArrayTuple (β := β) A shape)
def CatSimilarArrayVectorSpec : Prop :=
  ∀ {α β : Type} (A : Arr α) (shape : List I64), AllocationContract shape (catSimilarArrayVector (β := β) A shape)
def CatSimilarAbsVectorSpec : Prop :=
  ∀ {α β : Type} (A : Arr α) (shape : List I64), A.WF → AllocationContract shape (catSimilarAbsVector (β := β) A shape)

theorem arrayUndef_contract {β : Type} (shape : List I64) : AllocationContract shape (arrayUndef (β := β) shape) := by
  constructor
  · intro h
    have hn : shape.any (fun s => decide (s.val < 0) || decide (s.val = tmax)) = false := by
      rw [List.any_eq_false]
      intro s hs
      have := h.1 s hs
      simp [show ¬s.val < 0 by omega, show s.val ≠ tmax by omega]
    have hov : decide (tmax < (shape.map (fun s => s.val)).foldl (· * ·) 1) = false :=
      decide_eq_false_iff_not.mpr (Int.not_lt.mpr h.2)
    have e : dimsInvalid shape = false := by unfold dimsInvalid; rw [hn, hov]; rfl
    refine ⟨⟨shape, List.replicate ((shape.map (fun s => s.val.toNat)).foldl (· * ·) 1) none⟩, ?_, rfl, ?_⟩
    · simp only [arrayUndef, e, Bool.false_eq_true, ite_false]
    · simp only [List.length_replicate, List.prod_eq_foldl]
  · intro ⟨s, hs, hneg⟩
    have hn : shape.any (fun s => decide (s.val < 0) || decide (s.val = tmax)) = true := by
      simp only [List.any_eq_true]
      exact ⟨s, hs, by simp [hneg]⟩
    simp [arrayUndef, dimsInvalid, hn]

theorem catSimilarTupleSpec_proven : CatSimilarTupleSpec := by
  intro α β A shape
  exact arrayUndef_contract shape

theorem catSimilarVectorSpec_proven : CatSimilarVectorSpec := by
  intro α β A shape
  exact arrayUndef_contract shape

theorem catSimilarArrayTupleSpec_proven : CatSimilarArrayTupleSpec := by
  intro α β A shape
  exact arrayUndef_contract shape

theorem catSimilarArrayVectorSpec_proven : CatSimilarArrayVectorSpec := by
  intro α β A shape
  exact arrayUndef_contract shape

/-- With an empty shape vector, `similar(A, T, shape...)` selects `similar(A, T)`
which preserves A's dimensions rather than allocating a zero-dimensional array. -/
theorem catSimilarAbsVectorSpec_refuted : ¬ CatSimilarAbsVectorSpec := by
  intro h
  let A : Arr Int := ⟨[oneTo (i64 3)], .linear, [1, 2, 3]⟩
  obtain ⟨out, hout, hshape, _⟩ := (h (β := Int) A [] (by decide)).1 (by constructor <;> decide)
  have he : catSimilarAbsVector (β := Int) A [] = .ok ⟨[i64 3], [none, none, none]⟩ := by decide
  rw [he] at hout
  cases hout
  contradiction

/-- Valid dimensions encode exactly their membership, with the shortest possible flag
tuple that contains all dimensions; invalid non-positive dimensions are rejected. -/
def Dims2catValSpec : Prop :=
  ∀ dims : List Int,
    ((∃ d ∈ dims, d ≤ 0) → dims2catVal dims = .error .argumentError) ∧
    (dims ≠ [] → (∀ d ∈ dims, 1 ≤ d) → ∃ flags,
      dims2catVal dims = .ok flags ∧
      (∀ d ∈ dims, d ≤ (flags.length : Int)) ∧
      (flags.length : Int) ∈ dims ∧
      ∀ k : Nat, k < flags.length → flags[k]? = some (decide (((k : Int) + 1) ∈ dims)))

theorem foldMax_spec (xs : List Int) : ∀ m,
    m ≤ xs.foldl max m ∧ (∀ d ∈ xs, d ≤ xs.foldl max m) ∧ (xs.foldl max m = m ∨ xs.foldl max m ∈ xs) := by
  induction xs with
  | nil => intro m; simp
  | cons x xs ih =>
    intro m
    obtain ⟨h1, h2, h3⟩ := ih (max m x)
    simp only [List.foldl_cons]
    refine ⟨by omega, ?_, ?_⟩
    · intro d hd; rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · exact h2 d hd
    · rcases h3 with h3 | h3
      · by_cases hm : m ≤ x
        · right; exact List.mem_cons.mpr (Or.inl (by rw [h3]; omega))
        · left; rw [h3]; omega
      · right; exact List.mem_cons_of_mem _ h3

theorem dims2catValSpec_proven : Dims2catValSpec := by
  intro dims
  constructor
  · intro ⟨d, hd, he⟩
    have hb : dims.any (· ≤ 0) = true := by
      rw [List.any_eq_true]; exact ⟨d, hd, by simpa using he⟩
    simp [dims2catVal, dims2cat, hb]
  · intro hne hpos
    cases dims with
    | nil => contradiction
    | cons d ds =>
      have hd : 1 ≤ d := hpos d (by simp)
      obtain ⟨hm, hds, hmax⟩ := foldMax_spec ds d
      have hnonneg : 0 ≤ ds.foldl max d := by omega
      have hb : (d :: ds).any (· ≤ 0) = false := by
        rw [List.any_eq_false]
        intro x hx
        simp only [decide_eq_true_eq]
        have := hpos x hx
        omega
      refine ⟨(List.range (ds.foldl max d).toNat).map (fun (k : Nat) => (d :: ds).contains ((k : Int) + 1)),
        ?_, ?_, ?_, ?_⟩
      · simp only [dims2catVal, dims2cat, hb, Bool.false_eq_true, ite_false]
      · intro x hx
        simp only [List.length_map, List.length_range, Int.toNat_of_nonneg hnonneg]
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hm
        · exact hds x hx
      · simp only [List.length_map, List.length_range, Int.toNat_of_nonneg hnonneg]
        rcases hmax with hmax | hmax
        · simp [hmax]
        · exact List.mem_cons_of_mem _ hmax
      · intro k hk
        simp only [List.length_map, List.length_range] at hk
        simp [List.getElem?_map, List.getElem?_range hk]

end JuliaLean.AbstractArraySpecs

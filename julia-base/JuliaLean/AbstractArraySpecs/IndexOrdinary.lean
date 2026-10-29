import JuliaLean.AbstractArraySpecs.IndexingProofs
import JuliaLean.AbstractArraySpecs.Refutations

/-!
Indexing contracts for the restricted mutable `Arr` model. In particular, its
linear conversion treats vector axis values as the axes of the axis range.
-/

namespace JuliaLean.AbstractArraySpecs

/-- Omitted trailing indices (doc/src/manual/arrays.md "Omitted and extra indices":
"the trailing indices can be omitted ... for dimensions of length 1"): with at least one
and fewer than `ndims(A)` `Int` indices, `getindex`, `setindex!` and `get` act on the
element the manual's rules select and throw `BoundsError` (`get`: return the default)
when none is selected, for either `IndexStyle` and any axes. -/
def OmittedIndexingAgrees : Prop :=
  ∀ {α : Type} (A : Arr α) (I : List I64) (v d : α), A.WF → I ≠ [] → I.length < A.axes.length →
    getindex A I = refGet A I ∧ setindex A v I = refSet A v I ∧ getDefault A I d = refGetDefault A I d

/-- `A[]` on an `IndexLinear` array (manual: `A[]` is the idiom for the only element of
an array whose dimensions all have length 1): `getindex`, `setindex!` and
`get(A, (), default)` act on the only element and throw `BoundsError` (`get`: return the
default) for any other shape, for any axes. -/
def ZeroIndexLinearAgrees : Prop :=
  ∀ {α : Type} (A : Arr α) (v d : α), A.WF → A.style = .linear →
    getindex A [] = refGet A [] ∧ setindex A v [] = refSet A v [] ∧ getDefault A [] d = refGetDefault A [] d

/-- The contract of `IndexingAgreesWithReference` for ordinary arrays: every axis starts
at 1. Any number of `Int` indices, either `IndexStyle`, any element type. -/
def IndexingOrdinary : Prop :=
  ∀ {α : Type} (A : Arr α) (I : List I64) (v d : α), A.WF → (∀ r ∈ A.axes, r.lo = i64 1) →
    getindex A I = refGet A I ∧ setindex A v I = refSet A v I ∧ getDefault A I d = refGetDefault A I d

/-- `setindex!(A, v, I...)` with any number of `Int` indices writes the element the
manual's rules select and throws `BoundsError` when none is selected, for any axes. -/
def SetindexAgreesWithReference : Prop :=
  ∀ (A : Arr Int) (I : List I64) (v : Int), A.WF → setindex A v I = refSet A v I

/-- `get(A, I, default)` with any number of `Int` indices (including `()`) returns the
selected element or `default`, for any axes. -/
def GetDefaultAgreesWithReference : Prop :=
  ∀ (A : Arr Int) (I : List I64) (d : Int), A.WF → getDefault A I d = refGetDefault A I d

/-! ## Padding omitted indices with the axis starts -/

theorem refCartPos_starts (axs : List Ax) (h : axs.all (fun r => decide (r.len = 1)) = true) :
    refCartPos axs (axs.map (·.lo.val)) = some 0 := by
  induction axs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hl := len_def r
    simp only [List.map_cons, refCartPos]
    rw [if_pos (by omega), ih h2]
    simp

theorem refCartPos_pad (is : List Int) : ∀ (axs : List Ax) (p : Nat),
    is.length ≤ axs.length → refCartPos axs is = some p →
    refCartPos axs (is ++ (axs.drop is.length).map (·.lo.val)) = some p := by
  induction is with
  | nil =>
    intro axs p _ hp
    obtain ⟨rfl, hall⟩ := refCartPos_nil hp
    simpa using refCartPos_starts axs hall
  | cons i is ih =>
    intro axs p hlen hp
    match axs, hlen with
    | r :: rs, hlen =>
      simp only [List.length_cons, List.drop_succ_cons, List.cons_append, refCartPos] at hp ⊢
      split at hp
      · rename_i hin
        rw [if_pos hin]
        obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
        rw [ih rs p' (by simp at hlen; omega) hp']
        rfl
      · simp at hp

theorem map_val_pad (I : List I64) (axs : List Ax) :
    (I ++ (axs.drop I.length).map (·.lo)).map (·.val) =
      I.map (·.val) ++ (axs.drop (I.map (·.val)).length).map (·.lo.val) := by
  simp [List.map_append, List.map_map, Function.comp_def]

/-- `_to_subscript_indices` pads omitted indices with the axis starts, and the
padded tuple selects the same element. -/
theorem toSubscript_omitted {α : Type} (A : Arr α) (I : List I64)
    (hlen : I.length < A.axes.length) (h1 : I.length ≠ 1)
    (p : Nat) (hp : refCartPos A.axes (I.map (·.val)) = some p) :
    ∃ J, toSubscriptIndices A I = .ok J ∧ J.length = A.axes.length ∧
      refCartPos A.axes (J.map (·.val)) = some p := by
  have hpad := refCartPos_pad (I.map (·.val)) A.axes p (by simp; omega) hp
  rw [← map_val_pad] at hpad
  refine ⟨I ++ (A.axes.drop I.length).map (·.lo), ?_,
    by simp only [List.length_append, List.length_map, List.length_drop]; omega, hpad⟩
  obtain ⟨r, rs, hax⟩ : ∃ r rs, A.axes = r :: rs := by
    rcases h : A.axes with _ | ⟨r, rs⟩
    · rw [h] at hlen; simp at hlen
    · exact ⟨r, rs, rfl⟩
  rw [hax] at hlen
  match I, h1, hlen with
  | [], _, _ =>
    simp only [toSubscriptIndices, axisStarts, hax, List.length_nil, List.drop_zero, List.nil_append]
  | i :: i2 :: I', _, hlen =>
    simp only [toSubscriptIndices, hax]
    rw [if_pos (by simp only [List.length_cons] at hlen ⊢; omega)]

/-! ## The general indexing lemma -/

/-- Indexing agrees with the reference for every index count and either index style. -/
theorem indexing_general {α : Type} (A : Arr α) (hA : A.WF) (I : List I64) :
    getindex A I = refGet A I ∧ ∀ v, setindex A v I = refSet A v I := by
  by_cases hext : A.axes.length ≤ I.length
  · exact indexing_extra A hA I hext
  by_cases h1 : I.length = 1
  · obtain ⟨k, rfl⟩ := exists_single h1
    exact indexing_linear A hA k
  simp only [refGet_eq, refSet_eq, refPos_cart A I h1]
  have hcb := checkbounds_eq A hA I
  rw [refPos_cart A I h1] at hcb
  rcases hst : A.style with _ | _
  · rcases hq : refCartPos A.axes (I.map (·.val)) with _ | p
    · rw [hq] at hcb
      simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hcb
      simp only [getindex, setindex, hst, if_neg h1, hcb, bind_err, elemAt, storeAt, hq]
      refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl
    · rw [hq] at hcb
      simp only [Option.isSome_some, if_true] at hcb
      obtain ⟨k, hk, hlin⟩ := toLinearIndex_ok A hA I h1 p hq
      simp only [getindex, setindex, hst, if_neg h1, hcb, bind_ok, hk, canonGetL, canonSetL, hlin, hq]
      refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl
  · have hN : ¬ I.length = A.axes.length := by omega
    rcases hq : refCartPos A.axes (I.map (·.val)) with _ | p
    · rw [hq] at hcb
      simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hcb
      simp only [getindex, setindex, hst, if_neg hN, hcb, bind_err, elemAt, storeAt, hq]
      refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl
    · rw [hq] at hcb
      simp only [Option.isSome_some, if_true] at hcb
      obtain ⟨J, hJ, hl, hpos⟩ := toSubscript_omitted A I (by omega) h1 p hq
      simp only [getindex, setindex, hst, if_neg hN, hcb, bind_ok, hJ, canonGetC, canonSetC,
        hl, if_true, hpos, hq]
      refine ⟨?_, fun _ => ?_⟩ <;> first | trivial | rfl

theorem omittedIndexingAgrees_proven : OmittedIndexingAgrees := by
  intro α A I v d hA _ _
  obtain ⟨hg, hs⟩ := indexing_general A hA I
  exact ⟨hg, hs v, getDefault_of A hA I d hg⟩

theorem zeroIndexLinearAgrees_proven : ZeroIndexLinearAgrees := by
  intro α A v d hA _
  obtain ⟨hg, hs⟩ := indexing_general A hA []
  exact ⟨hg, hs v, getDefault_of A hA [] d hg⟩

theorem indexingOrdinary_proven : IndexingOrdinary := by
  intro α A I v d hA _
  obtain ⟨hg, hs⟩ := indexing_general A hA I
  exact ⟨hg, hs v, getDefault_of A hA I d hg⟩

/-- The indexing contract for the restricted `Arr` model. -/
theorem indexingAgreesWithReference_proven : IndexingAgreesWithReference := by
  intro A I v d hA
  obtain ⟨hg, hs⟩ := indexing_general A hA I
  exact ⟨hg, hs v, getDefault_of A hA I d hg⟩

end JuliaLean.AbstractArraySpecs

import JuliaLean.MultidimCov.ArrayV2DeleteProps

/-!
Properties of logical indexing with a `Bool` unit range (`base/array.jl:993`) and of the
converting `pushfirst!` (`base/array.jl:1777`).
-/

namespace JuliaLean.MultidimCov.ArrayV2

theorem logical_idx_eq (mask : List Bool) :
    ((List.range mask.length).filter fun k => mask.getD k false).map (fun (k : Nat) => ((k : Int) + 1)) =
      maskIdx mask true := by
  unfold maskIdx
  congr 1
  apply List.filter_congr
  intro k _; cases mask.getD k false <;> rfl

theorem mapM_getL_undef {A : Arr α} : ∀ (is : List Int), (∀ i ∈ is, inBounds A i = true) →
    (∃ i ∈ is, A.at i = none) → is.mapM (getL A) = .error .undefRef
  | [], _, h => by simp at h
  | i :: is, hb, ⟨j, hj, hjn⟩ => by
    simp only [List.mapM_cons]
    cases hi : A.at i with
    | none =>
      have hg : getL A i = .error .undefRef := by unfold getL; rw [if_pos (hb i (by simp)), hi]
      rw [hg, bind_error]
    | some x =>
      have hg : getL A i = .ok x := by unfold getL; rw [if_pos (hb i (by simp)), hi]
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [hi] at hjn; cases hjn
      rw [hg, bind_ok, mapM_getL_undef is (fun k hk => hb k (by simp [hk])) ⟨j, hj, hjn⟩, bind_error]

/-- `A[r]` for a `Bool` unit range `r` is logical indexing with `collect(r)` as the mask
(comment base/array.jl:992; manual "Logical indexing"): a mask whose length differs from
`length(A)` throws `BoundsError`; otherwise the result is the vector of the elements
`A[i]` where the mask is true, in order, and an `#undef` selected element throws
`UndefRefError`. -/
def P993 : Prop := ∀ {α : Type} (A : Arr α) (f l : Bool), Valid A → length A ≤ 2 ^ 58 →
    ((boolRange f l).length ≠ length A → m993 A f l = .error .bounds) ∧
    ((boolRange f l).length = length A → (∀ t ∈ maskIdx (boolRange f l) true, (A.at t).isSome) →
      ∃ X, m993 A f l = .ok X ∧ IsVec X (maskIdx (boolRange f l) true).length ∧
        contents X = (maskIdx (boolRange f l) true).map A.at) ∧
    ((boolRange f l).length = length A → (∃ t ∈ maskIdx (boolRange f l) true, A.at t = none) →
      m993 A f l = .error .undefRef)

theorem maskIdx_inBounds {A : Arr α} {mask : List Bool} (hl : (mask.length : Int) = length A) :
    ∀ t ∈ maskIdx mask true, inBounds A t = true := by
  intro t ht
  unfold maskIdx at ht
  simp only [List.mem_map, List.mem_filter, List.mem_range] at ht
  obtain ⟨k, ⟨hk, _⟩, rfl⟩ := ht
  rw [inBounds_iff]; omega

theorem p993 : P993 := by
  intro α A f l hA hl
  refine ⟨fun h => by unfold m993 logicalGet; rw [if_pos h], fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · have hb := maskIdx_inBounds (A := A) (mask := boolRange f l) h1
    obtain ⟨vs, e, hv⟩ := mapM_getL_ok (maskIdx (boolRange f l) true) (fun t ht => ⟨hb t ht, h2 t ht⟩)
    have hvl : vs.length = (maskIdx (boolRange f l) true).length := by simpa using congrArg List.length hv
    have hml : ((maskIdx (boolRange f l) true).length : Int) ≤ 2 ^ 58 := by
      unfold maskIdx; simp only [List.length_map]
      have := List.length_filter_le (fun k => (boolRange f l).getD k false == true) (List.range (boolRange f l).length)
      rw [List.length_range] at this; omega
    obtain ⟨X, eX, hX⟩ := newArray_ok (α := α) (dims := [(vs.length : Int)]) (by simp)
      (by simp [typemaxInt]; omega)
    refine ⟨safeWrites X 1 vs, ?_, ?_, ?_⟩
    · unfold m993 logicalGet
      rw [if_neg (by omega), logical_idx_eq]; dsimp only; rw [e, bind_ok, eX, bind_ok]; rfl
    · unfold IsVec; rw [(safeWrites_spec vs X 1).1, hX.1, hvl]
    · rw [contents_safeWrites_full (by simp [length, hX.1]), hv]
  · unfold m993 logicalGet
    rw [if_neg (by omega), logical_idx_eq]; dsimp only; rw [
      mapM_getL_undef _ (maskIdx_inBounds (A := A) (mask := boolRange f l) h1) h2, bind_error]

/-- `pushfirst!(a::Vector{T}, item)` (docstring base/array.jl:1757-1776): the item converted
to `T` becomes the first element, followed by the old elements; a failing conversion throws
that error. -/
def P1777 : Prop := ∀ {α β : Type} (conv : β → R α) (a : Arr α) (n : Int) (item : β), VecOK a n →
    (∀ e, conv item = .error e → pushfirstConv conv a item = .error e) ∧
    (∀ y, conv item = .ok y → ∃ a', pushfirstConv conv a item = .ok a' ∧ IsVec a' (n + 1) ∧
      contents a' = some y :: contents a)

theorem p1777 : P1777 := by
  intro α β conv a n item ha
  refine ⟨fun e he => by unfold pushfirstConv; rw [he, bind_error], fun y hy => ?_⟩
  obtain ⟨a', e, hv, _, hc⟩ := m1782_spec ha y
  exact ⟨a', by unfold pushfirstConv; rw [hy, bind_ok, e], hv, hc⟩

end JuliaLean.MultidimCov.ArrayV2

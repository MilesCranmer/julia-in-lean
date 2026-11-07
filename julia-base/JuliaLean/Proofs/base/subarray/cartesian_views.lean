import JuliaLean.base.subarray
import JuliaLean.Proofs.base.abstractarray.cartesian_shapes

namespace JuliaLean.Multidim

/-- Every array position a view can address lies inside the array: each index stays
within the true length of each dimension it covers (dimensions beyond `ndims(A)` have
length 1), whether or not `checkbounds` looked at it. -/
def viewInBounds (sz : List Nat) (I : List Idx) : Bool :=
  let parts := splitAxes I (axesFor sz (I.foldl (fun k i => k + i.ndims) 0))
  parts.all fun (i, ns) => match i, ns with
    | .slice n, [m] => decide (n ≤ m)
    | i, ns => checkIdx i ns

namespace SmallAux

/-! ## `selectdim` -/

theorem foldl_ndims (f : Nat → Idx) (hf : ∀ j, (f j).ndims = 1) :
    ∀ (L : List Nat) (k : Nat), (L.map f).foldl (fun k i => k + i.ndims) k = k + L.length
  | [], k => by simp
  | j :: L, k => by
    simp only [List.map_cons, List.foldl_cons, hf, List.length_cons]
    rw [foldl_ndims f hf L (k + 1)]; omega

theorem splitAxes_map (f : Nat → Idx) (h : Nat → Nat) (hf : ∀ j, (f j).ndims = 1) :
    ∀ L : List Nat, splitAxes (L.map f) (L.map h) = L.map fun j => (f j, [h j])
  | [] => rfl
  | j :: L => by
    simp [splitAxes, hf, splitAxes_map f h hf L]

theorem any_sel (f g : Nat → Idx) (h : Nat → Nat)
    (hb : ∀ j, f j = g j ∨ (f j = .slice (h j) ∧ g j = .colon))
    (L : List Nat) (P : Idx → Bool) (hP : ∀ m, P (.slice m) = P .colon) :
    (L.map f).any P = (L.map g).any P := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.map_cons, List.any_cons, ih]
    rcases hb j with e | ⟨e1, e2⟩
    · rw [e]
    · rw [e1, e2, hP]

theorem all_sel (f g : Nat → Idx) (h : Nat → Nat)
    (hb : ∀ j, f j = g j ∨ (f j = .slice (h j) ∧ g j = .colon))
    (L : List Nat) (Q : Idx × List Nat → Bool) (hQ : ∀ m, Q (.slice m, [m]) = Q (.colon, [m])) :
    (L.map fun j => (f j, [h j])).all Q = (L.map fun j => (g j, [h j])).all Q := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.map_cons, List.all_cons, ih]
    rcases hb j with e | ⟨e1, e2⟩
    · rw [e]
    · rw [e1, e2, hQ]

theorem filterMap_sel (f g : Nat → Idx) (h : Nat → Nat)
    (hb : ∀ j, f j = g j ∨ (f j = .slice (h j) ∧ g j = .colon))
    (L : List Nat) (Q : Idx × List Nat → Option Nat)
    (hQ : ∀ m, Q (.slice m, [m]) = Q (.colon, [m])) :
    (L.map fun j => (f j, [h j])).filterMap Q = (L.map fun j => (g j, [h j])).filterMap Q := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.map_cons, List.filterMap_cons, ih]
    rcases hb j with e | ⟨e1, e2⟩
    · rw [e]
    · rw [e1, e2, hQ]

theorem view_congr (sz : List Nat) (f g : Nat → Idx) (hf : ∀ j, (f j).ndims = 1)
    (hg : ∀ j, (g j).ndims = 1)
    (hb : ∀ j, f j = g j ∨ (f j = .slice (sz.getD j 0) ∧ g j = .colon)) :
    view sz ((List.range sz.length).map f) = view sz ((List.range sz.length).map g) := by
  have hax : axesFor sz sz.length = (List.range sz.length).map (fun j => sz.getD j 0) := by
    rw [range_map_getD]; simp [axesFor]
  simp only [view, foldl_ndims f hf, foldl_ndims g hg, List.length_range,
    Nat.zero_add, hax, splitAxes_map f (fun j => sz.getD j 0) hf,
    splitAxes_map g (fun j => sz.getD j 0) hg]
  rw [any_sel f g _ hb, all_sel f g _ hb, filterMap_sel f g _ hb]
  all_goals first | rfl | (intro m; rfl) | (intro m; simp [idxLen])

theorem rep_split (x y : Idx) (a b : Nat) : List.replicate a x ++ [y] ++ List.replicate b x =
    (List.range (a + 1 + b)).map fun j => if j = a then y else x := by
  apply List.ext_getElem
  · simp; omega
  · intro m h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rcases Nat.lt_trichotomy m a with hm | hm | hm
    · simp [hm, Nat.ne_of_lt hm]
    · subst hm
      simp [List.getElem_cons]
    · have hm1 : ¬ m < a := by omega
      have hm2 : m - a ≠ 0 := by omega
      simp [List.getElem_append, List.getElem_cons, hm1, hm2, Nat.ne_of_gt hm]

end SmallAux

open SmallAux


end JuliaLean.Multidim

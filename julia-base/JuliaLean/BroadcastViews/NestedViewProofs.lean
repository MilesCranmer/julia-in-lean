import JuliaLean.BroadcastViews.NestedView

/-! `view(view(A, I...), J...)[K...]` reads the same parent element as `view(A, I...)[J[K]...]`. -/

namespace JuliaLean.BroadcastViews

open JuliaLean

/-- For one-based index kinds, the view of a view `W = view(V, J...)` with `V = view(A, I...)`
(stored as `view(A, reindex(I, J)...)`) reads, at every in-bounds `K`, the parent subscripts
that `V` reads at `J[K]`: `reindex(reindex(I, J), K) == reindex(I, reindex(J, K))`. -/
def NestedViewCompose : Prop :=
  ∀ (I J : List VIdx) (K : List Int), KInBounds J K →
    readSubs (reindex I J) K = reindex I (readSubs J K)

private theorem at1_range (xs : List Int) (m : Nat) (k : Int) (h1 : 1 ≤ k) (h2 : k ≤ m) :
    at1 ((List.range m).map (fun k : Nat => at1 xs ((k : Int) + 1))) k = at1 xs k := by
  unfold at1
  have hk : (k - 1).toNat < m := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some]
  congr 2
  omega

private theorem at1_map (xs ks : List Int) (k : Int) (h1 : 1 ≤ k) (h2 : k ≤ ks.length) :
    at1 (ks.map (at1 xs)) k = at1 xs (at1 ks k) := by
  unfold at1
  have hk : (k - 1).toNat < ks.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  simp only [Option.map_some, Option.getD_some]
  rw [List.getD_eq_getElem?_getD (l := ks), List.getElem?_eq_getElem hk, Option.getD_some]

theorem nestedViewCompose : NestedViewCompose := by
  intro I
  induction I with
  | nil => intro J K _; simp [readSubs, reindex]
  | cons i is ih =>
    intro J K hK
    cases i with
    | scalar a =>
      simp only [readSubs, reindex] at ih ⊢
      rw [ih J K hK]
    | slice n =>
      cases J with
      | nil => simp [readSubs, reindex]
      | cons j js =>
        cases j with
        | scalar k =>
          simp only [readSubs, reindex, KInBounds] at ih hK ⊢
          rw [ih js K hK]
        | slice m =>
          cases K with
          | nil => simp [readSubs, reindex]
          | cons k K =>
            simp only [readSubs, reindex, KInBounds, List.map_cons] at ih hK ⊢
            rw [ih js K hK.2.2]
        | vec ks =>
          cases K with
          | nil => simp [readSubs, reindex]
          | cons k K =>
            simp only [readSubs, reindex, KInBounds, List.map_cons, index1] at ih hK ⊢
            rw [ih js K hK.2.2]
    | vec xs =>
      cases J with
      | nil => simp [readSubs, reindex]
      | cons j js =>
        cases j with
        | scalar k =>
          simp only [readSubs, reindex, KInBounds, index1] at ih hK ⊢
          rw [ih js K hK]
        | slice m =>
          cases K with
          | nil => simp [readSubs, reindex, index1]
          | cons k K =>
            simp only [readSubs, reindex, KInBounds, List.map_cons, index1] at ih hK ⊢
            rw [ih js K hK.2.2, at1_range xs m k hK.1 hK.2.1]
        | vec ks =>
          cases K with
          | nil => simp [readSubs, reindex, index1]
          | cons k K =>
            simp only [readSubs, reindex, KInBounds, List.map_cons, index1] at ih hK ⊢
            rw [ih js K hK.2.2, at1_map xs ks k hK.1 hK.2.1]

end JuliaLean.BroadcastViews

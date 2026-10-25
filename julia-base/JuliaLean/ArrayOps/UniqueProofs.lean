import JuliaLean.ArrayOps.Unique

/-!
Proof of `UniqueSpec`: `unique`, `allunique` (including the sorted fast path) and
`allequal` on `Vector{Int}`.
-/

namespace JuliaLean.ArrayOps

open JuliaLean

/-! ### `unique` -/

private theorem unique_fold : ∀ (l acc seen : List Int), (∀ x, x ∈ seen ↔ x ∈ acc) →
    l.foldl (fun acc x => if x ∈ acc then acc else acc ++ [x]) acc = acc ++ uniqueLoop seen l
  | [], acc, _, _ => by simp [uniqueLoop]
  | x :: rest, acc, seen, h => by
    by_cases hx : x ∈ acc
    · have hs : x ∈ seen := (h x).2 hx
      simp only [List.foldl_cons, hx, hs, ↓reduceIte, uniqueLoop]
      exact unique_fold rest acc seen h
    · have hs : x ∉ seen := fun h' => hx ((h x).1 h')
      simp only [List.foldl_cons, hx, hs, ↓reduceIte, uniqueLoop]
      rw [unique_fold rest (acc ++ [x]) (x :: seen) (by intro y; simp [h y, or_comm])]
      simp

private theorem uniqueLoop_sub : ∀ (seen l : List Int), ∀ y ∈ uniqueLoop seen l, y ∈ l
  | _, [] => by simp [uniqueLoop]
  | seen, x :: rest => by
    intro y hy
    unfold uniqueLoop at hy
    split at hy
    · exact List.mem_cons_of_mem _ (uniqueLoop_sub seen rest y hy)
    · rcases List.mem_cons.1 hy with rfl | hy
      · simp
      · exact List.mem_cons_of_mem _ (uniqueLoop_sub _ rest y hy)

private theorem map_wrap_val : ∀ L : List Int, (∀ y ∈ L, IntTy.i64.min ≤ y ∧ y ≤ IntTy.i64.max) →
    (L.map (JInt.wrap .i64)).map (·.val) = L
  | [], _ => rfl
  | y :: L, h => by
    simp only [List.map_cons]
    rw [map_wrap_val L (fun z hz => h z (by simp [hz]))]
    congr 1
    exact wrapInt_of_inRange .i64 y (h y (by simp))

/-! ### `allunique` -/

private theorem hashed_iff : ∀ (seen l : List Int),
    hashedLoop seen l = true ↔ l.Nodup ∧ ∀ x ∈ l, x ∉ seen
  | _, [] => by simp [hashedLoop]
  | seen, x :: rest => by
    by_cases hx : x ∈ seen
    · simp [hashedLoop, hx]
    · simp only [hashedLoop, hx, ↓reduceIte]
      rw [hashed_iff (x :: seen) rest]
      rw [List.nodup_cons]
      constructor
      · rintro ⟨hn, hr⟩
        refine ⟨⟨fun h => hr x h (by simp), hn⟩, fun y hy => ?_⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hx
        · exact fun h => hr y hy (List.mem_cons_of_mem _ h)
      · rintro ⟨⟨hxr, hn⟩, hr⟩
        refine ⟨hn, fun y hy h => ?_⟩
        rcases List.mem_cons.1 h with rfl | h
        · exact hxr hy
        · exact hr y (List.mem_cons_of_mem _ hy) h

private theorem hashed_nil (l : List Int) : hashedLoop [] l = true ↔ l.Nodup := by
  rw [hashed_iff]
  simp

private theorem indexed_iff : ∀ l : List Int, indexedAllunique l = true ↔ l.Nodup
  | [] => by simp [indexedAllunique]
  | a :: rest => by
    have h : rest.any (· == a) = true ↔ a ∈ rest := by simp
    by_cases ha : a ∈ rest
    · rw [indexedAllunique, if_pos (h.2 ha)]
      simp [List.nodup_cons, ha]
    · rw [indexedAllunique, if_neg (fun h' => ha (h.1 h')), indexed_iff rest, List.nodup_cons]
      simp [ha]

/-- The order the sorted scan follows: increasing or decreasing. -/
private def rel (incr : Bool) (x y : Int) : Prop := if incr then x < y else y < x

private theorem rel_ne {incr : Bool} {x y : Int} (h : rel incr x y) : x ≠ y := by
  cases incr <;> simp [rel] at h <;> omega

private theorem rel_trans {incr : Bool} {x y z : Int} (h1 : rel incr x y) (h2 : rel incr y z) :
    rel incr x z := by
  cases incr <;> simp [rel] at h1 h2 ⊢ <;> omega

private theorem scan_iff (whole : List Int) (incr : Bool) :
    ∀ (l pre : List Int) (p : Int), (pre ++ [p]).Pairwise (rel incr) → whole = pre ++ p :: l →
      (sortedScan whole incr p l = true ↔ whole.Nodup)
  | [], pre, p, hP, hw => by
    rw [sortedScan, hw]
    exact ⟨fun _ => hP.imp rel_ne, fun _ => rfl⟩
  | a :: rest, pre, p, hP, hw => by
    rw [sortedScan]
    by_cases hr : rel incr p a
    · have hc : (if incr then decide (p < a) else decide (a < p)) = true := by
        cases incr <;> simpa [rel] using hr
      rw [if_pos hc]
      have hP' : (pre ++ [p] ++ [a]).Pairwise (rel incr) := by
        rw [List.pairwise_append]
        refine ⟨hP, by simp, ?_⟩
        intro x hx y hy
        rw [List.mem_singleton] at hy
        subst hy
        rcases List.mem_append.1 hx with hx | hx
        · exact rel_trans ((List.pairwise_append.1 hP).2.2 x hx p (by simp)) hr
        · rw [List.mem_singleton] at hx
          subst hx
          exact hr
      exact scan_iff whole incr rest (pre ++ [p]) a hP' (by rw [hw]; simp)
    · have hc : ¬ (if incr then decide (p < a) else decide (a < p)) = true := by
        cases incr <;> simpa [rel] using hr
      rw [if_neg hc]
      by_cases he : p = a
      · rw [if_pos he]
        refine ⟨fun h => absurd h (by simp), fun hn => ?_⟩
        rw [hw, he] at hn
        simp [List.nodup_append, List.nodup_cons] at hn
      · rw [if_neg he]
        exact hashed_nil whole

private theorem allunique_iff (v : List JInt64) : allunique v = true ↔ (v.map (·.val)).Nodup := by
  unfold allunique
  dsimp only
  generalize v.map (·.val) = w
  by_cases h32 : w.length < 32
  · rw [if_pos h32]
    by_cases h2 : w.length < 2
    · rw [if_pos h2]
      match w, h2 with
      | [], _ => simp
      | [a], _ => simp
      | _ :: _ :: _, h => simp only [List.length_cons] at h; omega
    · rw [if_neg h2]
      exact indexed_iff w
  · rw [if_neg h32]
    match w, h32 with
    | [], h => simp at h
    | [a], h => simp at h
    | a1 :: a2 :: rest, _ =>
      dsimp only
      by_cases he : a1 = a2
      · subst he
        simp
      · rw [if_pos (show a1 ≠ a2 from he)]
        have hr : rel (decide (a1 < a2)) a1 a2 := by
          by_cases hl : a1 < a2
          · simp [rel, hl]
          · simp [rel, hl]
            omega
        have hP : ([a1] ++ [a2]).Pairwise (rel (decide (a1 < a2))) := by simp [hr]
        exact scan_iff (a1 :: a2 :: rest) (decide (a1 < a2)) rest [a1] a2 hP rfl

/-! ### `allequal` -/

private theorem allequal_iff (v : List JInt64) :
    allequal v = true ↔ ∀ x ∈ v, ∀ y ∈ v, x.val = y.val := by
  unfold allequal
  match v with
  | [] => simp
  | [a] => simp
  | a :: b :: rest =>
    rw [if_neg (show ¬ (a :: b :: rest).length ≤ 1 by simp)]
    simp only [List.all_eq_true, beq_iff_eq]
    constructor
    · intro h x hx y hy
      have key : ∀ z ∈ a :: b :: rest, z.val = a.val := by
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · rfl
        · exact h z hz
      rw [key x hx, key y hy]
    · intro h x hx
      exact h x (List.mem_cons_of_mem _ hx) a (by simp)

theorem uniqueSpec : UniqueSpec := by
  intro v
  refine ⟨?_, allunique_iff v, allequal_iff v⟩
  unfold unique
  rw [map_wrap_val _ ?_, unique_fold _ [] [] (fun _ => Iff.rfl), List.nil_append]
  intro y hy
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 (uniqueLoop_sub [] _ y hy)
  exact x.property

end JuliaLean.ArrayOps

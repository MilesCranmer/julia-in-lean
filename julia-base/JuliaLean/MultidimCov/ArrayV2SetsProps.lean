import JuliaLean.MultidimCov.ArrayV2Sets

/-!
Properties of the set-like operators on vectors (`ArrayV2Sets.lean`), from the docstrings in
`base/abstractset.jl`: results keep each element once, at its first appearance, in the
order of the first argument (then of the later arguments for `union!`/`symdiff!`).
-/

namespace JuliaLean.MultidimCov.ArrayV2

variable {α : Type} [DecidableEq α]

/-- The elements of a list not in `seen`, each once, at its first appearance. -/
def uniqAfter (seen : List α) : List α → List α
  | [] => []
  | x :: xs => if x ∈ seen then uniqAfter seen xs else x :: uniqAfter (seen ++ [x]) xs

/-- The distinct elements of a list in order of first appearance (`unique`). -/
def stableUnique (xs : List α) : List α := uniqAfter [] xs

theorem mem_uniqAfter : ∀ (s xs : List α) (y : α), y ∈ uniqAfter s xs → y ∉ s ∧ y ∈ xs
  | _, [], _, h => by simp [uniqAfter] at h
  | s, x :: xs, y, h => by
    unfold uniqAfter at h
    split at h
    · have := mem_uniqAfter s xs y h; exact ⟨this.1, List.mem_cons_of_mem _ this.2⟩
    · rename_i hx
      rcases List.mem_cons.mp h with h | h
      · subst h; exact ⟨hx, List.mem_cons_self⟩
      · have := mem_uniqAfter (s ++ [x]) xs y h
        exact ⟨fun hs => this.1 (List.mem_append_left _ hs), List.mem_cons_of_mem _ this.2⟩

theorem mem_append_uniqAfter : ∀ (s xs : List α) (y : α), y ∈ s ++ uniqAfter s xs ↔ y ∈ s ∨ y ∈ xs
  | s, [], y => by simp [uniqAfter]
  | s, x :: xs, y => by
    unfold uniqAfter
    split
    · rename_i hx
      rw [mem_append_uniqAfter s xs y]
      simp only [List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · subst h; exact Or.inl hx
        · exact Or.inr h
    · rw [show s ++ x :: uniqAfter (s ++ [x]) xs = (s ++ [x]) ++ uniqAfter (s ++ [x]) xs by simp,
        mem_append_uniqAfter (s ++ [x]) xs y]
      simp [or_assoc]

theorem nodup_append_uniqAfter : ∀ (s xs : List α), s.Nodup → (s ++ uniqAfter s xs).Nodup
  | s, [], h => by simpa [uniqAfter] using h
  | s, x :: xs, h => by
    unfold uniqAfter
    split
    · exact nodup_append_uniqAfter s xs h
    · rename_i hx
      rw [show s ++ x :: uniqAfter (s ++ [x]) xs = (s ++ [x]) ++ uniqAfter (s ++ [x]) xs by simp]
      apply nodup_append_uniqAfter
      rw [List.nodup_append]
      refine ⟨h, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
      intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hx ha

theorem setUnion_eq : ∀ (s itr : List α), setUnion s itr = s ++ uniqAfter s itr
  | s, [] => by simp [setUnion, uniqAfter]
  | s, x :: xs => by
    unfold setUnion uniqAfter
    rw [List.foldl_cons]
    unfold setPush
    split
    · exact setUnion_eq s xs
    · rw [show s ++ x :: uniqAfter (s ++ [x]) xs = (s ++ [x]) ++ uniqAfter (s ++ [x]) xs by simp]
      exact setUnion_eq (s ++ [x]) xs

theorem mkSet_eq (itr : List α) : mkSet itr = uniqAfter [] itr := by
  simp [mkSet, setUnion_eq]

theorem mkSet_nodup (itr : List α) : (mkSet itr).Nodup := by
  have := nodup_append_uniqAfter [] itr List.nodup_nil
  rw [mkSet_eq]; simpa using this

theorem mem_mkSet (itr : List α) (y : α) : y ∈ mkSet itr ↔ y ∈ itr := by
  have := mem_append_uniqAfter [] itr y
  rw [mkSet_eq]; simpa using this

theorem filterSt_append (p : α → List α → Bool × List α) :
    ∀ (xs ys s : List α), filterSt p (xs ++ ys) s =
      ((filterSt p xs s).1 ++ (filterSt p ys (filterSt p xs s).2).1, (filterSt p ys (filterSt p xs s).2).2)
  | [], ys, s => by simp [filterSt]
  | x :: xs, ys, s => by
    simp only [List.cons_append, filterSt]
    rw [filterSt_append p xs ys]
    split <;> simp

theorem mapfilterPush_eq (p : α → List α → Bool × List α) :
    ∀ (xs : List α) (st : List α × List α),
      mapfilterPush p xs st = (st.1 ++ (filterSt p xs st.2).1, (filterSt p xs st.2).2)
  | [], st => by simp [mapfilterPush, filterSt]
  | x :: xs, (v, s) => by
    simp only [mapfilterPush, filterSt]
    rw [mapfilterPush_eq p xs]
    split <;> simp

theorem m3177_eq (p : α → List α → Bool × List α) :
    ∀ (itrs : List (List α)) (v s : List α), m3177 p v s itrs = filterSt p (v ++ itrs.flatten) s
  | [], v, s => by simp [m3177]
  | itr :: rest, v, s => by
    have h : mapfilterPush p itr (filterSt p v s) = filterSt p (v ++ itr) s := by
      rw [mapfilterPush_eq, filterSt_append]
    unfold m3177
    rw [List.foldl_cons, h]
    have := m3177_eq p rest (v ++ itr) s
    unfold m3177 at this
    rw [this, List.flatten_cons, List.append_assoc]

/-- `_grow_filter!(seen)` keeps the first occurrence of each element not in `seen`. -/
theorem filterSt_grow : ∀ (xs s : List α), filterSt m3174 xs s = (uniqAfter s xs, s ++ uniqAfter s xs)
  | [], s => by simp [filterSt, uniqAfter]
  | x :: xs, s => by
    simp only [filterSt, uniqAfter]
    by_cases hx : x ∈ s
    · have hp : m3174 x s = (false, s) := by simp [m3174, m3164, hx]
      rw [hp]; simp only [hx, if_true, Bool.false_eq_true, if_false]
      exact filterSt_grow xs s
    · have hp : m3174 x s = (true, s ++ [x]) := by simp [m3174, m3164, setPush, hx]
      rw [hp]; simp only [hx, if_true, if_false]
      rw [filterSt_grow xs (s ++ [x])]
      simp

/-- `_shrink_filter!(keep)` for a duplicate-free `keep` keeps the first occurrence of each
element of `keep`. -/
theorem filterSt_shrink : ∀ (xs k seen : List α), k.Nodup → (∀ y ∈ seen, y ∉ k) →
    (filterSt m3175 xs k).1 = (uniqAfter seen xs).filter fun x => decide (x ∈ k)
  | [], _, _, _, _ => by simp [filterSt, uniqAfter]
  | x :: xs, k, seen, hk, hs => by
    simp only [filterSt, uniqAfter]
    by_cases hxs : x ∈ seen
    · have hxk : x ∉ k := hs x hxs
      have hp : m3175 x k = (false, k) := by simp [m3175, m3164, hxk]
      rw [hp]; simp only [hxs, Bool.false_eq_true, if_false, if_true]
      exact filterSt_shrink xs k seen hk hs
    · simp only [hxs, if_false]
      by_cases hxk : x ∈ k
      · have hp : m3175 x k = (true, k.erase x) := by simp [m3175, m3164, setPop, hxk]
        rw [hp]; simp only [if_true]
        rw [List.filter_cons, if_pos (by simp [hxk])]
        congr 1
        rw [filterSt_shrink xs (k.erase x) (seen ++ [x]) (hk.erase x) ?_]
        · apply List.filter_congr
          intro y hy
          have := (mem_uniqAfter _ _ _ hy).1
          have hne : y ≠ x := fun e => this (by simp [e])
          simp [List.mem_erase_of_ne hne]
        · intro y hy
          rcases List.mem_append.mp hy with hy | hy
          · exact fun h => hs y hy (List.erase_sublist.subset h)
          · simp at hy; subst hy; rw [hk.mem_erase_iff]; simp
      · have hp : m3175 x k = (false, k) := by simp [m3175, m3164, hxk]
        rw [hp]; simp only [Bool.false_eq_true, if_false]
        rw [List.filter_cons, if_neg (by simp [hxk])]
        apply filterSt_shrink xs k (seen ++ [x]) hk
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hs y hy
        · simp at hy; subst hy; exact hxk

theorem setIntersectAll_spec : ∀ (itrs : List (List α)) (s : List α), s.Nodup →
    (setIntersectAll s itrs).Nodup ∧ ∀ y, y ∈ setIntersectAll s itrs ↔ y ∈ s ∧ ∀ i ∈ itrs, y ∈ i
  | [], s, h => by simp [setIntersectAll, h]
  | itr :: rest, s, h => by
    unfold setIntersectAll
    rw [List.foldl_cons]
    have hn : (s.filter fun x => decide (x ∈ mkSet itr)).Nodup := h.sublist List.filter_sublist
    obtain ⟨h1, h2⟩ := setIntersectAll_spec rest _ hn
    unfold setIntersectAll at h1 h2
    refine ⟨h1, fun y => ?_⟩
    rw [h2]; simp [mem_mkSet, and_assoc]

theorem foldl_delete_spec : ∀ (itr s : List α), s.Nodup →
    (itr.foldl setDelete s).Nodup ∧ ∀ y, y ∈ itr.foldl setDelete s ↔ y ∈ s ∧ y ∉ itr
  | [], s, h => by simp [h]
  | x :: xs, s, h => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_delete_spec xs (setDelete s x) (h.erase x)
    refine ⟨h1, fun y => ?_⟩
    rw [h2, setDelete, h.mem_erase_iff]
    simp only [List.mem_cons, not_or]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨b, a, c⟩
    · rintro ⟨b, a, c⟩; exact ⟨⟨a, b⟩, c⟩

theorem setDiffAll_spec : ∀ (itrs : List (List α)) (s : List α), s.Nodup →
    (setDiffAll s itrs).Nodup ∧ ∀ y, y ∈ setDiffAll s itrs ↔ y ∈ s ∧ ∀ i ∈ itrs, y ∉ i
  | [], s, h => by simp [setDiffAll, h]
  | itr :: rest, s, h => by
    unfold setDiffAll
    rw [List.foldl_cons]
    obtain ⟨n1, m1⟩ := foldl_delete_spec itr s h
    obtain ⟨h1, h2⟩ := setDiffAll_spec rest _ n1
    unfold setDiffAll at h1 h2
    refine ⟨h1, fun y => ?_⟩
    rw [h2, m1]; simp [and_assoc]

theorem foldl_toggle_spec : ∀ (S s : List α), S.Nodup → s.Nodup →
    (S.foldl setToggle s).Nodup ∧ ∀ y, y ∈ S.foldl setToggle s ↔ (y ∈ s ↔ y ∉ S)
  | [], s, _, h => by simp [h]
  | x :: xs, s, hS, h => by
    rw [List.foldl_cons]
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hS
    have hn : (setToggle s x).Nodup := by
      unfold setToggle setDelete setPush
      by_cases hm : x ∈ s
      · simp only [hm, if_true]; exact h.erase x
      · simp only [hm, if_false]
        rw [List.nodup_append]
        refine ⟨h, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
        intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact hm ha
    obtain ⟨h1, h2⟩ := foldl_toggle_spec xs _ hxs hn
    refine ⟨h1, fun y => ?_⟩
    rw [h2]
    have hm : y ∈ setToggle s x ↔ (y = x ↔ y ∉ s) := by
      unfold setToggle setDelete setPush
      by_cases hxm : x ∈ s
      · simp only [hxm, if_true, h.mem_erase_iff]
        by_cases e : y = x
        · subst e; simp [hxm]
        · simp [e]
      · simp only [hxm, if_false, List.mem_append, List.mem_singleton]
        by_cases e : y = x
        · subst e; simp [hxm]
        · simp [e]
    rw [hm]
    by_cases e : y = x
    · subst e; simp [hx]
    · simp [e]

theorem setSymdiffAll_spec : ∀ (itrs : List (List α)) (s : List α), s.Nodup → ∀ y,
    y ∈ setSymdiffAll s itrs ↔ ((if y ∈ s then 1 else 0) + itrs.countP (fun i => decide (y ∈ i))) % 2 = 1
  | [], s, h, y => by
    simp only [setSymdiffAll, List.foldl_nil, List.countP_nil, Nat.add_zero]
    by_cases hy : y ∈ s <;> simp [hy]
  | itr :: rest, s, h, y => by
    unfold setSymdiffAll
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_toggle_spec (mkSet itr) s (mkSet_nodup itr) h
    have := setSymdiffAll_spec rest _ h1 y
    unfold setSymdiffAll at this
    rw [this, List.countP_cons]
    have h2y := h2 y
    rw [mem_mkSet] at h2y
    by_cases hs : y ∈ s <;> by_cases hi : y ∈ itr <;> by_cases hr : y ∈ (mkSet itr).foldl setToggle s <;>
      simp_all <;> omega

/-- `union!(v, itrs...)` (docstrings `base/abstractset.jl:62-84`, `union` at 13-54): `v` becomes the
distinct elements of all the arguments, in order of first appearance. -/
def P3185 : Prop := ∀ {α : Type} [DecidableEq α] (v : List α) (itrs : List (List α)),
    m3185 v itrs = stableUnique (v ++ itrs.flatten)

theorem p3185 : P3185 := by
  intro α _ v itrs
  unfold m3185
  rw [m3177_eq, filterSt_grow]
  rfl

/-- `symdiff!(v, itrs...)` (docstrings `base/abstractset.jl:258-289`): `v` becomes the elements
lying in an odd number of the arguments (each taken as a set), each once, in order of first
appearance across `v, itrs...`. -/
def P3188 : Prop := ∀ {α : Type} [DecidableEq α] (v : List α) (itrs : List (List α)),
    m3188 v itrs = (stableUnique (v ++ itrs.flatten)).filter
      fun x => decide ((v :: itrs).countP (fun i => decide (x ∈ i)) % 2 = 1)

theorem p3188 : P3188 := by
  intro α _ v itrs
  unfold m3188
  rw [m3177_eq]
  have hk : (setSymdiffAll [] (v :: itrs)).Nodup := by
    have : ∀ (args : List (List α)) (s : List α), s.Nodup → (setSymdiffAll s args).Nodup := by
      intro args
      induction args with
      | nil => intro s h; simpa [setSymdiffAll] using h
      | cons a rest ih =>
        intro s h
        unfold setSymdiffAll; rw [List.foldl_cons]
        exact ih _ (foldl_toggle_spec (mkSet a) s (mkSet_nodup a) h).1
    exact this _ [] List.nodup_nil
  rw [filterSt_shrink _ _ [] hk (by simp)]
  unfold stableUnique
  apply List.filter_congr
  intro y _
  have := setSymdiffAll_spec (v :: itrs) [] List.nodup_nil y
  simp only [List.not_mem_nil, if_false, Nat.zero_add] at this
  simp [this]

theorem m3191_eq (shrinker : List α → List (List α) → List α) (v : List α) (itrs : List (List α)) :
    m3191 shrinker v itrs = (stableUnique v).filter fun x => decide (x ∈ shrinker (stableUnique v) itrs) := by
  unfold m3191
  rw [filterSt_grow]
  rfl

/-- `intersect!(v, itrs...)` (docstring `base/abstractset.jl:184-191`): `v` becomes the distinct
elements of `v` that occur in every `itr`, in `v`'s order. -/
def P3198 : Prop := ∀ {α : Type} [DecidableEq α] (v : List α) (itrs : List (List α)),
    m3198 v itrs = (stableUnique v).filter fun x => itrs.all fun i => decide (x ∈ i)

theorem stableUnique_nodup (v : List α) : (stableUnique v).Nodup := by
  have := nodup_append_uniqAfter [] v List.nodup_nil
  simpa [stableUnique] using this

theorem p3198 : P3198 := by
  intro α _ v itrs
  unfold m3198
  rw [m3191_eq]
  apply List.filter_congr
  intro y hy
  have := (setIntersectAll_spec itrs _ (stableUnique_nodup v)).2 y
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq, this]; simp [hy]

/-- `setdiff!(v, itrs...)` (docstring `base/abstractset.jl:225-243`): `v` becomes the distinct
elements of `v` that occur in no `itr`, in `v`'s order. -/
def P3199 : Prop := ∀ {α : Type} [DecidableEq α] (v : List α) (itrs : List (List α)),
    m3199 v itrs = (stableUnique v).filter fun x => itrs.all fun i => decide (x ∉ i)

theorem p3199 : P3199 := by
  intro α _ v itrs
  unfold m3199
  rw [m3191_eq]
  apply List.filter_congr
  intro y hy
  have := (setDiffAll_spec itrs _ (stableUnique_nodup v)).2 y
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq, this]; simp [hy]

/-- `intersect(itr, itrs...)` for a vector or tuple `itr` (docstring `base/abstractset.jl:114-154`):
the elements occurring in all arguments, each once, in the order they first appear in `itr`. -/
def P3203 : Prop := ∀ {α : Type} [DecidableEq α] (itr : List α) (itrs : List (List α)),
    m3203 itr itrs = (stableUnique itr).filter fun x => itrs.all fun i => decide (x ∈ i)

theorem p3203 : P3203 := by
  intro α _ itr itrs
  obtain ⟨hn, hm⟩ := setIntersectAll_spec itrs (mkSet itr) (mkSet_nodup itr)
  unfold m3203 m3201
  rw [filterSt_shrink _ _ [] hn (by simp)]
  apply List.filter_congr
  intro y hy
  have hyi := (mem_uniqAfter _ _ _ hy).2
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq, hm, mem_mkSet]; simp [hyi]

/-- `setdiff(itr, itrs...)` (docstring `base/abstractset.jl:202-221`): the elements of `itr` in
none of the `itrs`, each once, in `itr`'s order. -/
def P3209 : Prop := ∀ {α : Type} [DecidableEq α] (itr : List α) (itrs : List (List α)),
    m3209 itr itrs = (stableUnique itr).filter fun x => itrs.all fun i => decide (x ∉ i)

theorem p3209 : P3209 := by
  intro α _ itr itrs
  obtain ⟨hn, hm⟩ := setDiffAll_spec itrs (mkSet itr) (mkSet_nodup itr)
  unfold m3209 m3201
  rw [filterSt_shrink _ _ [] hn (by simp)]
  apply List.filter_congr
  intro y hy
  have hyi := (mem_uniqAfter _ _ _ hy).2
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_eq, hm, mem_mkSet]; simp [hyi]

/-- `intersect(v::AbstractVector, r::AbstractRange)` (docstring `base/abstractset.jl:114-154`):
the distinct elements of `v` that lie in `r`, in `v`'s order. -/
def P3215v : Prop := ∀ {α : Type} [DecidableEq α] (v r : List α),
    m3215 v r = stableUnique (v.filter fun x => decide (x ∈ r))

theorem p3215v : P3215v := by
  intro α _ v r
  unfold m3215 m3201 stableUnique
  rw [filterSt_shrink _ _ [] (mkSet_nodup _) (by simp), List.filter_eq_self]
  intro y hy
  have := (mem_uniqAfter _ _ _ hy).2
  simp [mem_mkSet, this]

/-- `intersect(s, itrs...)` (docstring base/abstractset.jl:115-121): "The first argument
controls what kind of container is returned. If this is an array, it maintains the order
in which elements first appear": both mixed methods agree with intersecting the collected
range, i.e. the distinct elements of the first argument that occur in the second, in the
first argument's order. -/
def P3215 : Prop := ∀ r v : List Int,
    m3215 v r = stableUnique (v.filter fun x => decide (x ∈ r)) ∧
      m3221 r v = stableUnique (r.filter fun x => decide (x ∈ v))

/-- `intersect(1:3, [3, 2, 1]) == [3, 2, 1]`, not `[1, 2, 3]`. -/
theorem p3215_refuted : ¬ P3215 := by
  intro h
  have h1 := (h [1, 2, 3] [3, 2, 1]).2
  have e1 : m3221 ([1, 2, 3] : List Int) [3, 2, 1] = [3, 2, 1] := by decide
  have e2 : stableUnique (([1, 2, 3] : List Int).filter fun x => decide (x ∈ ([3, 2, 1] : List Int))) = [1, 2, 3] := by
    decide
  rw [e1, e2] at h1
  simp at h1

end JuliaLean.MultidimCov.ArrayV2

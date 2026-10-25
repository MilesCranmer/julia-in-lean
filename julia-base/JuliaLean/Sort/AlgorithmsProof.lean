import JuliaLean.Sort.Partial

/-! Correctness of the comparison sorting kernels of `Sort/Algorithms.lean`:
under a strict weak order, `insertionSort`, `scratchQuickSort` (with no
`lo`/`hi` target) and `sortGeneric` all return exactly the stable reference
sort `sortRef`. -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace JuliaLean.Sort

open JuliaLean

/-- `lt` is a strict weak order: irreflexive, transitive, and `¬lt` is
transitive (`lt a b = false → lt b c = false → lt a c = false`). -/
structure StrictWeakOrder {α : Type} (lt : α → α → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true
  ntrans : ∀ a b c, lt a b = false → lt b c = false → lt a c = false

/-- `InsertionSort` on the whole vector is the stable reference sort. -/
def InsertionSortCorrect : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool), StrictWeakOrder lt →
    ∀ v : Array α, (insertionSort lt v 1 v.size).toList = sortRef lt v.toList

/-- `ScratchQuickSort` without a target is the stable reference sort
(docstring, sort.jl:1065-1067), for every pivot rule choosing inside `lo:hi`. -/
def ScratchQuickSortCorrect : Prop :=
  ∀ (α : Type) [Inhabited α] (piv : Int → Int → Int) (lt : α → α → Bool),
    (∀ lo hi : Int, lo ≤ hi → lo ≤ piv lo hi ∧ piv lo hi ≤ hi) → StrictWeakOrder lt →
    ∀ v : Array α, (scratchQuickSort piv lt ⟨none, none⟩ v 1 v.size).toList = sortRef lt v.toList

/-- The default `sort!` for orderings that are not `UIntMappable` is stable:
it returns the stable reference sort. -/
def SortGenericStable : Prop :=
  ∀ (α : Type) [Inhabited α] (piv : Int → Int → Int) (lt : α → α → Bool),
    (∀ lo hi : Int, lo ≤ hi → lo ≤ piv lo hi ∧ piv lo hi ≤ hi) → StrictWeakOrder lt →
    ∀ v : Array α, (sortGeneric piv lt v).toList = sortRef lt v.toList

section
variable {α : Type} [Inhabited α] {lt : α → α → Bool}

/-! ### Order facts -/

theorem StrictWeakOrder.asymm (h : StrictWeakOrder lt) {a b : α} (hab : lt a b = true) :
    lt b a = false := by
  cases hba : lt b a
  · rfl
  · have := h.trans _ _ _ hab hba
    rw [h.irrefl] at this
    cases this

theorem StrictWeakOrder.lt_of_lt_of_nlt (h : StrictWeakOrder lt) {a b c : α}
    (hab : lt a b = true) (hcb : lt c b = false) : lt a c = true := by
  cases hac : lt a c
  · have := h.ntrans _ _ _ hac hcb
    rw [hab] at this
    cases this
  · rfl

theorem StrictWeakOrder.lt_of_nlt_of_lt (h : StrictWeakOrder lt) {a b c : α}
    (hba : lt b a = false) (hbc : lt b c = true) : lt a c = true := by
  cases hac : lt a c
  · have := h.ntrans _ _ _ hba hac
    rw [hbc] at this
    cases this
  · rfl

/-! ### One-based array access on list decompositions -/

theorem rd_eq {v : Array α} {n : Nat} {x : α} (hx : v.toList[n]? = some x) {i : Int}
    (hi : i = n + 1) : rd v i = x := by
  unfold rd
  rw [if_pos (by omega), Array.getD_eq_getD_getElem?, ← Array.getElem?_toList]
  have : (i - 1).toNat = n := by omega
  rw [this, hx, Option.getD_some]

theorem rd_mid {v : Array α} {P B : List α} {z : α} (hv : v.toList = P ++ z :: B) {i : Int}
    (hi : i = P.length + 1) : rd v i = z :=
  rd_eq (by rw [hv, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero]) hi

theorem rd_seg {v : Array α} {Ps E R : List α} (hv : v.toList = Ps ++ E ++ R) {b : Int}
    (hb : b = Ps.length + 1) (k : Nat) (hk : k < E.length) : rd v (b + k) = E[k] :=
  rd_eq (n := Ps.length + k)
    (by rw [hv, List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hk, List.getElem?_eq_getElem hk]) (by omega)

theorem wr_toList {v : Array α} {n : Nat} {i : Int} (hi : i = n + 1) (x : α) :
    (wr v i x).toList = v.toList.set n x := by
  unfold wr
  rw [if_pos (by omega), Array.toList_modify, List.modify_eq_set]
  have : (i - 1).toNat = n := by omega
  rw [this]

theorem wr_mid {v : Array α} {P B : List α} {z : α} (hv : v.toList = P ++ z :: B) {i : Int}
    (hi : i = P.length + 1) (x : α) : (wr v i x).toList = P ++ x :: B := by
  rw [wr_toList hi, hv, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self,
    List.set_cons_zero]

theorem exists_concat (l : List α) (k : Nat) (hl : l.length = k + 1) :
    ∃ l' b, l = l' ++ [b] ∧ l'.length = k := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', b, rfl⟩
  · simp at hl
  · refine ⟨l', b, by simp, ?_⟩
    simp at hl
    omega

theorem split_at (l : List α) (n : Nat) (h : n < l.length) :
    ∃ l1 x l2, l = l1 ++ x :: l2 ∧ l1.length = n :=
  ⟨l.take n, l[n], l.drop (n + 1),
    by rw [← List.drop_eq_getElem_cons h, List.take_append_drop],
    by simp only [List.length_take]; omega⟩

/-- Linear arithmetic over list lengths. -/
macro "lomega" : tactic =>
  `(tactic| ((try dsimp only at *); (try simp only [List.length_append, List.length_cons,
      List.length_nil, List.length_reverse, List.length_singleton, Array.length_toList] at *); omega))

/-! ### The reference sort -/

/-- Sorted for `lt`: no later element is less than an earlier one. -/
abbrev Sorted (lt : α → α → Bool) (l : List α) : Prop := l.Pairwise (fun a b => lt b a = false)

/-- `sortRef` started from an accumulator. -/
def insAll (lt : α → α → Bool) (S l : List α) : List α :=
  l.foldl (fun acc x => insertStable lt x acc) S

theorem insAll_cons (S : List α) (x : α) (l : List α) :
    insAll lt S (x :: l) = insAll lt (insertStable lt x S) l := rfl

theorem insAll_append (S l l' : List α) : insAll lt S (l ++ l') = insAll lt (insAll lt S l) l' :=
  List.foldl_append

theorem sortRef_eq (l : List α) : sortRef lt l = insAll lt [] l := rfl

theorem sortRef_concat (l : List α) (x : α) :
    sortRef lt (l ++ [x]) = insertStable lt x (sortRef lt l) := by
  rw [sortRef_eq, insAll_append]
  rfl

theorem mem_insertStable {x e : α} : ∀ {l : List α}, e ∈ insertStable lt x l ↔ e = x ∨ e ∈ l
  | [] => by simp [insertStable]
  | y :: ys => by
    simp only [insertStable]
    split
    · simp
    · rw [List.mem_cons, mem_insertStable, List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem length_insertStable (x : α) : ∀ l : List α, (insertStable lt x l).length = l.length + 1
  | [] => rfl
  | y :: ys => by
    simp only [insertStable]
    split
    · simp
    · simp [length_insertStable x ys]

theorem mem_insAll {e : α} : ∀ (l S : List α), e ∈ insAll lt S l ↔ e ∈ S ∨ e ∈ l
  | [], S => by simp [insAll]
  | x :: l, S => by
    rw [insAll_cons, mem_insAll l, mem_insertStable, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

theorem mem_sortRef {e : α} (l : List α) : e ∈ sortRef lt l ↔ e ∈ l := by
  rw [sortRef_eq, mem_insAll]
  simp

theorem length_insAll : ∀ (l S : List α), (insAll lt S l).length = S.length + l.length
  | [], S => by simp [insAll]
  | x :: l, S => by
    rw [insAll_cons, length_insAll l, length_insertStable]
    simp only [List.length_cons]
    omega

theorem length_sortRef (l : List α) : (sortRef lt l).length = l.length := by
  rw [sortRef_eq, length_insAll]
  simp

theorem sorted_insertStable (h : StrictWeakOrder lt) (x : α) :
    ∀ {l : List α}, Sorted lt l → Sorted lt (insertStable lt x l)
  | [], _ => by simp [insertStable]
  | y :: ys, hs => by
    have hs' := List.pairwise_cons.1 hs
    simp only [insertStable]
    split
    · rename_i hxy
      refine List.Pairwise.cons ?_ hs
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact h.asymm hxy
      · cases hax : lt a x
        · rfl
        · have := h.trans _ _ _ hax hxy
          rw [hs'.1 a ha] at this
          cases this
    · rename_i hxy
      refine List.Pairwise.cons ?_ (sorted_insertStable h x hs'.2)
      intro a ha
      rcases (mem_insertStable).1 ha with rfl | ha
      · simpa using hxy
      · exact hs'.1 a ha

theorem sorted_insAll (h : StrictWeakOrder lt) : ∀ (l S : List α), Sorted lt S → Sorted lt (insAll lt S l)
  | [], _, hS => hS
  | x :: l, S, hS => by
    rw [insAll_cons]
    exact sorted_insAll h l _ (sorted_insertStable h x hS)

theorem sorted_sortRef (h : StrictWeakOrder lt) (l : List α) : Sorted lt (sortRef lt l) :=
  sorted_insAll h l [] List.Pairwise.nil

theorem ins_of_ge (x : α) : ∀ (S : List α), (∀ y ∈ S, lt x y = false) →
    insertStable lt x S = S ++ [x]
  | [], _ => rfl
  | y :: ys, hS => by
    simp [insertStable, hS y (by simp), ins_of_ge x ys (fun z hz => hS z (by simp [hz]))]

theorem ins_lt_all (x : α) (S : List α) (hS : ∀ s ∈ S, lt x s = true) :
    insertStable lt x S = x :: S := by
  cases S with
  | nil => rfl
  | cons y ys => simp [insertStable, hS y (by simp)]

theorem ins_append_left (b : α) : ∀ (C S : List α), (∀ c ∈ C, lt b c = false) →
    insertStable lt b (C ++ S) = C ++ insertStable lt b S
  | [], _, _ => rfl
  | c :: C, S, hC => by
    show insertStable lt b (c :: (C ++ S)) = c :: (C ++ insertStable lt b S)
    simp only [insertStable, hC c (by simp), Bool.false_eq_true, ite_false]
    rw [ins_append_left b C S (fun c' hc' => hC c' (by simp [hc']))]

/-- Insertion step of the inner loop, scanning from the back of a sorted prefix. -/
theorem insertStable_concat (h : StrictWeakOrder lt) (x y : α) : ∀ (A : List α),
    Sorted lt (A ++ [y]) →
    insertStable lt x (A ++ [y]) = if lt x y then insertStable lt x A ++ [y] else A ++ [y, x]
  | [], _ => by cases hxy : lt x y <;> simp [insertStable, hxy]
  | z :: A, hs => by
    have hs' : Sorted lt (z :: (A ++ [y])) := hs
    have hs'' := List.pairwise_cons.1 hs'
    have hyz : lt y z = false := hs''.1 y (by simp)
    have ih := insertStable_concat h x y A hs''.2
    cases hxz : lt x z
    · cases hxy : lt x y <;> simp [insertStable, hxz, hxy, ih]
    · have hxy : lt x y = true := h.lt_of_lt_of_nlt hxz hyz
      simp [insertStable, hxz, hxy]

/-! ### `InsertionSort` -/

theorem insertLoop_spec (h : StrictWeakOrder lt) (lo : Int) (x : α) :
    ∀ (m : Nat) (v : Array α) (j : Int) (P A B : List α) (z : α),
      v.toList = P ++ A ++ z :: B → (P.length : Int) + 1 = lo → j = lo + m → A.length = m →
      Sorted lt A → (insertLoop lt lo x m v j).toList = P ++ insertStable lt x A ++ B
  | 0, v, j, P, A, B, z, hv, hP, hj, hA, _ => by
    have hA0 : A = [] := List.eq_nil_of_length_eq_zero hA
    subst hA0
    rw [insertLoop, wr_mid (v := v) (i := j) (P := P) (B := B) (z := z) (by simpa using hv)
      (by omega)]
    simp [insertStable]
  | m + 1, v, j, P, A, B, z, hv, hP, hj, hA, hs => by
    obtain ⟨A', y, rfl, hA'⟩ := exists_concat A m hA
    have hs' : Sorted lt A' := (List.pairwise_append.1 hs).1
    have hy : rd v (j - 1) = y :=
      rd_mid (P := P ++ A') (B := z :: B) (by rw [hv]; simp) (by lomega)
    rw [insertLoop]
    simp only [hy]
    rw [insertStable_concat h x y A' hs]
    cases hxy : lt x y
    · simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, eq_self_iff_true, ite_true,
        ite_false, ↓reduceIte]
      rw [wr_mid (v := v) (i := j) (P := P ++ A' ++ [y]) (B := B) (z := z) (by rw [hv]; simp)
        (by lomega)]
      simp
    · simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, eq_self_iff_true, ite_true,
        ite_false, ↓reduceIte]
      rw [insertLoop_spec h lo x m (wr v j y) (j - 1) P A' (y :: B) y
        (by rw [wr_mid (v := v) (i := j) (P := P ++ A' ++ [y]) (B := B) (z := z)
          (by rw [hv]; simp) (by lomega)]; simp)
        hP (by omega) hA' hs']
      simp

theorem insSortFold (h : StrictWeakOrder lt) (g : Array α → Nat → Array α) (lo : Int)
    (hg : ∀ w (k : Nat), g w k =
      insertLoop lt lo (rd w (lo + 1 + k)) ((lo + 1 + k) - lo).toNat w (lo + 1 + k))
    (v : Array α) (P Q : List α) (hP : (P.length : Int) + 1 = lo) :
    ∀ (k : Nat) (L R : List α), v.toList = P ++ (L ++ R) ++ Q → L.length = k + 1 →
      ((List.range k).foldl g v).toList = P ++ sortRef lt L ++ R ++ Q
  | 0, L, R, hv, hL => by
    obtain ⟨L', a, rfl, hL'⟩ := exists_concat L 0 hL
    have := List.eq_nil_of_length_eq_zero hL'
    subst this
    rw [List.range_zero, List.foldl_nil, hv]
    simp [sortRef, insertStable]
  | k + 1, L, R, hv, hL => by
    obtain ⟨L', a, rfl, hL'⟩ := exists_concat L (k + 1) hL
    have hw := insSortFold h g lo hg v P Q hP k L' (a :: R) (by rw [hv]; simp) hL'
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hg]
    have hx : rd ((List.range k).foldl g v) (lo + 1 + k) = a :=
      rd_mid (P := P ++ sortRef lt L') (B := R ++ Q) (by rw [hw]; simp)
        (by simp only [List.length_append, length_sortRef]; omega)
    rw [hx, show ((lo + 1 + (k : Int)) - lo).toNat = k + 1 by omega,
      insertLoop_spec h lo a (k + 1) ((List.range k).foldl g v) (lo + 1 + k) P (sortRef lt L')
        (R ++ Q) a
        (by rw [hw]; simp) hP (by omega) (by rw [length_sortRef]; exact hL')
        (sorted_sortRef h L'), sortRef_concat]
    simp

theorem insertionSort_spec (h : StrictWeakOrder lt) (v : Array α) (lo hi : Int) (P M Q : List α)
    (hv : v.toList = P ++ M ++ Q) (hP : (P.length : Int) + 1 = lo)
    (hM : (M.length : Int) = hi - lo + 1) :
    (insertionSort lt v lo hi).toList = P ++ sortRef lt M ++ Q := by
  unfold insertionSort
  cases hn : M.length with
  | zero =>
    have hM0 : M = [] := List.eq_nil_of_length_eq_zero hn
    subst hM0
    rw [show (hi - lo).toNat = 0 by omega, List.range_zero, List.foldl_nil, hv]
    simp [sortRef]
  | succ n =>
    rw [show (hi - lo).toNat = n by omega]
    exact (insSortFold h _ lo (fun w k => rfl) v P Q hP n M [] (by rw [hv]; simp) hn).trans
      (by simp)

theorem insertionSortCorrect : InsertionSortCorrect := by
  intro α _ lt h v
  have := insertionSort_spec h v 1 v.size [] v.toList [] (by simp) (by simp) (by simp)
  simpa using this

/-! ### Stable rearrangements of the input of `sortRef` -/

theorem ins_comm (h : StrictWeakOrder lt) {a b : α} (hab : lt a b = true) :
    ∀ S : List α, insertStable lt a (insertStable lt b S) = insertStable lt b (insertStable lt a S)
  | [] => by simp [insertStable, hab, h.asymm hab]
  | y :: ys => by
    have ih := ins_comm h hab ys
    have hba := h.asymm hab
    cases hay : lt a y <;> cases hby : lt b y
    · simp [insertStable, hay, hby, ih]
    · have := h.trans _ _ _ hab hby
      rw [hay] at this
      cases this
    · simp [insertStable, hay, hby, hab, hba]
    · simp [insertStable, hay, hby, hab, hba]

theorem bubble (h : StrictWeakOrder lt) (x : α) : ∀ (A S R : List α), (∀ e ∈ A, lt e x = true) →
    insAll lt (insertStable lt x S) (A ++ R) = insAll lt S (A ++ x :: R)
  | [], _, _, _ => rfl
  | a :: A, S, R, hA => by
    show insAll lt (insertStable lt a (insertStable lt x S)) (A ++ R) =
      insAll lt (insertStable lt a S) (A ++ x :: R)
    rw [ins_comm h (hA a (by simp))]
    exact bubble h x A (insertStable lt a S) R (fun e he => hA e (by simp [he]))

theorem block_swap (h : StrictWeakOrder lt) : ∀ (B A S R : List α),
    (∀ b ∈ B, ∀ a ∈ A, lt a b = true) → insAll lt S (B ++ A ++ R) = insAll lt S (A ++ B ++ R)
  | [], _, _, _, _ => by simp
  | x :: B, A, S, R, hBA => by
    show insAll lt (insertStable lt x S) (B ++ A ++ R) = insAll lt S (A ++ (x :: B) ++ R)
    rw [block_swap h B A (insertStable lt x S) R (fun b hb a ha => hBA b (by simp [hb]) a ha),
      List.append_assoc A B R, bubble h x A S (B ++ R) (fun e he => hBA x (by simp) e he)]
    simp

theorem filter_split (h : StrictWeakOrder lt) (g : α → Bool)
    (hg : ∀ a b, g b = false → g a = true → lt a b = true) :
    ∀ (X S : List α), insAll lt S X = insAll lt S (X.filter g ++ X.filter (fun e => !g e))
  | [], _ => by simp
  | x :: X, S => by
    cases hx : g x
    · simp only [List.filter_cons, hx, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        eq_self_iff_true, ite_true, ite_false, ↓reduceIte]
      rw [insAll_cons, filter_split h g hg X,
        bubble h x (X.filter g) S (X.filter (fun e => !g e))
          (fun e he => hg e x hx (List.mem_filter.1 he).2)]
    · simp only [List.filter_cons, hx, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        eq_self_iff_true, ite_true, ite_false, ↓reduceIte]
      rw [insAll_cons, filter_split h g hg X]
      rfl

theorem split_sorted : ∀ (C S B : List α), (∀ c ∈ C, ∀ b ∈ B, lt b c = false) →
    insAll lt (C ++ S) B = C ++ insAll lt S B
  | _, _, [], _ => rfl
  | C, S, b :: B, hCB => by
    rw [insAll_cons, insAll_cons, ins_append_left b C S (fun c hc => hCB c hc b (by simp))]
    exact split_sorted C _ B (fun c hc b' hb' => hCB c hc b' (by simp [hb']))

theorem sortRef_append (A B : List α) (hAB : ∀ a ∈ A, ∀ b ∈ B, lt b a = false) :
    sortRef lt (A ++ B) = sortRef lt A ++ sortRef lt B := by
  rw [sortRef_eq, insAll_append, sortRef_eq A, sortRef_eq B]
  have := split_sorted (insAll lt [] A) [] B
    (fun c hc b hb => hAB c ((mem_sortRef (lt := lt) A).1 (by rw [sortRef_eq]; exact hc)) b hb)
  simpa using this

/-- Stable partition around a pivot (the `rev = false` case of `partition!`). -/
theorem sortRef_part_core (h : StrictWeakOrder lt) (pv : α) (B A BL BH AL AH : List α)
    (sB : ∀ S, insAll lt S B = insAll lt S (BL ++ BH))
    (sA : ∀ S, insAll lt S A = insAll lt S (AL ++ AH))
    (hBL : ∀ x ∈ BL, lt pv x = false) (hBH : ∀ x ∈ BH, lt pv x = true)
    (hAL : ∀ x ∈ AL, lt x pv = true) (hAH : ∀ x ∈ AH, lt x pv = false) :
    sortRef lt (B ++ pv :: A) = sortRef lt (BL ++ AL) ++ pv :: sortRef lt (BH ++ AH) := by
  have e1 : sortRef lt (B ++ pv :: A) = sortRef lt (BL ++ (BH ++ (pv :: AL) ++ AH)) := by
    simp only [sortRef_eq]
    rw [insAll_append [] B, sB, ← insAll_append,
      show BL ++ BH ++ pv :: A = (BL ++ BH ++ [pv]) ++ A by simp,
      insAll_append [] _ A, sA, ← insAll_append]
    simp
  have e2 : sortRef lt (BL ++ (BH ++ (pv :: AL) ++ AH)) =
      sortRef lt (BL ++ (AL ++ pv :: (BH ++ AH))) := by
    simp only [sortRef_eq]
    rw [insAll_append [] BL, insAll_append [] BL,
      block_swap h BH (pv :: AL) _ AH (fun b hb a ha => by
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hBH b hb
        · exact h.trans _ _ _ (hAL a ha) (hBH b hb))]
    simp only [List.cons_append, List.append_assoc, insAll_cons]
    exact bubble h pv AL _ (BH ++ AH) hAL
  have hlo : ∀ a ∈ BL ++ AL ++ [pv], lt pv a = false := by
    intro a ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · exact hBL a ha
    · exact h.asymm (hAL a ha)
    · exact h.irrefl _
  have hhi : ∀ b ∈ BH ++ AH, lt b pv = false := by
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact h.asymm (hBH b hb)
    · exact hAH b hb
  rw [e1, e2, show BL ++ (AL ++ pv :: (BH ++ AH)) = (BL ++ AL ++ [pv]) ++ (BH ++ AH) by simp,
    sortRef_append _ _ (fun a ha b hb => h.ntrans _ _ _ (hhi b hb) (hlo a ha)),
    sortRef_concat, ins_of_ge pv (sortRef lt (BL ++ AL)) (fun y hy =>
      hlo y (List.mem_append.2 (Or.inl ((mem_sortRef _).1 hy))))]
  simp

/-! ### `partition!` -/

/-- Does an element before (resp. after) the pivot go to the `hi` end? -/
def fBef (lt : α → α → Bool) (rev : Bool) (pv : α) : α → Bool :=
  fun x => if rev then !(lt x pv) else lt pv x

def fAft (lt : α → α → Bool) (rev : Bool) (pv : α) : α → Bool :=
  fun x => if rev then lt pv x else !(lt x pv)

/-- Elements written to the low end of the destination, in source order. -/
def loPart (lt : α → α → Bool) (rev : Bool) (pv : α) (B A : List α) : List α :=
  B.filter (fun x => !fBef lt rev pv x) ++ A.filter (fun x => !fAft lt rev pv x)

/-- Elements written (reversed) to the high end of the destination, in source order. -/
def hiPart (lt : α → α → Bool) (rev : Bool) (pv : α) (B A : List α) : List α :=
  B.filter (fBef lt rev pv) ++ A.filter (fAft lt rev pv)

/-- The source order read through the `rev` flag. -/
def orient (rev : Bool) (l : List α) : List α := if rev then l.reverse else l

theorem fBef_false (pv : α) : fBef lt false pv = fun x => lt pv x := rfl
theorem fBef_true (pv : α) : fBef lt true pv = fun x => !(lt x pv) := rfl
theorem fAft_false (pv : α) : fAft lt false pv = fun x => !(lt x pv) := rfl
theorem fAft_true (pv : α) : fAft lt true pv = fun x => lt pv x := rfl

theorem length_orient (rev : Bool) (l : List α) : (orient rev l).length = l.length := by
  cases rev <;> simp [orient]

theorem length_filter_not (f : α → Bool) : ∀ l : List α,
    (l.filter f).length + (l.filter (fun x => !f x)).length = l.length
  | [] => rfl
  | x :: l => by
    have ih := length_filter_not f l
    cases hx : f x <;>
      simp only [List.filter_cons, hx, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        eq_self_iff_true, ite_true, ite_false, ↓reduceIte, List.length_cons] <;> omega

theorem length_lo_hi (lt : α → α → Bool) (rev : Bool) (pv : α) (B A : List α) :
    (loPart lt rev pv B A).length + (hiPart lt rev pv B A).length = B.length + A.length := by
  have h1 := length_filter_not (fBef lt rev pv) B
  have h2 := length_filter_not (fAft lt rev pv) A
  simp only [loPart, hiPart, List.length_append]
  omega

theorem sortRef_partition (h : StrictWeakOrder lt) (rev : Bool) (pv : α) (B A : List α) :
    sortRef lt (orient rev (B ++ pv :: A)) =
      sortRef lt (orient rev (loPart lt rev pv B A)) ++
        pv :: sortRef lt (orient (!rev) (hiPart lt rev pv B A).reverse) := by
  have core := fun (B A : List α) => sortRef_part_core h pv B A
    (B.filter (fun x => !lt pv x)) (B.filter (fun x => lt pv x))
    (A.filter (fun x => lt x pv)) (A.filter (fun x => !lt x pv))
    (fun S => by
      have := filter_split h (fun x => !lt pv x) (fun a b hb ha => h.lt_of_nlt_of_lt (b := pv)
        (by simpa using ha) (by simpa using hb)) B S
      simpa using this)
    (fun S => filter_split h (fun x => lt x pv) (fun a b hb ha => h.lt_of_lt_of_nlt ha hb) A S)
    (fun x hx => by simpa using (List.mem_filter.1 hx).2)
    (fun x hx => (List.mem_filter.1 hx).2)
    (fun x hx => (List.mem_filter.1 hx).2)
    (fun x hx => by simpa using (List.mem_filter.1 hx).2)
  cases rev
  · have e1 : orient false (loPart lt false pv B A) =
        B.filter (fun x => !lt pv x) ++ A.filter (fun x => lt x pv) := by
      simp [orient, loPart, fBef_false, fBef_true, fAft_false, fAft_true]
    have e2 : orient (!false) (hiPart lt false pv B A).reverse =
        B.filter (fun x => lt pv x) ++ A.filter (fun x => !lt x pv) := by
      simp [orient, hiPart, fBef_false, fBef_true, fAft_false, fAft_true]
    rw [e1, e2, show orient false (B ++ pv :: A) = B ++ pv :: A from rfl]
    exact core B A
  · have e0 : orient true (B ++ pv :: A) = A.reverse ++ pv :: B.reverse := by simp [orient]
    have e1 : orient true (loPart lt true pv B A) =
        A.reverse.filter (fun x => !lt pv x) ++ B.reverse.filter (fun x => lt x pv) := by
      simp [orient, loPart, fBef_false, fBef_true, fAft_false, fAft_true]
    have e2 : orient (!true) (hiPart lt true pv B A).reverse =
        A.reverse.filter (fun x => lt pv x) ++ B.reverse.filter (fun x => !lt x pv) := by
      simp [orient, hiPart, fBef_false, fBef_true, fAft_false, fAft_true]
    rw [e0, e1, e2]
    exact core A.reverse B.reverse

/-- The two scanning loops of `partition!`, sort.jl:1095-1108. -/
def pfold (f : α → Bool) (elt : Nat → α) (c hi : Int) (m : Nat) (init : Array α × Int) :
    Array α × Int :=
  (List.range m).foldl (fun (st : Array α × Int) (k : Nat) =>
    (wr st.1 ((if f (elt k) then hi else c + k) - st.2) (elt k),
      st.2 + (if f (elt k) then 1 else 0))) init

theorem pfold_succ (f : α → Bool) (elt : Nat → α) (c hi : Int) (m : Nat) (init : Array α × Int) :
    pfold f elt c hi (m + 1) init =
      (wr (pfold f elt c hi m init).1
          ((if f (elt m) then hi else c + m) - (pfold f elt c hi m init).2) (elt m),
        (pfold f elt c hi m init).2 + (if f (elt m) then 1 else 0)) := by
  unfold pfold
  rw [List.range_succ, List.foldl_append]
  rfl

theorem pfold_spec (f : α → Bool) (elt : Nat → α) (c hi : Int) :
    ∀ (m : Nat) (E : List α) (init : Array α × Int) (P Lo G Hi Q : List α),
      E.length = m → (∀ k (hk : k < E.length), elt k = E[k]) →
      init.1.toList = P ++ Lo ++ G ++ Hi.reverse ++ Q →
      c - init.2 = (P.length : Int) + 1 + Lo.length →
      hi - init.2 = (P.length : Int) + Lo.length + G.length →
      m ≤ G.length →
      (pfold f elt c hi m init).2 = init.2 + (E.filter f).length ∧
      ∃ G', G'.length + m = G.length ∧
        (pfold f elt c hi m init).1.toList =
          P ++ (Lo ++ E.filter (fun x => !f x)) ++ G' ++ (Hi ++ E.filter f).reverse ++ Q
  | 0, E, init, P, Lo, G, Hi, Q, hE, _, hd, _, _, _ => by
    have : E = [] := List.eq_nil_of_length_eq_zero hE
    subst this
    refine ⟨by simp [pfold], G, by simp, ?_⟩
    rw [show pfold f elt c hi 0 init = init from rfl, hd]
    simp
  | m + 1, E, init, P, Lo, G, Hi, Q, hE, helt, hd, hc, hh, hm => by
    obtain ⟨E', e, rfl, hE'⟩ := exists_concat E m hE
    have helt' : ∀ k (hk : k < E'.length), elt k = E'[k] := fun k hk => by
      rw [helt k (by lomega), List.getElem_append_left hk]
    have he : elt m = e := by
      rw [helt m (by lomega)]
      subst hE'
      simp
    obtain ⟨ho, G', hG', hd'⟩ :=
      pfold_spec f elt c hi m E' init P Lo G Hi Q hE' helt' hd hc hh (by omega)
    have hfl := length_filter_not f E'
    rw [pfold_succ, he]
    generalize pfold f elt c hi m init = st at ho hd' ⊢
    cases hfe : f e
    · obtain ⟨g, G'', rfl⟩ : ∃ g G'', G' = g :: G'' := by
        cases G' with
        | nil => simp at hG'; omega
        | cons g G'' => exact ⟨g, G'', rfl⟩
      simp only [Bool.false_eq_true, eq_self_iff_true, ite_true, ite_false, ↓reduceIte]
      refine ⟨by rw [ho]; simp [hfe, List.filter_cons] <;> omega, G'', by lomega, ?_⟩
      rw [wr_mid (v := st.1) (i := c + m - st.2) (P := P ++ (Lo ++ E'.filter (fun x => !f x)))
        (B := G'' ++ (Hi ++ E'.filter f).reverse ++ Q) (z := g) (by rw [hd']; simp)
        (by rw [ho]; lomega)]
      simp [hfe, List.filter_cons]
    · obtain ⟨G'', g, rfl, hG''⟩ := exists_concat G' (G'.length - 1) (by omega)
      simp only [Bool.false_eq_true, eq_self_iff_true, ite_true, ite_false, ↓reduceIte]
      refine ⟨by rw [ho]; simp [hfe, List.filter_cons] <;> omega, G'', by lomega, ?_⟩
      rw [wr_mid (v := st.1) (i := hi - st.2) (P := P ++ (Lo ++ E'.filter (fun x => !f x)) ++ G'')
        (B := (Hi ++ E'.filter f).reverse ++ Q) (z := g) (by rw [hd']; simp)
        (by rw [ho]; lomega)]
      simp [hfe, List.filter_cons]

/-- The state after both scanning loops of `partition!`. -/
def partR1 (piv : Int → Int → Int) (lt : α → α → Bool) (src dst : Array α) (lo hi off : Int)
    (rev : Bool) : Array α × Int :=
  pfold (fBef lt rev (rd src (piv lo hi))) (fun k => rd src (lo + k)) lo hi
    (piv lo hi - lo).toNat (dst, off)

def partR2 (piv : Int → Int → Int) (lt : α → α → Bool) (src dst : Array α) (lo hi off : Int)
    (rev : Bool) : Array α × Int :=
  pfold (fAft lt rev (rd src (piv lo hi))) (fun k => rd src (piv lo hi + k + 1)) (piv lo hi) hi
    (hi - piv lo hi).toNat (partR1 piv lt src dst lo hi off rev)

theorem partition_eq (piv : Int → Int → Int) (lt : α → α → Bool) (src dst : Array α)
    (lo hi off : Int) (rev pts : Bool) (pio : Int) :
    partition piv lt src dst lo hi off rev pts pio =
      (if pts then wr src (hi - (partR2 piv lt src dst lo hi off rev).2 + pio) (rd src (piv lo hi))
        else src,
       if pts then (partR2 piv lt src dst lo hi off rev).1
        else wr (partR2 piv lt src dst lo hi off rev).1
          (hi - (partR2 piv lt src dst lo hi off rev).2 + pio) (rd src (piv lo hi)),
       hi - (partR2 piv lt src dst lo hi off rev).2 + pio) := by
  cases pts <;> rfl

theorem partition_spec (piv : Int → Int → Int) (src dst : Array α)
    (lo hi off pio : Int) (rev pts : Bool) (Ps D Qs Pd Y Qd : List α)
    (hs : src.toList = Ps ++ D ++ Qs) (hd : dst.toList = Pd ++ Y ++ Qd)
    (hPs : (Ps.length : Int) + 1 = lo) (hPd : (Pd.length : Int) + 1 = lo - off)
    (hD : (D.length : Int) = hi - lo + 1) (hY : Y.length = D.length)
    (hp : lo ≤ piv lo hi ∧ piv lo hi ≤ hi) :
    ∃ (B A : List α) (pv g : α) (dA : Array α) (j : Int),
      D = B ++ pv :: A ∧
      dA.toList = Pd ++ loPart lt rev pv B A ++ g :: (hiPart lt rev pv B A).reverse ++ Qd ∧
      j = hi - off - (hiPart lt rev pv B A).length + pio ∧
      partition piv lt src dst lo hi off rev pts pio =
        (if pts then wr src j pv else src, if pts then dA else wr dA j pv, j) := by
  obtain ⟨B, pv, A, hBA, hBl⟩ := split_at D (piv lo hi - lo).toNat (by omega)
  have hDl : D.length = B.length + 1 + A.length := by rw [hBA]; lomega
  have hAl : A.length = (hi - piv lo hi).toNat := by omega
  have hpv : rd src (piv lo hi) = pv :=
    rd_mid (P := Ps ++ B) (B := A ++ Qs) (by rw [hs, hBA]; simp) (by lomega)
  have e1 : partR1 piv lt src dst lo hi off rev =
      pfold (fBef lt rev pv) (fun k => rd src (lo + k)) lo hi (piv lo hi - lo).toNat (dst, off) := by
    unfold partR1
    rw [hpv]
  have e2 : partR2 piv lt src dst lo hi off rev =
      pfold (fAft lt rev pv) (fun k => rd src (piv lo hi + k + 1)) (piv lo hi) hi
        (hi - piv lo hi).toNat (partR1 piv lt src dst lo hi off rev) := by
    unfold partR2
    rw [hpv]
  have h1 := pfold_spec (fBef lt rev pv) (fun k => rd src (lo + k)) lo hi (piv lo hi - lo).toNat
    B (dst, off) Pd [] Y [] Qd hBl
    (fun k hk => rd_seg (Ps := Ps) (R := pv :: A ++ Qs) (by rw [hs, hBA]; simp) hPs.symm k hk)
    (by simp [hd]) (by lomega) (by lomega) (by omega)
  rw [← e1] at h1
  obtain ⟨h1o, G1, hG1, h1d⟩ := h1
  have hfl1 := length_filter_not (fBef lt rev pv) B
  have h2 := pfold_spec (fAft lt rev pv) (fun k => rd src (piv lo hi + k + 1)) (piv lo hi) hi
    (hi - piv lo hi).toNat A (partR1 piv lt src dst lo hi off rev) Pd
    ([] ++ B.filter (fun x => !fBef lt rev pv x)) G1 ([] ++ B.filter (fBef lt rev pv)) Qd hAl
    (fun k hk => by
      have := rd_seg (Ps := Ps ++ B ++ [pv]) (E := A) (R := Qs) (b := piv lo hi + 1)
        (by rw [hs, hBA]; simp) (by lomega) k hk
      show rd src (piv lo hi + k + 1) = A[k]
      rw [show piv lo hi + (k : Int) + 1 = piv lo hi + 1 + k by omega]
      exact this)
    h1d (by rw [h1o]; lomega) (by rw [h1o]; lomega) (by omega)
  rw [← e2] at h2
  obtain ⟨h2o, G2, hG2, h2d⟩ := h2
  obtain ⟨G0, g, rfl, hG0⟩ := exists_concat G2 0 (by omega)
  have : G0 = [] := List.eq_nil_of_length_eq_zero hG0
  subst this
  rw [partition_eq, hpv]
  refine ⟨B, A, pv, g, _, _, hBA, ?_, ?_, rfl⟩
  · rw [h2d]
    simp [loPart, hiPart]
  · have hfl2 := length_filter_not (fAft lt rev pv) A
    rw [h2o, h1o]
    simp only [hiPart, List.length_append, List.nil_append]
    lomega

/-! ### `ScratchQuickSort` -/

/-- Correctness of `scratchQuickSortLoop` with fuel `fuel` on the range `lo:hi`,
whose data is `X` in `v` (or `Y` in `t` when `swap`), read through `rev`. -/
def QSSpec (piv : Int → Int → Int) (lt : α → α → Bool) (fuel : Nat) : Prop :=
  ∀ (v t : Array α) (lo hi offset : Int) (swap rev : Bool) (P X Q P' Y Q' : List α),
    v.toList = P ++ X ++ Q → t.toList = P' ++ Y ++ Q' →
    (P.length : Int) + 1 = lo → (P'.length : Int) + 1 = lo + offset →
    Y.length = X.length → (X.length : Int) = hi - lo + 1 → X.length < fuel →
    (scratchQuickSortLoop piv lt ⟨none, none⟩ fuel v t lo hi offset swap rev).1.toList =
        P ++ sortRef lt (orient rev (if swap then Y else X)) ++ Q ∧
      ∃ Y', (scratchQuickSortLoop piv lt ⟨none, none⟩ fuel v t lo hi offset swap rev).2.toList =
        P' ++ Y' ++ Q' ∧ Y'.length = Y.length

theorem len_sel (sw : Bool) {B1 A1 : List α} (h1 : B1.length = A1.length) :
    (if sw then B1 else A1).length = A1.length := by
  cases sw <;> simp [h1]

theorem qs_lower_first {piv : Int → Int → Int} {f : Nat} (ih : QSSpec piv lt f)
    (v t : Array α) (lo hi j offset : Int) (sw rev : Bool) (P A1 A2 Q P' B1 B2 Q' : List α)
    (pv g : α) (hv : v.toList = P ++ A1 ++ pv :: A2 ++ Q) (ht : t.toList = P' ++ B1 ++ g :: B2 ++ Q')
    (hP : (P.length : Int) + 1 = lo) (hP' : (P'.length : Int) + 1 = lo + offset)
    (h1 : B1.length = A1.length) (h2 : B2.length = A2.length)
    (hj : j = lo + A1.length) (hhi : hi = j + A2.length) (hf1 : A1.length < f)
    (hf2 : A2.length < f) :
    (scratchQuickSortLoop piv lt ⟨none, none⟩ f
        (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t lo (j - 1) offset sw rev).1
        (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t lo (j - 1) offset sw rev).2
        (j + 1) hi offset sw (!rev)).1.toList =
      P ++ sortRef lt (orient rev (if sw then B1 else A1)) ++
        pv :: sortRef lt (orient (!rev) (if sw then B2 else A2)) ++ Q ∧
    ∃ Y', (scratchQuickSortLoop piv lt ⟨none, none⟩ f
        (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t lo (j - 1) offset sw rev).1
        (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t lo (j - 1) offset sw rev).2
        (j + 1) hi offset sw (!rev)).2.toList = P' ++ Y' ++ Q' ∧
      Y'.length = B1.length + 1 + B2.length := by
  have hl := len_sel sw h1
  obtain ⟨l1, Y1, l2, l3⟩ := ih v t lo (j - 1) offset sw rev P A1 (pv :: A2 ++ Q) P' B1
    (g :: B2 ++ Q') (by rw [hv]; simp) (by rw [ht]; simp) hP hP' h1 (by omega) hf1
  obtain ⟨u1, Y2, u2, u3⟩ := ih
    (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t lo (j - 1) offset sw rev).1
    (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t lo (j - 1) offset sw rev).2
    (j + 1) hi offset sw (!rev) (P ++ sortRef lt (orient rev (if sw then B1 else A1)) ++ [pv]) A2 Q
    (P' ++ Y1 ++ [g]) B2 Q' (by rw [l1]; simp) (by rw [l2]; simp)
    (by simp only [List.length_append, length_sortRef, length_orient, hl]; lomega)
    (by lomega) h2 (by omega) hf2
  refine ⟨u1.trans (by simp), Y1 ++ g :: Y2, u2.trans (by simp), ?_⟩
  simp only [List.length_append, List.length_cons]
  omega

theorem qs_upper_first {piv : Int → Int → Int} {f : Nat} (ih : QSSpec piv lt f)
    (v t : Array α) (lo hi j offset : Int) (sw rev : Bool) (P A1 A2 Q P' B1 B2 Q' : List α)
    (pv g : α) (hv : v.toList = P ++ A1 ++ pv :: A2 ++ Q) (ht : t.toList = P' ++ B1 ++ g :: B2 ++ Q')
    (hP : (P.length : Int) + 1 = lo) (hP' : (P'.length : Int) + 1 = lo + offset)
    (h1 : B1.length = A1.length) (h2 : B2.length = A2.length)
    (hj : j = lo + A1.length) (hhi : hi = j + A2.length) (hf1 : A1.length < f)
    (hf2 : A2.length < f) :
    (scratchQuickSortLoop piv lt ⟨none, none⟩ f
        (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t (j + 1) hi offset sw (!rev)).1
        (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t (j + 1) hi offset sw (!rev)).2
        lo (j - 1) offset sw rev).1.toList =
      P ++ sortRef lt (orient rev (if sw then B1 else A1)) ++
        pv :: sortRef lt (orient (!rev) (if sw then B2 else A2)) ++ Q ∧
    ∃ Y', (scratchQuickSortLoop piv lt ⟨none, none⟩ f
        (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t (j + 1) hi offset sw (!rev)).1
        (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t (j + 1) hi offset sw (!rev)).2
        lo (j - 1) offset sw rev).2.toList = P' ++ Y' ++ Q' ∧
      Y'.length = B1.length + 1 + B2.length := by
  obtain ⟨u1, Y2, u2, u3⟩ := ih v t (j + 1) hi offset sw (!rev) (P ++ A1 ++ [pv]) A2 Q
    (P' ++ B1 ++ [g]) B2 Q' (by rw [hv]; simp) (by rw [ht]; simp) (by lomega) (by lomega) h2
    (by omega) hf2
  obtain ⟨l1, Y1, l2, l3⟩ := ih
    (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t (j + 1) hi offset sw (!rev)).1
    (scratchQuickSortLoop piv lt ⟨none, none⟩ f v t (j + 1) hi offset sw (!rev)).2
    lo (j - 1) offset sw rev P A1 (pv :: sortRef lt (orient (!rev) (if sw then B2 else A2)) ++ Q)
    P' B1 (g :: Y2 ++ Q') (by rw [u1]; simp) (by rw [u2]; simp) hP hP' h1 (by omega) hf1
  refine ⟨l1.trans (by simp), Y1 ++ g :: Y2, l2.trans (by simp), ?_⟩
  simp only [List.length_append, List.length_cons]
  omega

theorem copyTo_spec (dest src : Array α) (g : Array α → Nat → Array α) (d s : Int)
    (hg : ∀ w (k : Nat), g w k = wr w (d + k) (rd src (s + k)))
    (P X Q Ps Y Qs : List α)
    (hs : src.toList = Ps ++ Y ++ Qs) (hP : (P.length : Int) + 1 = d)
    (hPs : (Ps.length : Int) + 1 = s) :
    ∀ (k : Nat) (Y1 Y2 X1 X2 : List α), Y = Y1 ++ Y2 → X = X1 ++ X2 → Y1.length = k →
      X1.length = k → dest.toList = P ++ X ++ Q →
      ((List.range k).foldl g dest).toList = P ++ Y1 ++ X2 ++ Q
  | 0, Y1, Y2, X1, X2, _, hX, hY1, hX1, hd => by
    have := List.eq_nil_of_length_eq_zero hY1
    have := List.eq_nil_of_length_eq_zero hX1
    subst Y1 X1
    rw [List.range_zero, List.foldl_nil, hd, hX]
    simp
  | k + 1, Y1, Y2, X1, X2, hY, hX, hY1, hX1, hd => by
    obtain ⟨Y1', y, rfl, hY1'⟩ := exists_concat Y1 k hY1
    obtain ⟨X1', x, rfl, hX1'⟩ := exists_concat X1 k hX1
    have hw := copyTo_spec dest src g d s hg P X Q Ps Y Qs hs hP hPs k Y1' (y :: Y2) X1' (x :: X2)
      (by rw [hY]; simp) (by rw [hX]; simp) hY1' hX1' hd
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hg,
      rd_mid (v := src) (i := s + k) (P := Ps ++ Y1') (B := Y2 ++ Qs) (z := y)
        (by rw [hs, hY]; simp) (by lomega),
      wr_mid (v := (List.range k).foldl g dest) (i := d + k) (P := P ++ Y1') (B := X2 ++ Q) (z := x)
        (by rw [hw]; simp) (by lomega)]
    simp

theorem copyTo_eq (dest : Array α) (d : Int) (src : Array α) (s : Int) (P X Q Ps Y Qs : List α)
    (hd : dest.toList = P ++ X ++ Q) (hs : src.toList = Ps ++ Y ++ Qs)
    (hP : (P.length : Int) + 1 = d) (hPs : (Ps.length : Int) + 1 = s) (hXY : X.length = Y.length)
    (n : Int) (hn : n = Y.length) :
    (copyTo dest d src s n).toList = P ++ Y ++ Q := by
  unfold copyTo
  rw [show n.toNat = Y.length by omega]
  have := copyTo_spec dest src _ d s (fun w k => rfl) P X Q Ps Y Qs hs hP hPs
    Y.length Y [] X [] (by simp) (by simp) rfl hXY hd
  simpa using this

theorem reverse_short (M : List α) (h : M.length ≤ 1) : M.reverse = M := by
  match M, h with
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h =>
    simp only [List.length_cons] at h
    omega

theorem revFold (g : Array α → Nat → Array α) (lo hi : Int)
    (hg : ∀ w (k : Nat), g w k =
      wr (wr w (lo + k) (rd w (hi - k))) (hi - k) (rd w (lo + k)))
    (v : Array α) (P X Q : List α) (hv : v.toList = P ++ X ++ Q)
    (hP : (P.length : Int) + 1 = lo) (hX : (X.length : Int) = hi - lo + 1) :
    ∀ (k : Nat), 2 * k ≤ X.length → ∃ A M B, X = A ++ M ++ B ∧ A.length = k ∧ B.length = k ∧
      ((List.range k).foldl g v).toList = P ++ B.reverse ++ M ++ A.reverse ++ Q
  | 0, _ => ⟨[], X, [], by simp, rfl, rfl, by rw [List.range_zero, List.foldl_nil, hv]; simp⟩
  | k + 1, hk => by
    obtain ⟨A, M, B, hXe, hA, hB, hw⟩ := revFold g lo hi hg v P X Q hv hP hX k (by omega)
    have hM : M.length + 2 * k = X.length := by rw [hXe]; lomega
    obtain ⟨a, M1, rfl⟩ : ∃ a M1, M = a :: M1 := by
      cases M with
      | nil => simp at hM; omega
      | cons a M1 => exact ⟨a, M1, rfl⟩
    obtain ⟨M', b, rfl, hM'⟩ := exists_concat M1 (M1.length - 1) (by lomega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hg]
    generalize (List.range k).foldl g v = w at hw ⊢
    have ha : rd w (lo + k) = a :=
      rd_mid (P := P ++ B.reverse) (B := M' ++ b :: (A.reverse ++ Q)) (by rw [hw]; simp)
        (by lomega)
    have hb : rd w (hi - k) = b :=
      rd_mid (P := P ++ B.reverse ++ a :: M') (B := A.reverse ++ Q) (by rw [hw]; simp)
        (by lomega)
    rw [ha, hb]
    have hw1 : (wr w (lo + k) b).toList = (P ++ B.reverse) ++ b :: (M' ++ b :: (A.reverse ++ Q)) :=
      wr_mid (z := a) (by rw [hw]; simp) (by lomega) b
    refine ⟨A ++ [a], M', b :: B, by rw [hXe]; simp, by lomega, by lomega, ?_⟩
    rw [wr_mid (v := wr w (lo + k) b) (i := hi - k) (P := P ++ B.reverse ++ b :: M')
      (B := A.reverse ++ Q) (z := b) (by rw [hw1]; simp) (by lomega) a]
    simp

theorem reverseRange_spec (v : Array α) (lo hi : Int) (P X Q : List α)
    (hv : v.toList = P ++ X ++ Q) (hP : (P.length : Int) + 1 = lo)
    (hX : (X.length : Int) = hi - lo + 1) :
    (reverseRange v lo hi).toList = P ++ X.reverse ++ Q := by
  unfold reverseRange
  rw [show ((hi - lo + 1) / 2).toNat = X.length / 2 by omega]
  obtain ⟨A, M, B, hXe, hA, hB, hw⟩ :=
    revFold _ lo hi (fun w k => rfl) v P X Q hv hP hX (X.length / 2) (by omega)
  refine hw.trans ?_
  have hM : M.length ≤ 1 := by
    have := congrArg List.length hXe
    lomega
  rw [hXe]
  simp [reverse_short M hM]

theorem qs_spec (h : StrictWeakOrder lt) {piv : Int → Int → Int}
    (hpiv : ∀ lo hi : Int, lo ≤ hi → lo ≤ piv lo hi ∧ piv lo hi ≤ hi) :
    ∀ fuel, QSSpec piv lt fuel
  | 0 => by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf
    exact absurd hf (Nat.not_lt_zero _)
  | f + 1 => by
    intro v t lo hi offset swap rev P X Q P' Y Q' hv ht hP hP' hYX hX hf
    have ih := qs_spec h hpiv f
    rw [scratchQuickSortLoop]
    by_cases hbig : lo < hi ∧ hi - lo > smallThreshold
    · rw [if_pos hbig]
      cases swap
      · obtain ⟨B, A, pv, g, dA, j, hD, hdA, hj, hpart⟩ :=
          partition_spec (lt := lt) piv v t lo hi (-offset) (-offset) rev true P X Q P' Y Q'
            hv ht hP (by omega) hX hYX (hpiv lo hi (by omega))
        simp only [hpart, Bool.not_false, Bool.not_true, Bool.false_eq_true, eq_self_iff_true,
          ite_true, ite_false, ↓reduceIte, Option.isSome_none, false_and]
        have hlh := length_lo_hi lt rev pv B A
        have hXl : X.length = B.length + 1 + A.length := by rw [hD]; lomega
        obtain ⟨X1, x, X2, hX12, hX1⟩ := split_at X (loPart lt rev pv B A).length (by omega)
        have hX2 : X2.length = (hiPart lt rev pv B A).length := by
          have : X.length = X1.length + 1 + X2.length := by rw [hX12]; lomega
          omega
        have hv1 : (wr v j pv).toList = P ++ X1 ++ pv :: X2 ++ Q := by
          rw [wr_mid (v := v) (i := j) (P := P ++ X1) (B := X2 ++ Q) (z := x)
            (by rw [hv, hX12]; simp) (by lomega) pv]
          simp
        by_cases hc : j - lo < hi - j
        · rw [if_pos hc]
          obtain ⟨r1, Y', r2, r3⟩ := qs_lower_first ih (wr v j pv) dA lo hi j offset true rev
            P X1 X2 Q P' (loPart lt rev pv B A) (hiPart lt rev pv B A).reverse Q' pv g hv1 hdA
            hP hP' hX1.symm (by lomega) (by lomega) (by lomega) (by omega) (by omega)
          refine ⟨r1.trans ?_, Y', r2, ?_⟩
          · rw [hD, sortRef_partition h rev pv B A]
            simp
          · rw [r3]
            lomega
        · rw [if_neg hc]
          obtain ⟨r1, Y', r2, r3⟩ := qs_upper_first ih (wr v j pv) dA lo hi j offset true rev
            P X1 X2 Q P' (loPart lt rev pv B A) (hiPart lt rev pv B A).reverse Q' pv g hv1 hdA
            hP hP' hX1.symm (by lomega) (by lomega) (by lomega) (by omega) (by omega)
          refine ⟨r1.trans ?_, Y', r2, ?_⟩
          · rw [hD, sortRef_partition h rev pv B A]
            simp
          · rw [r3]
            lomega
      · obtain ⟨B, A, pv, g, dA, j, hD, hdA, hj, hpart⟩ :=
          partition_spec (lt := lt) piv t v (lo + offset) (hi + offset) offset 0 rev false P' Y Q'
            P X Q ht hv hP' (by omega) (by omega) hYX.symm
            (hpiv (lo + offset) (hi + offset) (by omega))
        simp only [hpart, Bool.not_false, Bool.not_true, Bool.false_eq_true, eq_self_iff_true,
          ite_true, ite_false, ↓reduceIte, Option.isSome_none, false_and]
        have hlh := length_lo_hi lt rev pv B A
        have hYl : Y.length = B.length + 1 + A.length := by rw [hD]; lomega
        obtain ⟨Y1, y, Y2, hY12, hY1⟩ := split_at Y (loPart lt rev pv B A).length (by omega)
        have hY2 : Y2.length = (hiPart lt rev pv B A).length := by
          have : Y.length = Y1.length + 1 + Y2.length := by rw [hY12]; lomega
          omega
        have hv1 : (wr dA j pv).toList =
            P ++ loPart lt rev pv B A ++ pv :: (hiPart lt rev pv B A).reverse ++ Q := by
          rw [wr_mid (v := dA) (i := j) (P := P ++ loPart lt rev pv B A)
            (B := (hiPart lt rev pv B A).reverse ++ Q) (z := g) (by rw [hdA]; simp) (by lomega) pv]
          simp
        have ht1 : t.toList = P' ++ Y1 ++ y :: Y2 ++ Q' := by rw [ht, hY12]; simp
        by_cases hc : j - lo < hi - j
        · rw [if_pos hc]
          obtain ⟨r1, Y', r2, r3⟩ := qs_lower_first ih (wr dA j pv) t lo hi j offset false rev
            P (loPart lt rev pv B A) (hiPart lt rev pv B A).reverse Q P' Y1 Y2 Q' pv y hv1 ht1
            hP hP' hY1 (by lomega) (by lomega) (by lomega) (by omega) (by lomega)
          refine ⟨r1.trans ?_, Y', r2, ?_⟩
          · rw [hD, sortRef_partition h rev pv B A]
            simp
          · rw [r3]
            omega
        · rw [if_neg hc]
          obtain ⟨r1, Y', r2, r3⟩ := qs_upper_first ih (wr dA j pv) t lo hi j offset false rev
            P (loPart lt rev pv B A) (hiPart lt rev pv B A).reverse Q P' Y1 Y2 Q' pv y hv1 ht1
            hP hP' hY1 (by lomega) (by lomega) (by lomega) (by omega) (by lomega)
          refine ⟨r1.trans ?_, Y', r2, ?_⟩
          · rw [hD, sortRef_partition h rev pv B A]
            simp
          · rw [r3]
            omega
    · rw [if_neg hbig]
      by_cases hlt : hi < lo
      · rw [if_pos hlt]
        have hX0 : X = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hY0 : Y = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hX0 hY0
        refine ⟨?_, [], ?_, rfl⟩
        · dsimp only
          rw [hv]
          cases swap <;> cases rev <;> rfl
        · dsimp only
          rw [ht]
      · rw [if_neg hlt]
        dsimp only
        refine ⟨?_, Y, ht, rfl⟩
        have hv1 : (if swap then copyTo v lo t (lo + offset) (hi - lo + 1) else v).toList =
            P ++ (if swap then Y else X) ++ Q := by
          cases swap
          · exact hv
          · exact copyTo_eq v lo t (lo + offset) P X Q P' Y Q' hv ht hP hP' hYX.symm _ (by omega)
        have hv2 : (if rev then reverseRange (if swap then copyTo v lo t (lo + offset) (hi - lo + 1)
              else v) lo hi
            else (if swap then copyTo v lo t (lo + offset) (hi - lo + 1) else v)).toList =
            P ++ orient rev (if swap then Y else X) ++ Q := by
          cases rev
          · exact hv1
          · exact reverseRange_spec _ lo hi P _ Q hv1 hP (by rw [len_sel swap hYX]; exact hX)
        exact insertionSort_spec h _ lo hi P _ Q hv2 hP
          (by rw [length_orient, len_sel swap hYX]; exact hX)

theorem scratchQuickSortCorrect : ScratchQuickSortCorrect := by
  intro α _ piv lt hpiv h v
  unfold scratchQuickSort
  have := (qs_spec h hpiv ((v.size : Int) - 1 + 2).toNat v
    (Array.replicate ((v.size : Int) - 1 + 1).toNat default) 1 v.size (1 - 1) false false
    [] v.toList [] [] (Array.replicate ((v.size : Int) - 1 + 1).toNat default).toList []
    (by simp) (by simp) (by simp) (by simp) (by simp <;> omega) (by simp) (by simp <;> omega)).1
  simpa [orient] using this

/-! ### `sort!` for orderings that are not `UIntMappable` -/

theorem pairwise_of_adj {R : α → α → Prop} (htr : ∀ a b c, R a b → R b c → R a c) :
    ∀ (l : List α), (∀ k (hk : k + 1 < l.length), R l[k] l[k + 1]) → l.Pairwise R
  | [], _ => List.Pairwise.nil
  | [_], _ => by simp
  | a :: b :: l, hadj => by
    have ih := pairwise_of_adj htr (b :: l) (fun k hk => by
      have := hadj (k + 1) (by lomega)
      simpa using this)
    refine List.Pairwise.cons ?_ ih
    intro c hc
    have hab : R a b := hadj 0 (by simp)
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact htr _ _ _ hab ((List.pairwise_cons.1 ih).1 c hc)

theorem adj_of_isSortedRange (lt' : α → α → Bool) (v : Array α)
    (hs : isSortedRange lt' v 1 v.size = true) :
    ∀ k (hk : k + 1 < v.toList.length), lt' v.toList[k + 1] v.toList[k] = false := by
  intro k hk
  unfold isSortedRange at hs
  have := List.all_eq_true.1 hs k (List.mem_range.2 (by lomega))
  try dsimp only at this
  rw [rd_eq (n := k + 1) (i := 1 + 1 + (k : Int)) (List.getElem?_eq_getElem hk) (by omega),
    rd_eq (n := k) (i := 1 + (k : Int)) (List.getElem?_eq_getElem (by omega)) (by omega)] at this
  simpa using this

theorem sorted_insAll_id : ∀ (l S : List α), Sorted lt (S ++ l) → insAll lt S l = S ++ l
  | [], S, _ => by simp [insAll]
  | x :: l, S, hs => by
    have hx : ∀ y ∈ S, lt x y = false := fun y hy => (List.pairwise_append.1 hs).2.2 y hy x (by simp)
    rw [insAll_cons, ins_of_ge x S hx, sorted_insAll_id l (S ++ [x]) (by simpa using hs)]
    simp

theorem desc_insAll (h : StrictWeakOrder lt) : ∀ (l S : List α),
    l.Pairwise (fun a b => lt b a = true) → (∀ x ∈ l, ∀ s ∈ S, lt x s = true) →
    insAll lt S l = l.reverse ++ S
  | [], S, _, _ => by simp [insAll]
  | x :: l, S, hp, hlS => by
    have hp' := List.pairwise_cons.1 hp
    have hl : ∀ y ∈ l, ∀ s ∈ x :: S, lt y s = true := by
      intro y hy s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · exact hp'.1 y hy
      · exact hlS y (by simp [hy]) s hs
    rw [insAll_cons, ins_lt_all x S (fun s hs => hlS x (by simp) s hs),
      desc_insAll h l (x :: S) hp'.2 hl]
    simp

theorem sortGenericStable : SortGenericStable := by
  intro α _ piv lt hpiv h v
  simp only [sortGeneric, initialOptimizations]
  split
  · exact insertionSortCorrect α lt h v
  · simp only [stableCheckSorted]
    split
    · rename_i hs
      have hp : Sorted lt v.toList :=
        pairwise_of_adj (R := fun a b => lt b a = false) (fun a b c hab hbc => h.ntrans c b a hbc hab)
          v.toList (adj_of_isSortedRange lt v hs)
      rw [sortRef_eq, sorted_insAll_id v.toList [] (by simpa using hp), List.nil_append]
    · split
      · rename_i _ hd
        have hp : v.toList.Pairwise (fun a b => lt b a = true) :=
          pairwise_of_adj (R := fun a b => lt b a = true) (fun a b c hab hbc => h.trans c b a hbc hab)
            v.toList (fun k hk => by simpa using adj_of_isSortedRange _ v hd k hk)
        rw [reverseRange_spec v 1 v.size [] v.toList [] (by simp) (by simp) (by simp), sortRef_eq,
          desc_insAll h v.toList [] hp (by simp)]
        simp
      · exact scratchQuickSortCorrect α piv lt hpiv h v

end

end JuliaLean.Sort

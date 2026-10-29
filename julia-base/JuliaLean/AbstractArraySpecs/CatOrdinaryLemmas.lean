import JuliaLean.AbstractArraySpecs.CatRowsRefute
import JuliaLean.AbstractArraySpecs.IndexProofs

/-!
Lemmas about the column-major enumeration used by the `cat` reference
(`colTuples`, `colIndex`) and the output writes of the `cat` model (`cartProd`,
`outPos`, `storeCells`).
-/

namespace JuliaLean.AbstractArraySpecs

/-- Product of a shape. -/
def pr : List Nat → Nat
  | [] => 1
  | n :: ns => n * pr ns

theorem foldl_mul_eq (l : List Nat) : ∀ a, l.foldl (· * ·) a = a * pr l := by
  induction l with
  | nil => intro a; simp [pr]
  | cons n ns ih => intro a; simp only [List.foldl_cons, pr]; rw [ih]; rw [Nat.mul_assoc]

theorem foldl_mul_one (l : List Nat) : l.foldl (· * ·) 1 = pr l := by
  rw [foldl_mul_eq]; simp

/-- A 0-based index tuple within a shape. -/
def Bnd : List Nat → List Nat → Prop
  | [], [] => True
  | i :: is, n :: ns => i < n ∧ Bnd is ns
  | _, _ => False

theorem Bnd.length : ∀ {t sh : List Nat}, Bnd t sh → t.length = sh.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [Bnd.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem sum_map_const_nat {β : Type} (n : Nat) : ∀ l : List β, (l.map (fun _ => n)).sum = l.length * n
  | [] => by simp
  | _ :: l => by simp only [List.map_cons, List.sum_cons, List.length_cons, sum_map_const_nat n l]; rw [Nat.succ_mul]; omega

theorem colTuples_length : ∀ sh : List Nat, (colTuples sh).length = pr sh
  | [] => rfl
  | n :: ns => by
    simp only [colTuples, pr, List.length_flatMap, List.length_map, List.length_range]
    rw [sum_map_const_nat n (colTuples ns), colTuples_length ns, Nat.mul_comm]

theorem colIndex_lt : ∀ {t sh : List Nat}, Bnd t sh → colIndex t sh < pr sh
  | [], [], _ => by simp [colIndex, pr]
  | i :: is, n :: ns, h => by
    have ih := colIndex_lt h.2
    have hi := h.1
    simp only [colIndex, pr]
    have : n * colIndex is ns + n ≤ n * pr ns := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left n ih
    omega
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem colIndex_inj : ∀ {t t' sh : List Nat}, Bnd t sh → Bnd t' sh →
    colIndex t sh = colIndex t' sh → t = t'
  | [], [], [], _, _, _ => rfl
  | i :: is, i' :: is', n :: ns, h, h', e => by
    simp only [colIndex] at e
    have hn : 0 < n := by have := h.1; omega
    have e1 : (i + n * colIndex is ns) % n = (i' + n * colIndex is' ns) % n := by rw [e]
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.1,
      Nat.mod_eq_of_lt h'.1] at e1
    subst e1
    have e2 : colIndex is ns = colIndex is' ns := by
      have := Nat.add_left_cancel e
      exact Nat.eq_of_mul_eq_mul_left hn this
    rw [colIndex_inj h.2 h'.2 e2]
  | [], [], _ :: _, h, _, _ => h.elim
  | _ :: _, _, [], h, _, _ => h.elim
  | [], _ :: _, [], _, h', _ => h'.elim
  | [], _ :: _, _ :: _, h, _, _ => h.elim
  | _ :: _, [], _ :: _, _, h', _ => h'.elim

/-- Indexing a concatenation of equal-length blocks. -/
theorem getElem?_flatMap_uniform {β γ : Type} (f : β → List γ) (n : Nat) (hn : 0 < n) :
    ∀ (L : List β), (∀ t ∈ L, (f t).length = n) → ∀ k : Nat,
      (L.flatMap f)[k]? = (L[k / n]?).bind (fun t => (f t)[k % n]?)
  | [], _, k => by simp
  | a :: L, hL, k => by
    have ha := hL a (by simp)
    simp only [List.flatMap_cons]
    by_cases hk : k < n
    · rw [List.getElem?_append_left (by omega), Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
      simp
    · rw [List.getElem?_append_right (by omega), ha,
        getElem?_flatMap_uniform f n hn L (fun t ht => hL t (by simp [ht])) (k - n)]
      have h1 : k / n = (k - n) / n + 1 := Nat.div_eq_sub_div hn (by omega)
      have h2 : k % n = (k - n) % n := Nat.mod_eq_sub_mod (by omega)
      rw [h1, h2]
      simp

theorem colTuples_getElem? : ∀ (sh : List Nat) (k : Nat) (hk : k < pr sh),
    ∃ t, (colTuples sh)[k]? = some t ∧ Bnd t sh ∧ colIndex t sh = k
  | [], k, hk => by
    simp only [pr] at hk
    have : k = 0 := by omega
    subst this
    exact ⟨[], rfl, trivial, rfl⟩
  | n :: ns, k, hk => by
    simp only [pr] at hk
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hk
      · exact h
    have hq : k / n < pr ns := by
      rw [Nat.div_lt_iff_lt_mul hn]; rw [Nat.mul_comm]; exact hk
    obtain ⟨u, hu, hub, huc⟩ := colTuples_getElem? ns (k / n) hq
    refine ⟨(k % n) :: u, ?_, ⟨Nat.mod_lt k hn, hub⟩, ?_⟩
    · simp only [colTuples]
      rw [getElem?_flatMap_uniform _ n hn _ (fun t _ => by simp), hu]
      simp [Nat.mod_lt k hn]
    · simp only [colIndex, huc]
      exact Nat.mod_add_div k n

theorem colTuples_at {t sh : List Nat} (h : Bnd t sh) : (colTuples sh)[colIndex t sh]? = some t := by
  obtain ⟨t', ht', hb', hc'⟩ := colTuples_getElem? sh (colIndex t sh) (colIndex_lt h)
  rw [ht', colIndex_inj hb' h hc']

theorem colTuples_get_bnd {sh : List Nat} {k : Nat} (hk : k < (colTuples sh).length) :
    Bnd (colTuples sh)[k] sh ∧ colIndex (colTuples sh)[k] sh = k := by
  rw [colTuples_length] at hk
  obtain ⟨t, ht, hb, hc⟩ := colTuples_getElem? sh k hk
  rw [List.getElem?_eq_some_iff] at ht
  obtain ⟨_, ht⟩ := ht
  rw [ht]; exact ⟨hb, hc⟩

/-! ## Folding stores -/

/-- The value a fold of stores leaves at position `p`, starting from `init`. -/
def hitVal {β κ : Type} (pos : κ → Nat) (n p : Nat) (init : Option (Option β)) (L : List (κ × β)) :
    Option (Option β) :=
  L.foldl (fun acc tv => if pos tv.1 = p then (if p < n then some (some tv.2) else none) else acc) init

theorem foldl_set_getElem? {β κ : Type} (pos : κ → Nat) (p : Nat) :
    ∀ (L : List (κ × β)) (C : List (Option β)),
      (L.foldl (fun cs tv => cs.set (pos tv.1) (some tv.2)) C)[p]? = hitVal pos C.length p C[p]? L
  | [], C => rfl
  | q :: L, C => by
    simp only [List.foldl_cons]
    rw [foldl_set_getElem? pos p L (C.set (pos q.1) (some q.2)), List.length_set, List.getElem?_set]
    unfold hitVal
    simp only [List.foldl_cons]
    congr 1
    by_cases h : pos q.1 = p
    · subst h; simp
    · simp [h]

theorem foldl_set_length {β κ : Type} (pos : κ → Nat) :
    ∀ (L : List (κ × β)) (C : List (Option β)),
      (L.foldl (fun cs tv => cs.set (pos tv.1) (some tv.2)) C).length = C.length
  | [], C => rfl
  | q :: L, C => by
    simp only [List.foldl_cons]
    rw [foldl_set_length pos L, List.length_set]

theorem hitVal_none {β κ : Type} (pos : κ → Nat) (n p : Nat) :
    ∀ (L : List (κ × β)) init, (∀ q ∈ L, pos q.1 ≠ p) → hitVal pos n p init L = init
  | [], _, _ => rfl
  | q :: L, init, h => by
    simp only [hitVal, List.foldl_cons]
    rw [if_neg (h q (by simp))]
    exact hitVal_none pos n p L init (fun q' hq' => h q' (by simp [hq']))

theorem hitVal_unique {β κ : Type} (pos : κ → Nat) (n p : Nat) (hp : p < n) (L : List (κ × β)) (k : Nat)
    (hk : k < L.length) (hpos : ∀ j (hj : j < L.length), pos L[j].1 = p ↔ j = k) (init) :
    hitVal pos n p init L = some (some L[k].2) := by
  have hsplit : L = L.take k ++ L[k] :: L.drop (k + 1) := by simp
  have hdrop : ∀ q ∈ L.drop (k + 1), pos q.1 ≠ p := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    rw [List.getElem_drop]
    intro e
    have := (hpos (k + 1 + j) (by simp at hj; omega)).mp e
    omega
  have e := congrArg (hitVal pos n p init) hsplit
  rw [e]
  unfold hitVal
  rw [List.foldl_append, List.foldl_cons]
  have := hitVal_none pos n p (L.drop (k + 1))
    (if pos L[k].1 = p then (if p < n then some (some L[k].2) else none) else
      (L.take k).foldl (fun acc tv => if pos tv.1 = p then (if p < n then some (some tv.2) else none) else acc) init)
    hdrop
  unfold hitVal at this
  rw [this, if_pos ((hpos k hk).mpr rfl), if_pos hp]

/-- A store fold writes the value at the unique tuple targeting a cell. -/
theorem storeCells_unique {β : Type} (A : CatOut β) (tuples : List (List I64))
    (vs : List β) (p k : Nat) (hp : p < A.cells.length)
    (hk : k < (tuples.zip vs).length)
    (hpos : ∀ j (hj : j < (tuples.zip vs).length),
      (outPos (tuples.zip vs)[j].1 A.shape).toNat = p ↔ j = k) :
    (storeCells A tuples vs)[p]? = some (some (tuples.zip vs)[k].2) := by
  unfold storeCells
  rw [foldl_set_getElem? (fun t => (outPos t A.shape).toNat) p]
  exact hitVal_unique (fun t => (outPos t A.shape).toNat) A.cells.length p hp
    (tuples.zip vs) k hk hpos A.cells[p]?

/-! ## `mapM` in `Except` -/

theorem mapM_ok {α β : Type} (conv : α → R β) (g : α → β) :
    ∀ (l : List α), (∀ v ∈ l, conv v = .ok (g v)) → l.mapM conv = .ok (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a (by simp), mapM_ok conv g l (fun v hv => h v (by simp [hv]))]
    rfl

/-- The `vcat` contract restricted to arrays with 1-based axes. -/
def VcatAnyOrdinarySpec : Prop :=
  ∀ {α : Type} (zero : α) (X : List (Item α)), CatPre [true] X →
    anyOffset X = false →
    CatAgrees X (vcatAny zero X) (refCat id zero [true] X)

/-- An empty vector followed by a matrix still has incompatible non-cat sizes. -/
def ordinaryEmptyVector : Arr Int := ⟨[oneTo (i64 0)], .linear, []⟩
def ordinaryMatrix : Arr Int :=
  ⟨[oneTo (i64 2), oneTo (i64 3)], .linear, [1, 2, 3, 4, 5, 6]⟩

theorem vcatAnyOrdinarySpec_refuted : ¬ VcatAnyOrdinarySpec := by
  intro h
  have bad := h (0 : Int) [.arr ordinaryEmptyVector, .arr ordinaryMatrix] (by
    refine ⟨by simp, ?_, ?_⟩
    · wf_items
    · intro s hs
      cases hs) (by decide)
  revert bad
  decide

/-- The typed vertical concatenation contract for 1-based arrays. -/
def TypedVcatAnyOrdinarySpec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β) (X : List (Item α)),
    CatPre [true] X → anyOffset X = false → ConvOK conv g X →
    CatAgrees X (typedVcatAny conv zero X) (refCat g zero [true] X)

theorem typedVcatAnyOrdinarySpec_refuted : ¬ TypedVcatAnyOrdinarySpec := by
  intro h
  have bad := h (fun x => (.ok x : R Int)) id 0
    [.arr ordinaryEmptyVector, .arr ordinaryMatrix] (by
      refine ⟨by simp, ?_, ?_⟩
      · wf_items
      · intro s hs
        cases hs) (by decide) (conv_id _)
  revert bad
  decide


/-- The `_cat` contract restricted to 1-based arrays. -/
def CatPromoteOrdinarySpec : Prop :=
  ∀ {α : Type} (zero : α) (dims : List Int) (X : List (Item α)),
    DimsOK dims → CatPre (flagsOf dims) X → anyOffset X = false →
    CatAgrees X (catPromote zero dims X) (refCat id zero (flagsOf dims) X)

theorem catPromoteOrdinarySpec_refuted : ¬ CatPromoteOrdinarySpec := by
  intro h
  have bad := h (0 : Int) [1] [.arr ordinaryEmptyVector, .arr ordinaryMatrix]
    (by simp [DimsOK]) (by
      refine ⟨by simp, ?_, ?_⟩
      · wf_items
      · intro s hs
        cases hs) (by decide)
  revert bad
  decide

/-- The `cat_t` contract restricted to 1-based arrays. -/
def CatTKwOrdinarySpec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β)
    (X : List (Item α)) (dims : List Int), DimsOK dims →
    CatPre (flagsOf dims) X → anyOffset X = false → ConvOK conv g X →
    CatAgrees X (catTKw conv zero X dims) (refCat g zero (flagsOf dims) X)

theorem catTKwOrdinarySpec_refuted : ¬ CatTKwOrdinarySpec := by
  intro h
  have bad := h (fun x => (.ok x : R Int)) id 0
    [.arr ordinaryEmptyVector, .arr ordinaryMatrix] [1] (by simp [DimsOK]) (by
      refine ⟨by simp, ?_, ?_⟩
      · wf_items
      · intro s hs
        cases hs) (by decide) (conv_id _)
  revert bad
  decide

/-- The two-array `vcat` contract restricted to 1-based arrays. -/
def Vcat2OrdinarySpec : Prop :=
  ∀ {α : Type} (zero : α) (A B : Arr α), CatPre [true] [.arr A, .arr B] →
    anyOffset [.arr A, .arr B] = false →
    CatAgrees [.arr A, .arr B] (vcat2 zero A B) (refCat id zero [true] [.arr A, .arr B])

theorem vcat2OrdinarySpec_refuted : ¬ Vcat2OrdinarySpec := by
  intro h
  have bad := h (0 : Int) ordinaryEmptyVector ordinaryMatrix (by
    refine ⟨by simp, ?_, ?_⟩
    · wf_items
    · intro s hs
      cases hs) (by decide)
  revert bad
  decide

/-- The two-array typed `vcat` contract restricted to 1-based arrays. -/
def TypedVcat2OrdinarySpec : Prop :=
  ∀ {α β : Type} (conv : α → R β) (g : α → β) (zero : β) (A B : Arr α),
    CatPre [true] [.arr A, .arr B] → anyOffset [.arr A, .arr B] = false →
    ConvOK conv g [.arr A, .arr B] →
    CatAgrees [.arr A, .arr B] (typedVcat2 conv zero A B) (refCat g zero [true] [.arr A, .arr B])

theorem typedVcat2OrdinarySpec_refuted : ¬ TypedVcat2OrdinarySpec := by
  intro h
  have bad := h (fun x => (.ok x : R Int)) id 0 ordinaryEmptyVector ordinaryMatrix
    (by
      refine ⟨by simp, ?_, ?_⟩
      · wf_items
      · intro s hs
        cases hs) (by decide) (conv_id _)
  revert bad
  decide

end JuliaLean.AbstractArraySpecs
